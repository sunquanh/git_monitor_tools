#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Git 仓库监控器 Web 版 - Flask 后端
复用 git_monitor.py 的 Git 操作函数，通过 REST API 暴露
"""
import os
import sys
import json
import re
import queue
import shutil
import signal
import tempfile
import atexit
import subprocess
import threading
import time
import webbrowser
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime
from collections import Counter
# 零依赖路由层：标准库 http.server 实现的迷你 Flask（离线机无需 pip install）
from flask_compat import Flask, jsonify, request, send_from_directory, Response, HTTPException
import logging

# 复用 git_monitor 的核心函数
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import git_monitor as gm

app = Flask(__name__, static_folder='web', static_url_path='')

# Windows: 子进程创建标志（CREATE_NO_WINDOW）。无控制台运行时（pythonw / 计划任务 /
# 分离进程），git/tasklist/wmic 等控制台子进程每次执行都会闪一个 CMD 窗口，
# 该标志阻止弹窗；有控制台时无副作用。POSIX 上为 0。
_SUBPROC_FLAGS = 0x08000000 if os.name == 'nt' else 0  # CREATE_NO_WINDOW

# Suppress Flask access logs, only show errors
log = logging.getLogger('werkzeug')
log.setLevel(logging.ERROR)

# ============================================================
# 危险操作审计日志
# ============================================================
# 追加写 JSONL（一行一条），不参与任何业务逻辑；写失败只吞掉，绝不影响主流程。
# 覆盖范围由 after_request 统一接管：所有写方法（POST/PUT/PATCH/DELETE）只要命中
# /api/... 就记一条，不再依赖每条路由记得手工调用 —— 避免"新增了危险接口但忘了审计"。
AUDIT_PATH = os.path.join(gm._BASE, 'git_monitor_audit.jsonl')
_AUDIT_LOCK = threading.Lock()
AUDIT_MAX_BYTES = 5 * 1024 * 1024   # 单文件上限，超过就轮转
AUDIT_KEEP = 3                      # 保留 .1 / .2 两份历史
# 只读的 POST（取 diff、校验补丁）不写审计，否则日志会被刷新动作刷满
_AUDIT_SKIP = {'diff', 'check', 'preview'}


def _rotate_audit_locked():
    """调用方必须已持有 _AUDIT_LOCK。按大小轮转，避免长期运行后单文件无限膨胀。"""
    try:
        if os.path.getsize(AUDIT_PATH) < AUDIT_MAX_BYTES:
            return
    except OSError:
        return
    for i in range(AUDIT_KEEP - 1, 0, -1):
        src = f'{AUDIT_PATH}.{i}'
        if os.path.exists(src):
            try:
                os.replace(src, f'{AUDIT_PATH}.{i + 1}')
            except OSError:
                pass
    try:
        os.replace(AUDIT_PATH, f'{AUDIT_PATH}.1')
    except OSError:
        pass


def _audit(op, repo, detail='', ok=True):
    """追加一条审计记录。
    src 取真实 TCP 对端地址（client_address），**不再信任 X-Forwarded-For** ——
    那个头任意客户端都能伪造；若存在则单独记到 xff 字段仅作参考。"""
    try:
        rec = {
            'time': time.strftime('%Y-%m-%d %H:%M:%S'),
            'op': op,
            'repo': repo,
            'detail': str(detail)[:300],
            'ok': bool(ok),
            'src': getattr(request, 'remote_addr', '') or 'local',
        }
        xff = request.headers.get('X-Forwarded-For')
        if xff:
            rec['xff'] = xff[:80]
        line = json.dumps(rec, ensure_ascii=False)
        with _AUDIT_LOCK:
            _rotate_audit_locked()
            with open(AUDIT_PATH, 'a', encoding='utf-8') as f:
                f.write(line + '\n')
        # 标记本次请求已手工记过账，after_request 的自动审计就不再重复写一条
        _repo_op_local.audited = True
    except Exception:
        pass  # 审计失败不影响操作本身


def _audit_request():
    """after_request 里统一记账：写方法 + /api/ 路径就落审计。
    op 取路径尾段（repo 级操作形如 push / stash/save），成功与否优先看响应体的 ok。
    路由里已手工调用过 _audit 的（能写更具体的 detail）不重复记录。"""
    try:
        if request.method not in ('POST', 'PUT', 'DELETE', 'PATCH'):
            return
        if getattr(_repo_op_local, 'audited', False):
            return
        path = request.path or ''
        if not path.startswith('/api/'):
            return
        parts = [p for p in path[len('/api/'):].split('/') if p]
        if not parts or any(p in _AUDIT_SKIP for p in parts):
            return
        if parts[0] in ('repo', 'workspace') and len(parts) >= 3:
            repo, op = parts[1], '/'.join(parts[2:])
        else:
            repo, op = '', '/'.join(parts)
        status, _headers, payload = request.result or (500, {}, b'')
        ok, detail = status < 400, ''
        if isinstance(payload, (bytes, bytearray)):
            try:
                body = json.loads(payload.decode('utf-8'))
                if isinstance(body, dict):
                    if 'ok' in body:
                        ok = ok and bool(body['ok'])
                    detail = body.get('output') or body.get('error') or ''
            except Exception:
                pass
        _audit(op, repo, str(detail).replace('\n', ' ')[:200], ok)
    except Exception:
        pass  # 审计绝不打断响应

# ============================================================
# 资源清理：进程退出时优雅关闭 watchdog/SSE/线程池
# ============================================================
_observer = None  # watchdog Observer 引用
_cleanup_done = False
_cleanup_lock = threading.Lock()

def cleanup():
    """进程退出时清理所有资源"""
    global _cleanup_done
    with _cleanup_lock:
        if _cleanup_done:
            return
        _cleanup_done = True
    # 1. 停止 watchdog Observer
    if _observer:
        try:
            _observer.stop()
            _observer.join(timeout=5)
        except Exception:
            pass
    # 2. 关闭所有 SSE 连接（发送 None 结束信号）
    # globals().get 防御：模块导入中途崩溃时 _sse_lock 可能尚未定义
    _lock = globals().get('_sse_lock')
    if _lock is None:
        return
    with _lock:
        for q in list(SSE_CLIENTS):
            try:
                q.put_nowait(None)
            except Exception:
                pass
        SSE_CLIENTS.clear()
    # 3. 清理脏标记定时器
    with _dirty_lock:
        if _dirty_timer:
            try:
                _dirty_timer.cancel()
            except Exception:
                pass
    # 4. 关闭共享线程池（不等待长任务，避免退出卡住）
    _ex = globals().get('_STATUS_EXECUTOR')
    if _ex is not None:
        try:
            _ex.shutdown(wait=False)
        except Exception:
            pass
    print('[cleanup] 资源已释放')

atexit.register(cleanup)

def signal_handler(sig, frame):
    """信号处理：优雅退出"""
    cleanup()
    sys.exit(0)

signal.signal(signal.SIGINT, signal_handler)    # Ctrl+C
if hasattr(signal, 'SIGBREAK'):
    # Windows：Ctrl+Break / 控制台关闭会走 SIGBREAK；配合启动脚本里
    # "命令行含 git_web.py 才定点清理" 的兜底，正常/异常退出都不会残留进程
    signal.signal(signal.SIGBREAK, signal_handler)
if hasattr(signal, 'SIGTERM'):
    signal.signal(signal.SIGTERM, signal_handler)

# ============================================================
# 扩展函数（当前 git_monitor.py 缺少的功能）
# ============================================================
def get_repo_size_info(repo_path):
    """仓库体积信息"""
    if not os.path.isdir(repo_path):
        return {}
    out, rc = gm.git(repo_path, 'count-objects', '-vH')
    if rc != 0:
        return {}
    info = {}
    for line in out.splitlines():
        if ':' in line:
            k, v = line.split(':', 1)
            info[k.strip()] = v.strip()
    def _num(k):
        try:
            return int(str(info.get(k, '0')).replace(',', '').split()[0])
        except:
            return 0
    return {
        'count': _num('count'),
        'size': info.get('size', '0'),
        'in_pack': _num('in-pack'),
        'size_pack': info.get('size-pack', '0'),
    }

def get_largest_files(repo_path, n=10, since_commits=5000):
    """历史中体积最大的文件 Top N（限制范围避免大仓库OOM）"""
    try:
        # 只扫描最近 N 个 commit，避免全量遍历
        objs_out, rc = gm.git(repo_path, 'rev-list', '--objects', '--max-count=' + str(since_commits), 'HEAD')
        if rc != 0:
            # fallback: 如果没有 HEAD（空仓库），返回空
            return []
        hash_path = {}
        for line in objs_out.splitlines():
            parts = line.split(' ', 1)
            if len(parts) == 2:
                hash_path[parts[0]] = parts[1]
        if not hash_path:
            return []
        # 批量查大小
        import subprocess
        p = subprocess.run(
            ['git', '-C', repo_path, 'cat-file', '--batch-check'],
            input='\n'.join(hash_path.keys()) + '\n',
            capture_output=True, text=True, encoding='utf-8',
            errors='replace', timeout=120, creationflags=_SUBPROC_FLAGS,
            env=gm._git_env())
        sizes = {}
        for line in p.stdout.splitlines():
            parts = line.split()
            if len(parts) >= 3 and parts[1] == 'blob':
                try:
                    sizes[parts[0]] = int(parts[2])
                except:
                    pass
        path_size = {}
        for h, pth in hash_path.items():
            s = sizes.get(h)
            if s is not None:
                path_size[pth] = max(path_size.get(pth, 0), s)
        top = sorted(path_size.items(), key=lambda x: -x[1])[:n]
        return [{'path': p, 'size': s} for p, s in top]
    except Exception as e:
        log.warning('get_largest_files 失败: %s', e)
        return []

def get_fsck_unreachable(repo_path):
    """悬空对象统计"""
    if not os.path.isdir(repo_path):
        return 0, {}
    out, rc = gm.git(repo_path, 'fsck', '--unreachable', timeout=60)
    if rc != 0:
        return 0, {}
    import re
    total = 0
    kinds = {}
    for line in out.splitlines():
        m = re.match(r'unreachable (\w+)', line)
        if m:
            total += 1
            kinds[m.group(1)] = kinds.get(m.group(1), 0) + 1
    return total, kinds

def get_file_history(repo_path, path):
    """文件历史追踪"""
    out, _ = gm.git(repo_path, 'log', '--follow', '--format=%H|%an|%ai|%s', '--', path)
    return gm.parse_log(out)

# ============================================================
# 配置（统一走 git_monitor 的加载/归一化/原子写盘，
# 避免配置缺失时把 DEFAULT_CONFIG 里的示例仓库路径写回用户配置）
# ============================================================
CONFIG_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'git_monitor.json')

def normalize_cfg_integrity(cfg):
    """清理配置里的失效引用（分组成员 / compare.repo / 通知仓库）。
    历史脏数据会让前端筛选永远匹配不到仓库。"""
    if not isinstance(cfg, dict):
        cfg = {}
    repos = cfg.get('repos') or {}
    groups = cfg.get('groups') or {}
    new_groups = {}
    for gname, members in groups.items():
        if not isinstance(members, list):
            continue
        valid = [m for m in members if m in repos]
        if valid:
            new_groups[gname] = valid
    cfg['groups'] = new_groups
    compare = dict(cfg.get('compare') or {})
    cr = compare.get('repo')
    if cr and cr not in repos:
        first = next(iter(repos), None)
        if first:
            compare['repo'] = first
        else:
            compare['enabled'] = False
        cfg['compare'] = compare
    if isinstance(cfg.get('notify_repos'), list):
        cfg['notify_repos'] = [x for x in cfg['notify_repos'] if x in repos]
    return cfg


def load_config():
    cfg = gm.load_config()
    return normalize_cfg_integrity(cfg)

CFG = load_config()
# REPOS 只作「整表替换」，禁止 in-place clear/update（多线程迭代会炸）
REPOS = dict(CFG.get('repos') or {})
CFG['repos'] = REPOS
REFRESH_INTERVAL = CFG.get('refresh_interval', 30)

_REPO_LOCKS = {}
_REPO_LOCKS_GUARD = threading.Lock()
_repo_op_local = threading.local()
_STATUS_CACHE = {}
_STATUS_CACHE_LOCK = threading.Lock()
_STATUS_CACHE_TTL = 5.0
_SSE_CLIENT_LIMIT = 8
# 共享线程池：避免每次 /api/repos 都新建/销毁线程池
_STATUS_EXECUTOR = ThreadPoolExecutor(max_workers=8)


def _get_repo_lock(name):
    with _REPO_LOCKS_GUARD:
        lock = _REPO_LOCKS.get(name)
        if lock is None:
            lock = threading.RLock()
            _REPO_LOCKS[name] = lock
        return lock


def _repos_snapshot():
    return dict(REPOS)


def _install_repos(new_repos):
    """写时复制替换 REPOS：不对共享字典 clear/update，避免遍历竞态。"""
    global REPOS
    cleaned = {str(k): str(v) for k, v in (new_repos or {}).items()}
    REPOS = cleaned
    CFG['repos'] = cleaned
    with _STATUS_CACHE_LOCK:
        for key in list(_STATUS_CACHE):
            if key not in cleaned:
                _STATUS_CACHE.pop(key, None)
    return cleaned


def invalidate_status_cache(name=None):
    with _STATUS_CACHE_LOCK:
        if name is None:
            _STATUS_CACHE.clear()
        else:
            _STATUS_CACHE.pop(name, None)


def _fetch_status_one(name, path):
    try:
        st = gm.get_status(path)
        st['name'] = name
        st['path'] = path
        return name, st
    except Exception as e:
        return name, {'invalid': True, 'error': str(e), 'name': name}


def _status_map_parallel(repos=None, max_age=0.0):
    """并行拉取多仓库状态；max_age>0 时优先用短 TTL 缓存。"""
    targets = _repos_snapshot() if repos is None else dict(repos)
    result = {}
    if not targets:
        return result
    pending = {}
    for name, path in targets.items():
        if max_age > 0:
            now = time.time()
            with _STATUS_CACHE_LOCK:
                item = _STATUS_CACHE.get(name)
                if item and item[2] == path and (now - item[0]) < max_age:
                    result[name] = item[1]
                    continue
        pending[name] = path
    if not pending:
        return result
    futs = {_STATUS_EXECUTOR.submit(_fetch_status_one, n, p): (n, p)
            for n, p in pending.items()}
    for fut in futs:
        name, path = futs[fut]
        name, st = fut.result()
        result[name] = st
        with _STATUS_CACHE_LOCK:
            _STATUS_CACHE[name] = (time.time(), st, path)
    return result


def _normalize_file_entries(files):
    """把前端 files 统一成 ws_discard 需要的 dict 列表。"""
    if files is None:
        return []
    if isinstance(files, (str, bytes)):
        files = [files]
    if isinstance(files, dict):
        files = [files]
    normalized = []
    for item in files or []:
        if isinstance(item, dict):
            path = str(item.get('path') or '')
            normalized.append({
                'path': path,
                'untracked': bool(item.get('untracked')),
                'staged': bool(item.get('staged')),
            })
        else:
            path = str(item or '')
            normalized.append({'path': path, 'untracked': False, 'staged': False})
    return normalized


_REPO_WRITE_LOCK_RE = re.compile(r'^/api/(?:repo|workspace)/([^/]+)')


@app.before_request
def _acquire_repo_write_lock():
    """同仓库写操作串行化：POST/PUT/DELETE/PATCH 按仓库名加锁。"""
    if request.method not in ('POST', 'PUT', 'DELETE', 'PATCH'):
        return None
    _repo_op_local.audited = False  # 每次写请求重置，供 after_request 去重
    m = _REPO_WRITE_LOCK_RE.match(request.path or '')
    if not m:
        return None
    name = m.group(1)
    lock = _get_repo_lock(name)
    if not lock.acquire(timeout=45):
        return jsonify({'ok': False, 'error': '仓库操作繁忙，请稍后再试',
                        'output': '仓库操作繁忙，请稍后再试'}), 429
    _repo_op_local.lock = lock
    _repo_op_local.name = name
    return None


@app.after_request
def _release_repo_write_lock():
    name = getattr(_repo_op_local, 'name', None)
    if name:
        invalidate_status_cache(name)
    lock = getattr(_repo_op_local, 'lock', None)
    if lock is not None:
        try:
            lock.release()
        except RuntimeError:
            pass
    _repo_op_local.lock = None
    _repo_op_local.name = None
    # 统一审计：放在锁释放之后，审计 IO 不占着仓库锁
    _audit_request()


def safe_repo_path(repo_path, rel):
    """校验相对路径不越出仓库根（防 ../ 穿越 + 符号链接攻击）。
    合法返回规范化绝对路径，否则返回 None。"""
    if not rel:
        return None
    parts = [p for p in str(rel).replace('\\', '/').split('/') if p not in ('', '.')]
    if not parts or any(p == '..' for p in parts):
        return None
    root = os.path.realpath(repo_path)
    # 检查仓库根目录本身是否是符号链接（防止通过 symlink 指向外部）
    if os.path.islink(repo_path):
        return None
    full = os.path.realpath(os.path.join(root, *parts))
    try:
        inside = os.path.commonpath([root, full]) == root
    except ValueError:
        return None
    if not inside:
        return None
    # 检查路径中是否有符号链接指向仓库外部
    check_path = root
    for part in parts:
        check_path = os.path.join(check_path, part)
        if os.path.islink(check_path):
            real_target = os.path.realpath(check_path)
            try:
                if os.path.commonpath([root, real_target]) != root:
                    return None
            except ValueError:
                return None
    return full


def validate_rel_paths(repo_path, paths):
    """批量校验，返回 (合法路径列表, 非法路径列表)"""
    ok, bad = [], []
    for p in paths or []:
        (ok.append(p) if safe_repo_path(repo_path, p) else bad.append(p))
    return ok, bad


def _no_dash(*vals):
    """拒绝以 '-' 开头的用户输入：subprocess 列表传参无 shell 注入，
    但 git 会把 '-xxx' 解析成自己的选项（如 branch='--all'、target='--orphan'）。
    分支名/标签名/ref 本来就不允许以 '-' 开头，直接在路由层挡掉。"""
    for v in vals:
        if v is None:
            continue
        s = str(v).strip()
        if s.startswith('-'):
            return False
    return True

# ============================================================
# 静态文件
# ============================================================
@app.route('/')
def index():
    return send_from_directory('web', 'index.html')

@app.route('/<path:path>')
def static_files(path):
    return send_from_directory('web', path)


# 统一错误出口：未捕获异常返回 JSON 而不是 Flask 的 HTML 500 页
# HTTPException 已由 flask_compat 提供


@app.errorhandler(HTTPException)
def _http_error(e):
    return jsonify({'error': e.description}), e.code


# ============================================================
# 本机服务安全：Host 白名单 + 写操作需自定义头
# 服务只绑定 127.0.0.1，但浏览器里任意网页都能向 127.0.0.1 发跨站请求：
# - Host 白名单 → 挡 DNS rebinding（恶意域名解析到 127.0.0.1 后 Host 不匹配）
# - 写操作校验 X-Requested-With 自定义头 → 跨站表单/fetch 带不了自定义头
#   （会触发 CORS 预检并被拒），挡住 CSRF；前端 api() 统一携带该头。
# ============================================================
_ALLOWED_HOSTS = {'127.0.0.1', 'localhost'}


@app.before_request
def _local_guard():
    host = (request.host or '').split(':')[0].lower()
    if host not in _ALLOWED_HOSTS:
        return jsonify({'error': '非法 Host，请通过 http://127.0.0.1 访问'}), 403
    if request.method in ('POST', 'PUT', 'DELETE', 'PATCH'):
        if request.headers.get('X-Requested-With') != 'XMLHttpRequest':
            return jsonify({'error': '缺少安全头，已拒绝跨站请求'}), 403
        # 同源校验：浏览器跨站 fetch 即使带自定义头，Origin 也会是外站/ null
        origin = (request.headers.get('Origin') or request.headers.get('Referer') or '').strip()
        if origin:
            from urllib.parse import urlparse
            oh = (urlparse(origin).hostname or '').lower()
            if oh and oh not in _ALLOWED_HOSTS:
                return jsonify({'error': '非法 Origin，已拒绝'}), 403
    return None


@app.errorhandler(Exception)
def _unhandled_error(e):
    log.warning('API 未处理异常: %s', e)
    # 脱敏：不返回完整错误信息给前端
    msg = str(e)
    # 隐藏文件路径
    import re as _re
    msg = _re.sub(r'[A-Z]:\\[\\\w./-]+', '<路径>', msg)
    msg = _re.sub(r'/[\w./-]{10,}', '<路径>', msg)
    return jsonify({'error': msg[:200]}), 500


# ============================================================
# 实时推送：文件监听（watchdog，可选依赖）+ SSE
# 仓库文件变化 → 防抖 1s → 推送最新状态给所有浏览器，替代高频轮询
# ============================================================
try:
    from watchdog.observers import Observer
    from watchdog.events import FileSystemEventHandler
    WATCHDOG_OK = True
except Exception:
    WATCHDOG_OK = False

SSE_CLIENTS = []
_sse_lock = threading.Lock()  # 保护 SSE_CLIENTS 的并发读写
_dirty = set()
_dirty_lock = threading.Lock()
_dirty_timer = None
_dirty_timer_lock = threading.Lock()  # 保护 _dirty_timer 的检查和赋值


def broadcast(obj):
    with _sse_lock:
        dead = []
        for q in list(SSE_CLIENTS):
            try:
                q.put_nowait(obj)
            except Exception:
                dead.append(q)
        for q in dead:
            try:
                SSE_CLIENTS.remove(q)
            except Exception:
                pass


def _flush_dirty():
    global _dirty_timer
    with _dirty_lock:
        names = list(_dirty)
        _dirty.clear()
    snap = _repos_snapshot()
    targets = {n: snap[n] for n in names if n in snap}
    if targets:
        status_map = _status_map_parallel(targets)
        for n in names:
            st = status_map.get(n)
            if st is None:
                p = snap.get(n)
                if not p:
                    continue
                st = {'invalid': True, 'error': '仓库已移除', 'name': n}
            broadcast({'type': 'repo', 'status': st})
    # 自重置：flush 结束后检查是否有新事件进来，有则重新调度，避免双 Timer 并发
    with _dirty_timer_lock:
        if _dirty:
            _dirty_timer = threading.Timer(1.0, _flush_dirty)
            _dirty_timer.daemon = True
            _dirty_timer.start()
        else:
            _dirty_timer = None


def mark_dirty(name):
    global _dirty_timer
    with _dirty_lock:
        _dirty.add(name)
    with _dirty_timer_lock:
        if _dirty_timer:
            return
        _dirty_timer = threading.Timer(1.0, _flush_dirty)
        _dirty_timer.daemon = True
        _dirty_timer.start()


if WATCHDOG_OK:
    # 高噪音目录：.git 内部对象读写、依赖目录、构建产物 —— 不触发状态刷新
    _WATCH_IGNORE_PARTS = ('.git', 'node_modules', '__pycache__', '.idea', '.vscode',
                           'dist', 'build', 'target', 'vendor')

    class _RepoHandler(FileSystemEventHandler):
        def __init__(self, name):
            self.name = name

        def on_any_event(self, event):
            p = str(getattr(event, 'src_path', '') or '').replace('\\', '/').lower()
            if any(f'/{part}/' in p or p.endswith(f'/{part}') for part in _WATCH_IGNORE_PARTS):
                return
            mark_dirty(self.name)


def start_repo_watchers():
    """启动文件监听（watchdog 缺失或失败时静默退回前端轮询）"""
    global _observer
    if not WATCHDOG_OK:
        print('[watchdog] 未安装（pip install watchdog），退回 30s 轮询')
        return
    try:
        obs = Observer()
        n = 0
        for name, path in _repos_snapshot().items():
            if os.path.isdir(path):
                obs.schedule(_RepoHandler(name), path, recursive=True)
                n += 1
        obs.daemon = True
        obs.start()
        _observer = obs  # 保存引用，退出时清理
        print(f'[watchdog] 实时监听 {n} 个仓库')
    except Exception as e:
        print(f'[watchdog] 启动失败，退回轮询: {e}')


_observer_restart_lock = threading.Lock()


def restart_repo_watchers():
    """仓库列表变化后重建监听（增删仓库、config 热更新 repos 时调用）。
    watchdog 未安装时是空操作；单实例工具，用锁防并发重建。"""
    if not WATCHDOG_OK:
        return
    with _observer_restart_lock:
        global _observer
        if _observer:
            try:
                _observer.stop()
                _observer.join(timeout=3)
            except Exception:
                pass
            _observer = None
        start_repo_watchers()


@app.route('/api/events')
def api_events():
    """SSE：实时推送仓库状态变化；15s 心跳保活。限制客户端数，避免长连接占满线程池。"""
    def gen():
        q = queue.Queue()
        with _sse_lock:
            if len(SSE_CLIENTS) >= _SSE_CLIENT_LIMIT:
                # 淘汰最早的一个，避免浏览器多开标签把 ThreadingHTTPServer 线程耗尽
                try:
                    old = SSE_CLIENTS.pop(0)
                    old.put_nowait(None)
                except Exception:
                    pass
            SSE_CLIENTS.append(q)
        try:
            yield 'retry: 3000\n\n'
            while True:
                try:
                    obj = q.get(timeout=15)
                    if obj is None:  # 清理信号
                        break
                    yield f"data: {json.dumps(obj, ensure_ascii=False)}\n\n"
                except queue.Empty:
                    yield ': ping\n\n'
        finally:
            with _sse_lock:
                try:
                    SSE_CLIENTS.remove(q)
                except Exception:
                    pass
    return Response(gen(), mimetype='text/event-stream',
                    headers={'Cache-Control': 'no-cache', 'X-Accel-Buffering': 'no'})

# ============================================================
# 统一内存限流器（线程安全滑动窗口）
# 单次间隔限流 = max_hits 1；grep 刷量限流 = max_hits 30 / 60s
# ============================================================
class _RateLimiter:
    """线程安全的滑动窗口限流器。默认 max_hits 次 / window 秒；
    is_limited 支持按调用覆盖，便于不同接口复用同一实现。"""

    def __init__(self, max_hits=30, window=60):
        self.max_hits = max_hits
        self.window = window
        self._hits = {}
        self._lock = threading.Lock()

    def is_limited(self, key, max_hits=None, window=None):
        max_hits = self.max_hits if max_hits is None else max_hits
        window = self.window if window is None else window
        now = time.time()
        with self._lock:
            hits = [t for t in self._hits.get(key, []) if now - t < window]
            if len(hits) >= max_hits:
                self._hits[key] = hits
                return True
            hits.append(now)
            self._hits[key] = hits
            return False

    def reset(self, key):
        with self._lock:
            self._hits.pop(key, None)


_global_limiter = _RateLimiter()


def rate_limit(key, min_interval=30):
    """简单限流：同一 key 在 min_interval 秒内只允许调用一次"""
    return not _global_limiter.is_limited(key, max_hits=1, window=min_interval)


def rate_limit_release(key):
    """释放限流窗口：重操作失败（异常）时调用，避免失败也锁 60 秒"""
    _global_limiter.reset(key)

# ============================================================
# 仓库状态 API
# ============================================================
@app.route('/api/repos')
def api_repos():
    """获取所有仓库状态（并行 + 短 TTL 缓存，避免多仓串行拖死刷新）"""
    return jsonify(_status_map_parallel(_repos_snapshot(), max_age=_STATUS_CACHE_TTL))

# ============================================================
# 仓库管理：界面化增删监控仓库（离线机不用再手改 git_monitor.json）
# ============================================================
def _is_git_repo(path):
    """/.git 存在（目录或 worktree 文件）即视为 Git 仓库"""
    return os.path.isdir(os.path.join(path, '.git')) or os.path.isfile(os.path.join(path, '.git'))


@app.route('/api/repos/add', methods=['POST'])
def api_repo_add():
    """添加监控仓库：校验名称唯一 + 路径存在且是 Git 仓库，成功即生效并写盘"""
    data = request.get_json(silent=True) or {}
    name = str(data.get('name', '') or '').strip()
    path = str(data.get('path', '') or '').strip().rstrip('\\')
    if not name or not path:
        return jsonify({'ok': False, 'output': '仓库名和路径都不能为空'}), 400
    if name in REPOS:
        return jsonify({'ok': False, 'output': f'仓库名「{name}」已存在，请换一个名字'}), 400
    norm = lambda p: os.path.normcase(os.path.normpath(p))
    dup = [n for n, p in REPOS.items() if norm(p) == norm(path)]
    if dup:
        return jsonify({'ok': False, 'output': f'该路径已被仓库「{dup[0]}」监控（Windows 路径不区分大小写）'}), 400
    if not os.path.isdir(path):
        return jsonify({'ok': False, 'output': f'路径不存在：{path}（注意是本工具所在电脑上的路径）'}), 400
    if not _is_git_repo(path):
        return jsonify({'ok': False, 'output': f'{path} 不是 Git 仓库（未找到 .git），请先 clone 或 git init'}), 400
    new_repos = _repos_snapshot()
    new_repos[name] = path
    _install_repos(new_repos)
    normalize_cfg_integrity(CFG)
    gm.save_config(CFG)
    restart_repo_watchers()
    return jsonify({'ok': True, 'output': f'已添加仓库「{name}」并开始监控'})


@app.route('/api/repos/update', methods=['POST'])
def api_repo_update():
    """修改已有监控仓库的名称/路径。

    改名时同步更新关联数据，避免出现"孤儿引用"：
    groups 分组、notify_repos 通知规则、draft_groups 草稿组、compare 默认仓库、
    发布快照历史（DORA 数据源）。顺序保持不变。"""
    data = request.get_json(silent=True) or {}
    name = str(data.get('name', '') or '').strip()
    new_name = str(data.get('new_name', '') or '').strip()
    new_path = str(data.get('path', '') or '').strip().rstrip('\\')
    if name not in REPOS:
        return jsonify({'ok': False, 'output': f'仓库「{name}」不在监控列表中'}), 400
    if not new_name and not new_path:
        return jsonify({'ok': False, 'output': '新名称和新路径至少填一个'}), 400
    if new_name and new_name != name and new_name in REPOS:
        return jsonify({'ok': False, 'output': f'仓库名「{new_name}」已被其它仓库占用'}), 400
    target_path = new_path or REPOS[name]
    if not os.path.isdir(target_path) or not _is_git_repo(target_path):
        return jsonify({'ok': False, 'output': f'{target_path} 不是可用的 Git 仓库目录（需存在 .git）'}), 400
    norm = lambda p: os.path.normcase(os.path.normpath(p))
    dup = [n for n, p in REPOS.items() if n != name and norm(p) == norm(target_path)]
    if dup:
        return jsonify({'ok': False, 'output': f'该路径已被仓库「{dup[0]}」监控（Windows 路径不区分大小写）'}), 400

    repos = _repos_snapshot()
    final_name = new_name or name
    new_repos = {}
    for k, v in repos.items():
        new_repos[final_name if k == name else k] = target_path if k == name else v

    if final_name != name:
        for g in (CFG.get('groups') or {}).values():
            if isinstance(g, list):
                for i, n in enumerate(g):
                    if n == name:
                        g[i] = final_name
        nr = CFG.get('notify_repos')
        if isinstance(nr, list):
            CFG['notify_repos'] = [final_name if n == name else n for n in nr]
        dg = CFG.get('draft_groups') or {}
        if name in dg:
            dg[final_name] = dg.pop(name)
        cmp_cfg = CFG.get('compare') or {}
        if isinstance(cmp_cfg, dict) and cmp_cfg.get('repo') == name:
            cmp_cfg['repo'] = final_name
        try:  # 发布快照历史跟随改名（DORA 指标数据不丢）
            rels = gm.load_releases() or {}
            if name in rels:
                rels[final_name] = rels.pop(name)
                gm._atomic_write_json(gm.RELEASES_PATH, rels)
        except Exception:
            pass  # 历史迁移失败不影响改名本身

    _install_repos(new_repos)
    normalize_cfg_integrity(CFG)
    gm.save_config(CFG)
    restart_repo_watchers()
    return jsonify({'ok': True,
                    'output': f'已保存：{final_name} -> {target_path}' + ('（关联的分组/通知/草稿组/发布历史已同步）' if final_name != name else '')})


@app.route('/api/repos/remove', methods=['POST'])
def api_repo_remove():
    """从监控列表移除仓库（只解除监控，不动磁盘上的仓库和 git_monitor.json 之外的任何数据）"""
    data = request.get_json(silent=True) or {}
    name = str(data.get('name', '') or '').strip()
    if name not in REPOS:
        return jsonify({'ok': False, 'output': f'仓库「{name}」不在监控列表中'}), 400
    new_repos = _repos_snapshot()
    new_repos.pop(name, None)
    _install_repos(new_repos)
    normalize_cfg_integrity(CFG)
    gm.save_config(CFG)
    restart_repo_watchers()
    return jsonify({'ok': True, 'output': f'已移除仓库「{name}」的监控'})


@app.route('/api/repo/<name>')
def api_repo_status(name):
    """获取单个仓库状态（复用 /api/repos 的短 TTL 缓存，避免每次再跑一遍 git status）"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    st = _status_map_parallel({name: path}, max_age=_STATUS_CACHE_TTL).get(name)
    st = dict(st) if st else gm.get_status(path)
    st['name'] = name
    st['path'] = path
    return jsonify(st)

@app.route('/api/repo/<name>/commits')
def api_commits(name):
    """获取提交历史"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    n = request.args.get('n', 50, type=int)
    n = max(1, min(n, 500))
    commits = gm.get_commits(path, n)
    return jsonify(commits)

_HASH_RE = re.compile(r'^[0-9a-fA-F]{4,40}$')


def _valid_hash(h):
    """提交哈希/引用合法性：4-40位十六进制。防止 URL 段注入 git 选项
    （如 /commit/--all 会把整个仓库 diff 吐出来，/commit/--exec=xxx 等）。"""
    return bool(h) and bool(_HASH_RE.match(h))


@app.route('/api/repo/<name>/commit/<hash>')
def api_commit_detail(name, hash):
    """获取提交详情"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    if not _valid_hash(hash):
        return jsonify({'error': '非法提交哈希'}), 400
    detail = gm.get_commit_show(path, hash)
    files = gm.get_changed_files(path, hash)
    return jsonify({'detail': detail, 'files': files})

@app.route('/api/repo/<name>/commit/<hash>/export-paths')
def api_export_commit_paths(name, hash):
    """导出提交文件路径列表（纯文本）"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    if not _valid_hash(hash):
        return jsonify({'error': '非法提交哈希'}), 400
    # 先尝试 diff-tree（普通提交）
    files = gm.get_changed_files(path, hash)
    file_list = []
    if isinstance(files, list):
        for f in files:
            if isinstance(f, dict):
                file_list.append(f.get('path', ''))
            elif isinstance(f, str):
                file_list.append(f)
    # 如果为空，尝试 git show --stat（兼容根提交）
    if not file_list:
        out, _ = gm.git(path, 'show', '--stat', '--format=', hash)
        for line in (out or '').splitlines():
            line = line.strip()
            if line and '|' in line:
                # 格式: "file.java | 23 +++"
                filepath = line.split('|')[0].strip()
                if filepath:
                    file_list.append(filepath)
    # 生成纯文本路径列表
    paths_text = '\n'.join(file_list)
    return jsonify({
        'paths': paths_text,
        'count': len(file_list),
        'filename': f'commit_{hash[:7]}_files.txt'
    })

@app.route('/api/repo/<name>/search')
def api_search(name):
    """搜索提交"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    keyword = request.args.get('q', '')
    author = request.args.get('author', '')
    since = request.args.get('since', 0, type=int)
    try:
        commits = gm.search_commits(path, keyword, author=author, since_days=since)
    except ValueError as e:
        # 正则语法错误等用户输入问题 → 400 并说明原因，而不是"搜不到"
        return jsonify({'error': str(e)}), 400
    return jsonify(commits)

# ============================================================
# 工作台 API
# ============================================================
@app.route('/api/workspace/<name>')
def api_workspace(name):
    """获取工作台文件列表"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    files = gm.get_workspace_status(path)
    return jsonify(files)

@app.route('/api/workspace/<name>/diff', methods=['POST'])
def api_workspace_diff(name):
    """获取文件 diff"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    data = request.json
    filepath = data.get('path', '')
    if safe_repo_path(path, filepath) is None:
        return jsonify({'error': f'非法文件路径: {filepath}'}), 400
    untracked = data.get('untracked', False)
    staged = data.get('staged', False)
    diff = gm.get_worktree_diff(path, filepath, untracked, staged=staged)
    return jsonify({'diff': diff})

@app.route('/api/workspace/<name>/stage', methods=['POST'])
def api_stage(name):
    """暂存文件"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    data = request.json
    files = data.get('files')
    if files is not None:
        if isinstance(files, (str, dict)):
            files = [files]
        paths = [f.get('path', '') if isinstance(f, dict) else str(f or '') for f in (files or [])]
        _, bad = validate_rel_paths(path, paths)
        if bad:
            return jsonify({'ok': False, 'output': f'非法路径: {bad}'}), 400
        files = paths
    out, rc = gm.ws_stage(path, files)
    return jsonify({'ok': rc == 0, 'output': out})

@app.route('/api/workspace/<name>/unstage', methods=['POST'])
def api_unstage(name):
    """取消暂存"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    data = request.json
    files = data.get('files')
    if files is not None:
        if isinstance(files, (str, dict)):
            files = [files]
        paths = [f.get('path', '') if isinstance(f, dict) else str(f or '') for f in files]
        _, bad = validate_rel_paths(path, paths)
        if bad:
            return jsonify({'ok': False, 'output': f'非法路径: {bad}'}), 400
        files = paths
    out, rc = gm.ws_unstage(path, files)
    return jsonify({'ok': rc == 0, 'output': out})

@app.route('/api/workspace/<name>/commit', methods=['POST'])
def api_commit(name):
    """提交已暂存内容"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    data = request.json
    message = data.get('message', '')
    auto_stage = data.get('auto_stage', False)  # 自动暂存全部变更
    amend = data.get('amend', False)  # 修正上一次提交（git commit --amend）
    # 空提交信息直接 400：交给 git 只会得到一段 "Aborting commit due to empty commit
    # message" 的英文输出，用户不知道是参数没传对（amend 允许不传，沿用原消息）
    if not str(message or '').strip() and not amend:
        return jsonify({'ok': False, 'error': '提交信息不能为空',
                        'output': '提交信息不能为空'}), 400
    if auto_stage:
        out, rc = gm.ws_stage_all_and_commit(path, message, amend=amend)
    else:
        out, rc = gm.ws_commit(path, message, amend=amend)
    return jsonify({'ok': rc == 0, 'output': out})

@app.route('/api/workspace/<name>/discard', methods=['POST'])
def api_discard(name):
    """丢弃更改"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    data = request.json
    files = _normalize_file_entries(data.get('files', []))
    if not files:
        return jsonify({'ok': False, 'output': '未选择文件'}), 400
    _, bad = validate_rel_paths(path, [f.get('path', '') for f in files])
    if bad:
        return jsonify({'ok': False, 'output': f'非法路径: {bad}'}), 400
    out, rc = gm.ws_discard(path, files)
    return jsonify({'ok': rc == 0, 'output': out})

@app.route('/api/workspace/<name>/stage-all', methods=['POST'])
def api_stage_all(name):
    """全部暂存"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    out, rc = gm.ws_stage(path)
    return jsonify({'ok': rc == 0, 'output': out})

@app.route('/api/workspace/<name>/discard-all', methods=['POST'])
def api_discard_all(name):
    """放弃所有更改"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    files = gm.get_workspace_status(path)
    if not files:
        return jsonify({'ok': True, 'output': '没有更改'})
    out, rc = gm.ws_discard(path, files)
    _audit('discard-all', name, f'{len(files)} 个文件', rc == 0)
    return jsonify({'ok': rc == 0, 'output': out})

# ============================================================
# 分支 API
# ============================================================
@app.route('/api/repo/<name>/branches')
def api_branches(name):
    """获取分支列表"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    local, remote = gm.get_branches(path)
    overview = gm.get_branch_overview(path)
    return jsonify({'local': local, 'remote': remote, 'overview': overview})

@app.route('/api/repo/<name>/checkout', methods=['POST'])
def api_checkout(name):
    """切换分支"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    data = request.json
    target = data.get('target', '')
    if not _no_dash(target):
        return jsonify({'ok': False, 'output': '非法引用名（不允许以 - 开头）'}), 400
    out, rc = gm.repo_checkout(path, target)
    return jsonify({'ok': rc == 0, 'output': out})

@app.route('/api/repo/<name>/create-branch', methods=['POST'])
def api_create_branch(name):
    """创建分支"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    data = request.json
    branch = data.get('branch', '')
    start = data.get('start_point')
    if not branch:
        return jsonify({'ok': False, 'output': '分支名不能为空'}), 400
    if not _no_dash(branch, start):
        return jsonify({'ok': False, 'output': '非法引用名（不允许以 - 开头）'}), 400
    out, rc = gm.repo_create_branch(path, branch, start)
    return jsonify({'ok': rc == 0, 'output': out})

@app.route('/api/repo/<name>/delete-branch', methods=['POST'])
def api_delete_branch(name):
    """删除分支"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    data = request.json
    branch = data.get('branch', '')
    if not branch:
        return jsonify({'ok': False, 'output': '分支名不能为空'}), 400
    if not _no_dash(branch):
        return jsonify({'ok': False, 'output': '非法引用名（不允许以 - 开头）'}), 400
    out, rc = gm.repo_delete_branch(path, branch)
    _audit('delete-branch', name, branch, rc == 0)
    return jsonify({'ok': rc == 0, 'output': out})

# ============================================================
# Stash API
# ============================================================
@app.route('/api/repo/<name>/stash')
def api_stash_list(name):
    """获取 stash 列表"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    stashes = gm.get_stash_list(path)
    return jsonify(stashes)

@app.route('/api/repo/<name>/stash/save', methods=['POST'])
def api_stash_save(name):
    """保存 stash"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    data = request.json
    msg = data.get('message', 'WIP')
    out, rc = gm.stash_save(path, msg)
    return jsonify({'ok': rc == 0, 'output': out})

@app.route('/api/repo/<name>/stash/apply', methods=['POST'])
def api_stash_apply(name):
    """应用 stash"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    data = request.json
    ref = data.get('ref', '')
    if not _no_dash(ref):
        return jsonify({'ok': False, 'output': '非法引用名（不允许以 - 开头）'}), 400
    out, rc = gm.stash_apply(path, ref)
    return jsonify({'ok': rc == 0, 'output': out})

@app.route('/api/repo/<name>/stash/drop', methods=['POST'])
def api_stash_drop(name):
    """删除 stash"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    data = request.json
    ref = data.get('ref', '')
    if not _no_dash(ref):
        return jsonify({'ok': False, 'output': '非法引用名（不允许以 - 开头）'}), 400
    out, rc = gm.stash_drop(path, ref)
    return jsonify({'ok': rc == 0, 'output': out})

# ============================================================
# 比对 API
# ============================================================
@app.route('/api/repo/<name>/compare', methods=['GET', 'POST'])
def api_compare(name):
    """分支比对（GET 兼容旧链接；快照写入有去重，POST 为推荐调用方式）"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    payload = request.get_json(silent=True) or {}

    def _p(key, default):
        v = request.args.get(key)
        return v if v is not None else payload.get(key, default)

    dev = _p('dev', 'develop')
    prod = _p('prod', 'main')
    direction = _p('direction', 'dev_to_prod')
    if not _no_dash(dev, prod):
        return jsonify({'error': '非法分支名'}), 400
    data = gm.compute_compare(path, dev, prod, direction)
    # 上线风险分级：配置文件/锁文件/SQL/基础设施定义 → 高（复用桌面版 file_risk）
    for f in data.get('files', []):
        f['risk'] = gm.file_risk(f.get('path', ''))
    # 仅 POST（用户主动比对）才记录发布快照：GET 不应产生副作用，
    # 也避免只读访问污染 DORA 指标。
    if request.method == 'POST' and data.get('ok'):
        try:
            gm.push_release_snapshot(data, name)
        except Exception:
            pass
    return jsonify(data)


@app.route('/api/repo/<name>/changelog')
def api_changelog(name):
    """按 conventional commits 生成 CHANGELOG + 建议版本号"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    dev = request.args.get('dev', 'develop')
    prod = request.args.get('prod', 'main')
    direction = request.args.get('direction', 'dev_to_prod')
    data = gm.compute_compare(path, dev, prod, direction)
    if not data.get('ok'):
        return jsonify({'error': data.get('error', '比对失败')}), 400
    msgs = [c.get('message', '') for c in data.get('commits', [])]
    bump = gm.analyze_bump(msgs)
    tags, _ = gm.git(path, 'tag', '-l', 'v*', '--sort=-v:refname')
    current = tags.splitlines()[0].strip() if (tags or '').strip() else ''
    return jsonify({
        'changelog_md': gm.build_changelog_md(msgs),
        'current_version': current,
        'suggested_version': gm.bump_version(current, bump),
        'bump': bump,
        'n_commits': len(msgs),
        'filename': f"CHANGELOG_{gm._safe_file_part(name)}_{gm.bump_version(current, bump)}.md",
    })


def _parse_rel_time(s):
    try:
        return datetime.strptime(s, '%Y-%m-%d %H:%M:%S').timestamp()
    except Exception:
        return 0


def compute_dora(days=90):
    """从发布快照（git_monitor_releases.json）计算 DORA 指标：
    部署频率（次/周）+ 变更前置时间（提交→发布 的中位小时数）"""
    hist = gm.load_releases()
    now = time.time()
    cutoff = now - days * 86400
    out = {}
    for repo, snaps in (hist or {}).items():
        path = REPOS.get(repo)
        if not path or not os.path.isdir(path):
            continue
        rels = [s for s in snaps
                if _parse_rel_time(s.get('time', '')) >= cutoff
                and s.get('direction', '') != 'prod_to_dev']
        weeks = max(days / 7.0, 1.0)
        need = []
        for s in rels:
            rt = _parse_rel_time(s.get('time', ''))
            for h in s.get('commits', []) or []:
                need.append((h, rt))
        leads = []
        if need:
            uniq = list({h for h, _ in need})
            outp, rc = gm.git(path, 'show', '-s', '--format=%h|%at', *uniq, timeout=30)
            tmap = {}
            for line in (outp or '').splitlines():
                parts = line.split('|')
                if len(parts) == 2:
                    try:
                        tmap[parts[0]] = int(parts[1])
                    except ValueError:
                        pass
            for h, rt in need:
                ct = tmap.get(h)
                if ct:
                    leads.append(max(0, rt - ct))
        leads.sort()
        # 真中位数（偶数样本取中间两数均值），避免"上中位"高估
        if leads:
            med = (leads[(len(leads) - 1) // 2] + leads[len(leads) // 2]) / 2.0
        else:
            med = None
        out[repo] = {
            'deploys': len(rels),
            'per_week': round(len(rels) / weeks, 2),
            'lead_median_h': round(med / 3600.0, 1) if med is not None else None,
            'samples': len(leads),
        }
    return out


@app.route('/api/dora')
def api_dora():
    days = request.args.get('days', 90, type=int)
    days = max(7, min(days, 365))
    return jsonify(compute_dora(days))


@app.route('/api/repo/<name>/release-md')
def api_release_md(name):
    """导出 Markdown 上线清单/回滚清单（复用桌面版 build_release_md）"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    dev = request.args.get('dev', 'develop')
    prod = request.args.get('prod', 'main')
    direction = request.args.get('direction', 'dev_to_prod')
    data = gm.compute_compare(path, dev, prod, direction)
    if not data.get('ok'):
        return jsonify({'error': data.get('error', '比对失败')}), 400
    return jsonify({
        'md': gm.build_release_md(data, name),
        'filename': f"release_{gm._safe_file_part(name)}_{gm._safe_file_part(dev)}_vs_{gm._safe_file_part(prod)}.md",
    })


@app.route('/api/weekly')
def api_weekly():
    """生成 Markdown 周报（复用桌面版 build_weekly_report）"""
    days = request.args.get('days', 30, type=int)
    days = max(1, min(days, 3650))
    repo = request.args.get('repo', '全部仓库')
    snap = _repos_snapshot()
    if repo != '全部仓库' and repo not in snap:
        return jsonify({'error': '仓库不存在'}), 404
    repos = {repo: snap[repo]} if repo != '全部仓库' else snap
    commits = gm.get_repo_commits(repos, days)
    return jsonify({
        'md': gm.build_weekly_report(commits, repo, days, True),
        'n_commits': len(commits),
        'filename': f"weekly_{gm._safe_file_part(repo)}_{days}d_{datetime.now().strftime('%Y%m%d')}.md",
    })

# ============================================================
# 统计 API
# ============================================================
@app.route('/api/stats')
def api_stats():
    """提交统计"""
    days = request.args.get('days', 30, type=int)
    days = max(1, min(days, 3650))
    scope = request.args.get('scope', 'all')
    by_date, by_author, by_repo_date, by_repo_author, by_type, by_repo_type = \
        gm.get_stats_detailed(_repos_snapshot(), days, all_branches=(scope != 'current'))
    return jsonify({
        'by_date': dict(by_date),
        'by_author': dict(by_author),
        'by_type': dict(by_type),
        'by_repo_date': {k: dict(v) for k, v in (by_repo_date or {}).items()},
        'by_repo_author': {k: dict(v) for k, v in (by_repo_author or {}).items()},
        'by_repo_type': {k: dict(v) for k, v in (by_repo_type or {}).items()},
    })

# ============================================================
# 优化4: 仓库健康度评分 API
# ============================================================
@app.route('/api/app-health')
@app.route('/api/health')  # 兼容旧调用（外部脚本/书签），新代码请用 /api/app-health
def api_health():
    """所有仓库健康度评分（复用 get_status 已算好的 health，不再串行重复扫描）"""
    status_map = _status_map_parallel(_repos_snapshot(), max_age=_STATUS_CACHE_TTL)
    result = {}
    for name, st in status_map.items():
        if st.get('invalid'):
            result[name] = {'score': 0, 'error': st.get('error') or '仓库无效'}
            continue
        result[name] = {
            'score': st.get('health', 0),
            'branch': st.get('branch', 'N/A'),
            'uncommitted': st.get('uncommitted', 0),
            'ahead': st.get('ahead', 0),
            'behind': st.get('behind', 0),
        }
    return jsonify(result)

# ============================================================
# 优化7: 标签管理 API
# ============================================================
@app.route('/api/repo/<name>/tags')
def api_tags(name):
    """获取标签列表"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    out, _ = gm.git(path, 'tag', '-l', '--format=%(refname:short)|%(objectname:short)|%(creatordate:short)')
    tags = []
    for line in out.splitlines():
        parts = line.split('|', 2)
        if len(parts) >= 2:
            tags.append({'name': parts[0], 'hash': parts[1], 'date': parts[2] if len(parts) > 2 else ''})
    return jsonify(tags)

@app.route('/api/repo/<name>/tag', methods=['POST'])
def api_create_tag(name):
    """创建标签"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    data = request.json
    tag_name = data.get('tag', '')
    commit_hash = data.get('commit')
    if not _no_dash(tag_name, commit_hash):
        return jsonify({'ok': False, 'output': '非法引用名（不允许以 - 开头）'}), 400
    out, rc = gm.repo_create_tag(path, tag_name, commit_hash)
    return jsonify({'ok': rc == 0, 'output': out})

@app.route('/api/repo/<name>/tag/delete', methods=['POST'])
def api_delete_tag(name):
    """删除标签"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    data = request.json
    tag_name = data.get('tag', '')
    if not _no_dash(tag_name):
        return jsonify({'ok': False, 'output': '非法引用名（不允许以 - 开头）'}), 400
    out, rc = gm.repo_delete_tag(path, tag_name)
    _audit('tag-delete', name, tag_name, rc == 0)
    return jsonify({'ok': rc == 0, 'output': out})

@app.route('/api/repo/<name>/tag/push', methods=['POST'])
def api_push_tag(name):
    """推送标签到远程"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    data = request.json
    tag_name = data.get('tag', '')
    if not _no_dash(tag_name):
        return jsonify({'ok': False, 'output': '非法引用名（不允许以 - 开头）'}), 400
    out, rc = gm.git(path, 'push', 'origin', tag_name, timeout=30)
    return jsonify({'ok': rc == 0, 'output': out})

# ============================================================
# 优化2: Hunk 级别暂存 API
# ============================================================
@app.route('/api/workspace/<name>/stage-hunk', methods=['POST'])
def api_stage_hunk(name):
    """暂存指定 hunk"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    data = request.json
    filepath = data.get('path', '')
    if safe_repo_path(path, filepath) is None:
        return jsonify({'ok': False, 'output': f'非法文件路径: {filepath}'}), 400
    hunk_index = data.get('hunk_index', 0)
    
    # 获取文件的 patch
    patch = gm.get_file_patch(path, filepath)
    headers, hunks = gm.split_hunks(patch)
    
    if hunk_index >= len(hunks):
        return jsonify({'ok': False, 'output': '无效的 hunk 索引'})
    
    # 构建单个 hunk 的 patch
    hunk_patch = '\n'.join(headers + hunks[hunk_index])
    out, rc = gm.git_apply_cached(path, hunk_patch)
    return jsonify({'ok': rc == 0, 'output': out})

@app.route('/api/workspace/<name>/unstage-hunk', methods=['POST'])
def api_unstage_hunk(name):
    """只取消暂存指定 hunk（对 --cached diff 的 hunk 做逆向应用）"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    data = request.json
    filepath = data.get('path', '')
    if safe_repo_path(path, filepath) is None:
        return jsonify({'ok': False, 'output': '非法文件路径: %s' % filepath}), 400
    hunk_index = data.get('hunk_index', 0)

    patch, _ = gm.git(path, 'diff', '--cached', '--', filepath)
    headers, hunks = gm.split_hunks(patch or '')
    if hunk_index >= len(hunks):
        return jsonify({'ok': False, 'output': '无效的 hunk 索引'})
    hunk_patch = chr(10).join(headers + hunks[hunk_index])
    out, rc = gm.git_apply_cached_reverse(path, hunk_patch)
    return jsonify({'ok': rc == 0, 'output': out})

# ============================================================
# 优化6: 增强搜索 API（正则+作者+日期范围）
# ============================================================
@app.route('/api/repo/<name>/search-enhanced')
def api_search_enhanced(name):
    """增强搜索：支持正则、作者、日期范围"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    keyword = request.args.get('q', '')
    author = request.args.get('author', '')
    since = request.args.get('since', '')
    until = request.args.get('until', '')
    regex = request.args.get('regex', 'false').lower() == 'true'
    if len(keyword) > 200 or len(author) > 100:
        return jsonify({'error': '查询过长（关键词≤200，作者≤100）'}), 400

    # 构建 git log 命令
    args = ['log', '--all', '--format=%H|%an|%ai|%s']
    
    if keyword:
        if regex:
            # --perl-regexp 必须在 --grep 之前：它只影响其后的 --grep
            try:
                import re as _re
                _re.compile(keyword)
            except _re.error as e:
                return jsonify({'error': f'正则表达式有误: {e}'}), 400
            args.extend(['--perl-regexp', '--grep', keyword, '-i'])
        else:
            args.extend(['--grep', keyword, '-i'])
    
    if author:
        args.extend(['--author', author])
    
    if since:
        args.extend([f'--since={since}'])
    if until:
        args.extend([f'--until={until}'])
    
    args.extend(['-100'])
    try:
        out, rc = gm.git(path, *args, timeout=20)
        if rc != 0:
            return jsonify({'error': f'搜索失败: {(out or "").strip()[:200]}'}), 400
    except Exception as e:
        return jsonify({'error': f'搜索失败: {e}'}), 400
    commits = gm.parse_log(out)
    return jsonify(commits)

# ============================================================
# 提交图 API
# ============================================================
@app.route('/api/repo/<name>/graph')
def api_graph(name):
    """提交图数据"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    n = request.args.get('n', 100, type=int)
    n = max(1, min(n, 500))  # 封顶500，与 /commits 一致；防止超大 n 拖垮大仓库
    commits = gm.get_graph_log(path, n)
    ref_map = gm.get_ref_map(path)
    rows, pos = gm.layout_graph(commits)
    return jsonify({
        'commits': commits,
        'ref_map': ref_map,
        'rows': [{'hash': r['commit']['hash'], 'lane': r['lane']} for r in rows],
    })

# ============================================================
# Git 操作 API
# ============================================================
@app.route('/api/repo/<name>/pull', methods=['POST'])
def api_pull(name):
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    # rebase=true 时用 pull --rebase（避免产生多余的 merge 提交）
    data = request.json or {}
    t = gm.net_timeout()
    if data.get('rebase'):
        out, rc = gm.git(path, 'pull', '--rebase', timeout=t)
    else:
        out, rc = gm.repo_pull(path)
    return jsonify({'ok': rc == 0, 'output': gm._net_out(out, rc, t)})

@app.route('/api/repo/<name>/push', methods=['POST'])
def api_push(name):
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    out, rc = gm.repo_push(path)
    return jsonify({'ok': rc == 0, 'output': out})

@app.route('/api/repo/<name>/fetch', methods=['POST'])
def api_fetch(name):
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    out, rc = gm.repo_fetch(path)
    return jsonify({'ok': rc == 0, 'output': out})

@app.route('/api/repo/<name>/cherry-pick', methods=['POST'])
def api_cherry_pick(name):
    """把指定提交摘到当前分支；产生冲突时返回 conflict=True 引导到冲突页"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    data = request.json or {}
    h = str(data.get('hash', '') or '').strip()
    if not h or not _no_dash(h) or not re.fullmatch(r'[0-9a-fA-F]{4,40}', h):
        return jsonify({'ok': False, 'output': '非法提交哈希'}), 400
    out, rc = gm.git(path, 'cherry-pick', h, timeout=120)
    if rc != 0 and 'now empty' in (out or ''):
        # 改动已在当前分支（重复摘取）：清掉半完成的 sequencer 状态，友好返回
        gm.git(path, 'cherry-pick', '--abort')
        return jsonify({'ok': True, 'output': '该提交的改动已存在于当前分支，无需重复摘取', 'noop': True})
    conflict = rc != 0 and bool(gm.get_conflict_files(path))
    return jsonify({'ok': rc == 0, 'output': out,
                    'conflict': conflict,
                    'output_str': (out or '')[:400]})

@app.route('/api/repo/<name>/revert', methods=['POST'])
def api_revert(name):
    """回滚指定提交（生成反向提交）"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    data = request.json or {}
    h = (data.get('hash') or '').strip()
    if not h or not re.match(r'^[0-9a-fA-F]{4,40}$', h):
        return jsonify({'ok': False, 'output': '非法提交哈希'}), 400
    out, rc = gm.repo_revert(path, h)
    return jsonify({'ok': rc == 0, 'output': out})

@app.route('/api/repo/<name>/reset', methods=['POST'])
def api_reset(name):
    """重置分支到指定提交（soft/mixed/hard；hard 由前端二次确认）"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    data = request.json or {}
    target = (data.get('target') or 'HEAD').strip()
    mode = data.get('mode', 'mixed')
    if not _no_dash(target):
        return jsonify({'ok': False, 'output': '非法引用名（不允许以 - 开头）'}), 400
    out, rc = gm.repo_reset(path, target, mode)
    _audit('reset', name, f'{mode} -> {target}', rc == 0)
    return jsonify({'ok': rc == 0, 'output': out})

@app.route('/api/repo/<name>/rebase/skip', methods=['POST'])
def api_rebase_skip(name):
    """跳过当前冲突提交，继续 rebase"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    out, rc = gm.repo_skip_rebase(path)
    return jsonify({'ok': rc == 0, 'output': out})

# ============================================================
# 补丁导出/导入（离线机器间转移提交）
# ============================================================
@app.route('/api/repo/<name>/patch/commit', methods=['GET'])
def api_commit_patch(name):
    """读取单个提交的 patch 文本（format-patch --stdout，前端预览/复制/下载）"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    h = request.args.get('hash', '').strip()
    if not h or not re.match(r'^[0-9a-fA-F]{4,40}$', h):
        return jsonify({'error': '非法提交哈希'}), 400
    out, rc = gm.get_commit_patch(path, h)
    if rc != 0:
        return jsonify({'error': out or '导出失败'}), 400
    return jsonify({'patch': out, 'filename': f'{h[:7]}.patch'})

@app.route('/api/repo/<name>/patch/check', methods=['POST'])
def api_patch_check(name):
    """检测补丁能否干净应用（不改动仓库）"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    data = request.json or {}
    out, rc = gm.apply_patch(path, data.get('patch', ''), check_only=True)
    return jsonify({'ok': rc == 0, 'output': out})

@app.route('/api/repo/<name>/patch/apply', methods=['POST'])
def api_patch_apply(name):
    """应用补丁（git am --3way，冲突时返回冲突提示）"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    data = request.json or {}
    patch = data.get('patch', '')
    if not (patch or '').strip():
        return jsonify({'ok': False, 'output': '补丁内容为空'}), 400
    out, rc = gm.apply_patch(path, patch)
    return jsonify({'ok': rc == 0, 'output': out,
                    'conflict': rc != 0 and 'CONFLICT' in (out or '').upper()})

@app.route('/api/repo/<name>/patch/abort', methods=['POST'])
def api_patch_abort(name):
    """放弃当前 git am 会话"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    out, rc = gm.abort_patch(path)
    return jsonify({'ok': rc == 0, 'output': out})

@app.route('/api/repo/<name>/patch/continue', methods=['POST'])
def api_patch_continue(name):
    """解决冲突后继续 git am 会话"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    out, rc = gm.continue_patch(path)
    return jsonify({'ok': rc == 0, 'output': out})

# ============================================================
# 工作区 vs 指定提交对比
# ============================================================
@app.route('/api/repo/<name>/diff-worktree-vs')
def api_diff_worktree_vs(name):
    """工作区（含暂存区）与任意指定提交的对比 diff"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    h = request.args.get('hash', '').strip()
    if not h or not re.match(r'^[0-9a-fA-F]{4,40}$', h):
        return jsonify({'error': '非法提交哈希'}), 400
    return jsonify({'diff': gm.get_worktree_vs_commit_diff(path, h)})

# ============================================================
# 每仓库提交身份 / fetch-pull-push 参数 / .gitignore 编辑器
# ============================================================
@app.route('/api/repo/<name>/identity')
def api_get_identity(name):
    """读取仓库本地提交身份"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    ident = gm.get_repo_identity(path)
    ident['options'] = gm.get_repo_git_options(path)
    return jsonify(ident)

@app.route('/api/repo/<name>/identity', methods=['POST'])
def api_set_identity(name):
    """设置仓库本地提交身份 + 行为选项（name/email 留空=清除回退全局）"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    data = request.json or {}
    out, rc = gm.set_repo_identity(path, data.get('name', ''), data.get('email', ''))
    # 可选：同时设置行为选项
    opt_err = []
    for k, v in (data.get('options') or {}).items():
        o_out, o_rc = gm.set_repo_git_option(path, k, v)
        if o_rc != 0:
            opt_err.append(o_out)
    if opt_err:
        out += '\n' + '\n'.join(opt_err)
        rc = 1
    return jsonify({'ok': rc == 0, 'output': out})

@app.route('/api/repo/<name>/gitignore')
def api_get_gitignore(name):
    """读取 .gitignore 内容"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    return jsonify({'content': gm.read_gitignore(path)})

@app.route('/api/repo/<name>/gitignore', methods=['POST'])
def api_set_gitignore(name):
    """写入 .gitignore（不自动提交）"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    data = request.json or {}
    out, rc = gm.write_gitignore(path, data.get('content', ''))
    return jsonify({'ok': rc == 0, 'output': out})

@app.route('/api/repo/<name>/gitignore/explain')
def api_explain_gitignore(name):
    """逐行解释 .gitignore 规则（纯离线）+ 检查指定路径是否被忽略。
    传 content 参数时解释编辑器中的实时内容，否则解释磁盘上的文件。"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    content = request.args.get('content')
    if content is None:
        content = gm.read_gitignore(path)
    lines = []
    for i, ln in enumerate(content.splitlines(), 1):
        lines.append({'line': i, 'text': ln, 'explain': gm.explain_gitignore_line(ln)})
    test_paths = [p.strip() for p in request.args.get('test', '').split('|') if p.strip()]
    ignored = gm.check_ignored(path, test_paths) if test_paths else []
    return jsonify({'lines': lines, 'ignored': ignored})

@app.route('/api/repo/<name>/open-folder', methods=['POST'])
def api_open_folder(name):
    """在资源管理器中打开仓库目录"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    if not os.path.isdir(path):
        return jsonify({'ok': False, 'error': '目录不存在'})
    try:
        if os.name == 'nt':
            os.startfile(path)
        else:
            import subprocess
            subprocess.Popen(['xdg-open', path])
        return jsonify({'ok': True})
    except Exception as e:
        return jsonify({'ok': False, 'error': str(e)})

# ============================================================
# 仓库体检 API
# ============================================================
@app.route('/api/repo/<name>/health')
def api_repo_health(name):
    """仓库体检：体积、大文件、悬空对象（限流：60秒内不可重复调用）"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    # 限流：防止频繁触发重操作
    if not rate_limit(f'health:{name}', min_interval=60):
        return jsonify({'error': '体检操作过于频繁，请60秒后重试', 'retry_after': 60}), 429
    
    # 体积信息
    size_info = get_repo_size_info(path)
    
    # 大文件排行（限制范围）
    largest = get_largest_files(path, n=10, since_commits=5000)
    
    # 悬空对象
    unreachable_total, unreachable_kinds = get_fsck_unreachable(path)
    
    # 敏感信息扫描（与独立扫描页同一实现 gm.scan_secrets，字段适配健康页展示）
    try:
        raw = gm.scan_secrets(path, max_commits=100, since_days=90)
        secrets = [{'hash7': s.get('commit', '')[:7], 'path': s.get('file', ''),
                    'type': s.get('type', ''),
                    'snippet': (s.get('match', '')[:80] +
                                (f"（第{s['line']}行）" if s.get('line') else ''))}
                   for s in raw]
    except Exception:
        rate_limit_release(f'health:{name}')  # 失败不占用限流窗口
        raise
    
    return jsonify({
        'size_info': size_info,
        'largest_files': largest,
        'unreachable': {'total': unreachable_total, 'kinds': unreachable_kinds},
        'secrets': secrets,
    })

@app.route('/api/repo/<name>/file-history')
def api_file_history(name):
    """文件历史追踪"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    filepath = request.args.get('path', '')
    if not filepath:
        return jsonify({'error': '请指定文件路径'}), 400
    if safe_repo_path(path, filepath) is None:
        return jsonify({'error': f'非法文件路径: {filepath}'}), 400
    commits = get_file_history(path, filepath)
    return jsonify(commits)


@app.route('/api/repo/<name>/blame')
def api_blame(name):
    """逐行溯源（git blame，复用桌面版 get_blame）"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    filepath = request.args.get('path', '')
    if safe_repo_path(path, filepath) is None:
        return jsonify({'error': f'非法文件路径: {filepath}'}), 400
    rows = gm.get_blame(path, filepath)
    return jsonify({'rows': rows, 'path': filepath})


_grep_limiter = _RateLimiter(max_hits=30, window=60)


@app.route('/api/repo/<name>/grep')
def api_grep(name):
    """代码内容搜索（git grep，离线）。

    加固：限制查询长度（防超长正则导致灾难性回溯）、加轻量频率限制
    （防恶意/误用刷爆工作线程），正则模式仍保留 -E 但已受长度与频限约束。
    """
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    q = (request.args.get('q', '') or '').strip()
    if not q:
        return jsonify({'results': []})
    if len(q) > 200:
        return jsonify({'error': '查询过长（上限 200 字符）'}), 400
    # 兼容层 request 无 remote_addr：优先取代理头，否则用 Host 作为限流维度
    client = request.headers.get('X-Forwarded-For') or request.host or 'local'
    if _grep_limiter.is_limited(client):
        return jsonify({'error': '请求过于频繁，请稍后再试'}), 429
    use_fixed = request.args.get('fixed', 'false').lower() == 'true'
    args = ['grep', '-n', '-I']          # -n 行号，-I 跳过二进制
    args.append('-F' if use_fixed else '-E')
    args += ['-e', q, '--']
    out, rc = gm.git(path, *args, timeout=20)
    if rc not in (0, 1):                 # 1 = 无匹配（正常）
        return jsonify({'error': (out or '搜索失败').strip()[:200]}), 400
    all_lines = out.splitlines() if out else []
    results = []
    for line in all_lines[:500]:
        parts = line.split(':', 2)
        if len(parts) == 3:
            results.append({'file': parts[0], 'line': parts[1], 'content': parts[2]})
    return jsonify({'results': results, 'truncated': len(all_lines) > 500})

@app.route('/api/workspace/<name>/stage-lines', methods=['POST'])
def api_stage_lines(name):
    """行级暂存"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    data = request.json
    filepath = data.get('path', '')
    if safe_repo_path(path, filepath) is None:
        return jsonify({'ok': False, 'output': f'非法文件路径: {filepath}'}), 400
    lines = data.get('lines', [])  # 行号列表
    
    # 获取文件的 patch
    patch = gm.get_file_patch(path, filepath)
    if not patch:
        return jsonify({'ok': False, 'output': '无法获取文件差异'})
    
    # 构建行级 patch
    line_patch = gm.build_line_patch(patch, set(lines))
    if not line_patch:
        return jsonify({'ok': False, 'output': '没有可暂存的行'})
    
    # 应用 patch
    out, rc = gm.git_apply_cached(path, line_patch)
    return jsonify({'ok': rc == 0, 'output': out})

# ============================================================
# 配置 API（刷新间隔等）
# ============================================================
@app.route('/api/config')
def api_config():
    """获取配置（含前端需要的分组/模板/通知规则/草稿组/AI 设置）"""
    return jsonify({
        'refresh_interval': CFG.get('refresh_interval', 30),
        'net_timeout': CFG.get('net_timeout', 120),
        'theme': CFG.get('theme', 'light'),
        'groups': CFG.get('groups', {}),
        'commit_templates': CFG.get('commit_templates', []),
        'notify_repos': CFG.get('notify_repos', []),
        'draft_groups': CFG.get('draft_groups', {}),
        'ai_model': CFG.get('ai_model', ''),
    })

@app.route('/api/config', methods=['POST'])
def api_update_config():
    """更新配置（支持热更新：repos/compare/groups/presets/theme/refresh_interval）"""
    data = request.json
    global CFG, REPOS, REFRESH_INTERVAL
    
    if 'refresh_interval' in data:
        CFG['refresh_interval'] = max(5, int(data['refresh_interval']))
        REFRESH_INTERVAL = CFG['refresh_interval']
    if 'net_timeout' in data:
        # 网络命令超时（fetch/pull/push）：10~1800s，防止误填成 0 或超大值
        CFG['net_timeout'] = max(10, min(int(data['net_timeout']), 1800))
    if 'theme' in data:
        CFG['theme'] = data['theme']
    if 'repos' in data and isinstance(data['repos'], dict):
        # ⚠ 不再盲信整个 repos 字典：逐项校验路径存在且是 Git 仓库，
        # 防止绕过 /api/repos/add 的校验写入任意路径（包含非法/不存在路径会污染配置）
        cleaned = {}
        for rname, rpath in data['repos'].items():
            rname = str(rname or '').strip()
            rpath = str(rpath or '').strip().rstrip('\\')
            if rname and os.path.isdir(rpath) and _is_git_repo(rpath):
                cleaned[rname] = rpath
        dropped = len(data['repos']) - len(cleaned)
        _install_repos(cleaned)
        restart_repo_watchers()
        if dropped:
            log.warning('/api/config repos: %d 个无效仓库被拒绝', dropped)
    if 'compare' in data and isinstance(data['compare'], dict):
        CFG['compare'] = data['compare']
    if 'groups' in data and isinstance(data['groups'], dict):
        CFG['groups'] = data['groups']
    if 'presets' in data and isinstance(data['presets'], list):
        CFG['presets'] = data['presets']
    if 'sound' in data:
        CFG['sound'] = bool(data['sound'])
    if 'auto_refresh' in data:
        CFG['auto_refresh'] = bool(data['auto_refresh'])
    if 'notify_repos' in data and isinstance(data['notify_repos'], list):
        CFG['notify_repos'] = [str(x) for x in data['notify_repos'] if x in REPOS]
    if 'draft_groups' in data and isinstance(data['draft_groups'], dict):
        CFG['draft_groups'] = data['draft_groups']
    if 'ai_model' in data:
        CFG['ai_model'] = str(data['ai_model'] or '').strip()

    normalize_cfg_integrity(CFG)
    gm.save_config(CFG)
    return jsonify({'ok': True})

# ============================================================
# Interactive Rebase API
# ============================================================
@app.route('/api/repo/<name>/rebase/commits')
def api_rebase_commits(name):
    """获取可用于 interactive rebase 的提交列表"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    onto = request.args.get('onto', 'HEAD~10')
    if not _no_dash(onto):
        return jsonify({'error': '非法引用名（不允许以 - 开头）'}), 400
    n = request.args.get('n', 20, type=int)
    commits = gm.get_rebase_commits(path, onto, n)
    return jsonify(commits)

@app.route('/api/repo/<name>/rebase', methods=['POST'])
def api_rebase(name):
    """执行 interactive rebase"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    data = request.json
    onto = data.get('onto', 'HEAD~10')
    if not _no_dash(onto):
        return jsonify({'ok': False, 'output': '非法引用名（不允许以 - 开头）'}), 400
    actions = data.get('actions', [])
    out, rc = gm.interactive_rebase(path, onto, actions)
    return jsonify({'ok': rc == 0, 'output': out})

@app.route('/api/repo/<name>/squash', methods=['POST'])
def api_squash(name):
    """合并最近 N 个提交"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    data = request.json
    last_n = data.get('n', 2)
    message = data.get('message')
    out, rc = gm.squash_commits(path, last_n, message)
    return jsonify({'ok': rc == 0, 'output': out})

@app.route('/api/repo/<name>/rebase/abort', methods=['POST'])
def api_rebase_abort(name):
    """中止 rebase"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    out, rc = gm.abort_rebase(path)
    return jsonify({'ok': rc == 0, 'output': out})

@app.route('/api/repo/<name>/rebase/continue', methods=['POST'])
def api_rebase_continue(name):
    """继续 rebase"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    out, rc = gm.continue_rebase(path)
    return jsonify({'ok': rc == 0, 'output': out})

# ============================================================
# 冲突解决 API
# ============================================================
@app.route('/api/repo/<name>/conflicts')
def api_conflicts(name):
    """获取冲突文件列表"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    files = gm.get_conflict_files(path)
    return jsonify({'files': files, 'count': len(files)})

def _conflict_diff3(path, filepath):
    """用 git merge-file --diff3 重跑一次三方合并，拿到带 base 段的冲突标记。

    工作区文件里的冲突标记只有 ours/theirs 两段，base（共同祖先）对应哪几行
    必须由合并算法自己对齐才知道。git merge-file 就是 git 内部的合并引擎，
    用它比在 Python 里手写行对齐可靠得多，也不用新增依赖。

    返回带 `||||||| base` 段的合并文本；二进制 / 非 UTF-8 / 阶段缺失时返回 ''。
    """
    stages = {}
    for n, key in ((1, 'base'), (2, 'ours'), (3, 'theirs')):
        out, rc = gm.git(path, 'show', f':{n}:{filepath}')
        if rc != 0:
            return ''
        if '\x00' in out:
            return ''          # 二进制文件没有"逐块合并"这回事
        stages[key] = out
    tmpdir = tempfile.mkdtemp(prefix='gitmon_cf_')
    try:
        paths = []
        for key in ('ours', 'base', 'theirs'):
            p = os.path.join(tmpdir, key)
            # newline='' 保留原样换行：Windows 下默认会把 \n 翻成 \r\n，
            # merge-file 会认为整个文件都被改过，冲突块会爆炸。
            with open(p, 'w', encoding='utf-8', newline='') as f:
                f.write(stages[key])
            paths.append(p)
        out, rc = gm.git(path, 'merge-file', '-p', '--diff3',
                         '-L', 'ours', '-L', 'base', '-L', 'theirs',
                         *paths, timeout=20)
        # rc=1 表示"有冲突"，这是正常结果；rc<0 才是执行失败
        if rc < 0:
            return ''
        return out or ''
    except Exception:
        return ''
    finally:
        shutil.rmtree(tmpdir, ignore_errors=True)


@app.route('/api/repo/<name>/conflict/<path:filepath>')
def api_conflict_content(name, filepath):
    """获取冲突文件的三方内容"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    content = gm.get_conflict_content(path, filepath)
    full = safe_repo_path(path, filepath)
    if full and os.path.isfile(full):
        try:
            with open(full, 'r', encoding='utf-8', errors='replace') as f:
                content['worktree'] = f.read()  # 工作区文件（含 <<<<<<< 标记，前端逐块解析用）
        except Exception:
            content['worktree'] = ''
    # ?diff3=1 才额外跑一次三方合并：默认路径不为老调用方增加一次子进程开销
    if request.args.get('diff3') in ('1', 'true', 'yes'):
        content['diff3'] = _conflict_diff3(path, filepath)
    return jsonify(content)

@app.route('/api/repo/<name>/conflict/resolve', methods=['POST'])
def api_resolve_conflict(name):
    """解决冲突"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    data = request.json
    filepath = data.get('path', '')
    content = data.get('content', '')
    if safe_repo_path(path, filepath) is None:
        return jsonify({'ok': False, 'output': f'非法文件路径: {filepath}'}), 400
    out, rc = gm.resolve_conflict(path, filepath, content)
    return jsonify({'ok': rc == 0, 'output': out})

@app.route('/api/repo/<name>/merge', methods=['POST'])
def api_merge(name):
    """合并分支"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    data = request.json
    source = data.get('source', '')
    no_ff = data.get('no_ff', False)
    if not _no_dash(source):
        return jsonify({'ok': False, 'output': '非法引用名（不允许以 - 开头）'}), 400
    out, rc = gm.merge_branch(path, source, no_ff)
    return jsonify({'ok': rc == 0, 'output': out})

@app.route('/api/repo/<name>/rebase-onto', methods=['POST'])
def api_rebase_onto(name):
    """变基到指定分支"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    data = request.json
    onto = data.get('onto', '')
    if not _no_dash(onto):
        return jsonify({'ok': False, 'output': '非法引用名（不允许以 - 开头）'}), 400
    out, rc = gm.rebase_branch(path, onto)
    return jsonify({'ok': rc == 0, 'output': out})

# ============================================================
# 提交规范检查 API
# ============================================================
CONVENTIONAL_RE = re.compile(r'^(feat|fix|docs|refactor|chore|test|perf|style|ci|build|revert)(\([^)]*\))?:\s*.+')

def validate_commit_message(msg):
    """检查提交信息是否符合 conventional commits"""
    if not msg:
        return {'valid': False, 'error': '提交信息不能为空'}
    if len(msg) > 100:
        return {'valid': False, 'error': f'提交信息过长({len(msg)}字符)，建议不超过100字符'}
    if CONVENTIONAL_RE.match(msg):
        return {'valid': True, 'type': 'conventional'}
    # 宽松模式：只要不是纯数字或无意义字符就算通过
    if re.match(r'^[a-zA-Z\u4e00-\u9fa5]', msg):
        return {'valid': True, 'type': 'plain', 'warning': '建议使用 conventional commits 格式 (feat/fix/docs: ...)'}
    return {'valid': False, 'error': '提交信息格式不规范，建议使用 feat: / fix: / docs: 等前缀'}

@app.route('/api/validate-commit')
def api_validate_commit():
    """验证提交信息"""
    msg = request.args.get('msg', '')
    result = validate_commit_message(msg)
    return jsonify(result)

# ============================================================
# 敏感信息扫描 API
# ============================================================
@app.route('/api/repo/<name>/scan-secrets')
def api_scan_secrets(name):
    """扫描敏感信息"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    # 限流
    if not rate_limit(f'secrets:{name}', min_interval=60):
        return jsonify({'error': '扫描过于频繁，请60秒后重试'}), 429
    since_days = request.args.get('since_days', 90, type=int)
    try:
        secrets = gm.scan_secrets(path, max_commits=100, since_days=since_days)
    except Exception:
        rate_limit_release(f'secrets:{name}')  # 失败不占用限流窗口
        raise
    return jsonify({'secrets': secrets, 'count': len(secrets)})

# ============================================================
# 大文件预警 API
# ============================================================
@app.route('/api/repo/<name>/check-large-files')
def api_check_large_files(name):
    """检查工作区大文件"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    threshold = request.args.get('threshold', 1048576, type=int)  # 默认1MB
    files = gm.get_workspace_status(path)
    large = []
    for f in (files or []):
        filepath = f.get('path', '')
        full = os.path.join(path, filepath)
        if os.path.isfile(full):
            size = os.path.getsize(full)
            if size > threshold:
                large.append({'path': filepath, 'size': size, 'size_human': f'{size/1024/1024:.1f}MB'})
    return jsonify({'files': large, 'count': len(large), 'threshold': threshold})

# ============================================================
# 多仓库批量操作 API（并行执行 + SSE 逐仓库推送进度）
# ============================================================
def _batch_run(op_name, op, repos_dict=None):
    """并行对仓库执行 op(path)，单仓库失败不影响其它；每完成一个立即
    通过 SSE 推送进度（前端实时反馈），全部完成后返回汇总。
    repos_dict 可传 {名称:路径} 子集（按分组批量时用）。"""
    from concurrent.futures import ThreadPoolExecutor
    targets = dict(repos_dict if repos_dict is not None else REPOS)
    results = {}

    def _one(kv):
        name, path = kv
        lock = _get_repo_lock(name)
        if not lock.acquire(timeout=45):
            results[name] = {'ok': False, 'error': '仓库操作繁忙，请稍后再试'}
        else:
            try:
                out, rc = op(path)
                results[name] = {'ok': rc == 0, 'output': out}
            except Exception as e:
                results[name] = {'ok': False, 'error': str(e)}
            finally:
                invalidate_status_cache(name)
                lock.release()
        broadcast({'type': 'batch_progress', 'op': op_name, 'repo': name,
                   'ok': results[name].get('ok', False),
                   'done': len(results), 'total': len(targets)})

    with ThreadPoolExecutor(max_workers=min(4, max(1, len(targets)))) as ex:
        list(ex.map(_one, list(targets.items())))
    return results

@app.route('/api/batch/pull', methods=['POST'])
def api_batch_pull():
    """批量 pull（并行）。body 可选 {group: 分组名} 只对分组内仓库执行"""
    data = request.get_json(silent=True) or {}
    targets = REPOS
    group = data.get('group')
    if group:
        members = (CFG.get('groups') or {}).get(group) or []
        targets = {n: REPOS[n] for n in members if n in REPOS}
        if not targets:
            return jsonify({'error': '分组「%s」内没有有效仓库' % group}), 404
    return jsonify(_batch_run('pull', gm.repo_pull, targets))

@app.route('/api/batch/fetch', methods=['POST'])
def api_batch_fetch():
    """批量 fetch（并行）。body 可选 {group: 分组名} 只对分组内仓库执行"""
    data = request.get_json(silent=True) or {}
    targets = REPOS
    group = data.get('group')
    if group:
        members = (CFG.get('groups') or {}).get(group) or []
        targets = {n: REPOS[n] for n in members if n in REPOS}
        if not targets:
            return jsonify({'error': '分组「%s」内没有有效仓库' % group}), 404
    return jsonify(_batch_run('fetch', gm.repo_fetch, targets))

# ============================================================
# CI/CD 集成 API
# ============================================================
@app.route('/api/repo/<name>/ci-status')
def api_ci_status(name):
    """获取 CI/CD 构建状态（支持 GitHub Actions 和 GitLab CI）"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    # 检查 GitHub Actions / GitLab CI
    workflows_dir = os.path.join(path, '.github', 'workflows')
    gitlab_ci = os.path.join(path, '.gitlab-ci.yml')
    has_github = os.path.isdir(workflows_dir)
    has_gitlab = os.path.isfile(gitlab_ci)
    if not has_github and not has_gitlab:
        return jsonify({'has_ci': False, 'message': '未配置 CI/CD（未找到 .github/workflows 或 .gitlab-ci.yml）'})
    try:
        workflows = []
        if has_github:
            import glob
            yml_files = glob.glob(os.path.join(workflows_dir, '*.yml')) + glob.glob(os.path.join(workflows_dir, '*.yaml'))
            for f in yml_files:
                name_match = re.search(r'name:\s*(.+)', open(f, encoding='utf-8', errors='replace').read())
                workflows.append({
                    'file': os.path.basename(f),
                    'name': name_match.group(1).strip() if name_match else os.path.basename(f),
                    'type': 'github-actions'
                })
        if has_gitlab:
            # 读取 .gitlab-ci.yml 的 stages（可选解析，失败不影响）
            stage_list = []
            try:
                with open(gitlab_ci, encoding='utf-8', errors='replace') as f:
                    ci_content = f.read()
                import re as _re
                stages_match = _re.search(r'^stages:\s*\n((?:  - .+\n?)+)', ci_content, _re.M)
                if stages_match:
                    stage_list = _re.findall(r'  - (.+)', stages_match.group(1))
            except Exception:
                pass
            workflows.append({
                'file': '.gitlab-ci.yml',
                'name': 'GitLab CI',
                'type': 'gitlab-ci',
                'stages': stage_list
            })
        return jsonify({'has_ci': True, 'workflows': workflows, 'count': len(workflows)})
    except Exception as e:
        return jsonify({'has_ci': True, 'error': str(e)})

# ============================================================
# PR/MR 视图 API
# ============================================================
@app.route('/api/repo/<name>/pull-requests')
def api_pull_requests(name):
    """获取 PR/MR 列表（轻量级：只统计提交数，不做完整diff）"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    # 获取所有远程分支
    local, remote = gm.get_branches(path)
    local_names = set()
    for b in (local or []):
        local_names.add(b if isinstance(b, str) else b.get('name', ''))
    # 主分支：优先本地存在的，否则用 origin/ 引用（新 clone 可能只有远程）
    main_branch = 'main'
    for b in list(local or []) + list(remote or []):
        b_name = b if isinstance(b, str) else b.get('name', '')
        short = b_name.split('origin/', 1)[1] if b_name.startswith('origin/') else b_name
        if short in ('main', 'master', 'develop'):
            main_branch = short
            break
    main_ref = main_branch if main_branch in local_names else f'origin/{main_branch}'

    # 一次 for-each-ref 拿到所有远程分支名 + 最新标题（避免每分支再跑一次 log）
    out_ref, _ = gm.git(path, 'for-each-ref',
                        '--format=%(refname:short)|%(subject)', 'refs/remotes')
    branches = []
    for line in (out_ref or '').splitlines():
        if '|' not in line:
            continue
        branch_name, subj = line.split('|', 1)
        if not branch_name or 'HEAD' in branch_name:
            continue
        short = branch_name.split('origin/', 1)[1] if branch_name.startswith('origin/') else branch_name
        if not short or short == main_branch:
            continue
        remote_ref = branch_name if branch_name.startswith('origin/') else f'origin/{short}'
        branches.append((short, remote_ref, (subj or '').strip()))

    # 每分支仅 1 次 rev-list（--left-right 一次拿 ahead+behind）：
    # 每分支 3 次 → 1 次，另加 1 次 for-each-ref 取全部标题（get_branches 仍在最前调用）
    prs = []
    for short, remote_ref, subj in branches:
        try:
            out_ab, rc_ab = gm.git(path, 'rev-list', '--count', '--left-right',
                                   f'{main_ref}...{remote_ref}')
            if rc_ab != 0:
                continue
            parts = (out_ab or '').split()
            if len(parts) != 2:
                continue
            behind, ahead = int(parts[0]), int(parts[1])
            if ahead == 0 and behind == 0:
                continue  # 已同步，跳过
            prs.append({'branch': short, 'title': subj or short,
                        'ahead': ahead, 'behind': behind})
        except Exception:
            pass
    return jsonify({'prs': prs, 'count': len(prs), 'base': main_branch})

# ============================================================
# 撤销 / 二分定位 / 提交信息建议 / 发布时间线
# ============================================================
@app.route('/api/repo/<name>/undo', methods=['POST'])
def api_undo(name):
    """撤销最近一次提交（reset --soft ORIG_HEAD，改动保留在暂存区可重新提交）"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    out, rc = gm.undo_last_commit(path)
    return jsonify({'ok': rc == 0, 'output': out})


@app.route('/api/repo/<name>/bisect/status')
def api_bisect_status(name):
    """二分定位状态：是否进行中 + 当前待测提交"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    in_prog, cur = gm.bisect_status(path)
    return jsonify({'in_progress': in_prog, 'current': cur})


@app.route('/api/repo/<name>/bisect/start', methods=['POST'])
def api_bisect_start(name):
    """开始二分：bad 默认 HEAD，good 为最后一个正常版本"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    data = request.json or {}
    bad = data.get('bad') or 'HEAD'
    good = data.get('good') or None
    if not _no_dash(bad, good):
        return jsonify({'ok': False, 'output': '非法引用名（不允许以 - 开头）'}), 400
    out, rc = gm.bisect_start(path, bad, good)
    return jsonify({'ok': rc == 0, 'output': out})


@app.route('/api/repo/<name>/bisect/mark', methods=['POST'])
def api_bisect_mark(name):
    """把当前检测提交标记为 good/bad，返回下一个待测提交"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    data = request.json or {}
    out, rc = gm.bisect_mark(path, bool(data.get('good')))
    return jsonify({'ok': rc == 0, 'output': out, 'done': rc == 0 and 'is the first bad commit' in (out or '')})


@app.route('/api/repo/<name>/bisect/reset', methods=['POST'])
def api_bisect_reset(name):
    """结束二分，回到原分支"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    out, rc = gm.bisect_reset(path)
    return jsonify({'ok': rc == 0, 'output': out})


@app.route('/api/repo/<name>/suggest-commit')
def api_suggest_commit(name):
    """提交信息建议：本地启发式（改动文件类型/规模 → conventional 前缀+摘要）。
    配置了 ai_model 且本机 Ollama(127.0.0.1:11434) 可用时用本地模型生成——数据不出本机。"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    ns, _ = gm.git(path, 'diff', '--cached', '--numstat')
    if not (ns or '').strip():
        ns, _ = gm.git(path, 'diff', '--numstat')
    files, adds, dels = [], 0, 0
    for line in (ns or '').splitlines():
        parts = line.split('\t')
        if len(parts) == 3:
            files.append(parts[2])
            adds += int(parts[0]) if parts[0].isdigit() else 0
            dels += int(parts[1]) if parts[1].isdigit() else 0
    if not files:
        return jsonify({'message': '', 'source': 'none', 'hint': '没有待提交的变更'})

    def prefix_for(p):
        pl = p.lower().replace('\\', '/')
        if 'test' in pl:
            return 'test'
        if pl.endswith('.md') or '/docs/' in pl:
            return 'docs'
        if '.github/' in pl or '.gitlab' in pl or 'jenkins' in pl:
            return 'ci'
        if 'dockerfile' in pl or pl.endswith('.lock') or 'requirements' in pl or pl.endswith('pom.xml'):
            return 'build'
        if pl.endswith('.sql') or '/migration' in pl:
            return 'feat'
        return 'feat'

    cnt = Counter(prefix_for(x) for x in files)
    prefix = cnt.most_common(1)[0][0]
    shown = '、'.join(os.path.basename(x) for x in files[:3])
    more = f' 等 {len(files)} 个文件' if len(files) > 3 else ''
    heuristic = f'{prefix}: 更新{shown}{more}（+{adds}/-{dels}）'

    ai_model = (CFG.get('ai_model') or '').strip()
    if ai_model:
        try:
            import urllib.request
            diff_out, _ = gm.git(path, 'diff', 'HEAD', '-U1')
            prompt = ('根据下面的 git diff 写一条 conventional commits 中文提交信息，'
                      '格式如 "feat: xxx"，一行、不超过72字符，只输出信息本身：\n\n'
                      + (diff_out or '')[:4000])
            req = urllib.request.Request(
                'http://127.0.0.1:11434/api/generate',
                data=json.dumps({'model': ai_model, 'prompt': prompt, 'stream': False}).encode('utf-8'),
                headers={'Content-Type': 'application/json'})
            with urllib.request.urlopen(req, timeout=10) as resp:
                ans = json.loads(resp.read().decode('utf-8', errors='replace')).get('response', '').strip()
            if ans:
                return jsonify({'message': ans.splitlines()[0][:100], 'source': 'ai', 'model': ai_model})
        except Exception:
            pass  # Ollama 未启动/模型不存在 → 静默回退启发式
    return jsonify({'message': heuristic, 'source': 'heuristic'})


@app.route('/api/releases')
def api_releases():
    """发布快照时间线（DORA 指标的原始数据，按时间倒序，每仓库最多50条）"""
    hist = gm.load_releases() or {}
    out = {}
    for repo, snaps in hist.items():
        rows = sorted(snaps or [], key=lambda s: _parse_rel_time(s.get('time', '')), reverse=True)
        out[repo] = rows[:50]
    return jsonify(out)


# ============================================================
# Cherry-pick / Reflog / 重置 / 图片 diff / 智能拆分提交
# ============================================================
@app.route('/api/repo/<name>/cherry-pick/abort', methods=['POST'])
def api_cherry_pick_abort(name):
    """中止 cherry-pick，回到摘取前状态"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    out, rc = gm.git(path, 'cherry-pick', '--abort')
    return jsonify({'ok': rc == 0, 'output': out})

@app.route('/api/repo/<name>/reflog')
def api_reflog(name):
    """操作历史（reflog）列表：每次 commit/checkout/merge/rebase/reset 的记录"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    n = request.args.get('n', 50, type=int)
    n = max(1, min(n, 200))
    out, rc = gm.git(path, 'reflog', '-n', str(n), '--date=short',
                     '--format=%gd|%gs|%h|%ci')
    rows = []
    for ln in (out or '').splitlines():
        parts = ln.split('|', 3)
        if len(parts) == 4:
            rows.append({'ref': parts[0], 'action': parts[1],
                         'hash7': parts[2], 'date': parts[3][:16]})
    return jsonify({'rows': rows})

@app.route('/api/repo/<name>/reset-to', methods=['POST'])
def api_reset_to(name):
    """回退到 reflog 里的任意位置。mode: soft(保留改动在暂存区) /
    mixed(保留改动在工作区) / hard(彻底丢弃，危险)"""
    path = REPOS.get(name)
    if not path:
        return jsonify({'error': '仓库不存在'}), 404
    data = request.json
    target = str(data.get('target', '') or '').strip()
    mode = str(data.get('mode', 'soft') or '').strip()
    if not target or not _no_dash(target):
        return jsonify({'ok': False, 'output': '非法目标'}), 400
    if mode not in ('soft', 'mixed', 'hard'):
        return jsonify({'ok': False, 'output': '非法模式（soft/mixed/hard）'}), 400
    out, rc = gm.git(path, 'reset', '--' + mode, target, timeout=30)
    _audit('reset-to', name, f'{mode} -> {target}', rc == 0)
    return jsonify({'ok': rc == 0, 'output': out})

_MIME_MAP = {'.png': 'image/png', '.jpg': 'image/jpeg', '.jpeg': 'image/jpeg',
             '.gif': 'image/gif', '.webp': 'image/webp', '.bmp': 'image/bmp'}

def _blob_b64(repo, spec):
    """git cat-file 读取对象内容转 base64（图片 diff 用）。失败返回 (None, 原因)"""
    if ':' in spec:
        rev, p = spec.split(':', 1)
        if not rev.strip() or not _no_dash(rev):
            return None, '非法引用'
        if safe_repo_path(repo, p) is None:
            return None, '非法路径'
    elif not _no_dash(spec):
        return None, '非法引用'
    try:
        r = subprocess.run(['git', '-C', repo, 'cat-file', '-p', spec],
                           capture_output=True, timeout=30,
                           creationflags=gm._SUBPROC_FLAGS, env=gm._git_env())
        if r.returncode != 0:
            return None, '对象不存在'
        if len(r.stdout) > 8 * 1024 * 1024:
            return None, '文件过大（>8MB）'
        import base64
        return base64.b64encode(r.stdout).decode('ascii'), ''
    except Exception as e:
        return None, str(e)

@app.route('/api/repo/<name>/image')
def api_image(name):
    """读取新旧两版图片（base64）。old/new 为 <rev>:<路径> 形式的对象描述；
    worktree_new=1 时新图直接读工作区磁盘文件。"""
    repo = REPOS.get(name)
    if not repo:
        return jsonify({'error': '仓库不存在'}), 404
    path = request.args.get('path', '')
    if safe_repo_path(repo, path) is None:
        return jsonify({'error': '非法文件路径'}), 400
    ext = os.path.splitext(path)[1].lower()
    if ext not in _MIME_MAP:
        return jsonify({'error': '不是受支持的图片类型'}), 400
    mime = _MIME_MAP[ext]
    resp = {'mime': mime}

    def _pack(b64, err):
        return {'b64': b64, 'exists': b64 is not None, 'error': err}

    old_spec = request.args.get('old', '')
    if old_spec:
        b64, err = _blob_b64(repo, old_spec)
        resp['old'] = _pack(b64, err)
    new_spec = request.args.get('new', '')
    if new_spec:
        b64, err = _blob_b64(repo, new_spec)
        resp['new'] = _pack(b64, err)
    if request.args.get('worktree_new') == '1':
        full = safe_repo_path(repo, path)
        b64, err = None, '文件不存在'
        if full and os.path.isfile(full):
            try:
                if os.path.getsize(full) > 8 * 1024 * 1024:
                    err = '文件过大（>8MB）'
                else:
                    import base64
                    with open(full, 'rb') as f:
                        b64 = base64.b64encode(f.read()).decode('ascii')
                    err = ''
            except Exception as e:
                b64, err = None, str(e)
        resp['new'] = _pack(b64, err)
    return jsonify(resp)

@app.route('/api/repo/<name>/composer')
def api_composer(name):
    """智能拆分提交预览：按文件类型/目录把未提交改动聚类成若干组，
    每组给一条建议提交信息（离线启发式；配置 ai_model 时前端可再润色）"""
    repo = REPOS.get(name)
    if not repo:
        return jsonify({'error': '仓库不存在'}), 404
    files = gm.get_workspace_status(repo) or []
    groups = {}
    for f in files:
        p = str(f.get('path', '')).replace('\\', '/')
        pl = p.lower()
        if 'test' in pl:
            pre = 'test'
        elif pl.endswith('.md') or '/docs/' in pl:
            pre = 'docs'
        elif '.github/' in pl or '.gitlab' in pl or 'jenkins' in pl:
            pre = 'ci'
        elif 'dockerfile' in pl or pl.endswith('.lock') or 'requirements' in pl or pl.endswith('pom.xml'):
            pre = 'build'
        else:
            pre = 'feat'
        g = groups.setdefault(pre, {'files': [], 'adds': 0, 'dels': 0})
        g['files'].append(p)
        g['adds'] += f.get('added', 0) or 0
        g['dels'] += f.get('removed', 0) or 0
    order = {'feat': 0, 'build': 1, 'ci': 2, 'docs': 3, 'test': 4}
    out = []
    for pre, g in groups.items():
        shown = '、'.join(os.path.basename(x) for x in g['files'][:2])
        more = ' 等 %d 个文件' % len(g['files']) if len(g['files']) > 2 else ''
        out.append({'prefix': pre, 'files': g['files'],
                    'message': '%s: 更新%s%s（+%d/-%d）' % (pre, shown, more, g['adds'], g['dels'])})
    out.sort(key=lambda x: order.get(x['prefix'], 9))
    return jsonify({'groups': out})


# ============================================================
# 启动
# ============================================================
if __name__ == '__main__':
    import socket
    port = int(os.environ.get('GIT_WEB_PORT', '8420'))

    def _port_state(p):
        """返回 'free'(空闲) / 'alive'(有活服务) / 'zombie'(死进程残留占用)。
        崩溃退出的程序可能在内核里留下无人 accept 的 LISTEN socket：
        TCP 握手能通（内核代答）但永远不会有响应——这种占用无法接管，
        只能等持有句柄的进程退出或重启系统。"""
        s = socket.socket()
        s.settimeout(1.5)
        try:
            s.connect(('127.0.0.1', p))
        except OSError:
            return 'free'
        try:
            s.sendall(b'GET /api/config HTTP/1.0\r\nHost: localhost\r\n\r\n')
            data = s.recv(64)
            return 'alive' if data else 'zombie'
        except OSError:
            return 'zombie'
        finally:
            s.close()

    def _port_owners(p):
        """查出占用端口的进程：[(pid, 进程名, 命令行), ...]（纯标准库，离线可用）。
        netstat 拿 LISTENING 的 PID，tasklist 拿进程名，wmic 拿命令行；
        任一步失败不影响整体（字段留空）。"""
        owners = []
        try:
            out = subprocess.run(['netstat', '-ano', '-p', 'tcp'], capture_output=True,
                                 text=True, timeout=10, encoding='utf-8', errors='replace',
                                 creationflags=_SUBPROC_FLAGS).stdout
            pids = {ln.split()[-1] for ln in out.splitlines()
                    if ln.strip() and ln.split()[-1].isdigit()
                    and (':' + str(p)) in ln and 'LISTENING' in ln.upper()}
        except Exception:
            return owners
        for pid in sorted(pids, key=lambda x: int(x)):
            name, cmdline = '', ''
            try:
                out = subprocess.run(['tasklist', '/FI', 'PID eq ' + pid, '/FO', 'CSV', '/NH'],
                                     capture_output=True, text=True, timeout=10,
                                     encoding='utf-8', errors='replace',
                                     creationflags=_SUBPROC_FLAGS).stdout
                for line in out.strip().splitlines():
                    parts = [x.strip() for x in line.split(',')]
                    # CSV 列序：映像名称, PID, 会话名, 会话号, 内存
                    if len(parts) >= 1 and parts[0].strip('"'):
                        name = parts[0].strip('"')
                        break
            except Exception:
                pass
            try:
                out = subprocess.run(
                    ['wmic', 'process', 'where', 'processid=' + pid, 'get', 'commandline', '/value'],
                    capture_output=True, text=True, timeout=10, encoding='utf-8', errors='replace',
                    creationflags=_SUBPROC_FLAGS).stdout
                for ln in out.splitlines():
                    if ln.startswith('CommandLine='):
                        cmdline = ln[len('CommandLine='):].strip()
                        break
            except Exception:
                pass
            owners.append((pid, name, cmdline))
        return owners

    def _is_ours(name, cmdline):
        blob = (str(name) + ' ' + str(cmdline)).lower()
        return 'git_web.py' in blob

    def _exit_with_hint():
        if sys.stdin and sys.stdin.isatty():
            input("\n按回车键退出...")
        sys.exit(1)

    state = _port_state(port)
    if state in ('alive', 'zombie'):
        owners = _port_owners(port)
        ours = [o for o in owners if _is_ours(o[1], o[2])]
        others = [o for o in owners if o not in ours]
        print("\n[错误] 端口 %d 已被占用！占用信息：" % port)
        for pid, name, cmd in owners:
            tag = '  <-- 本工具的实例' if _is_ours(name, cmd) else ''
            print("  进程 PID %s  %s%s" % (pid, name or '(未知进程)', tag))
            if cmd:
                print("    命令行: %s" % cmd[:160])
        if not owners:
            print("  （未能识别占用进程，可能需要管理员权限查看）")
        if state == 'alive' and ours:
            print("\n这是本工具已在运行（可能之前的窗口还没关）。")
            print("  1. 直接打开 http://127.0.0.1:%d 即可使用，无需重复启动；" % port)
            print("  2. 若想重启工具，先结束旧实例：")
            for pid, name, cmd in ours:
                print("     taskkill /F /PID %s" % pid)
            print("  3. 或换端口启动：set GIT_WEB_PORT=9000 后运行本程序。")
        else:
            print("\n处理方式（任选其一）：")
            n = 0
            for pid, name, cmd in others:
                n += 1
                print("  %d. 结束占用进程（%s）：" % (n, name or 'PID ' + pid))
                print("     taskkill /F /PID %s" % pid)
                if n >= 3:
                    break
            if n == 0:
                n += 1
                print("  %d. 在任务管理器详细信息页按 PID 找到占用进程并结束" % n)
            n += 1
            print("  %d. 或换端口启动：set GIT_WEB_PORT=9000 后运行本程序。" % n)
            if state == 'zombie':
                n += 1
                print("  %d. 若是崩溃残留的僵死占用且无法结束，重启电脑即可释放。" % n)
        _exit_with_hint()
    # 访问日志静默
    import logging
    logging.getLogger('werkzeug').setLevel(logging.ERROR)
    logging.getLogger('flask.app').setLevel(logging.ERROR)
    print("Git Repository Monitor started")
    print("URL: http://127.0.0.1:%d" % port)
    print("Close this window to stop")
    print()
    start_repo_watchers()
    # 环境自检：离线排障时一眼看出缺什么
    try:
        first_path = next(iter(REPOS.values()), os.getcwd())
        gv, _ = gm.git(first_path, '--version')
        n_ok = sum(1 for p in REPOS.values() if os.path.isdir(p) and os.path.exists(os.path.join(p, '.git')))
        print('[self-check] git: %s | watchdog: %s | 仓库: %d 个（有效 %d）' % (
            (gv or '未找到!').strip(), '已安装（实时推送）' if WATCHDOG_OK else '未安装（30 秒轮询）',
            len(REPOS), n_ok))
        if n_ok < len(REPOS):
            invalid = [n for n, p in REPOS.items() if not (os.path.isdir(p) and os.path.exists(os.path.join(p, '.git')))]
            print('[self-check] 无效仓库: %s（可在设置的仓库管理中移除或修正路径）' % ', '.join(invalid))
    except Exception as e:
        print('[self-check] 跳过：%s' % e)
    # 启动完成后自动打开浏览器（socket 绑定需要一点时间，延迟 1.2 秒）；
    # 设置环境变量 GIT_WEB_NO_BROWSER=1 可跳过（脚本/无人值守场景）
    if os.environ.get('GIT_WEB_NO_BROWSER', '') != '1':
        url = 'http://127.0.0.1:%d' % port

        def _open_browser(u):
            try:
                print('[browser] 正在打开 %s' % u)
                webbrowser.open(u)
            except Exception as e:
                print('[browser] 自动打开失败（手动访问 %s 即可）：%s' % (u, e))

        threading.Timer(1.2, _open_browser, args=(url,)).start()
    app.run(host='127.0.0.1', port=port, debug=False)
