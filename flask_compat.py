#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""flask_compat — 用 Python 标准库实现的迷你 Flask 兼容层。

背景：工具要在离线电脑上"拷过去就能跑"，不能依赖 pip 安装 Flask。
本模块实现了 git_web.py 实际用到的 Flask 接口子集（基于 http.server）：

    Flask / @app.route(支持 <name>、<path:xxx> 参数) / app.run
    jsonify / request(args/json/headers/method/host/get_json) / Response(含流式 SSE)
    send_from_directory(带路径穿越防护) / before_request / errorhandler / test_client

不在子集内的 Flask 特性（模板/Jinja、session、blueprint 等）未实现。
路由处理逻辑：ThreadingHTTPServer（每连接一线程，SSE 长连接友好），
HTTP/1.1 keep-alive：普通响应带 Content-Length，流式响应用 chunked 编码。
"""

import json
import os
import re
import threading
import time
from email.utils import formatdate
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlparse, parse_qs, unquote

# 兼容层所在目录：send_from_directory 的相对目录（如 'web'）以此为基准，
# 不依赖启动时的工作目录
_BASE_DIR = os.path.dirname(os.path.abspath(__file__))

_JSON_CT = 'application/json; charset=utf-8'


class HTTPException(Exception):
    """werkzeug.exceptions.HTTPException 的最小替身"""

    def __init__(self, code=500, description='', name=''):
        super().__init__(description or str(code))
        self.code = code
        self.description = description or 'Error'
        self.name = name or 'Error'


# 统一安全响应头（所有响应都带）。frame-ancestors / X-Frame-Options 用于挡点击劫持：
# 本工具的 CSRF 防线依赖「跨站请求带不上自定义头」，但被 iframe 嵌入后请求由页面
# 自己发出、头是齐的，不挡 iframe 等于绕过 CSRF 防护。
SECURITY_HEADERS = {
    'X-Frame-Options': 'DENY',
    'Content-Security-Policy': "frame-ancestors 'none'; base-uri 'self'; form-action 'self'",
    'X-Content-Type-Options': 'nosniff',
    'Referrer-Policy': 'no-referrer',
}


class Response:
    """统一响应对象。body=普通字节；stream=生成器（SSE 等流式场景）"""

    def __init__(self, body=None, status=200, mimetype=None, headers=None, stream=None):
        if isinstance(body, str):
            body = body.encode('utf-8')
        self.body = body if body is not None else b''
        self.status = status
        self.mimetype = mimetype
        self.headers = dict(headers or {})
        self.stream = stream


def jsonify(*args):
    """Flask jsonify：单参数 dict/list 直接序列化"""
    obj = args[0] if len(args) == 1 else (args or None)
    return Response(json.dumps(obj, ensure_ascii=False).encode('utf-8'),
                    mimetype=_JSON_CT)


class _Args:
    """request.args：大小写不敏感取值 + Flask 式 type 强转"""

    def __init__(self, data):
        self._data = data  # {key: [values]}

    def get(self, key, default=None, type=None):
        vals = self._data.get(key)
        if not vals:
            return default
        v = vals[0]
        if type is not None and type is not str:
            try:
                return type(v)
            except (ValueError, TypeError):
                return default
        return v


class _Headers:
    """request.headers：大小写不敏感 get"""

    def __init__(self, pairs):
        self._pairs = [(str(k).lower(), v) for k, v in (pairs or [])]

    def get(self, key, default=None):
        k = str(key).lower()
        for kk, v in self._pairs:
            if kk == k:
                return v
        return default


class _Request:
    """thread-local 的请求上下文（等价 Flask 的 request 代理）"""

    _local = threading.local()

    @classmethod
    def _bind(cls, req):
        cls._local.req = req

    @classmethod
    def _current(cls):
        return getattr(cls._local, 'req', None)

    # ---- 代理属性（直接把 _Request 当 Flask 的 request 用） ----
    def __init__(self, method, path, query, headers, body, host, remote=''):
        self.method = method
        self.path = path
        self.args = _Args(parse_qs(query, keep_blank_values=True))
        self.headers = headers
        self.body = body
        self.host = host
        # 真实 TCP 对端地址（不受 X-Forwarded-For 影响，审计日志用它）
        self.remote_addr = remote or ''
        self._json_cache = ...
        self.result = None  # (status, headers, payload)，由 dispatch 的 emit 填充

    @property
    def json(self):
        """Flask 语义：空 body 视为 {}（方便 data.get 写法）；坏 JSON 抛 400。
        顶层必须是对象：`null` / `[1,2]` / `"abc"` 一律 400 —— 否则下游 data.get()
        抛 AttributeError，前端只能看到 500 和 Python 异常原文。"""
        if self._json_cache is ...:
            if not self.body:
                self._json_cache = {}
            else:
                try:
                    parsed = json.loads(self.body.decode('utf-8'))
                except Exception:
                    raise HTTPException(400, 'JSON 请求体解析失败')
                if parsed is None:
                    parsed = {}
                elif not isinstance(parsed, dict):
                    raise HTTPException(400, 'JSON 请求体必须是对象（{...}）')
                self._json_cache = parsed
        return self._json_cache

    def get_json(self, silent=False, force=False):
        v = self.json
        if v is None and not silent:
            raise HTTPException(400, '无法解析 JSON 请求体')
        return v


class _Proxy:
    """模块级 request 代理：转发到当前线程绑定的 _Request"""

    def __getattr__(self, name):
        req = _Request._current()
        if req is None:
            raise RuntimeError('request 只能在请求处理线程内访问')
        return getattr(req, name)


request = _Proxy()


# ---------------- 路由匹配 ----------------
def _compile_rule(rule):
    """'/api/repo/<name>/commit/<hash>' → (regex, ['name','hash'])
    <path:xxx> 匹配含 / 的剩余部分；<xxx> 匹配单个路径段"""
    param_names = []

    def repl(m):
        inner = m.group(1)
        if ':' in inner:
            conv, name = inner.split(':', 1)
        else:
            conv, name = 'string', inner
        param_names.append(name)
        return '(?P<%s>.+)' % name if conv == 'path' else '(?P<%s>[^/]+)' % name

    pattern = re.sub(r'<([^<>]+)>', repl, rule)
    return re.compile('^' + pattern + '$'), param_names


def send_from_directory(directory, path):
    """静态文件（带 ../ 穿越防护）。相对目录以本模块所在目录为基准"""
    root = directory if os.path.isabs(directory) else os.path.join(_BASE_DIR, directory)
    root = os.path.realpath(root)
    full = os.path.realpath(os.path.join(root, unquote(str(path))))
    try:
        safe = os.path.commonpath([root, full]) == root
    except ValueError:
        # 跨盘符（Windows 不同驱动器）时 commonpath 抛 ValueError，视为非法路径
        safe = False
    if not safe or not os.path.isfile(full):
        raise HTTPException(404, '文件不存在')
    ext = os.path.splitext(full)[1].lower()
    ctype = {
        '.html': 'text/html; charset=utf-8', '.js': 'text/javascript; charset=utf-8',
        '.css': 'text/css; charset=utf-8', '.json': 'application/json; charset=utf-8',
        '.png': 'image/png', '.jpg': 'image/jpeg', '.jpeg': 'image/jpeg',
        '.gif': 'image/gif', '.svg': 'image/svg+xml', '.ico': 'image/x-icon',
        '.woff': 'font/woff', '.woff2': 'font/woff2', '.map': 'application/json',
    }.get(ext, 'application/octet-stream')
    # 静态资源带 ETag / Last-Modified：首页 286 KB，每次打开全量重传太浪费。
    # mtime+size 足够区分版本（文件改了必然变），命中直接 304 空体。
    try:
        st = os.stat(full)
        etag = 'W/"%x-%x"' % (int(st.st_mtime), st.st_size)
        cache_hdrs = {
            'ETag': etag,
            'Last-Modified': formatdate(st.st_mtime, usegmt=True),
            'Cache-Control': 'no-cache',
        }
        if (request.headers.get('If-None-Match') or '') == etag:
            return Response(b'', status=304, headers=cache_hdrs)
    except (OSError, RuntimeError, AttributeError):
        # 非请求上下文（如 GUI 直接调用）或 stat 失败：退化为普通响应
        cache_hdrs = {}
    with open(full, 'rb') as f:
        data = f.read()
    return Response(data, mimetype=ctype, headers=cache_hdrs)


class _Rule:
    def __init__(self, rule, methods, func):
        self.rule = rule
        # 显式声明的 methods 全部保留；GET 自动附带 HEAD（Flask 同款语义）。
        # ⚠ 不能写成 "GET in methods ? {GET,HEAD} : methods"——那会把
        # methods=['GET','POST'] 的 POST 丢掉，导致 POST 全部 404
        self.methods = set(methods) | ({'HEAD'} if 'GET' in methods else set())
        self.regex, self.params = _compile_rule(rule)
        self.func = func
        # 匹配权重：静态字符越多越具体（Flask 同款语义）。
        # 没有它，catch-all 的 '/<path:path>' 会按注册顺序抢先吞掉所有 API 路径。
        self.static_len = len(re.sub(r'<[^<>]+>', '', rule))


class Flask:
    """迷你 Flask 应用：route/before_request/errorhandler/run/test_client"""

    def __init__(self, import_name=None, static_folder=None, static_url_path=None):
        self.import_name = import_name
        self.routes = []
        self._before = []
        self._after = []
        self._error_handlers = []
        self.url_map = self  # 兼容旧测试代码的 app.url_map.iter_rules()

    # ---- 注册 ----
    def route(self, rule, methods=None):
        methods = methods or ['GET']

        def deco(func):
            self.routes.append(_Rule(rule, methods, func))
            return func
        return deco

    def before_request(self, func):
        self._before.append(func)
        return func

    def after_request(self, func):
        self._after.append(func)
        return func

    def errorhandler(self, cls_or_code):
        def deco(func):
            self._error_handlers.append((cls_or_code, func))
            return func
        return deco

    def iter_rules(self):
        return iter(self.routes)

    # ---- 分发（服务器与 test_client 共用） ----
    def _normalize(self, result):
        """视图返回值 → Response：支持 Response / dict / (payload, status) 元组"""
        status = None
        if isinstance(result, tuple) and len(result) == 2:
            result, status = result
        if not isinstance(result, Response):
            result = jsonify(result)
        if status is not None:
            result.status = status
        return result

    def _run_error_handler(self, exc):
        for cls_or_code, fn in self._error_handlers:
            if isinstance(cls_or_code, type) and isinstance(exc, cls_or_code):
                try:
                    return self._normalize(fn(exc))
                except Exception:
                    pass
            elif isinstance(cls_or_code, int) and isinstance(exc, HTTPException) and exc.code == cls_or_code:
                try:
                    return self._normalize(fn(exc))
                except Exception:
                    pass
        # 没有注册匹配的处理器：HTTP 异常按状态码兜底，其它 500
        if isinstance(exc, HTTPException):
            return jsonify({'error': exc.description}), exc.code
        return jsonify({'error': 'Internal Server Error'}), 500

    def dispatch(self, method, path, query, headers, body, host, remote=''):
        """返回 (status, headers_dict, payload)。
        payload 为 bytes（普通响应）或迭代器（SSE 流式响应）"""
        req = _Request(method, path, query, headers, body, host, remote)
        _Request._bind(req)

        def emit(rv):
            """统一出口：记录本次响应（status/payload），供 after_request 的
            审计钩子判断这次写操作成功与否，避免每条路由都手工传 rc。"""
            result = self._resp(self._normalize(rv))
            req.result = result
            return result

        try:
            # 1) before_request（CSRF/Host 校验等；返回非 None 即短路）
            for fn in self._before:
                rv = fn()
                if rv is not None:
                    return emit(rv)
            # 2) 路由匹配（静态部分多者优先，等权保持注册顺序）
            match_path = path
            if len(match_path) > 1 and match_path.endswith('/'):
                match_path = match_path.rstrip('/')  # 尾斜杠透明等价
            for rule in sorted(self.routes, key=lambda r: -r.static_len):
                if method not in rule.methods and not (method == 'HEAD' and 'GET' in rule.methods):
                    continue
                m = rule.regex.match(match_path)
                if not m:
                    continue
                try:
                    rv = rule.func(**m.groupdict())
                except HTTPException as e:
                    return emit(self._run_error_handler(e))
                except Exception as e:
                    return emit(self._run_error_handler(e))
                return emit(rv)
            return emit(self._run_error_handler(
                HTTPException(404, '接口不存在' if path.startswith('/api/') else 'Not Found')))
        finally:
            # after_request：释放仓库写锁、失效状态缓存、写审计等（短路时也要跑）
            for fn in self._after:
                try:
                    fn()
                except Exception:
                    pass
            _Request._bind(None)

    @staticmethod
    def _resp(response):
        headers = dict(response.headers)
        # 统一安全响应头：普通响应、静态文件、错误页、SSE 全覆盖
        for k, v in SECURITY_HEADERS.items():
            headers.setdefault(k, v)
        if response.stream is not None:
            headers['Transfer-Encoding'] = 'chunked'
            headers.setdefault('Cache-Control', 'no-cache')
            ct = response.mimetype or 'text/plain; charset=utf-8'
            if 'charset' not in ct and ct.startswith('text/'):
                ct += '; charset=utf-8'
            headers['Content-Type'] = ct
            return response.status, headers, response.stream
        headers['Content-Type'] = response.mimetype or _JSON_CT
        return response.status, headers, response.body

    # ---- 真实服务器 ----
    def run(self, host='127.0.0.1', port=5000, debug=False):
        app = self

        class Handler(BaseHTTPRequestHandler):
            protocol_version = 'HTTP/1.1'
            timeout = 300  # 死连接（客户端崩溃/断网）最多挂 5 分钟线程即回收

            def _handle(self):
                parsed = urlparse(self.path)
                length = int(self.headers.get('Content-Length') or 0)
                if length > 10 * 1024 * 1024:
                    # 排空 body（分块丢弃，不占内存）再回 413，避免客户端连接被重置
                    remaining = length
                    while remaining > 0:
                        chunk = self.rfile.read(min(65536, remaining))
                        if not chunk:
                            break
                        remaining -= len(chunk)
                    self.send_response(413)
                    self.send_header('Content-Type', 'application/json; charset=utf-8')
                    self.send_header('Content-Length', '0')
                    for k, v in SECURITY_HEADERS.items():
                        self.send_header(k, v)
                    self.end_headers()
                    self.close_connection = True
                    return
                body = self.rfile.read(length) if length else b''
                headers = _Headers(list(self.headers.items()))
                host_hdr = self.headers.get('Host', '')
                try:
                    status, hdrs, payload = app.dispatch(self.command, unquote(parsed.path),
                                                         parsed.query, headers, body, host_hdr,
                                                         remote=self.client_address[0])
                except Exception:
                    status, hdrs, payload = 500, {'Content-Type': _JSON_CT}, \
                        b'{"error": "Internal Server Error"}'
                self.send_response(status)
                for k, v in hdrs.items():
                    self.send_header(k, v)
                if isinstance(payload, (bytes, bytearray)):
                    self.send_header('Content-Length', str(len(payload)))
                    self.end_headers()
                    if self.command != 'HEAD':
                        self.wfile.write(payload)
                else:  # 流式（SSE）：chunked 编码，逐块 flush
                    self.end_headers()
                    try:
                        for chunk in payload:
                            if isinstance(chunk, str):
                                chunk = chunk.encode('utf-8')
                            if not chunk:
                                continue
                            self.wfile.write(b'%x\r\n' % len(chunk) + chunk + b'\r\n')
                            self.wfile.flush()
                        self.wfile.write(b'0\r\n\r\n')
                        self.wfile.flush()
                    except (ConnectionAbortedError, BrokenPipeError, OSError):
                        pass  # 客户端断开（关标签页/刷新）属正常

            do_GET = do_POST = do_PUT = do_DELETE = do_PATCH = do_HEAD = _handle

            def do_OPTIONS(self):
                self.send_response(204)
                self.send_header('Allow', 'GET, POST, PUT, DELETE, PATCH, HEAD, OPTIONS')
                self.send_header('Content-Length', '0')
                self.end_headers()

            def log_message(self, *a):
                pass  # 静默访问日志（与原版抑制 werkzeug 日志一致）

        server = ThreadingHTTPServer((host, port), Handler)
        print(f' * Running on http://{host}:{port}/ (stdlib http.server, zero-dependency)')
        try:
            server.serve_forever()
        except KeyboardInterrupt:
            pass
        finally:
            server.server_close()

    # ---- 测试客户端（供回归测试不经网络直接打接口） ----
    def test_client(self):
        return _TestClient(self)


class _TestResp:
    def __init__(self, status, headers, body):
        self.status_code = status
        self.headers = headers
        self.data = body if isinstance(body, (bytes, bytearray)) else b''

    def get_json(self):
        return json.loads(self.data.decode('utf-8')) if self.data else None


class _TestClient:
    def __init__(self, app):
        self.app = app

    def _req(self, method, path, json_body=None, headers=None, data=None):
        hdr_pairs = list((headers or {}).items())
        headers = _Headers(hdr_pairs)
        body = b''
        if json_body is not None:
            body = json.dumps(json_body).encode('utf-8')
        elif data is not None:
            body = data.encode('utf-8') if isinstance(data, str) else data
        parsed = urlparse(path)
        # Host 与真实服务器同源：取 Host 头（CSRF/Host 白名单测试依赖它）
        host = dict(hdr_pairs).get('Host') or '127.0.0.1'
        status, hdrs, payload = self.app.dispatch(method, unquote(parsed.path), parsed.query,
                                                  headers, body, host)
        if not isinstance(payload, (bytes, bytearray)):
            payload = b''.join(c.encode('utf-8') if isinstance(c, str) else c
                               for c in list(payload)[:200])
        return _TestResp(status, hdrs, payload)

    def get(self, path, headers=None, **kw):
        return self._req('GET', path, headers=headers, **kw)

    def post(self, path, json=None, headers=None, **kw):
        return self._req('POST', path, json_body=json, headers=headers, **kw)

    def options(self, path, headers=None, **kw):
        return self._req('OPTIONS', path, headers=headers, **kw)
