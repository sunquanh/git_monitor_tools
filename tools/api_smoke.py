#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
API 冒烟自检（零依赖，纯标准库）

用途：改完 git_web.py / web/index.html 后，快速确认主要只读接口没被改坏，
并检测接口返回结构（字段增删 / 类型变化）相对快照的“漂移”——改 A 坏 B 时能第一时间发现。

用法：
  1. 先启动服务：python git_web.py（或双击 启动.bat）
  2. 首次建立快照：python tools/api_smoke.py --init
  3. 日常检查：    python tools/api_smoke.py

选项：
  --base URL     服务地址（默认 http://127.0.0.1:8420；设了环境变量 GIT_WEB_PORT 时用该端口）
  --snapshot P   快照文件路径（默认与本脚本同目录的 api_snapshot.json）
  --init         把本次结果写入快照（覆盖），供以后比对
  --timeout N    单请求超时秒数（默认 15）

检查方式：只发 GET，不改任何数据。对每个接口记录 HTTP 状态码 + JSON 结构签名
（递归展开的“键路径 -> 类型”，深度上限 4，列表只取首元素签名）。
数据值本身（如提交数、时间戳）变化不算漂移，不参与比对。

退出码：0 全部通过；1 有失败或漂移；2 服务连不上。
"""

import argparse
import json
import os
import sys
import urllib.error
import urllib.parse
import urllib.request

MAX_DEPTH = 4


def type_name(v):
    if v is None:
        return "null"
    if isinstance(v, bool):
        return "bool"
    if isinstance(v, int):
        return "int"
    if isinstance(v, float):
        return "float"
    if isinstance(v, str):
        return "str"
    if isinstance(v, list):
        return "list"
    if isinstance(v, dict):
        return "dict"
    return type(v).__name__


def signature(v, prefix="", depth=0):
    """把 JSON 值展开成 {键路径: 类型} 的扁平签名。"""
    out = {}
    if isinstance(v, dict):
        if depth >= MAX_DEPTH or not v:
            out[prefix or "$"] = "dict"
            return out
        for k in sorted(v.keys()):
            path = f"{prefix}.{k}" if prefix else str(k)
            out.update(signature(v[k], path, depth + 1))
    elif isinstance(v, list):
        if depth >= MAX_DEPTH or not v:
            out[prefix or "$"] = "list"
            return out
        out.update(signature(v[0], prefix + "[]", depth + 1))
    else:
        out[prefix or "$"] = type_name(v)
    return out


def fetch(base, path, timeout):
    url = base.rstrip("/") + path
    req = urllib.request.Request(url, headers={"User-Agent": "api-smoke/1.0"})
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            body = resp.read()
            return resp.status, resp.headers.get_content_type(), body
    except urllib.error.HTTPError as e:
        return e.code, e.headers.get_content_type() if e.headers else "", e.read()


def check_endpoint(base, path, timeout):
    status, ctype, body = fetch(base, path, timeout)
    entry = {"status": status}
    if ctype == "application/json":
        try:
            data = json.loads(body.decode("utf-8", "replace"))
            entry["sig"] = signature(data)
            entry["_data"] = data
        except (ValueError, UnicodeDecodeError):
            entry["sig"] = {"$": "invalid-json"}
    else:
        entry["sig"] = {"$": ctype or "unknown"}
    return entry


def first_repo_name(repos_data):
    """从 /api/repos 的返回里灵活取第一个仓库名（兼容 list/dict 两种形状）。"""
    if isinstance(repos_data, list) and repos_data:
        first = repos_data[0]
        if isinstance(first, dict):
            return first.get("name") or first.get("repo") or ""
        return str(first)
    if isinstance(repos_data, dict) and repos_data:
        return str(next(iter(repos_data.keys())))
    return ""


def build_endpoints(base, timeout):
    """固定只读接口 + 按第一个仓库动态拼出的 per-repo 接口。"""
    paths = ["/", "/api/config", "/api/repos", "/api/app-health",
             "/api/stats", "/api/dora", "/api/weekly"]
    results = {}
    for p in paths:
        results[p] = check_endpoint(base, p, timeout)
    name = first_repo_name(results["/api/repos"].pop("_data", None))
    if name:
        q = urllib.parse.quote(name, safe="")
        for p in [f"/api/repo/{q}", f"/api/repo/{q}/commits",
                  f"/api/repo/{q}/branches", f"/api/repo/{q}/tags",
                  f"/api/repo/{q}/stash", f"/api/repo/{q}/graph",
                  f"/api/workspace/{q}"]:
            results[p] = check_endpoint(base, p, timeout)
    else:
        print("提示：/api/repos 里没有仓库，per-repo 接口本次跳过")
    for entry in results.values():
        entry.pop("_data", None)
    return results


def diff_entries(path, old, new):
    problems = []
    if old["status"] != new["status"]:
        problems.append(f"{path}：状态码 {old['status']} -> {new['status']}")
    old_sig, new_sig = old.get("sig", {}), new.get("sig", {})
    for k in sorted(set(old_sig) - set(new_sig)):
        problems.append(f"{path}：字段消失 {k}（原类型 {old_sig[k]}）")
    for k in sorted(set(new_sig) - set(old_sig)):
        problems.append(f"{path}：新增字段 {k}（类型 {new_sig[k]}）")
    for k in sorted(set(old_sig) & set(new_sig)):
        if old_sig[k] != new_sig[k]:
            problems.append(f"{path}：字段类型变化 {k}：{old_sig[k]} -> {new_sig[k]}")
    return problems


def main():
    ap = argparse.ArgumentParser(description="git_web API 冒烟自检")
    default_port = os.environ.get("GIT_WEB_PORT", "8420")
    ap.add_argument("--base", default=f"http://127.0.0.1:{default_port}")
    ap.add_argument("--snapshot", default=os.path.join(os.path.dirname(os.path.abspath(__file__)), "api_snapshot.json"))
    ap.add_argument("--init", action="store_true", help="把本次结果写入快照")
    ap.add_argument("--timeout", type=float, default=15)
    args = ap.parse_args()

    try:
        current = build_endpoints(args.base, args.timeout)
    except (urllib.error.URLError, OSError) as e:
        print(f"连不上服务 {args.base}：{e}")
        print("请先启动服务（python git_web.py 或 启动.bat）再运行本脚本。")
        return 2

    if args.init:
        with open(args.snapshot, "w", encoding="utf-8") as f:
            json.dump(current, f, ensure_ascii=False, indent=1, sort_keys=True)
        print(f"快照已写入 {args.snapshot}（共 {len(current)} 个接口）")
        return 0

    if not os.path.exists(args.snapshot):
        print(f"快照不存在：{args.snapshot}")
        print("先运行一次：python tools/api_smoke.py --init")
        return 2

    with open(args.snapshot, encoding="utf-8") as f:
        snapshot = json.load(f)

    problems = []
    for path in sorted(set(snapshot) - set(current)):
        problems.append(f"{path}：快照里有、本次未检查到（接口被删？）")
    for path in sorted(set(current) - set(snapshot)):
        problems.append(f"{path}：新增接口（快照里没有，确认后用 --init 更新快照）")
    for path in sorted(set(snapshot) & set(current)):
        problems.extend(diff_entries(path, snapshot[path], current[path]))

    checked = len(set(snapshot) & set(current))
    if problems:
        print(f"冒烟未通过（检查了 {checked} 个接口，发现 {len(problems)} 处差异）：")
        for p in problems:
            print("  - " + p)
        return 1
    print(f"冒烟通过：{checked} 个接口状态码与结构签名与快照一致")
    return 0


if __name__ == "__main__":
    sys.exit(main())
