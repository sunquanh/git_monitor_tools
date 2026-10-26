#!/usr/bin/env python3
"""推送前扫描（pre-push 钩子调用）：扫描待推送 diff 新增行里的密钥与本机绝对路径。

用法：git push 时由钩子自动调用，stdin 为 pre-push 的 ref 行
      （local_ref local_sha remote_ref remote_sha）；也可手动跑：
      git push --dry-run 不触发钩子，手动验证用：
      printf 'refs/heads/x <local> refs/heads/x <remote>\n' | python3 tools/push_scan.py
规则与网页端推送扫描（git_monitor.scan_outgoing）同一套；两边模式如有改动请同步。
新分支（remote_sha 全 0）时以 origin/HEAD 的 merge-base 为比对起点；取不到则跳过并提示。
发现可疑内容打印清单并 exit 1；无问题 exit 0。误报时用 git push --no-verify 跳过。
纯标准库，无第三方依赖。
"""
import re
import subprocess
import sys

SECRET_PATTERNS = [
    ("AWS Access Key", re.compile(r"\bAKIA[0-9A-Z]{16}\b")),
    ("GitHub Token", re.compile(r"\bgh[pousr]_[A-Za-z0-9]{16,}\b")),
    ("OpenAI Key", re.compile(r"\bsk-[A-Za-z0-9_-]{20,}\b")),
    ("密码赋值", re.compile(
        r"(?i)(?<![a-z])(password|passwd|pwd|secret|token|api[_-]?key|access[_-]?key|auth[_-]?token)(?![a-z])"
        r"\s*[=:]\s*['\"][^'\"]{4,}['\"]")),
]
PRIVATE_KEY_FILE_RE = re.compile(
    r"(^|/)(id_(rsa|dsa|ecdsa|ed25519)|[^/]+\.(pem|key|pfx|p12))$", re.IGNORECASE)
WIN_PATH_RE = re.compile(r"(?<![A-Za-z0-9_.-])[A-Za-z]:[\\/][^\s\"'<>|]+")


def git(root, *args):
    p = subprocess.run(["git", "-C", root] + list(args),
                       capture_output=True, text=True, timeout=120)
    return p.stdout, p.returncode


def scan_diff(diff_text):
    findings = []
    cur_file, new_line = "", 0
    for raw in (diff_text or "").splitlines():
        if raw.startswith("diff --git "):
            cur_file = raw.split(" b/", 1)[1] if " b/" in raw else ""
            if cur_file and PRIVATE_KEY_FILE_RE.search(cur_file):
                findings.append(f"{cur_file}:0 [私钥文件] {cur_file}")
            continue
        m = re.match(r"@@ -\d+(?:,\d+)? \+(\d+)", raw)
        if m:
            new_line = int(m.group(1))
            continue
        if not raw.startswith("+") or raw.startswith("+++"):
            continue
        content = raw[1:]
        for name, pat in SECRET_PATTERNS:
            mm = pat.search(content)
            if mm:
                findings.append(f"{cur_file}:{new_line} [{name}] {mm.group(0)[:80]}")
        mm = WIN_PATH_RE.search(content)
        if mm:
            findings.append(f"{cur_file}:{new_line} [本机绝对路径] {mm.group(0)[:80]}")
        new_line += 1
    return findings


def main():
    root = sys.argv[1] if len(sys.argv) > 1 else "."
    findings = []
    for line in sys.stdin:
        parts = line.split()
        if len(parts) < 4:
            continue
        local_ref, local_sha, _remote_ref, remote_sha = parts[:4]
        if set(local_sha) == {"0"}:
            continue  # 删除分支：无新增内容可扫
        if set(remote_sha) == {"0"}:
            base, rc = git(root, "merge-base", local_sha, "origin/HEAD")
            base = base.strip() if rc == 0 else ""
            if not base:
                print(f"[push_scan] {local_ref} 是新分支且无 origin/HEAD 可比对，跳过扫描")
                continue
            old = base
        else:
            old = remote_sha
        diff, rc = git(root, "diff", "-U0", "--no-color", "--no-renames",
                       f"{old}..{local_sha}")
        if rc != 0:
            continue
        findings.extend(scan_diff(diff))
    if not findings:
        return 0
    print("[push_scan] 待推送内容扫描发现可疑内容：")
    for f in findings[:50]:
        print("  " + f)
    if len(findings) > 50:
        print(f"  ……等共 {len(findings)} 条")
    return 1


if __name__ == "__main__":
    sys.exit(main())
