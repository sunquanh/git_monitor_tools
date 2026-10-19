#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Git 仓库监控器 - 实时监控多仓库提交变化 + 上线前分支差异比对
功能：仓库状态总览 / 分组搜索 / 提交历史 / 文件列表导出 / 弹窗+声音通知 /
      开发分支 vs 生产分支比对（多预设）/ 提交图 / 统计面板 / 仓库操作（pull/push/fetch/checkout）/
      浅色/深色主题 / 一键周报 / 快捷键 / 内置设置界面（无第三方依赖，离线可用）
配置：同目录下的 git_monitor.json（首次运行自动生成模板，可改路径/分支，无需改代码）
"""

import os
import sys
import json
import csv
import io
import shutil
import subprocess
import threading
import time
import re
import webbrowser
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timedelta

# tkinter 是桌面 GUI 的可选依赖。Web 版（git_web）在无 Tk 环境
# （Linux/Docker/无显示器）也必须能正常导入本模块，因此改为可选导入：
# 不可用时仅置为 None 并标记 TK_AVAILABLE，GUI 入口会先检查该标志。
try:
    import tkinter as tk
    import tkinter.font as tkfont
    from tkinter import ttk, messagebox, filedialog, Menu
    TK_AVAILABLE = True
except Exception:
    # tkinter 不可用（无显示环境）：提供占位基类，使 GUI 类定义
    # （class Toast(tk.Toplevel) 等）在 import 阶段不报错。这些类
    # 仅在 TK_AVAILABLE 为 True 时才会被实例化（见 main()）。
    class _TkStub(object):
        pass
    class _tk:
        Tk = Toplevel = Frame = Canvas = Label = Button = _TkStub
        LabelFrame = Scale = Scrollbar = Entry = Text = Listbox = _TkStub
        Menu = PhotoImage = Message = Checkbutton = Radiobutton = _TkStub
        PanedWindow = Spinbox = _TkStub
    tk = _tk
    tkfont = None
    ttk = type('_ttk', (), {})
    messagebox = filedialog = Menu = None
    TK_AVAILABLE = False

if os.name == "nt":
    try:
        import winsound
    except Exception:
        winsound = None

# Windows: 子进程创建标志。无控制台运行时（pythonw / 计划任务 / 分离进程启动），
# git 等控制台子进程每次执行都会让系统新分配一个 CMD 窗口（闪黑框）；
# CREATE_NO_WINDOW 阻止弹窗。有控制台运行时该标志无副作用；POSIX 上为 0（允许传 0）。
_SUBPROC_FLAGS = 0x08000000 if os.name == "nt" else 0  # CREATE_NO_WINDOW

# Pillow（仅用于 PNG 导出 / 窗口图标）：可选依赖，缺失时自动降级（离线机可不装）
PIL_AVAILABLE = False
try:
    from PIL import Image, ImageDraw
    PIL_AVAILABLE = True
except Exception:
    Image = ImageDraw = None


# 字体：Windows 8+ 自带 Microsoft YaHei UI，中文显示远好于 Segoe UI
# 字体：更现代的字体栈
FONT_UI = "Microsoft YaHei UI"
FONT_UI_B = "Microsoft YaHei UI"
FONT_MONO = "Cascadia Code"  # 现代等宽字体，比 Consolas 更清晰

_FONTS = {}


def _font(spec):
    """惰性创建并缓存 tkfont.Font，避免每次 measure 都新建"""
    if tkfont is None:
        raise RuntimeError("tkinter 不可用，无法创建字体（桌面 GUI 未安装 Tk）")
    if spec not in _FONTS:
        _FONTS[spec] = tkfont.Font(font=spec)
    return _FONTS[spec]


def _blend(c1, c2, t):
    """两个颜色按 t 比例插值（支持 #RRGGBB 与常见颜色名）"""
    def hx(v):
        return (v >> 16) & 255, (v >> 8) & 255, v & 255
    named = {"white": "#FFFFFF", "black": "#000000"}
    c1 = named.get(c1.lower(), c1)
    c2 = named.get(c2.lower(), c2)
    a, b = hx(int(c1[1:], 16)), hx(int(c2[1:], 16))
    m = tuple(int(x + (y - x) * t) for x, y in zip(a, b))
    return "#%02X%02X%02X" % m


def time_ago(iso_str):
    """ISO 时间 → 中文相对时间（刚刚 / N 分钟前 / N 小时前 / N 天前）"""
    try:
        s = iso_str.strip()
        if "T" not in s:
            s = s.replace(" ", "T", 1)
        s = s[:19]  # 只取到秒，忽略时区；兼容旧版 Python fromisoformat 的空格/时区解析问题
        if len(s) == 16:  # 仅到分钟（如提交图 %Y-%m-%d %H:%M）：补秒
            s += ":00"
        dt = datetime.fromisoformat(s)
        secs = (datetime.now() - dt).total_seconds()
    except Exception:
        return ""
    if secs < 0:
        return ""
    if secs < 60:
        return "刚刚"
    if secs < 3600:
        return f"{int(secs // 60)} 分钟前"
    if secs < 86400:
        return f"{int(secs // 3600)} 小时前"
    if secs < 86400 * 7:
        return f"{int(secs // 86400)} 天前"
    return dt.strftime("%m-%d")


# ============================================================
# DPI 缩放：高分屏（125%/150%）下字体按系统 DPI 变大，但 Canvas 像素坐标不变，
# 会导致文字重叠。所有手绘像素坐标统一走 S()，保证与字体同步缩放。
# ============================================================
def dpi_factor():
    if os.name == "nt":
        try:
            import ctypes
            ctypes.windll.shcore.SetProcessDpiAwareness(1)
            return ctypes.windll.user32.GetDpiForSystem() / 96.0
        except Exception:
            pass
    return 1.0


DPIS = dpi_factor()


def S(v):
    """像素坐标按 DPI 缩放（100% 时原样返回）"""
    return int(v * DPIS)


# ============================================================
# 配置加载（外置到 git_monitor.json，方便离线机器改路径/分支）
# ============================================================
if getattr(sys, "frozen", False):
    _BASE = os.path.dirname(sys.executable)          # PyInstaller 打包后：exe 同目录
else:
    _BASE = os.path.dirname(os.path.abspath(__file__))

CONFIG_PATH = os.path.join(_BASE, "git_monitor.json")

DEFAULT_CONFIG = {
    "refresh_interval": 30,
    "theme": "light",
    "auto_refresh": True,
    "sound": True,
    "tray": True,
    "minimize_to_tray": True,
    "repos": {
        "aiops-backend":      r"C:\workspace\git-workspace\yl\yl-backend\aiops-backend",
        "aiops-data-service": r"C:\workspace\git-workspace\yl\yl-data\aiops-data-service",
        "aiops-frontend":     r"C:\workspace\git-workspace\yl\yl-front\aiops-frontend",
    },
    "groups": {},
    "compare": {
        "enabled": True,
        "repo": "aiops-backend",
        "dev_branch": "develop",
        "prod_branch": "main",
        "direction": "dev_to_prod",
        "auto_fetch": True,
    },
    "presets": [],
}


def _normalize_groups(cfg):
    """保证 groups 结构合法：每个仓库至少属于一个分组，空配置时兜底为「默认」。"""
    repos = cfg.get("repos", {})
    groups = cfg.setdefault("groups", {})
    if not isinstance(groups, dict):
        groups = {}
        cfg["groups"] = groups
    member = set()
    for g, names in list(groups.items()):
        if not isinstance(names, list):
            groups[g] = [n for n in (names or []) if isinstance(n, str)]
        member.update(n for n in groups[g] if n in repos)
    if set(repos) - member and "默认" not in groups:
        groups["默认"] = list(repos)
    return cfg


def load_config():
    """读取配置；不存在则写入默认模板"""
    if os.path.exists(CONFIG_PATH):
        try:
            with open(CONFIG_PATH, "r", encoding="utf-8") as f:
                cfg = json.load(f)
            try:
                cfg["refresh_interval"] = max(5, int(cfg.get("refresh_interval", 30)))
            except Exception:
                cfg["refresh_interval"] = 30
            cfg.setdefault("repos", {})
            cfg.setdefault("compare", DEFAULT_CONFIG["compare"])
            cfg.setdefault("presets", [])
            cfg.setdefault("theme", "light")
            cfg.setdefault("auto_refresh", True)
            cfg.setdefault("sound", True)
            cfg.setdefault("tray", True)
            cfg.setdefault("minimize_to_tray", True)
            return _normalize_groups(cfg)
        except Exception:
            # 配置损坏：先备份现场再回退默认，避免静默覆盖导致排查无据
            try:
                shutil.copy2(CONFIG_PATH, CONFIG_PATH + ".bak")
            except Exception:
                pass
    cfg = json.loads(json.dumps(DEFAULT_CONFIG))
    _normalize_groups(cfg)
    save_config(cfg)
    return cfg


def _atomic_write_json(path, obj):
    """原子写 JSON：先写临时文件再 os.replace，避免中途崩溃/断电损坏配置。"""
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(obj, f, ensure_ascii=False, indent=2)
    os.replace(tmp, path)


def save_config(cfg):
    # 写盘前把当前版本留一份 .bak（防手滑改坏/双实例覆盖后无法找回）
    try:
        if os.path.exists(CONFIG_PATH):
            shutil.copy2(CONFIG_PATH, CONFIG_PATH + ".bak")
    except Exception:
        pass  # 备份失败不阻塞保存
    _atomic_write_json(CONFIG_PATH, cfg)


def reload_config():
    """从磁盘重新读取 git_monitor.json，刷新全局 CFG / REPOS / COMPARE / REFRESH_INTERVAL。
    每次比对/刷新前调用，让磁盘上的最新配置立即生效。"""
    global CFG, REPOS, REFRESH_INTERVAL, COMPARE
    CFG = load_config()
    REPOS = CFG["repos"]
    REFRESH_INTERVAL = CFG["refresh_interval"]
    COMPARE = CFG["compare"]
    COMPARE.setdefault("auto_fetch", True)


CFG = load_config()
REPOS = CFG["repos"]
REFRESH_INTERVAL = CFG["refresh_interval"]
COMPARE = CFG["compare"]
COMPARE.setdefault("auto_fetch", True)   # 兼容旧配置：缺失时默认开启


# ============================================================
# 主题（浅色 / 深色）。全局颜色变量由 apply_theme() 赋值，切换主题后重建 UI 生效
# ============================================================
THEMES = {
    "light": {
        "bg":            "#F8FAFC",
        "panel":         "#FFFFFF",
        "accent":        "#3B82F6",
        "accent_hover":  "#2563EB",
        "accent_soft":   "#EFF6FF",
        "text":          "#1E293B",
        "muted":         "#64748B",
        "border":        "#E2E8F0",
        "header":        "#0F172A",
        "header_sub":    "#94A3B8",
        "row_alt":       "#F8FAFC",
        "btn_hover":     "#F1F5F9",
        "btn_disabled":  "#94A3B8",
        "status_clean":    ("#10B981", "已同步", "clean"),
        "status_modified": ("#F59E0B", "有改动", "modified"),
        "status_behind":   ("#EF4444", "落后", "behind"),
        "status_ahead":    ("#3B82F6", "领先", "ahead"),
        "status_invalid":  ("#94A3B8", "无效", "invalid"),
        "soft_clean":    "#D1FAE5",
        "soft_modified": "#FEF3C7",
        "soft_behind":   "#FEE2E2",
        "soft_ahead":    "#DBEAFE",
        "soft_invalid":  "#F1F5F9",
        "tag_add_bg":    "#D1FAE5", "tag_add_fg": "#065F46",
        "tag_del_bg":    "#FEE2E2", "tag_del_fg": "#991B1B",
        "tag_mod_bg":    "#FEF3C7", "tag_mod_fg": "#92400E",
        "diff_add_bg":   "#D1FAE5", "diff_del_bg": "#FEE2E2",
        "diff_hunk_bg":  "#EDE9FE", "diff_prelude_bg": "#F8FAFC",
        "lanes":         ["#3B82F6", "#10B981", "#EF4444", "#8B5CF6",
                          "#F59E0B", "#06B6D4", "#EC4899", "#64748B"],
        "graph_line":    "#CBD5E1",
        "select_bg":     "#DBEAFE", "select_fg": "#1E293B",
        "scroll_bg":     "#CBD5E1",
        "input_border":  "#CBD5E1",
    },
    "dark": {
        "bg":            "#0F172A",
        "panel":         "#1E293B",
        "accent":        "#3B82F6",
        "accent_hover":  "#60A5FA",
        "accent_soft":   "#1E3A5F",
        "text":          "#F1F5F9",
        "muted":         "#94A3B8",
        "border":        "#334155",
        "header":        "#020617",
        "header_sub":    "#64748B",
        "row_alt":       "#1E293B",
        "btn_hover":     "#334155",
        "btn_disabled":  "#475569",
        "status_clean":    ("#10B981", "已同步", "clean"),
        "status_modified": ("#F59E0B", "有改动", "modified"),
        "status_behind":   ("#EF4444", "落后", "behind"),
        "status_ahead":    ("#3B82F6", "领先", "ahead"),
        "status_invalid":  ("#64748B", "无效", "invalid"),
        "soft_clean":    "#064E3B",
        "soft_modified": "#78350F",
        "soft_behind":   "#7F1D1D",
        "soft_ahead":    "#1E3A5F",
        "soft_invalid":  "#1E293B",
        "tag_add_bg":    "#064E3B", "tag_add_fg": "#6EE7B7",
        "tag_del_bg":    "#7F1D1D", "tag_del_fg": "#FCA5A5",
        "tag_mod_bg":    "#78350F", "tag_mod_fg": "#FCD34D",
        "diff_add_bg":   "#064E3B", "diff_del_bg": "#7F1D1D",
        "diff_hunk_bg":  "#2E1065", "diff_prelude_bg": "#1E293B",
        "lanes":         ["#3B82F6", "#10B981", "#EF4444", "#8B5CF6",
                          "#F59E0B", "#06B6D4", "#EC4899", "#94A3B8"],
        "graph_line":    "#475569",
        "select_bg":     "#1E40AF", "select_fg": "#FFFFFF",
        "scroll_bg":     "#475569",
        "input_border":  "#475569",
    },
}

THEME_BG = THEMES["light"]["bg"]
THEME_PANEL = THEMES["light"]["panel"]
THEME_ACCENT = THEMES["light"]["accent"]
THEME_ACCENT_HOVER = THEMES["light"]["accent_hover"]
THEME_ACCENT_SOFT = THEMES["light"]["accent_soft"]
THEME_TEXT = THEMES["light"]["text"]
THEME_MUTED = THEMES["light"]["muted"]
THEME_BORDER = THEMES["light"]["border"]
THEME_HEADER = THEMES["light"]["header"]
THEME_HEADER_SUB = THEMES["light"]["header_sub"]
THEME_ROW_ALT = THEMES["light"]["row_alt"]
THEME_BTN_HOVER = THEMES["light"]["btn_hover"]
THEME_BTN_DISABLED = THEMES["light"]["btn_disabled"]
SELECT_BG = THEMES["light"]["select_bg"]
SELECT_FG = THEMES["light"]["select_fg"]
THEME_SCROLLBAR = THEMES["light"]["scroll_bg"]
THEME_INPUT_BORDER = THEMES["light"]["input_border"]
COLOR_CLEAN = "#E8F5E9"
COLOR_MODIFIED = "#FFF8E1"
COLOR_BEHIND = "#FFEBEE"
COLOR_INVALID = "#ECEFF1"
STATUS_STYLE = THEMES["light"].get("status_clean") and {
    "clean": THEMES["light"]["status_clean"],
    "modified": THEMES["light"]["status_modified"],
    "behind": THEMES["light"]["status_behind"],
    "ahead": THEMES["light"]["status_ahead"],
    "invalid": THEMES["light"]["status_invalid"],
}
LANE_COLORS = THEMES["light"]["lanes"]
GRAPH_LINE = THEMES["light"]["graph_line"]
TAG_COLORS = {
    "A": (THEMES["light"]["tag_add_bg"], THEMES["light"]["tag_add_fg"]),
    "D": (THEMES["light"]["tag_del_bg"], THEMES["light"]["tag_del_fg"]),
    "M": (THEMES["light"]["tag_mod_bg"], THEMES["light"]["tag_mod_fg"]),
}
DIFF_ADD_BG = THEMES["light"]["diff_add_bg"]
DIFF_DEL_BG = THEMES["light"]["diff_del_bg"]
DIFF_HUNK_BG = THEMES["light"]["diff_hunk_bg"]
DIFF_PRELUDE_BG = THEMES["light"]["diff_prelude_bg"]
STATUS_SOFT = {
    "clean": THEMES["light"]["soft_clean"], "modified": THEMES["light"]["soft_modified"],
    "behind": THEMES["light"]["soft_behind"], "ahead": THEMES["light"]["soft_ahead"],
    "invalid": THEMES["light"]["soft_invalid"],
}


def system_theme():
    """读取 Windows 系统深浅色设置（离线）：返回 "light" 或 "dark"。"""
    if os.name != "nt":
        return "light"
    try:
        import winreg
        with winreg.OpenKey(
                winreg.HKEY_CURRENT_USER,
                r"Software\Microsoft\Windows\CurrentVersion\Themes\Personalize") as k:
            v, _ = winreg.QueryValueEx(k, "AppsUseLightTheme")
            return "light" if v else "dark"
    except Exception:
        return "light"


# 主题选项（设置界面显示标签 → 内部键；system = 跟随系统）
THEME_OPTIONS = [("light", "浅色"), ("dark", "深色"), ("system", "跟随系统")]
THEME_LABELS = {k: v for k, v in THEME_OPTIONS}
THEME_KEYS = {v: k for k, v in THEME_OPTIONS}


def apply_theme(name):
    """把主题字典赋值到全局颜色变量。调用后需重建 UI 才能完全生效。
    name 为 "system" 时按 Windows 系统深浅色设置解析。"""
    global THEME_BG, THEME_PANEL, THEME_ACCENT, THEME_ACCENT_HOVER, \
        THEME_ACCENT_SOFT, THEME_TEXT, THEME_MUTED, THEME_BORDER, \
        THEME_HEADER, THEME_HEADER_SUB, THEME_ROW_ALT, THEME_BTN_HOVER, \
        THEME_BTN_DISABLED, SELECT_BG, SELECT_FG, THEME_SCROLLBAR, \
        THEME_INPUT_BORDER, COLOR_CLEAN, COLOR_MODIFIED, COLOR_BEHIND, \
        COLOR_INVALID, STATUS_STYLE, LANE_COLORS, GRAPH_LINE, TAG_COLORS, \
        DIFF_ADD_BG, DIFF_DEL_BG, DIFF_HUNK_BG, DIFF_PRELUDE_BG, STATUS_SOFT
    if name == "system":
        name = system_theme()
    t = THEMES.get(name, THEMES["light"])
    THEME_BG = t["bg"]
    THEME_PANEL = t["panel"]
    THEME_ACCENT = t["accent"]
    THEME_ACCENT_HOVER = t["accent_hover"]
    THEME_ACCENT_SOFT = t["accent_soft"]
    THEME_TEXT = t["text"]
    THEME_MUTED = t["muted"]
    THEME_BORDER = t["border"]
    THEME_HEADER = t["header"]
    THEME_HEADER_SUB = t["header_sub"]
    THEME_ROW_ALT = t["row_alt"]
    THEME_BTN_HOVER = t["btn_hover"]
    THEME_BTN_DISABLED = t["btn_disabled"]
    SELECT_BG = t["select_bg"]
    SELECT_FG = t["select_fg"]
    THEME_SCROLLBAR = t["scroll_bg"]
    THEME_INPUT_BORDER = t["input_border"]
    COLOR_CLEAN = t["tag_add_bg"]
    COLOR_MODIFIED = t["tag_mod_bg"]
    COLOR_BEHIND = t["tag_del_bg"]
    COLOR_INVALID = t["bg"]
    STATUS_STYLE = {
        "clean": t["status_clean"], "modified": t["status_modified"],
        "behind": t["status_behind"], "ahead": t["status_ahead"],
        "invalid": t["status_invalid"],
    }
    LANE_COLORS = t["lanes"]
    GRAPH_LINE = t["graph_line"]
    TAG_COLORS = {
        "A": (t["tag_add_bg"], t["tag_add_fg"]),
        "D": (t["tag_del_bg"], t["tag_del_fg"]),
        "M": (t["tag_mod_bg"], t["tag_mod_fg"]),
    }
    DIFF_ADD_BG = t["diff_add_bg"]
    DIFF_DEL_BG = t["diff_del_bg"]
    DIFF_HUNK_BG = t["diff_hunk_bg"]
    DIFF_PRELUDE_BG = t["diff_prelude_bg"]
    STATUS_SOFT = {
        "clean": t["soft_clean"], "modified": t["soft_modified"],
        "behind": t["soft_behind"], "ahead": t["soft_ahead"],
        "invalid": t["soft_invalid"],
    }


apply_theme(CFG.get("theme", "light"))


# ============================================================
# Git 操作封装
# ============================================================
# 所有 git 子进程的基础环境：本地工具不应交互式索要凭据/分页。
_BASE_GIT_ENV = {
    "GIT_TERMINAL_PROMPT": "0",
    "GIT_PAGER": "cat",
}


def _git_env(extra=None):
    """构造 git 子进程环境：当前环境 + 非交互基线，再叠加调用方覆盖。
    绕过 git() 直接调 subprocess.run 的地方也要走这里，否则
    GIT_TERMINAL_PROMPT/GIT_PAGER 的防护会在那几条路径上失效。"""
    full = os.environ.copy()
    full.update(_BASE_GIT_ENV)
    if extra:
        full.update(extra)
    return full


def git(repo_path, *args, timeout=15, env=None, input=None):
    """执行 git 命令，返回 (stdout, returncode)。
    本地命令默认 15s 超时（status/log/diff 足够）；网络命令（fetch/pull/push）
    由调用方显式传更长 timeout，避免离线/慢网时刷新卡住。
    env: 在「当前环境 + _BASE_GIT_ENV」基础上覆盖的环境变量（如 GIT_EDITOR）。
    input: 作为 stdin 传给 git（check-ignore --stdin / apply - / am - 需要）。
    带 -c core.quotePath=false: 非 ASCII 文件名(中文/特殊字符)在 status/diff
    numstat 等输出中原样显示, 否则会被 C 风格八进制转义导致路径解析失败。"""
    # 非交互环境：GIT_TERMINAL_PROMPT=0 让缺凭据的 fetch/pull/push 直接失败返回，
    # 而不是在无 tty 的工作线程里等一个永远不会到来的密码输入（会一直挂到超时）。
    # GIT_PAGER=cat 避免某些全局配置把输出接到分页器。调用方 env 仍可覆盖。
    full_env = _git_env(env)
    try:
        # 自动添加 safe.directory 配置以解决多用户环境下的所有权问题
        git_cmd = ["git", "-C", repo_path, "-c", "core.quotePath=false", "-c", f"safe.directory={repo_path}"] + list(args)
        r = subprocess.run(
            git_cmd,
            capture_output=True, text=True, timeout=timeout,
            encoding="utf-8", errors="replace", env=full_env,
            input=input, creationflags=_SUBPROC_FLAGS
        )
        # ⚠️ 必须 rstrip 而非 strip: porcelain 第一行是 " M file" 这种以空格开头
        # 的未暂存状态, strip() 会把首行前导空格剥掉 → XY 列错位、路径左移一位,
        # 工作台把第一个文件误判为"已暂存"、路径变 ".txt" 之类 → 暂存/丢弃全失效。
        out = r.stdout.rstrip()
        # 失败且无 stdout 时把 stderr 透出(否则调用方只能看到 rc 号, 看不到真实报错)
        if r.returncode != 0 and not out:
            out = (r.stderr or "").rstrip()
        return out, r.returncode
    except Exception as e:
        return str(e), 1


def _unquote_git_path(s):
    """还原 git 对路径的 C 风格转义(porcelain/numstat 输出中的引号包裹形式)。

    设 core.quotePath=false 后非 ASCII 直接原样输出, 但含空格/引号/反斜杠/控制符
    的路径仍会被 C 风格转义(如 \"a b.txt\"、\"x\"、\\n 等), 这里统一还原。
    """
    if not (len(s) >= 2 and s[0] == '"' and s[-1] == '"'):
        return s
    body = s[1:-1]
    out = bytearray()
    i = 0
    _MAP = {'n': b'\n', 't': b'\t', '\\': b'\\', '"': b'"'}
    while i < len(body):
        c = body[i]
        if c == '\\' and i + 1 < len(body):
            nxt = body[i + 1]
            if nxt in _MAP:
                out.extend(_MAP[nxt])
                i += 2
                continue
            if nxt.isdigit():
                j = i + 1
                octs = ''
                while j < len(body) and len(octs) < 3 and body[j].isdigit():
                    octs += body[j]
                    j += 1
                if octs:
                    out.append(int(octs, 8))
                    i = j
                    continue
        out.extend(c.encode('utf-8'))
        i += 1
    try:
        return out.decode('utf-8')
    except Exception:
        return out.decode('utf-8', errors='replace')


def pick_ws_repo(info_map, repos):
    """工作台自动选仓: 返回第一个有未提交变更的仓库名(用监控轮询的缓存状态), 无则 None。"""
    for name in repos:
        st = (info_map or {}).get(name) or {}
        if st.get("uncommitted"):
            return name
    return None


def get_status(repo_path):
    """获取仓库状态字典。
    用一次 `git status --porcelain=v2 --branch` 同时拿分支 / 未提交数 / 领先落后
    （原来要 3 次 git 调用），无上游跟踪时回退 rev-list 推算。"""
    if not os.path.isdir(repo_path):
        return {"invalid": True, "branch": "N/A", "uncommitted": 0,
                "ahead": 0, "behind": 0, "last_commit": "路径无效",
                "last_date": "", "last_hash": "", "added": 0, "removed": 0}

    branch, ahead, behind, uncommitted, have_ab = "N/A", 0, 0, 0, False
    out, _ = git(repo_path, "status", "--porcelain=v2", "--branch")
    for line in out.splitlines():
        if line.startswith("# branch.head "):
            branch = line[len("# branch.head "):].strip() or "N/A"
        elif line.startswith("# branch.ab "):
            m = re.match(r"^# branch\.ab \+(\d+) -(\d+)$", line)
            if m:
                ahead, behind = int(m.group(1)), int(m.group(2))
                have_ab = True
        elif line and not line.startswith("#"):
            uncommitted += 1  # 1.x/2.x 变更行 + u 冲突行 + ? 未跟踪行

    # 无上游跟踪（或 detached）时没有 branch.ab：回退用 rev-list 推算
    if not have_ab:
        # detached HEAD 时 branch 形如 "(detached ...)"，需先解析其真实上游
        cmp_ref = None
        if branch.startswith("("):
            up, urc = git(repo_path, "rev-parse", "--abbrev-ref", "HEAD@{upstream}")
            if urc == 0 and up.strip():
                cmp_ref = up.strip()
        elif branch != "N/A":
            cmp_ref = f"origin/{branch}"
        if cmp_ref:
            ab_out, _ = git(repo_path, "rev-list", "--left-right", "--count",
                            f"{cmp_ref}...HEAD")
            if ab_out and "\t" in ab_out:
                behind_str, ahead_str = ab_out.split("\t")
                try:
                    behind = int(behind_str.strip())
                    ahead = int(ahead_str.strip())
                except ValueError:
                    pass

    # 一次 log 同时取短哈希/完整哈希/日期/标题/作者，省一次 git 进程启动
    last, _ = git(repo_path, "log", "-1", "--format=%h|%H|%ai|%s|%an")
    last_hash = ""
    last_date = ""
    last_author = ""
    if "|" in last:
        parts = last.split("|", 4)
        h, full_h, d, s = parts[0], parts[1], parts[2], parts[3]
        last_author = parts[4] if len(parts) > 4 else ""
        last = f"{h} - {s}"
        last_date = d
        last_hash = full_h

    # 变更量徽章：vs HEAD 的净增/删行数（未跟踪文件不计；无变更时不跑 numstat 省一次调用）
    added = removed = 0
    if uncommitted > 0:
        ns, nrc = git(repo_path, "diff", "HEAD", "--numstat")
        if nrc == 0:
            for line in ns.splitlines():
                parts = line.split("\t")
                if len(parts) == 3:
                    try:
                        added += int(parts[0])
                        removed += int(parts[1])
                    except ValueError:
                        pass

    # 健康度评分 (0-100)
    health = 100
    health -= min(uncommitted * 2, 30)  # 未提交扣分，最多30
    health -= min(behind * 3, 40)       # 落后扣分，最多40
    health -= min(ahead * 1, 10)        # 领先轻微扣分
    health = max(0, health)
    
    return {
        "invalid": False,
        "branch": branch,
        "uncommitted": uncommitted,
        "ahead": ahead,
        "behind": behind,
        "last_commit": last or "无提交",
        "last_date": last_date,
        "last_hash": last_hash or "",
        "last_author": last_author,
        "added": added,
        "removed": removed,
        "health": health,
    }


def parse_log(out):
    """把 `git log --format=%H|%an|%ai|%s` 的输出解析为提交列表"""
    commits = []
    for line in out.splitlines():
        if "|" not in line:
            continue
        parts = line.split("|", 3)
        if len(parts) == 4:
            commits.append({
                "hash": parts[0], "hash7": parts[0][:7],
                "author": parts[1], "date": parts[2][:16], "message": parts[3],
            })
    return commits


def get_commits(repo_path, n=50):
    out, _ = git(repo_path, "log", f"-{n}", "--format=%H|%an|%ai|%s")
    return parse_log(out)


def get_changed_files(repo_path, commit_hash):
    out, _ = git(repo_path, "diff-tree", "--no-commit-id", "--name-status", "-r", commit_hash)
    files = []
    for line in out.splitlines():
        parts = line.split("\t", 1)
        if len(parts) == 2:
            files.append({"status": parts[0], "path": parts[1]})
    return files


# 提交详情/diff 的服务端截断上限：超大提交（如含生成文件的提交）原始 diff 可能几百 KB，
# 全量传给前端会拖慢响应和渲染（点击提交图卡顿的根源）。超过上限截断并附标记。
DIFF_OUTPUT_MAX_BYTES = 100 * 1024


def get_commit_show(repo_path, commit_hash, max_bytes=DIFF_OUTPUT_MAX_BYTES):
    """提交详情（show --stat -p）。超过 max_bytes 截断，末尾附截断标记，
    避免超大提交拖慢接口响应与前端渲染。"""
    out, _ = git(repo_path, "show", "--stat", "-p", commit_hash, timeout=30)
    data = out.encode("utf-8", errors="replace")
    if max_bytes and len(data) > max_bytes:
        data = data[:max_bytes]
        out = data.decode("utf-8", errors="replace")
        # 按行截断，避免把最后一行切成半个字符
        out = out[:out.rfind("\n") + 1] if "\n" in out else out
        out += f"\n... [diff 过大已截断：原始 {len(data)}+ 字节，仅显示前 {max_bytes // 1024} KB，可用“导出补丁”获取完整内容]"
    return out


def open_in_explorer(path):
    try:
        if os.name == "nt":
            os.startfile(path)
        elif os.name == "posix":
            webbrowser.open(f"file://{path}")
    except Exception:
        pass


def open_with_default_app(path):
    """用系统默认应用打开文件（如默认编辑器/查看器）。返回是否成功。
    nt: os.startfile 即按扩展名调用默认程序；posix: xdg-open。"""
    try:
        if os.name == "nt":
            os.startfile(path)
        elif os.name == "posix":
            subprocess.Popen(["xdg-open", path])
        else:
            return False
        return True
    except Exception:
        return False


# ---------- 仓库操作 ----------
def get_branches(repo_path):
    """返回 (本地分支列表, 远程分支列表)"""
    local, _ = git(repo_path, "branch", "--format=%(refname:short)")
    remote, _ = git(repo_path, "branch", "-r", "--format=%(refname:short)")
    return ([l.strip() for l in local.splitlines() if l.strip()],
            [r.strip() for r in remote.splitlines() if r.strip()])


def repo_fetch(repo_path):
    out, rc = git(repo_path, "fetch", "--all", "--prune", timeout=15)
    return out, rc


def repo_pull(repo_path):
    out, rc = git(repo_path, "pull", timeout=30)
    return out, rc


def repo_push(repo_path):
    out, rc = git(repo_path, "push", timeout=30)
    return out, rc


def repo_checkout(repo_path, target):
    """target 形如 develop 或 origin/feature-x"""
    if target.startswith("origin/"):
        args = ["checkout", "-B", target[len("origin/"):],
                "--track", target]
    else:
        args = ["checkout", target]
    out, rc = git(repo_path, *args)
    return out, rc


# ---------- 高级操作（右键菜单 / 分支面板） ----------
def repo_cherry_pick(repo_path, commit_hash):
    """把指定提交应用到当前分支（cherry-pick，离线）"""
    return git(repo_path, "cherry-pick", commit_hash, timeout=90)


def repo_revert(repo_path, commit_hash):
    """回滚指定提交（revert --no-edit，生成反向提交）"""
    return git(repo_path, "revert", "--no-edit", commit_hash, timeout=90)


# ---------- Interactive Rebase ----------
def get_rebase_commits(repo_path, onto, n=20):
    """获取可用于 interactive rebase 的提交列表"""
    out, rc = git(repo_path, "log", f"-{n}", "--format=%H|%h|%an|%ai|%s", onto + "..HEAD")
    if rc != 0:
        return []
    commits = []
    for line in (out or '').splitlines():
        parts = line.split('|', 4)
        if len(parts) == 5:
            commits.append({
                'hash': parts[0], 'hash7': parts[1], 'author': parts[2],
                'date': parts[3], 'message': parts[4]
            })
    return commits


def interactive_rebase(repo_path, onto, actions):
    """执行 interactive rebase（全程非交互，Web 后端可安全调用）
    actions: [{hash, action: pick|squash|fixup|reword|drop, new_message?}]

    实现要点：
    - todo 只用 pick/drop/fixup + exec 行；GIT_SEQUENCE_EDITOR=cp 直接采用我们
      的 todo，GIT_EDITOR=true 兜底防止任何编辑器交互挂起。
    - reword(带新消息) = pick + `exec git commit --amend -F 消息文件`；
      squash(带新消息) = fixup + 同款 amend（等价"合并后改写为指定消息"）；
      squash 不带消息 = fixup（保留被合并提交的原消息，git squash 必开编辑器，
      离线非交互场景只能这样降级）。
    - 消息写入临时文件并用正斜杠路径引用，避免 Windows 反斜杠在 sh 里的转义坑。
    """
    if not actions:
        return "没有可操作的提交", 1
    # rebase 要求工作区干净，提前给出可读错误而不是 git 的原始报错
    st_out, _ = git(repo_path, "status", "--porcelain")
    if (st_out or "").strip():
        return "工作区有未提交的更改，请先提交或 stash 后再 Rebase", 1
    # 第一个生效的动作必须是 pick（对基底提交做 squash/fixup 无意义，git 会直接报错）
    first = next((a for a in actions if a.get("action") != "drop"), None)
    if first and first.get("action") in ("squash", "fixup"):
        return "第一个提交不能是 squash/fixup（它没有可合并的上一个提交）", 1

    import tempfile
    # 过滤掉已是 onto 祖先的提交（含 onto 自身）：pick 它们会产生空提交并卡住 rebase
    def _is_ancestor(h):
        _, rc = git(repo_path, "merge-base", "--is-ancestor", h, onto)
        return rc == 0
    skipped = []
    kept = []
    for a in actions:
        h = (a.get("hash", "") or "").strip()
        if h and a.get("action", "pick") != "drop" and _is_ancestor(h):
            skipped.append(h[:7])
        else:
            kept.append(a)
    actions = kept
    if skipped:
        notes = [f"已跳过 {len(skipped)} 个基底已有的提交: {', '.join(skipped)}"]
    else:
        notes = []
    if not actions:
        return "没有可操作的提交（所选提交都在基底之内）", 1
    msg_dir = tempfile.mkdtemp(prefix="gm_rebase_")
    todo_lines = []  # notes 已在上面初始化（祖先过滤提示），此处勿重复置空
    msg_idx = 0
    for a in actions:
        action = a.get("action", "pick")
        h = (a.get("hash", "") or "").strip()
        msg = (a.get("new_message", "") or "").strip()
        if not h:
            continue
        if action == "reword" and msg:
            msg_file = os.path.join(msg_dir, f"msg{msg_idx}.txt").replace("\\", "/")
            msg_idx += 1
            with open(msg_file, "w", encoding="utf-8", newline="\n") as f:
                f.write(msg + "\n")
            todo_lines.append(f"pick {h}")
            todo_lines.append(f'exec git commit --amend -F "{msg_file}"')
        elif action == "squash" and msg:
            msg_file = os.path.join(msg_dir, f"msg{msg_idx}.txt").replace("\\", "/")
            msg_idx += 1
            with open(msg_file, "w", encoding="utf-8", newline="\n") as f:
                f.write(msg + "\n")
            todo_lines.append(f"fixup {h}")
            todo_lines.append(f'exec git commit --amend -F "{msg_file}"')
        elif action == "squash":
            todo_lines.append(f"fixup {h}")
            notes.append("squash 未提供新消息，已按 fixup 处理（保留被合并提交的原消息）")
        else:
            todo_lines.append(f"{action} {h}")
    todo_content = "\n".join(todo_lines) + "\n"
    todo_path = os.path.join(msg_dir, "todo.txt")
    with open(todo_path, "w", encoding="utf-8", newline="\n") as f:
        f.write(todo_content)
    todo_ref = todo_path.replace("\\", "/")
    try:
        out, rc = git(repo_path, "rebase", "-i", onto, timeout=300, env={
            "GIT_SEQUENCE_EDITOR": f'cp "{todo_ref}"',
            "GIT_EDITOR": "true",
        })
        if rc != 0 and not (out or "").strip():
            out = "Rebase 失败（可能产生冲突），可在「冲突」页解决后点击继续 Rebase"
        if notes:
            out = (out or "") + "\n" + "\n".join(notes)
        return out, rc
    finally:
        shutil.rmtree(msg_dir, ignore_errors=True)


def squash_commits(repo_path, last_n, message=None):
    """合并最近 N 个提交"""
    if last_n < 2:
        return '需要至少2个提交', 1
    # 获取 HEAD~N 的 hash
    out, rc = git(repo_path, "rev-parse", f"HEAD~{last_n}")
    if rc != 0:
        return out, rc
    onto = out.strip()
    # 使用 reset --soft 实现 squash
    out, rc = git(repo_path, "reset", "--soft", onto)
    if rc != 0:
        return out, rc
    # 提交
    if message:
        return git(repo_path, "commit", "-m", message)
    else:
        return git(repo_path, "commit", "--no-edit")


def get_conflict_files(repo_path):
    """获取冲突文件列表"""
    out, rc = git(repo_path, "diff", "--name-only", "--diff-filter=U")
    if rc != 0:
        return []
    return [f.strip() for f in (out or '').splitlines() if f.strip()]


def get_conflict_content(repo_path, filepath):
    """获取冲突文件的三方内容（ours/theirs/base）"""
    # 读取当前冲突文件
    out, rc = git(repo_path, "show", ":2:" + filepath)  # ours
    ours = out if rc == 0 else ''
    out, rc = git(repo_path, "show", ":3:" + filepath)  # theirs
    theirs = out if rc == 0 else ''
    # 尝试获取 base
    out, rc = git(repo_path, "show", ":1:" + filepath)  # base
    base = out if rc == 0 else ''
    return {'ours': ours, 'theirs': theirs, 'base': base}


def resolve_conflict(repo_path, filepath, content):
    """解决冲突：用指定内容覆盖文件并标记为已解决"""
    # 写入解决后的内容
    full_path = os.path.join(repo_path, filepath)
    try:
        with open(full_path, 'w', encoding='utf-8') as f:
            f.write(content)
    except Exception as e:
        return str(e), 1
    # 标记为已解决
    return git(repo_path, "add", filepath)


def merge_branch(repo_path, source, no_ff=False):
    """合并分支"""
    args = ["merge"]
    if no_ff:
        args.append("--no-ff")
    args.append(source)
    return git(repo_path, *args, timeout=60)


def rebase_branch(repo_path, onto):
    """变基到指定分支"""
    return git(repo_path, "rebase", onto, timeout=120)


def abort_rebase(repo_path):
    """中止 rebase"""
    return git(repo_path, "rebase", "--abort")


def continue_rebase(repo_path):
    """继续 rebase"""
    return git(repo_path, "rebase", "--continue")


def repo_create_branch(repo_path, branch, start_point=None):
    """新建分支（可指定起点提交）"""
    args = ["branch", branch] + ([start_point] if start_point else [])
    return git(repo_path, *args)


def repo_delete_branch(repo_path, branch):
    """强制删除本地分支（-D，含未合并提交）"""
    return git(repo_path, "branch", "-D", branch)


def repo_rename_branch(repo_path, old, new):
    """重命名本地分支"""
    return git(repo_path, "branch", "-m", old, new)


def repo_merge_branch(repo_path, branch):
    """把指定分支合并到当前分支（离线）"""
    return git(repo_path, "merge", branch, timeout=90)


def repo_create_tag(repo_path, tag, commit_hash=None):
    """打标签（可指定提交）"""
    args = ["tag", tag] + ([commit_hash] if commit_hash else [])
    return git(repo_path, *args)


def repo_delete_tag(repo_path, tag):
    """删除本地标签"""
    return git(repo_path, "tag", "-d", tag)


# ---------- Reset / Rebase skip（Web 版） ----------
def repo_reset(repo_path, target, mode="mixed"):
    """重置分支到指定提交。mode: soft(保留暂存+工作区) / mixed(保留工作区) / hard(全部丢弃)。"""
    mode = (mode or "mixed").strip().lower()
    if mode not in ("soft", "mixed", "hard"):
        return "非法 reset 模式: %s" % mode, 1
    return git(repo_path, "reset", "--" + mode, target, timeout=60)


def repo_skip_rebase(repo_path):
    """跳过当前冲突提交，继续 rebase（rebase --skip）"""
    return git(repo_path, "rebase", "--skip", timeout=60)


# ---------- 补丁导出/导入（离线机器间转移提交） ----------
def get_commit_patch(repo_path, commit_hash):
    """读取单个提交的 patch 文本（format-patch --stdout，1 个提交）"""
    return git(repo_path, "format-patch", "-1", "--stdout", commit_hash, timeout=30)


def apply_patch(repo_path, patch_text, check_only=False):
    """应用补丁：默认 git am --3way（生成提交）；check_only=True 时用
    git apply --check 只检测能否干净应用，不改动仓库。"""
    if check_only:
        return git(repo_path, "apply", "--check", "-", input=patch_text, timeout=60)
    return git(repo_path, "am", "--3way", "-", input=patch_text, timeout=120)


def abort_patch(repo_path):
    """放弃当前 git am 会话，恢复到打补丁前的状态"""
    return git(repo_path, "am", "--abort", timeout=30)


def continue_patch(repo_path):
    """解决冲突后继续 git am 会话"""
    return git(repo_path, "am", "--continue", timeout=60)


# ---------- 工作区 vs 指定提交 ----------
def get_worktree_vs_commit_diff(repo_path, commit_hash):
    """工作区（含暂存区）与任意指定提交的对比 diff（离线）"""
    out, rc = git(repo_path, "diff", commit_hash, timeout=30)
    return out if rc == 0 else (out or "diff 失败")


# ---------- 每仓库提交身份 / fetch-pull-push 参数 ----------
def get_repo_identity(repo_path):
    """读取仓库本地提交身份（user.name / user.email），has_local 标记是否设置了本地覆盖"""
    name, _ = git(repo_path, "config", "--local", "--get", "user.name")
    email, _ = git(repo_path, "config", "--local", "--get", "user.email")
    return {"name": name.strip(), "email": email.strip(),
            "has_local": bool(name.strip() or email.strip())}


def set_repo_identity(repo_path, name, email):
    """设置仓库本地提交身份；留空表示清除本地覆盖（回退全局）"""
    outputs, rc = [], 0
    for key, val in (("user.name", name or ""), ("user.email", email or "")):
        val = (val or "").strip()
        if val:
            out, c = git(repo_path, "config", "--local", key, val)
        else:
            out, c = git(repo_path, "config", "--local", "--unset", key)
            if c != 0 and "" not in out:
                c = 0  # 本来就没设置，unset 报错可忽略
        outputs.append(out)
        if c != 0:
            rc = c
    return "\n".join(o for o in outputs if o), rc


def get_repo_git_options(repo_path):
    """读取常用的 fetch/pull/push 行为选项（本地配置）"""
    opts = {}
    for key in ("pull.ff", "pull.rebase", "fetch.prune", "push.default"):
        out, rc = git(repo_path, "config", "--local", "--get", key)
        if rc == 0 and out.strip():
            opts[key] = out.strip()
    return opts


def set_repo_git_option(repo_path, key, value):
    """设置 fetch/pull/push 行为选项（白名单键，防止任意配置注入）"""
    allowed = {
        "pull.ff": ("true", "false", "only"),
        "pull.rebase": ("true", "false", "merges", "interactive"),
        "fetch.prune": ("true", "false"),
        "push.default": ("simple", "current", "upstream", "nothing"),
    }
    key = (key or "").strip()
    value = (value or "").strip()
    if key not in allowed:
        return "不支持的配置键: %s（仅支持 pull.ff / pull.rebase / fetch.prune / push.default）" % key, 1
    if value not in allowed[key]:
        return "非法取值 %s（%s 允许: %s）" % (value, key, ", ".join(allowed[key])), 1
    return git(repo_path, "config", "--local", key, value)


# ---------- .gitignore 编辑器 ----------
def read_gitignore(repo_path):
    """读取仓库根目录 .gitignore 内容（不存在返回空串）"""
    p = os.path.join(repo_path, ".gitignore")
    if os.path.isfile(p):
        try:
            with open(p, "r", encoding="utf-8", errors="replace") as f:
                return f.read()
        except Exception as e:
            return ""
    return ""


def write_gitignore(repo_path, content):
    """写入 .gitignore（UTF-8，不自动提交）"""
    try:
        with open(os.path.join(repo_path, ".gitignore"), "w", encoding="utf-8", newline="\n") as f:
            f.write(content or "")
        return "已写入 .gitignore（未提交，需要时请在工作台提交）", 0
    except Exception as e:
        return str(e), 1


def explain_gitignore_line(line):
    """逐行解释 .gitignore 规则（纯离线，无 AI）"""
    s = line.strip()
    if not s:
        return "空行"
    if s.startswith("#"):
        return "注释"
    if s == "!":
        return "无效规则（取反缺少模式）"
    negated = s.startswith("!")
    body = s[1:] if negated else s
    if not body:
        return "无效规则"
    trailing_slash = body.endswith("/")
    leading_slash = body.startswith("/")
    has_mid_slash = "/" in body.rstrip("/")
    parts = []
    if negated:
        parts.append("取反：重新包含匹配的文件")
    if trailing_slash:
        parts.append("只匹配目录")
    if leading_slash:
        parts.append("锚定到 .gitignore 所在目录")
    elif has_mid_slash:
        parts.append("相对路径匹配（含中间目录）")
    else:
        parts.append("匹配任意层级的同名文件/目录")
    if "*" in body or "?" in body or "[" in body:
        parts.append("含通配符")
    return "；".join(parts)


def check_ignored(repo_path, paths):
    """批量检查路径是否被忽略，返回 [{path, ignored}]（离线）"""
    if not paths:
        return []
    out, rc = git(repo_path, "check-ignore", "--stdin", input="\n".join(paths) + "\n", timeout=30)
    ignored_set = set(l for l in out.splitlines() if l.strip())
    return [{"path": p, "ignored": p in ignored_set} for p in paths]


# ---------- 撤销 / 二分定位 ----------
def undo_last_commit(repo_path):
    """撤销最近一次提交（reset --soft）：改动保留在暂存区，可重新提交。
    目标引用选择：ORIG_HEAD 优先，但 ORIG_HEAD == HEAD 时（重复 undo / 之前的
    reset 已把 ORIG_HEAD 拉平）它等于"重置到自己"= 空操作且 rc=0，用户会以为
    撤销成功实际什么都没发生 —— 此时必须退回 HEAD~1。"""
    head, _ = git(repo_path, "rev-parse", "HEAD")
    head = (head or "").strip()
    orig, rc = git(repo_path, "rev-parse", "--verify", "ORIG_HEAD")
    orig = (orig or "").strip()
    if rc == 0 and orig and orig != head:
        return git(repo_path, "reset", "--soft", "ORIG_HEAD")
    # 无 ORIG_HEAD 或 ORIG_HEAD==HEAD：退回 HEAD~1
    out, rc = git(repo_path, "rev-parse", "--verify", "HEAD~1")
    if rc != 0:
        return "没有可撤销的提交（当前仓库不足 2 个提交）", 1
    return git(repo_path, "reset", "--soft", out.strip())


def bisect_start(repo_path, bad="HEAD", good=None):
    """开始二分定位：bad 默认当前 HEAD，good 为最后一个正常版本"""
    args = ["bisect", "start", bad]
    if good:
        args.append(good)
    return git(repo_path, *args, timeout=30)


def bisect_mark(repo_path, good):
    """标记当前提交为 good（True）/ bad（False），返回输出含下一个待测提交"""
    return git(repo_path, "bisect", "good" if good else "bad", timeout=30)


def bisect_reset(repo_path):
    """结束二分，回到原分支"""
    return git(repo_path, "bisect", "reset", timeout=30)


def bisect_status(repo_path):
    """二分进行中？返回 (in_progress, 当前检测提交信息)。
    用 `git bisect log` 的返回码判断是否在二分会话中。"""
    out, rc = git(repo_path, "bisect", "log")
    if rc != 0:
        return False, None
    cur, _ = git(repo_path, "log", "-1", "--format=%h|%s")
    return True, cur


# ---------- hunk 级暂存 ----------
def git_apply_cached(repo_path, patch_text):
    """把 patch 文本应用到暂存区（git apply --cached，patch 走 stdin）。
    用于 hunk 级暂存：只暂存一个 @@ 块而不是整个文件。"""
    try:
        # git apply 严格要求 patch 末行以换行结尾，否则报 "corrupt patch"
        if not patch_text.endswith("\n"):
            patch_text += "\n"
        # ⚠ 必须用字节流：Windows 上 text=True 会把 stdin 的 \n 翻译成 \r\n，
        # git apply 按字节比对索引内容（LF）→ "patch does not apply"
        p = subprocess.run(
            ["git", "-C", repo_path, "apply", "--cached", "--recount", "-"],
            input=patch_text.encode("utf-8"),
            capture_output=True, timeout=30, creationflags=_SUBPROC_FLAGS,
            env=_git_env())
        out = p.stdout.decode("utf-8", errors="replace").rstrip()
        if p.returncode != 0 and not out:
            out = (p.stderr or b"").decode("utf-8", errors="replace").rstrip()
        return out, p.returncode
    except Exception as e:
        return str(e), 1


def git_apply_cached_reverse(repo_path, patch_text):
    """把 patch 从暂存区反向撤销（git apply --cached -R）。
    用于「只取消暂存此块」：对 --cached diff 的单个 hunk 做逆向应用。"""
    try:
        if not patch_text.endswith("\n"):
            patch_text += "\n"
        # creationflags 之前漏了：正向加了 CREATE_NO_WINDOW，反向没加，
        # 于是 Windows 上「取消暂存此块」会弹一个空控制台窗口闪一下。
        p = subprocess.run(
            ["git", "-C", repo_path, "apply", "--cached", "-R", "-"],
            input=patch_text.encode("utf-8"),
            capture_output=True, timeout=30, creationflags=_SUBPROC_FLAGS,
            env=_git_env())
        out = p.stdout.decode("utf-8", errors="replace").rstrip()
        if p.returncode != 0 and not out:
            out = (p.stderr or b"").decode("utf-8", errors="replace").rstrip()
        return out, p.returncode
    except Exception as e:
        return str(e), 1


def split_hunks(patch):
    """把单个文件的 git diff patch 拆成 (文件头行, [每个 @@ 块的独立行列表])。
    文件头 = diff --git / index / --- / +++ 等行（第一个 @@ 之前）。"""
    headers, hunks = [], []
    cur = None
    for ln in (patch or "").splitlines():
        if ln.startswith("@@"):
            cur = []
            hunks.append(cur)
        if cur is not None:
            cur.append(ln)
        else:
            headers.append(ln)
    return headers, hunks


def get_file_patch(repo_path, path):
    """工作区 vs 暂存区的单文件 patch（hunk 暂存用，与工作台预览同源）。"""
    out, _ = git(repo_path, "diff", "--", path)
    return out


# ---------- 行级暂存 ----------
_HUNK_HEADER_RE = re.compile(r"^@@ -(\d+)(?:,(\d+))? \+\d+(?:,\d+)? @@(.*)$")


def build_line_patch(patch, selected_lines):
    """按选中的 patch 行号构建"只含所选变更"的行级 patch（行级暂存用）。

    patch 为 get_file_patch 的输出，selected_lines 是 patch-lines 接口同款
    行号集合：对整段 patch 文本（含文件头/@@ 行）从 1 起逐行编号。
    转换规则（保证产物对 git apply --cached 仍然合法）：
      - 选中的 '+' 行保留；未选中的 '+' 行直接丢弃（不进暂存区）；
      - 选中的 '-' 行保留为 '-'；未选中的 '-' 行降级为上下文行（暂存区里该行原样保留）；
      - 上下文行全部保留；"\\ No newline" 行跟随其前一行去留；
      - 没有任何选中变更的 hunk 整块丢弃，@@ 起始行按前序 hunk 的保留变更重新推算。
    没有任何选中变更时返回 ''。
    """
    if not patch:
        return ""
    lines = patch.splitlines()
    selected = set(selected_lines or ())
    # 文件头 = 第一个 @@ 之前的所有行（diff --git / index / --- / +++ 等）
    i = 0
    while i < len(lines) and not lines[i].startswith("@@"):
        i += 1
    out = lines[:i]
    delta = 0  # 前序已保留 hunk 的净行数变化（+ - -），用于推算后续 hunk 的 +start
    kept_any = False
    while i < len(lines):
        m = _HUNK_HEADER_RE.match(lines[i])
        if not m:
            i += 1
            continue
        old_start = int(m.group(1))
        tail = m.group(3) or ""  # 第二个 @@ 后的函数上下文提示，原样保留
        i += 1
        new_body = []
        kept_add = kept_del = 0
        prev_kept = False
        while i < len(lines) and not lines[i].startswith("@@"):
            num, ln = i + 1, lines[i]
            if ln.startswith("+"):
                if num in selected:
                    new_body.append(ln)
                    kept_add += 1
                    prev_kept = True
                else:
                    prev_kept = False
            elif ln.startswith("-"):
                if num in selected:
                    new_body.append(ln)
                    kept_del += 1
                else:
                    new_body.append(" " + ln[1:])  # 降级为上下文
                prev_kept = True
            elif ln.startswith("\\"):
                if prev_kept:
                    new_body.append(ln)
            else:
                new_body.append(ln if ln.startswith(" ") else " " + ln)
                prev_kept = True
            i += 1
        if not kept_add and not kept_del:
            continue  # 该 hunk 无选中变更
        n_ctx = sum(1 for ln in new_body if ln.startswith(" "))
        n_add = sum(1 for ln in new_body if ln.startswith("+"))
        n_del = sum(1 for ln in new_body if ln.startswith("-"))
        old_count = n_ctx + n_del  # old 侧内容与原 hunk 一致（ctx + del）
        new_count = n_ctx + n_add
        # old 侧为空（纯新增 hunk）时语义是"插在第 old_start 行之后"，起始 +1
        new_start = old_start + delta + (0 if old_count else 1)
        out.append(f"@@ -{old_start},{old_count} +{new_start},{new_count} @@{tail}")
        out.extend(new_body)
        delta += kept_add - kept_del
        kept_any = True
    if not kept_any:
        return ""
    return "\n".join(out) + "\n"


# ---------- 敏感信息扫描 ----------
_SECRET_PATTERNS = [
    ("AWS Access Key", re.compile(r"\bAKIA[0-9A-Z]{16}\b")),
    ("GitHub Token", re.compile(r"\bgh[pousr]_[A-Za-z0-9]{16,}\b")),
    ("OpenAI Key", re.compile(r"\bsk-[A-Za-z0-9_-]{20,}\b")),
    ("密码赋值", re.compile(
        # 边界用字母视角而非 \b：变量名里的下划线（db_password/MY_SECRET）不算边界
        r"(?i)(?<![a-z])(password|passwd|pwd|secret|token|api[_-]?key|access[_-]?key|auth[_-]?token)(?![a-z])"
        r"\s*[=:]\s*[\'\"][^\'\"]{4,}[\'\"]")),
]
_PRIVATE_KEY_FILE_RE = re.compile(
    r"(^|/)(id_(rsa|dsa|ecdsa|ed25519)|[^/]+\.(pem|key|pfx|p12))$", re.IGNORECASE)


def scan_secrets(repo_path, max_commits=100, since_days=90):
    """扫描最近提交新增行中的敏感信息（密钥/令牌/密码赋值/私钥文件）。

    返回 [{commit, author, date, file, line, type, match}]，按提交时间新→旧；
    同一 (文件, 类型, 内容) 只记最近一次出现的提交；私钥文件按"提交触及该文件"
    记一条（match=路径）；最多返回 200 条，防止极端仓库刷屏。
    """
    since = (datetime.now() - timedelta(days=since_days)).strftime("%Y-%m-%d")
    # %x00 记录行首 NUL 标记提交边界（diff 内容行不可能以 NUL 开头）；
    # -U0 去掉上下文行，使 '+' 行行号从 @@ 头直接连加；--no-renames 保持 diff 结构简单
    out, _ = git(repo_path, "log", "-p", "-U0", "--no-color", "--no-renames",
                 f"--since={since}", "-n", str(max_commits),
                 "--pretty=format:%x00%H|%an|%ci", timeout=120)
    findings, seen = [], set()
    commit = author = date = ""
    file = ""
    new_line = 0
    for raw in (out or "").splitlines():
        if len(findings) >= 200:
            break
        if raw.startswith("\x00"):
            parts = raw[1:].split("|", 2)
            if len(parts) == 3:
                commit, author, date = parts
            continue
        if raw.startswith("diff --git "):
            file = raw.split(" b/", 1)[1] if " b/" in raw else ""
            new_line = 0
            if file and _PRIVATE_KEY_FILE_RE.search(file):
                key = (file, "私钥文件", file)
                if key not in seen:
                    seen.add(key)
                    findings.append({"commit": commit, "author": author, "date": date,
                                     "file": file, "line": 0, "type": "私钥文件",
                                     "match": file})
            continue
        m = re.match(r"@@ -\d+(?:,\d+)? \+(\d+)", raw)
        if m:
            new_line = int(m.group(1))
            continue
        if not raw.startswith("+") or raw.startswith("+++"):
            continue
        content = raw[1:]
        for type_name, pat in _SECRET_PATTERNS:
            mm = pat.search(content)
            if mm:
                key = (file, type_name, mm.group(0))
                if key not in seen:
                    seen.add(key)
                    findings.append({"commit": commit, "author": author, "date": date,
                                     "file": file, "line": new_line, "type": type_name,
                                     "match": mm.group(0)})
        new_line += 1
    return findings


# ---------- Blame ----------
def parse_blame(out):
    """解析 git blame 默认格式输出：每行 → {hash, author, date, line, content}。"""
    rows = []
    for line in (out or "").splitlines():
        m = re.match(r"^([0-9a-f]{7,40})\s+\((.*?)\s+(\d{4}-\d{2}-\d{2})\s+(\d+)\)\s?(.*)$",
                     line)
        if m:
            rows.append({"hash": m.group(1), "author": m.group(2),
                         "date": m.group(3), "line": int(m.group(4)),
                         "content": m.group(5)})
    return rows


def get_blame(repo_path, path, staged=False):
    """逐行溯源：git blame（-w 忽略空白；staged=True 时 blame 暂存区版本）"""
    args = ["blame", "--date=short", "-w", "--"]
    if staged:
        args.insert(1, "--cached")
    args.append(path)
    out, _ = git(repo_path, *args, timeout=60)
    return parse_blame(out)


# ---------- Stash ----------
def get_stash_list(repo_path):
    """stash 列表：[{ref, msg, date}]（ref 形如 stash@{0}）"""
    out, _ = git(repo_path, "stash", "list", "--format=%gd|%gs|%ci")
    rows = []
    for line in out.splitlines():
        parts = line.split("|", 2)
        if len(parts) == 3:
            rows.append({"ref": parts[0], "msg": parts[1] or "（无说明）",
                         "date": parts[2][:16]})
    return rows


def stash_save(repo_path, message):
    return git(repo_path, "stash", "push", "-m", message, timeout=60)


def stash_apply(repo_path, ref):
    return git(repo_path, "stash", "apply", ref, timeout=90)


def stash_drop(repo_path, ref):
    return git(repo_path, "stash", "drop", ref)


def stash_show(repo_path, ref):
    out, _ = git(repo_path, "stash", "show", "-p", ref)
    return out


# ---------- 发布历史（比对快照，本地 json） ----------
RELEASES_PATH = os.path.join(_BASE, "git_monitor_releases.json")


def load_releases():
    """读取发布历史 {仓库: [快照…]}；损坏时返回空（不影响主功能）。"""
    try:
        if os.path.exists(RELEASES_PATH):
            with open(RELEASES_PATH, "r", encoding="utf-8") as f:
                return json.load(f)
    except Exception:
        pass
    return {}


_RELEASES_LOCK = threading.Lock()  # 保护 load→改→写 的并发一致性


def push_release_snapshot(data, repo, limit=30):
    """比对成功 → 记一条快照（每仓库限 limit 条；与上一条完全相同则跳过）。
    返回更新后的历史字典。"""
    entry = {
        "time": datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
        "dev": data.get("dev", ""), "prod": data.get("prod", ""),
        "direction": data.get("direction", ""),
        "n_commits": len(data.get("commits", [])),
        "n_files": len(data.get("files", [])),
        "commits": [c.get("hash7", "") for c in data.get("commits", [])],
        "files": [f.get("path", "") for f in data.get("files", [])],
    }
    # 加锁覆盖 load→改→写，避免并发比对各自读到旧历史后互相覆盖（丢快照）
    with _RELEASES_LOCK:
        hist = load_releases()
        lst = hist.setdefault(repo, [])
        if lst:
            last = lst[0]
            # 内容级去重：dev/prod/提交列表/文件列表全部一致才跳过
            # （只比数量会把"提交数相同但内容不同"的比对误去重）
            if (last.get("dev") == entry["dev"]
                    and last.get("prod") == entry["prod"]
                    and last.get("commits") == entry["commits"]
                    and last.get("files") == entry["files"]):
                return hist  # 与上次比对结果相同，不重复记录（自动刷新会频繁触发）
        lst.insert(0, entry)
        if len(lst) > limit:
            # 超出部分归档到独立文件而不是丢弃（长期使用历史可查）
            overflow = lst[limit:]
            del lst[limit:]
            try:
                arch_path = RELEASES_PATH.replace(".json", "_archive.json")
                if os.path.exists(arch_path):
                    with open(arch_path, "r", encoding="utf-8") as f:
                        archived = json.load(f)
                else:
                    archived = {}
                archived.setdefault(repo, []).extend(overflow)
                _atomic_write_json(arch_path, archived)
            except Exception:
                pass  # 归档失败不阻塞主流程
        _atomic_write_json(RELEASES_PATH, hist)
        return hist


def search_commits(repo_path, keyword, n=200, author="", since_days=0):
    """全量历史搜索（离线）：
    - keyword 同时匹配提交信息（--grep）与作者名（--author，另跑一次合并去重）；
    - 若 keyword 形如 hash（4-40 位十六进制），额外尝试精确解析该提交；
    - 支持正则表达式搜索（以 / 开头的 keyword 视为正则）；
    - author / since_days 为附加筛选（与 keyword 同时存在时为 AND 关系，仅在
      提交信息侧生效——与 git log 语义一致）。
    与 get_commits 不同：搜的是全部提交而不是内存里预加载的 50 条。"""
    commits = []
    seen = set()
    base = ["log", "--all", "--format=%H|%an|%ai|%s"]
    if keyword:
        # 支持正则搜索（以 / 开头）
        use_regex = keyword.startswith("/")
        grep_flag = "--grep" if not use_regex else "--perl-regexp"
        out, _ = git(repo_path, *base, f"-{n}", grep_flag, keyword.lstrip("/"), "-i")
        commits = parse_log(out)
        seen = {c["hash"] for c in commits}
        # 作者名搜索
        out2, _ = git(repo_path, *base, f"-{n}", "--author", keyword, "-i")
        for c in parse_log(out2):
            if c["hash"] not in seen:
                commits.append(c)
                seen.add(c["hash"])
        # 短哈希搜索
        if re.fullmatch(r"[0-9a-fA-F]{4,40}", keyword):
            out3, rc = git(repo_path, "log", "-1",
                           "--format=%H|%an|%ai|%s", keyword)
            if rc == 0 and out3:
                for c in parse_log(out3):
                    if c["hash"] not in seen:
                        commits.append(c)
                        seen.add(c["hash"])
    elif author or since_days:
        args = list(base) + [f"-{n}"]
        if author:
            args += ["--author", author]
        if since_days:
            args += [f"--since={since_days} days ago"]
        out, _ = git(repo_path, *args)
        commits = parse_log(out)
    return commits


def get_branch_overview(repo_path):
    """分支概览：本地 + 远程跟踪分支的最新提交 / ahead / behind。
    返回 [{name, kind, hash7, date, subject, ahead, behind}]（kind: 本地/远程）。"""
    out, _ = git(repo_path, "for-each-ref",
                 "--format=%(refname:short)|%(refname)|%(upstream:short)|"
                 "%(upstream:track)|%(objectname:short)|%(subject)|%(authordate:short)",
                 "refs/heads", "refs/remotes")
    rows = []
    for line in out.splitlines():
        parts = line.split("|", 6)
        if len(parts) != 7:
            continue
        short, full, _up, track, h7, subj, date = parts
        if full.startswith("refs/remotes/") and short.endswith("/HEAD"):
            continue  # 符号引用 origin/HEAD 无实际内容，跳过
        kind = "本地" if full.startswith("refs/heads/") else "远程"
        ahead = behind = 0
        m = re.search(r"ahead (\d+)", track or "")
        if m:
            ahead = int(m.group(1))
        m = re.search(r"behind (\d+)", track or "")
        if m:
            behind = int(m.group(1))
        rows.append({"name": short, "kind": kind, "hash7": h7,
                     "date": date, "subject": subj or "（无）",
                     "ahead": ahead, "behind": behind})
    return rows


# ---------- 提交图 / 统计 ----------
def get_graph_log(repo_path, n=300):
    """`git log --all --topo-order`：带父提交信息，供提交图布局"""
    out, _ = git(repo_path, "log", "--all", "--topo-order",
                 f"-{n}", "--format=%H|%P|%an|%ai|%s")
    commits = []
    for line in out.splitlines():
        parts = line.split("|", 4)
        if len(parts) == 5:
            commits.append({
                "hash": parts[0],
                "parents": [p for p in parts[1].split() if p],
                "author": parts[2], "date": parts[3][:16],
                "message": parts[4],
            })
    return commits


def get_ref_map(repo_path):
    """hash -> [{name, kind}]（kind: branch/remote/tag/other），供提交图标注区分"""
    out, _ = git(repo_path, "for-each-ref",
                 "--format=%(objectname)%09%(refname:short)%09%(refname)",
                 "refs/heads", "refs/remotes", "refs/tags")
    m = {}
    for line in out.splitlines():
        parts = line.split("\t")
        if len(parts) == 3:
            h, short, full = parts
            if full.startswith("refs/heads/"):
                kind = "branch"
            elif full.startswith("refs/tags/"):
                kind = "tag"
            elif full.startswith("refs/remotes/"):
                kind = "remote"
            else:
                kind = "other"
            m.setdefault(h, []).append({"name": short, "kind": kind})
    return m


def layout_graph(commits):
    """把提交列表布局成 lanes（gitk 风格 first-fit）。
    返回 (rows, pos)：rows 为 [{commit, lane}]，pos 为 hash -> (row, lane)。"""
    lanes = []            # lane index -> 该 lane 当前线头上挂着的 hash
    free_lanes = []       # 空闲 lane 索引
    pos = {}
    rows = []
    for i, c in enumerate(commits):
        h = c["hash"]
        if h in lanes:
            lane = lanes.index(h)
        else:
            lane = free_lanes.pop(0) if free_lanes else len(lanes)
            if lane == len(lanes):
                lanes.append(None)
        pos[h] = (i, lane)
        rows.append({"commit": c, "lane": lane})
        parents = c["parents"]
        if parents:
            lanes[lane] = parents[0]
        else:
            lanes[lane] = None
            free_lanes.append(lane)
        for p in parents[1:]:
            if p in pos or p in lanes:
                continue
            pl = free_lanes.pop(0) if free_lanes else len(lanes)
            if pl == len(lanes):
                lanes.append(None)
            lanes[pl] = p
    return rows, pos


def get_stats(repo_paths, days):
    """统计近 days 天提交：按日期 / 按作者聚合（兼容旧调用，细节见 get_stats_detailed）"""
    repos = {f"repo{i}": p for i, p in enumerate(repo_paths)}
    by_date, by_author, _, _, _, _ = get_stats_detailed(repos, days)
    return by_date, by_author


def get_stats_detailed(repos, days, all_branches=True):
    """统计近 days 天提交，返回 (by_date, by_author, by_repo_date, by_repo_author,
    by_type, by_repo_type)。类型 = conventional commit 前缀（feat/fix/...），无前缀归 other。
    repos: {名称: 路径}；by_repo_* 供多选过滤时重算排行。
    all_branches=False 时只统计当前分支（口径更贴近"团队最近在做什么"）。"""
    since = f"--since={days} days ago"
    by_date, by_author = Counter(), Counter()
    by_type = Counter()
    by_repo_date, by_repo_author, by_repo_type = {}, {}, {}
    for name, path in repos.items():
        if not os.path.isdir(path):
            continue
        args = ["log", "--date=short", since, "--format=%cd|%an|%s"]  # %cd=committer date，与 --since 一致
        if all_branches:
            args.insert(1, "--all")
        out, _ = git(path, *args)
        rd, ra, rt = Counter(), Counter(), Counter()
        for line in out.splitlines():
            parts = line.split("|", 2)
            if len(parts) != 3:
                continue
            d, a, s = parts
            m = COMMIT_PREFIX_RE.match(s or "")
            t = m.group(1) if m else "other"
            by_date[d] += 1
            by_author[a] += 1
            by_type[t] += 1
            rd[d] += 1
            ra[a] += 1
            rt[t] += 1
        if rd:
            by_repo_date[name] = rd
            by_repo_author[name] = ra
            by_repo_type[name] = rt
    return by_date, by_author, by_repo_date, by_repo_author, by_type, by_repo_type


def apply_repo_filter(by_date, by_author, by_repo_date, by_repo_author,
                      by_repo_type, selected):
    """按多选过滤重算统计数据（图表与导出共用）。selected: 仓库名集合。
    返回 (by_date, by_author, by_repo_date, by_type)：作者/类型从按仓库明细重聚，
    保证被排除的仓库不污染排行。"""
    if selected is None:
        agg = Counter()
        for rt in (by_repo_type or {}).values():
            agg.update(rt)
        return (dict(by_date), dict(by_author), dict(by_repo_date), agg)
    fbd, fbra, fbrd, fbrt = Counter(), Counter(), {}, Counter()
    for n, rd in (by_repo_date or {}).items():
        if n in selected:
            fbd.update(rd)
            fbrd[n] = Counter(rd)
    for n, ra in (by_repo_author or {}).items():
        if n in selected:
            fbra.update(ra)
    for n, rt in (by_repo_type or {}).items():
        if n in selected:
            fbrt.update(rt)
    return fbd, fbra, fbrd, fbrt


def filter_repos_by_set(repos, selected):
    """按多选过滤 {名称: 路径} 仓库字典；selected=None 视为全选。"""
    if selected is None:
        return dict(repos)
    return {n: p for n, p in repos.items() if n in selected}


def compute_author_layout(names, acw, measure, name_right=92, min_gap=12,
                          max_frac=0.45):
    """作者排行布局：按名字实际渲染宽度动态右移条形区，保证名字与条形永不重叠。
    names: 作者名列表；acw: 画布宽；measure: str→像素宽 可调用（tkfont.measure，
    天然考虑 DPI 缩放）。超长名字按画布比例截断加 …。返回 (条形起始 x, 显示名列表)。"""
    max_w = max((acw - 40) * max_frac, 40)
    disp = []
    for name in names:
        d = name
        while measure(d) > max_w and len(d) > 1:
            d = d[:-1]
        disp.append(d if d == name else d + "…")
    widths = [measure(d) for d in disp]
    bar_x = max(name_right, 6 + (max(widths) if widths else 0) + min_gap)
    return bar_x, disp


def build_bar_tooltip(date, count, detail=None):
    """柱形图悬停提示文本。detail: [(仓库名, 次数)]（堆叠模式按次数倒序）。"""
    lines = [f"{date}  ·  共 {count} 次提交"]
    if detail:
        for n, c in detail:
            lines.append(f"  {n}: {c}")
    return "\n".join(lines)


def _csv_safe(v):
    """CSV 字段安全：对 =+-@ 开头的字段加 ' 前缀，防 Excel 公式注入"""
    v = str(v)
    return "'" + v if v[:1] in "=+-@" else v


def build_stats_csv(by_date, by_author, days, repo, by_repo_date=None,
                    by_type=None):
    """统计面板 → CSV 文本（周报素材）。
    by_date: Counter(日期→次数)，by_author: Counter(作者→次数)，
    by_repo_date: {仓库: Counter(日期→次数)}（可选，导出每日按仓库明细），
    by_type: Counter(类型→次数)（可选，导出提交类型分布）。
    用 csv 模块写入：逗号/引号/换行字段安全，且对 =+-@ 开头的字段加前缀防 Excel 公式注入。"""
    now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    repo_label = "全部仓库" if repo == "全部仓库" else repo
    buf = io.StringIO()
    w = csv.writer(buf)
    safe = _csv_safe

    w.writerow(["周报统计"])
    w.writerow([safe("仓库"), safe(repo_label)])
    w.writerow([safe("统计范围"), safe(f"近 {days} 天")])
    w.writerow([safe("生成时间"), safe(now)])
    w.writerow([])
    w.writerow(["=== 每日提交 ==="])
    w.writerow(["date", "count"])
    for d, c in sorted(by_date.items()):
        w.writerow([d, c])
    w.writerow([])
    w.writerow(["=== 每日提交明细（按仓库）==="])
    w.writerow(["date", "repo", "count"])
    if by_repo_date:
        for d, r, c in sorted((d, r, c) for r, rd in by_repo_date.items()
                              for d, c in rd.items()):
            w.writerow([d, safe(r), c])
    w.writerow([])
    w.writerow(["=== 提交类型分布 ==="])
    w.writerow(["type", "count"])
    if by_type:
        for k, c in sorted(by_type.items(), key=lambda x: -x[1]):
            w.writerow([safe(k), c])
    w.writerow([])
    w.writerow(["=== 作者提交排行 ==="])
    w.writerow(["author", "count"])
    for a, c in sorted(by_author.items(), key=lambda x: -x[1]):
        w.writerow([safe(a), c])
    return buf.getvalue()


def build_weekly_detail_csv(commits, repo_label="全部仓库", days=30):
    """周报「每日提交明细」→ CSV 文本（与 build_stats_csv 同风格，Excel 可直接透视）。
    commits: get_repo_commits() 的输出；含「每日提交明细（按仓库）」与完整「提交明细」
    两张表，生成周报时随 MD 一键另存。注意：CSV 覆盖整个 days 窗口（MD 里的表格为
    近 14 天展示口径），数据更全，便于 Excel 透视。"""
    now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    buf = io.StringIO()
    w = csv.writer(buf)
    safe = _csv_safe
    w.writerow(["周报统计"])
    w.writerow([safe("仓库"), safe(repo_label)])
    w.writerow([safe("统计范围"), safe(f"近 {days} 天")])
    w.writerow([safe("生成时间"), safe(now)])
    w.writerow([])
    w.writerow(["=== 每日提交明细（按仓库）==="])
    w.writerow(["date", "repo", "count"])
    dl = Counter((c["date"], c["repo"]) for c in commits)
    for (d, r), cnt in sorted(dl.items()):
        w.writerow([d, safe(r), cnt])
    w.writerow([])
    w.writerow(["=== 提交明细 ==="])
    w.writerow(["date", "repo", "hash7", "author", "message"])
    for c in sorted(commits, key=lambda x: x["date"], reverse=True):
        w.writerow([c["date"], safe(c["repo"]), safe(c["hash7"]),
                    safe(c["author"]), safe(c["message"])])
    return buf.getvalue()


def get_repo_commits(repos, days):
    """收集近 days 天每个仓库（--all）的提交，返回 [{repo, hash7, date, author, message}]。
    repos: {配置名: 路径} 字典。date 为 YYYY-MM-DD。"""
    since = f"--since={days} days ago"
    out_list = []
    for name, path in repos.items():
        if not os.path.isdir(path):
            continue
        out, _ = git(path, "log", "--all", "--date=short", since,
                     "--format=%h|%ad|%an|%s")
        for line in out.splitlines():
            parts = line.split("|", 3)
            if len(parts) == 4:
                out_list.append({
                    "repo": name, "hash7": parts[0], "date": parts[1],
                    "author": parts[2], "message": parts[3],
                })
    return out_list


def _week_label(iso_week):
    """(年, ISO周) → '2026-W32'"""
    return f"{iso_week[0]}-W{iso_week[1]:02d}"


def _md_esc(s):
    """Markdown 表格单元格转义（| 与换行）"""
    return (s or "").replace("|", "\\|").replace(chr(10), " ").strip()


def build_weekly_report(commits, repo_label="全部仓库", days=30, include_details=True):
    """按自然周聚合提交，生成 Markdown 周报（纯函数，便于测试）。
    commits: get_repo_commits() 的输出；repo_label: 统计范围显示名。"""
    now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    total = len(commits)
    by_author = Counter(c["author"] for c in commits)
    by_repo = Counter(c["repo"] for c in commits)

    # 按自然周聚合（ISO 周，周一到周日）
    weekly = Counter()
    for c in commits:
        try:
            iso = datetime.strptime(c["date"], "%Y-%m-%d").isocalendar()
            weekly[(iso[0], iso[1])] += 1
        except Exception:
            continue
    week_keys = sorted(weekly)
    daily = Counter(c["date"] for c in commits)

    lines = []
    lines.append(f"# 📅 周报：{repo_label}（近 {days} 天）\n")
    lines.append(f"> 生成时间：{now}")
    lines.append(f"> 统计范围：{repo_label} · 近 {days} 天 · 含 {len(by_repo)} 个仓库\n")

    # 概览
    lines.append("## 概览")
    lines.append(f"- 总提交：**{total}**")
    lines.append(f"- 活跃作者：**{len(by_author)}** 位")
    lines.append(f"- 覆盖仓库：**{len(by_repo)}** 个")
    lines.append(f"- 日均提交：**{total / max(days, 1):.1f}** 次/天")
    lines.append("")

    # 每周趋势（带环比）
    lines.append("## 每周提交趋势")
    if week_keys:
        lines.append("| 周 | 提交数 | 环比 |")
        lines.append("| --- | --- | --- |")
        prev = None
        for wk in week_keys:
            cnt = weekly[wk]
            if prev is None:
                ratio = "—"
            else:
                pct = (cnt - prev) * 100 // max(prev, 1)
                sign = "+" if pct > 0 else ""
                ratio = f"{sign}{pct}%"
            lines.append(f"| {_week_label(wk)} | {cnt} | {ratio} |")
            prev = cnt
    else:
        lines.append("（近 {} 天没有提交）".format(days))
    lines.append("")

    # 作者排行
    lines.append("## 作者提交排行")
    top = sorted(by_author.items(), key=lambda x: -x[1])[:10]
    if top:
        lines.append("| 作者 | 提交数 |")
        lines.append("| --- | --- |")
        for a, c in top:
            lines.append(f"| {_md_esc(a)} | {c} |")
    else:
        lines.append("（无）")
    lines.append("")

    # 仓库分布
    lines.append("## 仓库分布")
    if by_repo:
        lines.append("| 仓库 | 提交数 | 占比 |")
        lines.append("| --- | --- | --- |")
        for r, c in sorted(by_repo.items(), key=lambda x: -x[1]):
            pct = c * 100 / max(total, 1)
            lines.append(f"| {_md_esc(r)} | {c} | {pct:.0f}% |")
    else:
        lines.append("（无）")
    lines.append("")

    # 每日趋势（最近 14 天，字符条）
    lines.append("## 每日提交趋势（最近 14 天）")
    today = datetime.now().date()
    date_list = [(today - timedelta(days=i)).isoformat() for i in range(13, -1, -1)]
    mx = max((daily.get(d, 0) for d in date_list), default=0) or 1
    lines.append("| 日期 | 提交 | 分布 |")
    lines.append("| --- | --- | --- |")
    for d in date_list:
        cnt = daily.get(d, 0)
        bar = "█" * int(round(cnt * 20 / mx)) if cnt else ""
        lines.append(f"| {d} | {cnt} | {bar} |")
    lines.append("")

    # 每日提交明细（按仓库，近 14 天；可选，与「包含提交明细」联动）
    if include_details and commits:
        lines.append("## 每日提交明细（近 14 天）")
        dl = Counter((c["date"], c["repo"]) for c in commits
                     if c["date"] >= (datetime.now().date()
                                      - timedelta(days=13)).isoformat())
        if dl:
            lines.append("| 日期 | 仓库 | 提交 |")
            lines.append("| --- | --- | --- |")
            for (d, r), cnt in sorted(dl.items(), reverse=True):
                lines.append(f"| {d} | {_md_esc(r)} | {cnt} |")
        else:
            lines.append("（近 14 天无提交）")
        lines.append("")

    # 提交明细（可选）
    if include_details and commits:
        lines.append("## 提交明细")
        lines.append("| 日期 | 作者 | 仓库 | Hash | 提交信息 |")
        lines.append("| --- | --- | --- | --- | --- |")
        for c in sorted(commits, key=lambda x: x["date"], reverse=True):
            lines.append(f"| {_md_esc(c['date'])} | {_md_esc(c['author'])} | "
                         f"{_md_esc(c['repo'])} | `{_md_esc(c['hash7'])}` | "
                         f"{_md_esc(c['message'])} |")
        lines.append("")

    # 提交类型分布（conventional commits 前缀）
    lines.append("## 提交类型分布")
    by_type = Counter()
    for c in commits:
        m = COMMIT_PREFIX_RE.match(c.get("message") or "")
        by_type[m.group(1) if m else "other"] += 1
    if by_type:
        lines.append("| 类型 | 提交数 | 占比 |")
        lines.append("| --- | --- | --- |")
        for k, cnt in sorted(by_type.items(), key=lambda x: -x[1]):
            lines.append(f"| {_md_esc(COMMIT_TYPE_CN.get(k, k))} | {cnt} | "
                         f"{cnt * 100 // max(total, 1)}% |")
    else:
        lines.append("（无）")
    lines.append("")

    lines.append("---")
    lines.append("> 由 Git 仓库监控器自动生成。")
    return "\n".join(lines) + "\n"


# ============================================================
# 分支比对（开发分支 vs 生产分支）
# ============================================================
def get_ahead_commits(repo_path, base, head):
    """base..head：head 有而 base 没有的提交（即待上线内容）"""
    out, _ = git(repo_path, "log", f"{base}..{head}", "--format=%H|%an|%ai|%s")
    return parse_log(out)


def get_branch_file_diff(repo_path, base, head):
    """git diff base head：两分支间的变动文件"""
    out, _ = git(repo_path, "diff", "--name-status", base, head)
    files = []
    for line in out.splitlines():
        parts = line.split("\t", 1)
        if len(parts) == 2:
            files.append({"status": parts[0], "path": parts[1]})
    return files


def get_file_diff(repo_path, base, head, path):
    """两分支间某个文件的具体 diff"""
    out, _ = git(repo_path, "diff", base, head, "--", path)
    return out


def get_workspace_status(repo_path):
    """工作台：未提交变更清单。
    返回 [{status, status_cn, path, added, removed, staged, untracked, conflict}]。
    - status: 显示字母（?=未跟踪 U=冲突 A/M/D/R=新增/修改/删除/重命名）
    - staged: 是否存在已暂存部分（status --porcelain 的 X 列非空）
    - added/removed: vs HEAD 的增删行数（git diff HEAD --numstat）"""
    if not os.path.isdir(repo_path):
        return []
    out, _rc = git(repo_path, "status", "--porcelain")
    if not out or _rc != 0:
        return []  # 非仓库/失败时 stderr 已被 git() 透出, 这里避免把它当状态行解析
    nums = {}
    ns, nrc = git(repo_path, "diff", "HEAD", "--numstat")
    if nrc == 0:
        for line in ns.splitlines():
            parts = line.split("\t")
            if len(parts) == 3:
                try:
                    nums[_unquote_git_path(parts[2])] = (int(parts[0]), int(parts[1]))
                except ValueError:
                    pass
    files = []
    for line in out.splitlines():
        xy = line[:2]
        rest = line[3:]
        if " -> " in rest:
            rest = rest.split(" -> ", 1)[1]  # 重命名/复制：只保留新路径
        path = _unquote_git_path(rest)
        untracked = xy == "??"
        conflict = "U" in xy
        staged = xy[0] in "MADRC"
        unstaged = xy[1] in "MD"
        if untracked:
            letter, status_cn = "?", "未跟踪"
        elif conflict:
            letter, status_cn = "U", "冲突"
        elif staged and unstaged:
            letter, status_cn = "M", "修改+暂存"
        elif staged:
            letter = xy[0]
            status_cn = f"暂存·{STATUS_CN.get(letter, letter)}"
        else:
            letter = xy[1]
            status_cn = STATUS_CN.get(letter, letter)
        added, removed = nums.get(path, (0, 0))
        files.append({
            "status": letter, "status_cn": status_cn, "path": path,
            "added": added, "removed": removed,
            "staged": staged, "unstaged": unstaged,
            "untracked": untracked, "conflict": conflict,
        })
    return files


def get_worktree_diff(repo_path, path, untracked=False, limit=200_000, staged=False):
    """未提交变更的 diff 预览：
    - 未跟踪文件直接读内容；
    - staged=True（已暂存文件）输出暂存区 vs HEAD 的 diff（--cached）；
    - 否则输出工作区 vs 暂存区的 diff（默认 git diff），保证"暂存某块后该块从预览消失"。"""
    if untracked:
        fp = os.path.join(repo_path, path)
        try:
            with open(fp, "r", encoding="utf-8", errors="replace") as f:
                content = f.read(limit)
        except Exception as e:
            return f"（读取失败: {e}）"
        if len(content) >= limit:
            content += "\n…（内容过长已截断）"
        return "（未跟踪新文件，非 diff）\n" + content
    if staged:
        out, rc = git(repo_path, "diff", "--cached", "--", path)
    else:
        out, rc = git(repo_path, "diff", "--", path)
    if rc != 0:
        out, _ = git(repo_path, "diff", "--cached", "--", path)  # 无 HEAD 的裸仓库回退
    return out or "（无差异）"


def ws_stage(repo_path, paths=None):
    """暂存：paths=None 全部，否则指定文件"""
    if paths is None:
        return git(repo_path, "add", "-A")
    return git(repo_path, "add", "--", *paths)


def ws_unstage(repo_path, paths=None):
    """取消暂存（不动工作区）：paths=None 全部"""
    if paths is None:
        return git(repo_path, "reset")
    return git(repo_path, "reset", "HEAD", "--", *paths)


def ws_discard(repo_path, files):
    """丢弃选中文件的改动：已跟踪 restore 还原；未跟踪直接删除文件（调用方需已确认）。
    files: get_workspace_status 的返回项列表。"""
    tracked = [f["path"] for f in files if not f["untracked"]]
    untracked = [f["path"] for f in files if f["untracked"]]
    msgs, rc = [], 0
    if tracked:
        # --staged --worktree 同时还原暂存区与工作区到 HEAD —— 否则已暂存文件的改动
        # 只被还原到"暂存区版本"(改动依然存在), 用户感知"丢弃没生效"
        out, r2 = git(repo_path, "restore", "--staged", "--worktree", "--", *tracked)
        if r2 != 0:
            # 旧版 git(<2.23) 无 restore: 先取消暂存再还原工作区
            git(repo_path, "reset", "HEAD", "--", *tracked)
            out, r2 = git(repo_path, "checkout", "--", *tracked)
        rc = r2
        # 注: 无 HEAD 的新仓库(从未提交)里"已暂存"文件无法用 restore/reset 还原,
        # 会走 fallback 后诚实报错; 未跟踪文件(新仓库的常态)由下方 os.remove 处理
        msgs.append(out or (f"已还原 {len(tracked)} 个文件" if r2 == 0 else f"还原失败(rc={r2})"))
    for p in untracked:
        try:
            os.remove(os.path.join(repo_path, p))
            msgs.append(f"已删除未跟踪文件 {p}")
        except Exception as e:
            msgs.append(str(e))
            rc = 1
    return "\n".join(msgs), rc


def build_discard_confirm_text(files, limit=8):
    """构建「丢弃选中」确认弹窗文案（纯函数，便于测试）。
    每行一个文件：已跟踪标注 vs HEAD 改动行数(+a/−r)，未跟踪标注「将直接删除」。
    返回 (title, body)；超过 limit 省略并注明总数。"""
    files = list(files or [])
    # 未跟踪统计必须看全部文件：丢弃作用于所有选中项，切片之外被删的未跟踪文件
    # 也要触发「删除后无法恢复」警示，否则会误导用户以为只还原已跟踪文件
    n_untracked = sum(1 for f in files if f.get("untracked"))
    shown = files[:limit]
    lines = []
    for f in shown:
        if f.get("untracked"):
            lines.append(f"⚠️  {f['path']}    （未跟踪 · 将直接删除）")
        else:
            a, r = f.get("added", 0), f.get("removed", 0)
            lines.append(f"📄  {f['path']}    （改动 +{a}/−{r}）")
    if len(files) > limit:
        lines.append(f"… 等共 {len(files)} 个文件")
    # 风险提示按场景区分：含未跟踪 → 删除不可恢复；纯已跟踪 → 还原到最近一次提交
    warn = "含未跟踪文件，删除后无法恢复" if n_untracked else "改动将还原到最近一次提交"
    title = f"丢弃 {len(files)} 个文件的改动"
    body = ("将丢弃以下文件的改动：\n\n"
            + "\n".join(lines)
            + f"\n\n⚠️ {warn}，确定继续？")
    return title, body


def ws_commit(repo_path, message):
    """提交已暂存内容"""
    return git(repo_path, "commit", "-m", message)


def ws_stage_all_and_commit(repo_path, message):
    """一键暂存全部变更并提交：git add -A → git commit -m。
    未跟踪文件一并纳入（全部=工作区所有变更）。返回 (out, rc)。"""
    out, rc = git(repo_path, "add", "-A")
    if rc != 0:
        return out, rc
    return ws_commit(repo_path, message)


# ---------- 提交信息模板 / 历史记忆 ----------
COMMIT_PREFIXES = ["", "feat:", "fix:", "docs:", "refactor:",
                   "chore:", "test:", "perf:", "style:"]
# conventional commits：feat: / fix(api): 等（scope 可选）
COMMIT_PREFIX_RE = re.compile(r"^(feat|fix|docs|refactor|chore|test|perf|style)(\([^)]*\))?:\s*")


def apply_commit_prefix(prefix, current):
    """把前缀应用到提交信息：去掉旧前缀后加新前缀（避免重复、支持替换与 scope）。
    prefix 为空时返回原文。"""
    p = (prefix or "").strip()
    cur = (current or "").strip()
    if not p:
        return cur
    cleaned = COMMIT_PREFIX_RE.sub("", cur)
    return p + " " + cleaned if cleaned else p


# 提交模板变量：保存模板时保留原文，提交时自动替换
COMMIT_VARS = ("{branch}", "{date}", "{time}", "{repo}")


# ============================================================
# Conventional Changelog：版本建议 + CHANGELOG 生成（纯函数，便于测试）
# ============================================================
SEMVER_RE = re.compile(r"^v?(\d+)\.(\d+)\.(\d+)$")
COMMIT_BREAKING_RE = re.compile(r"^(feat|fix|refactor|perf|style|docs|chore|test|build|ci)(\([^)]*\))?!:", re.I)
BREAKING_FOOTER_RE = re.compile(r"BREAKING[- ]CHANGE", re.I)


def analyze_bump(messages):
    """按 conventional commits 规则分析版本级别：
    含 BREAKING CHANGE（!: 或 footer）→ major；含 feat → minor；
    含 fix/perf/refactor → patch；否则 none（无需发版）。"""
    major = minor = patch = False
    for m in messages or []:
        s = (m or "").strip()
        if not s:
            continue
        if BREAKING_FOOTER_RE.search(s) or COMMIT_BREAKING_RE.match(s):
            major = True
        mm = COMMIT_PREFIX_RE.match(s)
        if mm:
            t = mm.group(1).lower()
            if t == "feat":
                minor = True
            elif t in ("fix", "perf", "refactor"):
                patch = True
    if major:
        return "major"
    if minor:
        return "minor"
    if patch:
        return "patch"
    return "none"


def bump_version(current, bump):
    """current 形如 v1.2.3（无 tag 返回 ''）；按 bump 输出下一版本号。
    无当前版本时从 v1.0.0 起步。bump=none 返回 current。"""
    m = SEMVER_RE.match((current or "").strip())
    if bump == "none" or bump is None:
        return current or ""
    if not m:
        return "v1.0.0"
    x, y, z = int(m.group(1)), int(m.group(2)), int(m.group(3))
    if bump == "major":
        return f"v{x + 1}.0.0"
    if bump == "minor":
        return f"v{x}.{y + 1}.0"
    return f"v{x}.{y}.{z + 1}"


def build_changelog_md(messages):
    """把提交信息按 conventional 类型分组渲染成 CHANGELOG Markdown。"""
    groups = {"feat": [], "fix": [], "perf": [], "refactor": [], "other": []}
    breaking = []
    for m in messages or []:
        s = (m or "").strip()
        if not s:
            continue
        if BREAKING_FOOTER_RE.search(s) or COMMIT_BREAKING_RE.match(s):
            breaking.append(s)
        mm = COMMIT_PREFIX_RE.match(s)
        t = mm.group(1).lower() if mm else "other"
        if t in groups:
            groups[t].append(s)
        else:
            groups["other"].append(s)
    lines = [f"# 🧾 Changelog（{len([m for m in messages or [] if (m or '').strip()])} 个提交）", ""]
    if breaking:
        lines += ["## ⚠️ 破坏性变更", ""] + [f"- {x}" for x in breaking] + [""]
    titles = {"feat": "✨ 新功能", "fix": "🐛 修复", "perf": "⚡ 性能优化",
              "refactor": "📦 重构", "other": "📁 其他"}
    for k in ("feat", "fix", "perf", "refactor", "other"):
        if groups[k]:
            lines += [f"## {titles[k]}", ""] + [f"- {x}" for x in groups[k]] + [""]
    return "\n".join(lines).rstrip() + "\n"


def expand_commit_vars(msg, branch="", date="", time="", repo=""):
    """提交模板变量替换：{branch} 当前分支 / {date} 日期 / {time} 时间 / {repo} 仓库名。"""
    if not msg:
        return msg
    return (msg.replace("{branch}", branch)
                .replace("{date}", date)
                .replace("{time}", time)
                .replace("{repo}", repo))


def push_commit_history(history, message, limit=20):
    """记录一条提交信息到历史：去重、最近在前、上限 limit。返回新列表。"""
    history = list(history or [])
    msg = (message or "").strip()
    if not msg:
        return history
    hist = [m for m in history if m != msg]
    hist.insert(0, msg)
    return hist[:limit]


# 比对方向：dev_to_prod = 看 dev 比 prod 多了什么（待上线）；prod_to_dev = 看 prod 比 dev 多了什么（回滚风险）
CMP_DIRECTIONS = {
    "dev_to_prod": "开发 → 生产（待上线）",
    "prod_to_dev": "生产 → 开发（回滚风险）",
}

# conventional commit 类型 → 提交历史行 tag（整行着色）
COMMIT_TYPE_TAGS = {
    "feat": "type_feat", "fix": "type_fix", "docs": "type_docs",
    "refactor": "type_refactor", "chore": "type_chore", "test": "type_test",
    "perf": "type_perf", "style": "type_style",
}
COMMIT_TYPE_COLORS = {
    "feat": "#22C55E", "fix": "#EF4444", "docs": "#F59E0B",
    "refactor": "#3B82F6", "chore": "#06B6D4", "test": "#A855F7",
    "perf": "#F97316", "style": "#14B8A6",
}
# 类型中文名（统计图 / 周报共用）
COMMIT_TYPE_CN = {"feat": "功能", "fix": "修复", "docs": "文档",
                  "refactor": "重构", "chore": "杂务", "test": "测试",
                  "perf": "性能", "style": "风格", "other": "其他"}

# 上线风险分级：命中即标记高风险（配置文件 / 依赖锁文件 / SQL / 基础设施定义）
HIGH_RISK_PATTERNS = (
    r"\.ya?ml$", r"\.env(\.\w+)?$", r"\.properties$",
    r"application.*\.(json|properties)$", r"config\.(json|php|py)$",
    r"(package-lock\.json|pnpm-lock\.yaml|yarn\.lock|poetry\.lock)$",
    r"(pom\.xml|build\.gradle(\.kts)?|requirements.*\.txt|go\.sum|Cargo\.lock|composer\.lock)$",
    r"\.sql$", r"docker-compose.*\.ya?ml$", r"Dockerfile$",
    r"\.tf$", r"\.tfvars$", r"k8s|kubernetes", r"helm",
)


def file_risk(path):
    """上线文件风险分级：配置文件 / 锁文件 / SQL / 基础设施定义 → 高风险。"""
    p = (path or "").replace("\\", "/")
    for pat in HIGH_RISK_PATTERNS:
        if re.search(pat, p, re.I):
            return "高"
    return "低"


def group_files(files):
    """把变动文件按顶层目录分组，返回 [(目录, [文件…])]，根目录归入 (根目录)。"""
    groups = {}
    for f in files or []:
        p = (f.get("path") or "").replace("\\", "/")
        top = p.split("/")[0] if "/" in p else "(根目录)"
        groups.setdefault(top, []).append(f)
    return sorted(groups.items())


# git 文件状态字母 → 中文标签（比对表 / CSV / MD 导出共用）
STATUS_CN = {"A": "新增", "M": "修改", "D": "删除", "R": "重命名", "C": "复制"}


def _safe_file_part(name):
    """文件名用：把分支名/仓库名里的非法字符换成下划线（feature/foo → feature_foo）。"""
    return re.sub(r"[\\/:*?\"<>|]", "_", name or "")


def _resolve_branch(repo_path, name, auto_fetch=True, progress=None):
    """解析分支引用：优先本地分支 refs/heads/<name>，回退到 origin 远程跟踪分支。
    返回 (ref, found, fetched)。auto_fetch=True 时：
      - 若本地与 origin 跟踪引用都找不到，自动执行
        `git fetch origin +refs/heads/<name>:refs/remotes/origin/<name>` 拉成跟踪引用再解析
        （解决单分支 clone 导致远端分支查不到的问题）；
      - 若命中的是远程跟踪引用 refs/remotes/origin/<name>，会先 `git fetch origin <name>`
        刷新它再返回，避免用过期的 origin/<name> 去比对（否则本地新提交不会出现在结果里）。
    progress: 可选回调，接收步骤字符串用于界面日志展示。"""
    def log(msg):
        if progress:
            progress(msg)
    name = (name or "").strip()
    log(f"· 解析分支 {name}：先查本地 refs/heads/{name}")
    for ref in (f"refs/heads/{name}", f"refs/remotes/origin/{name}"):
        out, rc = git(repo_path, "rev-parse", "--verify", ref)
        if rc == 0 and out.strip():
            # 命中远程跟踪引用：开启自动拉取时先刷新，确保不是过期引用
            if auto_fetch and ref.startswith("refs/remotes/origin/"):
                log(f"· 命中远程跟踪引用 {ref}，先 `git fetch origin {name}` 刷新…")
                git(repo_path, "fetch", "origin", name, timeout=90)
                out, rc = git(repo_path, "rev-parse", "--verify", ref)
                if rc == 0 and out.strip():
                    log(f"· 分支 {name} 已解析为 {ref}（已刷新到最新）")
                    return ref, True, True
            log(f"· 分支 {name} 已解析为 {ref}")
            return ref, True, False
    if auto_fetch:
        log(f"· 本地与远程跟踪均无 {name}，尝试 `git fetch origin "
            f"+refs/heads/{name}:refs/remotes/origin/{name}`")
        git(repo_path, "fetch", "origin",
            f"+refs/heads/{name}:refs/remotes/origin/{name}", timeout=90)
        out, rc = git(repo_path, "rev-parse", "--verify",
                      f"refs/remotes/origin/{name}")
        if rc == 0 and out.strip():
            log(f"· 已从 origin 拉取并解析 {name} → refs/remotes/origin/{name}")
            return f"refs/remotes/origin/{name}", True, True
    log(f"· 分支 {name} 解析失败（本地 / 远程跟踪 / 自动拉取均未找到）")
    return "", False, False


def _ref_label(ref):
    """把完整引用渲染成可读标签，并标注是本地还是远程（远程可能过期）。"""
    if not ref:
        return "（未解析）"
    if ref.startswith("refs/heads/"):
        return ref[len("refs/heads/"):] + " ·本地"
    if ref.startswith("refs/remotes/origin/"):
        return ref[len("refs/remotes/origin/"):] + " ·origin(可能过期)"
    return ref


def compute_compare(repo_path, dev, prod, direction="dev_to_prod", auto_fetch=True, progress=None):
    """比对 dev 与 prod 分支，返回 {ok, error?, commits, files, dev, prod, base, head, direction}。
    progress: 可选回调，接收步骤字符串用于界面日志展示。"""
    def log(msg):
        if progress:
            progress(msg)
    dev = (dev or "").strip()
    prod = (prod or "").strip()
    log(f"开始比对：仓库 {repo_path}")
    log(f"方向={'prod→dev（回滚风险）' if direction == 'prod_to_dev' else 'dev→prod（待上线）'}；"
        f"开发={dev}　生产={prod}")
    dev_ref, dev_ok, _ = _resolve_branch(repo_path, dev, auto_fetch, progress)
    prod_ref, prod_ok, _ = _resolve_branch(repo_path, prod, auto_fetch, progress)

    if not (dev_ok and prod_ok):
        log("✗ 比对中止：存在无法解析的分支")
        local, _ = git(repo_path, "branch", "--format=%(refname:short)")
        remote, _ = git(repo_path, "branch", "-r", "--format=%(refname:short)")
        local_list = [l.strip() for l in local.splitlines() if l.strip()]
        remote_list = [l.strip() for l in remote.splitlines() if l.strip()]
        missing = []
        if not dev_ok:
            missing.append(f"dev:{dev}")
        if not prod_ok:
            missing.append(f"prod:{prod}")
        detail = (f"找不到分支 → {' / '.join(missing)}（请检查比对设置）\n\n"
                  f"该仓库本地分支：{', '.join(local_list) or '（无）'}\n"
                  f"该仓库远程分支：{', '.join(remote_list) or '（无）'}\n\n"
                  f"提示：git_monitor.json 里的 dev_branch / prod_branch 需与上面列表一致；"
                  f"若只有远程分支（origin/xxx），直接填 xxx 即可，程序会自动识别。"
                  + ("\n\n注意：已尝试自动从 origin 拉取缺失分支但仍失败，"
                     "请确认该分支已推送到 origin（git ls-remote --heads origin 可查）。"
                     if auto_fetch else ""))
        return {"ok": False, "error": detail,
                "commits": [], "files": [], "dev": dev, "prod": prod,
                "base": "", "head": "", "direction": direction}

    if direction == "prod_to_dev":
        base, head = dev_ref, prod_ref        # 看 prod 比 dev 多了什么
    else:
        base, head = prod_ref, dev_ref        # 看 dev 比 prod 多了什么
    log(f"基准(base)={_ref_label(base)}　目标(head)={_ref_label(head)}")
    # 防御：base 与 head 解析为同一引用 → 相当于"拿分支跟自己比"，必然 0/0，
    # 通常是 dev_branch 与 prod_branch 在配置里配成了同一个分支。明确报错而非静默 0。
    if base == head:
        log("⚠ base 与 head 解析为同一引用，比对无意义（请检查 dev_branch / prod_branch）")
        detail = (f"基准与目标为同一分支：{_ref_label(base)}\n\n"
                  f"请检查 git_monitor.json：dev_branch（当前={dev}）与 "
                  f"prod_branch（当前={prod}）不能配成同一个分支，否则相当于拿分支跟自己比，"
                  f"结果永远 0 提交 / 0 文件。\n\n"
                  f"正确示例：dev_branch=develop，prod_branch=main。")
        return {"ok": False, "error": detail, "commits": [], "files": [],
                "dev": dev, "prod": prod, "base": base, "head": head,
                "direction": direction}
    log("计算待上线提交：git log <base>..<head> …")
    commits = get_ahead_commits(repo_path, base, head)
    log(f"  → 得到 {len(commits)} 个提交")
    log("计算变动文件：git diff --name-status <base> <head> …")
    files = get_branch_file_diff(repo_path, base, head)
    log(f"  → 得到 {len(files)} 个变动文件")
    log("✓ 比对完成")
    return {"ok": True, "commits": commits, "files": files, "dev": dev,
            "prod": prod, "base": base, "head": head, "direction": direction}


def build_release_md(data, repo):
    """把比对结果渲染成 Markdown 上线清单 + 发布说明模板（纯函数，便于测试）。
    data 为 compute_compare 的返回字典（ok=True 时含 commits/files/base/head/direction）。
    方向为 prod_to_dev 时输出回滚风险清单。"""
    now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    direction = data.get("direction", "dev_to_prod")
    is_rollback = direction == "prod_to_dev"
    title = "⚠ 回滚风险清单" if is_rollback else "🚀 上线清单"
    dir_label = "生产 → 开发（回滚风险）" if is_rollback else "开发 → 生产（待上线）"

    lines = []
    lines.append(f"# {title}：{repo}\n")
    lines.append(f"> 比对方向：{dir_label}")
    lines.append(f"> 基准：{_ref_label(data.get('base', ''))} → "
                 f"目标：{_ref_label(data.get('head', ''))}")
    lines.append(f"> 生成时间：{now}\n")

    commits = data.get("commits", [])
    files = data.get("files", [])
    verb = "回滚" if is_rollback else "上线"
    lines.append(f"## 待{verb}提交（{len(commits)}）")
    if commits:
        lines.append("| Hash | 时间 | 作者 | 提交信息 |")
        lines.append("| --- | --- | --- | --- |")
        for c in commits:
            lines.append(f"| `{_md_esc(c.get('hash7'))}` | {_md_esc(c.get('date'))} | "
                         f"{_md_esc(c.get('author'))} | {_md_esc(c.get('message'))} |")
    else:
        lines.append("（无）")
    lines.append("")

    lines.append(f"## 变动文件（{len(files)}）")
    if files:
        status_map = STATUS_CN
        lines.append("| 状态 | 文件 |")
        lines.append("| --- | --- |")
        for fi in files:
            letter = fi.get("status", "?")[0] if fi.get("status") else "?"
            lines.append(f"| {status_map.get(letter, letter)} | `{_md_esc(fi.get('path'))}` |")
    else:
        lines.append("（无）")
    lines.append("")

    lines.append("## 📋 发布说明（Release Notes 草稿）")
    lines.append(f"本次{'回滚' if is_rollback else '发布'}共 {len(commits)} 个提交、"
                 f"{len(files)} 个文件变更。")
    lines.append("")
    if commits:
        for c in commits:
            lines.append(f"- [ ] `{_md_esc(c.get('hash7'))}` {_md_esc(c.get('message'))}"
                         f"（{_md_esc(c.get('author'))}）")
    else:
        lines.append("- [ ] （无待上线提交）")
    lines.append("")
    lines.append("---")
    lines.append("> 由 Git 仓库监控器自动生成；勾选/改写上方条目后可作为正式发布说明。")
    return "\n".join(lines) + "\n"


# ============================================================
# 通知弹窗 + 声音
# ============================================================
def notify_sound():
    if os.name == "nt" and winsound and CFG.get("sound", True):
        try:
            winsound.MessageBeep(winsound.MB_ICONASTERISK)
        except Exception:
            pass


_TOAST_ACTIVE = 0


class Toast(tk.Toplevel):
    """右下角通知弹窗：多个同时出现时自动向上堆叠，避免互相遮挡。"""
    def __init__(self, parent, title, msg):
        global _TOAST_ACTIVE
        super().__init__(parent)
        self.overrideredirect(True)
        self.attributes("-topmost", True)
        sw, sh = self.winfo_screenwidth(), self.winfo_screenheight()
        _TOAST_ACTIVE += 1
        off = (_TOAST_ACTIVE - 1) % 6
        self.geometry(f"320x90+{sw - 340}+{sh - 140 - off * 100}")
        self.configure(bg=THEME_BG)
        fr = tk.Frame(self, bg=THEME_PANEL,
                      highlightbackground=THEME_BORDER, highlightthickness=1)
        fr.pack(fill=tk.BOTH, expand=True)
        tk.Label(fr, text=f"📢 {title}", bg=THEME_PANEL, fg=THEME_ACCENT,
                 font=(FONT_UI, 10, "bold")).pack(anchor=tk.W, padx=12, pady=(10, 2))
        tk.Label(fr, text=msg, bg=THEME_PANEL, fg=THEME_TEXT,
                 font=(FONT_UI, 9), wraplength=290).pack(anchor=tk.W, padx=12)
        self.after(5000, self._close)

    def _close(self):
        global _TOAST_ACTIVE
        _TOAST_ACTIVE = max(0, _TOAST_ACTIVE - 1)
        try:
            self.destroy()
        except Exception:
            pass


# ============================================================
# 系统托盘（ctypes 零依赖；配置 tray=true 时启用）
# ============================================================
_TRAY_ACTIVE = False
_TRAY_HWND = None
_TRAY_WNDPROC = None  # 保持窗口过程引用，防止被 GC 回收


def _tray_thread(app):
    """独立线程：隐藏消息窗口 + Shell_NotifyIcon。点击托盘图标通过
    app.root.after(0, ...) 回到主线程（Tkinter after 跨线程安全）。
    失败（无桌面会话等）时静默降级，不影响主程序。"""
    global _TRAY_ACTIVE, _TRAY_HWND, _TRAY_WNDPROC
    try:
        import ctypes
        from ctypes import wintypes
    except Exception:
        return
    user32 = ctypes.windll.user32
    shell32 = ctypes.windll.shell32
    kernel32 = ctypes.windll.kernel32
    # 指针宽类型：兼容 Python 3.8/3.9（wintypes 无 WPARAM/LPARAM/LRESULT）
    # WPARAM 无符号 / LPARAM、LRESULT 有符号，64 位下均为 8 字节
    WP = ctypes.c_size_t
    LP = ctypes.c_ssize_t

    class NOTIFYICONDATAW(ctypes.Structure):
        _fields_ = [
            ("cbSize", wintypes.DWORD),
            ("hWnd", wintypes.HWND),
            ("uID", wintypes.UINT),
            ("uFlags", wintypes.UINT),
            ("uCallbackMessage", wintypes.UINT),
            ("hIcon", wintypes.HICON),
            ("szTip", wintypes.WCHAR * 128),
            ("dwState", wintypes.DWORD),
            ("dwStateMask", wintypes.DWORD),
            ("szInfo", wintypes.WCHAR * 256),
            ("uVersion", wintypes.UINT),
            ("szInfoTitle", wintypes.WCHAR * 64),
            ("dwInfoFlags", wintypes.DWORD),
            ("guidItem", ctypes.c_byte * 16),
            ("hBalloonIcon", wintypes.HICON),
        ]

    WNDPROC = ctypes.WINFUNCTYPE(ctypes.c_ssize_t, wintypes.HWND,
                                 wintypes.UINT, WP, LP)
    WM_APP_TRAY = 0x8001

    @WNDPROC
    def wndproc(hwnd, msg, wparam, lparam):
        try:
            if msg == WM_APP_TRAY:
                if lparam in (0x202, 0x203):   # WM_LBUTTONUP / WM_LBUTTONDBLCLK
                    app.root.after(0, app._tray_restore)
                elif lparam == 0x205:          # WM_RBUTTONUP → 主线程弹菜单
                    app.root.after(0, app._tray_popup_menu)
            return user32.DefWindowProcW(hwnd, msg, wparam, lparam)
        except Exception:
            # 退出竞态期（root 已销毁 / 异常消息）不抛给 ctypes，避免 "Exception ignored"
            return 0

    class WNDCLASSW(ctypes.Structure):
        _fields_ = [
            ("style", wintypes.UINT),
            ("lpfnWndProc", WNDPROC),
            ("cbClsExtra", ctypes.c_int),
            ("cbWndExtra", ctypes.c_int),
            ("hInstance", wintypes.HINSTANCE),
            ("hIcon", wintypes.HICON),
            ("hCursor", wintypes.HANDLE),
            ("hbrBackground", wintypes.HBRUSH),
            ("lpszMenuName", wintypes.LPCWSTR),
            ("lpszClassName", wintypes.LPCWSTR),
        ]

    _TRAY_WNDPROC = wndproc  # 防 GC

    # 关键：显式声明 Win32 函数签名。未声明时 ctypes 按 32 位 c_int 转换参数与返回值——
    # 64 位 WPARAM/LPARAM（含指针等高位非零数据）会溢出报 "int too long to convert"，
    # 64 位窗口句柄会被截断。此块修复退出时 DefWindowProcW 的 OverflowError。
    user32.DefWindowProcW.argtypes = [wintypes.HWND, wintypes.UINT, WP, LP]
    user32.DefWindowProcW.restype = LP
    user32.CreateWindowExW.argtypes = [
        wintypes.DWORD, wintypes.LPCWSTR, wintypes.LPCWSTR, wintypes.DWORD,
        ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_int,
        wintypes.HWND, wintypes.HMENU, wintypes.HINSTANCE, ctypes.c_void_p]
    user32.CreateWindowExW.restype = wintypes.HWND
    # GetModuleHandleW 在 kernel32（不在 user32），挂错模块会报 function not found
    kernel32.GetModuleHandleW.argtypes = [wintypes.LPCWSTR]
    kernel32.GetModuleHandleW.restype = wintypes.HMODULE
    user32.LoadIconW.argtypes = [wintypes.HINSTANCE, ctypes.c_void_p]
    user32.LoadIconW.restype = wintypes.HICON
    user32.LoadCursorW.argtypes = [wintypes.HINSTANCE, ctypes.c_void_p]
    user32.LoadCursorW.restype = wintypes.HANDLE
    user32.PostMessageW.argtypes = [wintypes.HWND, wintypes.UINT, WP, LP]
    user32.PostMessageW.restype = wintypes.BOOL
    user32.DestroyWindow.argtypes = [wintypes.HWND]
    user32.DestroyWindow.restype = wintypes.BOOL
    user32.PeekMessageW.argtypes = [ctypes.POINTER(wintypes.MSG), wintypes.HWND,
                                    wintypes.UINT, wintypes.UINT, wintypes.UINT]
    user32.PeekMessageW.restype = wintypes.BOOL
    user32.TranslateMessage.argtypes = [ctypes.POINTER(wintypes.MSG)]
    user32.TranslateMessage.restype = wintypes.BOOL
    user32.DispatchMessageW.argtypes = [ctypes.POINTER(wintypes.MSG)]
    user32.DispatchMessageW.restype = LP
    user32.RegisterClassW.argtypes = [ctypes.POINTER(WNDCLASSW)]
    user32.RegisterClassW.restype = ctypes.c_ushort  # ATOM
    shell32.Shell_NotifyIconW.argtypes = [wintypes.DWORD,
                                          ctypes.POINTER(NOTIFYICONDATAW)]
    shell32.Shell_NotifyIconW.restype = wintypes.BOOL

    wc = WNDCLASSW()
    wc.style = 0
    wc.lpfnWndProc = wndproc
    wc.cbClsExtra = wc.cbWndExtra = 0
    wc.hInstance = kernel32.GetModuleHandleW(None)
    wc.hCursor = user32.LoadCursorW(None, 32512)  # IDC_ARROW
    wc.lpszClassName = "GitMonitorTrayWnd"
    if not user32.RegisterClassW(ctypes.byref(wc)):
        _TRAY_ACTIVE = False
        return
    hwnd = user32.CreateWindowExW(0, "GitMonitorTrayWnd", "GitMonitorTray", 0,
                                  0, 0, 0, 0, None, None, wc.hInstance, None)
    if not hwnd:
        _TRAY_ACTIVE = False
        return
    _TRAY_HWND = hwnd

    nid = NOTIFYICONDATAW()
    nid.cbSize = ctypes.sizeof(NOTIFYICONDATAW)
    nid.hWnd = hwnd
    nid.uID = 1
    nid.uFlags = 0x1 | 0x2 | 0x4   # NIF_MESSAGE | NIF_ICON | NIF_TIP
    nid.uCallbackMessage = WM_APP_TRAY
    nid.hIcon = _make_tray_icon() or user32.LoadIconW(None, 32512)  # 程序图标，无 PIL 时用系统默认
    _tray_hicon = nid.hIcon
    nid.szTip = "Git 仓库监控器"
    if not shell32.Shell_NotifyIconW(0, ctypes.byref(nid)):  # NIM_ADD
        _TRAY_ACTIVE = False
        user32.DestroyWindow(hwnd)
        _TRAY_HWND = None
        return
    shell32.Shell_NotifyIconW(4, ctypes.byref(nid))  # NIM_SETVERSION

    # 消息循环：PeekMessage 轮询，_TRAY_ACTIVE=False（退出程序）时清理退出
    msg = wintypes.MSG()
    while _TRAY_ACTIVE:
        while user32.PeekMessageW(ctypes.byref(msg), None, 0, 0, 1):  # PM_REMOVE
            if msg.message == 0x0012:  # WM_QUIT
                _TRAY_ACTIVE = False
                break
            user32.TranslateMessage(ctypes.byref(msg))
            user32.DispatchMessageW(ctypes.byref(msg))
        if not _TRAY_ACTIVE:
            break
        time.sleep(0.05)

    shell32.Shell_NotifyIconW(2, ctypes.byref(nid))  # NIM_DELETE
    user32.DestroyWindow(hwnd)
    if _tray_hicon:
        user32.DestroyIcon(_tray_hicon)
    _TRAY_HWND = None


# ============================================================
# 仓库状态卡片（Canvas 圆角卡片：状态光晕圆点 + 分支徽章 + 统计胶囊 + 相对时间）
# ============================================================
class RepoCard(tk.Canvas):
    """单个仓库的状态卡片，全部用 Canvas 手绘，支持 hover 高亮"""
    HEIGHT = 120

    def __init__(self, master, name, on_activate, **kw):
        super().__init__(master, bg=THEME_BG, bd=0, highlightthickness=0,
                         height=self.HEIGHT, cursor="hand2", **kw)
        self.name = name
        self.on_activate = on_activate
        self._data = None
        self._hover = False
        self.bind("<Configure>", lambda e: self._redraw())
        # 单击查看提交历史，双击跳转到该仓库的工作台，右键更多操作
        self.bind("<Button-1>", lambda e: self.on_activate(self.name, single=True))
        self.bind("<Double-1>", lambda e: self.on_activate(self.name))
        self.bind("<Button-3>", lambda ev: self.on_activate(self.name, right=True, event=ev))
        self.bind("<Enter>", lambda e: self._set_hover(True))
        self.bind("<Leave>", lambda e: self._set_hover(False))

    def _set_hover(self, on):
        self._hover = on
        self._redraw()

    def update(self, color, label, branch, uncommitted, ahead, behind, last, ago,
               added=0, removed=0):
        self._data = (color, label, branch, uncommitted, ahead, behind, last, ago,
                      added, removed)
        self._redraw()

    def _rounded(self, x1, y1, x2, y2, r, fill, outline):
        """圆角矩形：四角用 arc，四边用 line，凸角无凹陷"""
        self.create_arc(x1, y1, x1 + 2 * r, y1 + 2 * r, start=90, extent=90,
                        style="pieslice", fill=fill, outline="")
        self.create_arc(x2 - 2 * r, y1, x2, y1 + 2 * r, start=0, extent=90,
                        style="pieslice", fill=fill, outline="")
        self.create_arc(x1, y2 - 2 * r, x1 + 2 * r, y2, start=180, extent=90,
                        style="pieslice", fill=fill, outline="")
        self.create_arc(x2 - 2 * r, y2 - 2 * r, x2, y2, start=270, extent=90,
                        style="pieslice", fill=fill, outline="")
        self.create_rectangle(x1 + r, y1, x2 - r, y2, fill=fill, outline="")
        self.create_rectangle(x1, y1 + r, x2, y2 - r, fill=fill, outline="")
        if outline and outline != fill:
            self.create_arc(x1, y1, x1 + 2 * r, y1 + 2 * r, start=90, extent=90,
                            style="arc", outline=outline, width=1)
            self.create_arc(x2 - 2 * r, y1, x2, y1 + 2 * r, start=0, extent=90,
                            style="arc", outline=outline, width=1)
            self.create_arc(x1, y2 - 2 * r, x1 + 2 * r, y2, start=180, extent=90,
                            style="arc", outline=outline, width=1)
            self.create_arc(x2 - 2 * r, y2 - 2 * r, x2, y2, start=270, extent=90,
                            style="arc", outline=outline, width=1)
            self.create_line(x1 + r, y1, x2 - r, y1, fill=outline, width=1)
            self.create_line(x1 + r, y2, x2 - r, y2, fill=outline, width=1)
            self.create_line(x1, y1 + r, x1, y2 - r, fill=outline, width=1)
            self.create_line(x2, y1 + r, x2, y2 - r, fill=outline, width=1)

    def _chip(self, x, y, text, bg, fg, bold=True):
        """小胶囊标签，返回下一个 x 坐标"""
        f = _font((FONT_UI, 8, "bold") if bold else (FONT_UI, 8))
        tw = f.measure(text)
        w, h = tw + 16, 19
        self._rounded(x, y, x + w, y + h, 9, bg, bg)
        self.create_text(x + w / 2, y + h / 2, text=text, fill=fg,
                         font=(FONT_UI, 8, "bold") if bold else (FONT_UI, 8))
        return x + w + 8

    def _redraw(self):
        self.delete("all")
        w = max(self.winfo_width(), 240)
        H = self.HEIGHT
        if self._data is None:
            self._rounded(2, 3, w - 2, H - 3, 12, THEME_PANEL, THEME_BORDER)
            self.create_text(30, H / 2, anchor="w", text=self.name,
                             fill=THEME_MUTED, font=(FONT_UI, 11, "bold"))
            self.create_text(w - 30, H / 2, anchor="e", text="等待刷新…",
                             fill=THEME_MUTED, font=(FONT_UI, 9))
            return
        color, label, branch, unc, ahead, behind, last, ago, added, removed = self._data
        border = THEME_ACCENT if self._hover else THEME_BORDER
        self._rounded(2, 3, w - 2, H - 3, 12, THEME_PANEL, border)

        # 状态圆点 + 光晕
        cx, cy = 27, H / 2
        glow = _blend(color, THEME_BG, 0.45)
        self.create_oval(cx - 13, cy - 13, cx + 13, cy + 13, fill=glow, outline="")
        self.create_oval(cx - 7, cy - 7, cx + 7, cy + 7, fill=color,
                         outline=THEME_PANEL, width=2)

        # 标题
        tf = _font((FONT_UI, 13, "bold"))
        title = self.name
        if tf.measure(title) > w - 320:
            while tf.measure(title + "…") > w - 320 and len(title) > 1:
                title = title[:-1]
            title += "…"
        self.create_text(52, 30, anchor="w", text=title, fill=THEME_TEXT,
                         font=(FONT_UI, 13, "bold"))

        # 分支徽章（右上角）
        branch = (branch or "—").strip()
        if branch and branch != "N/A":
            bf = _font((FONT_UI, 9, "bold"))
            tw = bf.measure(branch)
            bw, bh = tw + 20, 22
            bx = w - bw - 14
            self._rounded(bx, 18, bx + bw, 18 + bh, 11, THEME_ACCENT_SOFT, THEME_ACCENT_SOFT)
            self.create_text(bx + bw / 2, 18 + bh / 2, text=branch, fill=THEME_ACCENT,
                             font=(FONT_UI, 9, "bold"))

        # 统计胶囊（无标签行，仅显示非零计数，用颜色区分状态）
        px = 52
        if unc > 0:
            px = self._chip(px, 60, f"未提交 {unc}", COLOR_MODIFIED, TAG_COLORS["M"][1])
        if ahead > 0:
            px = self._chip(px, 60, f"领先 {ahead}", THEME_ACCENT_SOFT, THEME_ACCENT)
        if behind > 0:
            px = self._chip(px, 60, f"落后 {behind}", COLOR_BEHIND, TAG_COLORS["D"][1])
        if added or removed:
            px = self._chip(px, 60, f"+{added}/-{removed}", THEME_ACCENT_SOFT, THEME_ACCENT)
        if not any([unc, ahead, behind, added, removed]):
            tag = self._tag_of(label)
            soft = STATUS_SOFT.get(tag, THEME_ACCENT_SOFT)
            fg = {"clean": STATUS_STYLE["clean"][0], "modified": STATUS_STYLE["modified"][0],
                  "behind": STATUS_STYLE["behind"][0], "ahead": THEME_ACCENT,
                  "invalid": THEME_MUTED}.get(tag, THEME_ACCENT)
            self._chip(px, 60, label, soft, fg)

        # 最近提交 + 相对时间
        lf = _font((FONT_UI, 9))
        last = last or "无提交"
        if lf.measure(last) > w - 360:
            while lf.measure(last + "…") > w - 360 and len(last) > 1:
                last = last[:-1]
            last += "…"
        self.create_text(52, 98, anchor="w", text=last, fill=THEME_MUTED,
                         font=(FONT_UI, 9))
        if ago:
            self.create_text(w - 16, 98, anchor="e", text=ago, fill=THEME_MUTED,
                             font=(FONT_UI, 9))

    @staticmethod
    def _tag_of(label):
        for k, (_, lbl, tag) in STATUS_STYLE.items():
            if lbl == label:
                return tag
        return ""


# ============================================================
# 概览统计胶囊（可点击筛选仓库状态）
# ============================================================
class StatChip(tk.Frame):
    """统计胶囊：彩色圆点 + 文案 + 数量，点击切换筛选"""
    def __init__(self, master, key, label, dot_color, soft, on_click, selected=False):
        super().__init__(master, bg=soft, cursor="hand2",
                         highlightbackground=THEME_ACCENT if selected else THEME_BORDER,
                         highlightthickness=2 if selected else 1)
        self.key = key
        self.on_click = on_click
        dot = tk.Canvas(self, width=10, height=10, bg=soft, bd=0, highlightthickness=0)
        dot.create_oval(1, 1, 9, 9, fill=dot_color, outline="")
        dot.pack(side=tk.LEFT, padx=(8, 5), pady=6)
        self.label_var = tk.StringVar(value=f"{label} 0")
        lbl = tk.Label(self, textvariable=self.label_var, bg=soft, fg=THEME_TEXT,
                       font=(FONT_UI, 9))
        lbl.pack(side=tk.LEFT, padx=(0, 10))
        for w in (self, dot, lbl):
            w.bind("<Button-1>", lambda e, k=key: on_click(k))

    def set_count(self, n):
        self.label_var.set(f"{self.label_var.get().rsplit(' ', 1)[0]} {n}")

    def set_selected(self, sel):
        self.configure(highlightbackground=THEME_ACCENT if sel else THEME_BORDER,
                       highlightthickness=2 if sel else 1)


# ============================================================
# 主应用
# ============================================================
class GitMonitorApp:
    def __init__(self, root):
        self.root = root
        self.root.title("Git 仓库监控器")
        self.root.geometry("1100x720")
        self.root.minsize(920, 560)

        self.known_hash = {}
        self.known_uncommitted = {}
        self.first_load = True
        self._refreshing = False      # 刷新进行中守卫，避免叠加并发刷新
        self._pending_refresh = False # 刷新期间收到手动刷新请求 → 跑完后再补一次

        # 异步加载请求序号：快速切换仓库/主题重建后丢弃过期线程结果，防止旧数据覆盖新数据
        self._commits_req = 0
        self._stats_req = 0
        self._graph_req = 0
        self._ws_req = 0
        self._branch_req = 0
        self._stash_req = 0
        self._settings_open = False   # 设置窗口打开中：自动刷新跳过 reload_config

        # 比对状态追踪
        self.known_release = set()
        self.first_compare = True
        self.last_cmp_dir = None          # 上一次自动比对的方向（方向切换时静默通知，避免误报）
        self.cmp_base = COMPARE.get("prod_branch", "")
        self.cmp_head = COMPARE.get("dev_branch", "")
        self._cmp_running = False         # 比对进行中守卫，避免并发叠加

        self.all_commits = []
        self.current_repo = None
        self._active_repo = None

        # 渲染缓存（主题切换重建 UI 后用于恢复内容）
        self._gen = 0                     # UI 代数，重建时 +1，过期回调直接丢弃
        self._last_info = None
        self._last_cmp = None
        self._graph_data = None
        self._graph_repo = None
        self._graph_scale = 1.0  # 提交图缩放（Ctrl+滚轮）
        self._stats = None

        # 分组 / 搜索 / 状态筛选
        self.group_var = tk.StringVar(value="全部")
        self.repo_search_var = tk.StringVar()
        self.repo_search_var.trace_add("write", lambda *a: self._on_repo_filter())
        self.summary_key = "all"
        self.summary_chips = {}

        self._configure_styles()
        self._build_ui()
        self._bind_shortcuts()

        # 系统托盘（配置 tray=true 时启用；独立线程，失败静默降级不影响主程序）
        global _TRAY_ACTIVE
        if CFG.get("tray", True) and os.name == "nt":
            _TRAY_ACTIVE = True
            threading.Thread(target=_tray_thread, args=(self,), daemon=True).start()
        self._tray_enabled = (CFG.get("tray", True)
                              and CFG.get("minimize_to_tray", True)
                              and os.name == "nt")
        if self._tray_enabled:
            self.root.bind("<Unmap>", self._on_maybe_minimize)

        self.refresh()
        self.polling = True
        threading.Thread(target=self._background_poll, daemon=True).start()

    # -------------------- 主题 / 重建 --------------------
    def _switch_theme(self, name):
        """切换主题：重算颜色 → 重建主 UI → 只持久化 theme 键。
        不整份 save_config：避免把设置窗里尚未保存的其它改动意外落盘。"""
        apply_theme(name)
        CFG["theme"] = name
        try:
            with open(CONFIG_PATH, "r", encoding="utf-8") as f:
                _cfg = json.load(f)
            _cfg["theme"] = name
            _atomic_write_json(CONFIG_PATH, _cfg)
        except Exception:
            pass
        self._rebuild_ui()

    def _rebuild_ui(self):
        self._gen += 1
        for w in self.root.winfo_children():
            if isinstance(w, tk.Toplevel):
                continue  # 弹窗（设置/diff）不随主窗口重建销毁，避免丢失未保存内容
            w.destroy()
        # 取消统计图防抖重绘定时器：旧画布已销毁，迟到的重绘会在已销毁控件上报错
        if getattr(self, "_stats_redraw_after", None) is not None:
            try:
                self.root.after_cancel(self._stats_redraw_after)
            except Exception:
                pass
            self._stats_redraw_after = None
        self._configure_styles()
        self._build_ui()
        self._bind_shortcuts()
        self._refresh_group_cb()
        if self._last_info is not None:
            self._rebuild_cards(self._last_info)
            self._render_commits(self.all_commits)
        if self._last_cmp is not None:
            self._repopulate_compare_trees(self._last_cmp)
        if self._graph_data is not None and self._graph_repo:
            self._draw_graph(self._graph_data, self._graph_repo)
        if self._stats is not None:
            self._draw_stats(*self._stats)
        self.status_var.set("UI 已重建（主题已切换）")

    # -------------------- 样式 --------------------
    def _configure_styles(self):
        style = ttk.Style()
        try:
            style.theme_use("clam")
        except Exception:
            pass
        # 全局默认
        style.configure(".", font=(FONT_UI, 10), background=THEME_BG,
                        foreground=THEME_TEXT, bordercolor=THEME_BORDER,
                        darkcolor=THEME_BG, lightcolor=THEME_BG)
        # 普通按钮
        style.configure("TButton", font=(FONT_UI, 10), padding=(10, 6),
                        background=THEME_PANEL, foreground=THEME_TEXT,
                        bordercolor=THEME_BORDER, relief="flat")
        style.map("TButton",
                  background=[("active", THEME_BTN_HOVER),
                              ("disabled", THEME_BTN_DISABLED)],
                  bordercolor=[("active", THEME_ACCENT)])
        # 主按钮（强调）
        style.configure("Accent.TButton", font=(FONT_UI, 10, "bold"),
                        padding=(14, 6), background=THEME_ACCENT,
                        foreground="white", borderwidth=0, relief="flat")
        style.map("Accent.TButton",
                  background=[("active", THEME_ACCENT_HOVER),
                              ("disabled", THEME_BTN_DISABLED)],
                  foreground=[("disabled", THEME_MUTED)])
        # 树形表格
        style.configure("Treeview", font=(FONT_UI, 10), rowheight=30,
                        background=THEME_PANEL, foreground=THEME_TEXT,
                        fieldbackground=THEME_PANEL, bordercolor=THEME_BORDER)
        style.configure("Treeview.Heading", font=(FONT_UI, 10, "bold"),
                        background=THEME_ACCENT_SOFT, foreground=THEME_TEXT,
                        borderwidth=0, relief="flat", padding=(6, 8))
        style.map("Treeview",
                  background=[("selected", SELECT_BG)],
                  foreground=[("selected", SELECT_FG)])
        # 标签页
        style.configure("TNotebook", background=THEME_BG, borderwidth=0)
        style.configure("TNotebook.Tab", font=(FONT_UI, 10),
                        background=THEME_BG, foreground=THEME_MUTED,
                        padding=(22, 11), borderwidth=0)
        style.map("TNotebook.Tab",
                  background=[("selected", THEME_PANEL), ("active", THEME_BTN_HOVER)],
                  foreground=[("selected", THEME_ACCENT)])
        # 分组框
        style.configure("TLabelframe", background=THEME_BG,
                        bordercolor=THEME_INPUT_BORDER, relief="flat")
        style.configure("TLabelframe.Label", font=(FONT_UI, 10, "bold"),
                        foreground=THEME_ACCENT, background=THEME_BG)
        # 输入控件
        style.configure("TCombobox", font=(FONT_UI, 10), padding=4,
                        fieldbackground=THEME_PANEL, background=THEME_PANEL,
                        bordercolor=THEME_INPUT_BORDER)
        style.configure("TEntry", font=(FONT_UI, 10), padding=4,
                        fieldbackground=THEME_PANEL, bordercolor=THEME_INPUT_BORDER)
        style.configure("TCheckbutton", font=(FONT_UI, 10),
                        background=THEME_BG, foreground=THEME_TEXT)
        style.configure("TPanedwindow", background=THEME_BG)
        style.configure("TScrollbar", background=THEME_SCROLLBAR, troughcolor=THEME_BG,
                        arrowcolor=THEME_MUTED, bordercolor=THEME_BG, relief="flat")
        style.configure("TProgressbar", background=THEME_ACCENT,
                        troughcolor=THEME_BG)
        style.configure("TSpinbox", font=(FONT_UI, 10), fieldbackground=THEME_PANEL,
                        arrowcolor=THEME_MUTED)

    # -------------------- UI 构建 --------------------
    def _build_ui(self):
        self.root.configure(bg=THEME_BG)

        # 顶部标题栏 - 简洁现代设计
        tf = tkfont.Font(family=FONT_UI, size=16, weight="bold")
        sf = tkfont.Font(family=FONT_UI, size=9)
        title_y = 16 + tf.metrics("linespace") // 2
        sub_y = title_y + tf.metrics("linespace") // 2 + 4 + sf.metrics("linespace") // 2
        head_h = sub_y + sf.metrics("linespace") // 2 + 16
        header = tk.Canvas(self.root, height=head_h, bd=0, highlightthickness=0)
        header.pack(fill=tk.X)
        header.pack_propagate(False)
        # 渐变背景
        c_top = _blend(THEME_HEADER, THEME_ACCENT, 0.15)
        c_bot = THEME_HEADER
        for y in range(head_h):
            header.create_line(0, y, 4000, y, fill=_blend(c_top, c_bot, y / head_h))
        # Logo
        cy = head_h // 2
        header.create_oval(cy - 14, cy - 14, cy + 14, cy + 14,
                           fill=_blend(THEME_ACCENT, "white", 0.12), outline="")
        header.create_oval(cy - 8, cy - 8, cy + 8, cy + 8,
                           fill=THEME_ACCENT, outline="")
        tx = cy + 26
        header.create_text(tx, title_y, text="Git 仓库监控器", anchor="w", fill="white",
                           font=(FONT_UI, 16, "bold"))
        header.create_text(tx, sub_y, text="实时状态 · 上线前差异比对 · 离线可用", anchor="w",
                           fill=THEME_HEADER_SUB, font=(FONT_UI, 9))
        # 版本徽章
        v3 = header.create_text(3800, title_y, text="v3.0", anchor="e",
                                fill="white", font=(FONT_UI, 9, "bold"))
        header.bind("<Configure>", lambda e, tag=v3: header.coords(tag, e.width - 20, title_y))

        # 工具栏
        toolbar = ttk.Frame(self.root, padding=(12, 8))
        toolbar.pack(fill=tk.X)
        ttk.Label(toolbar, text="分组:").pack(side=tk.LEFT)
        self.group_cb = ttk.Combobox(toolbar, textvariable=self.group_var,
                                     values=["全部"] + list(CFG.get("groups", {})),
                                     state="readonly", width=10)
        self.group_cb.pack(side=tk.LEFT, padx=4)
        self.group_cb.bind("<<ComboboxSelected>>", lambda e: self._on_repo_filter())
        ttk.Label(toolbar, text="搜索:").pack(side=tk.LEFT, padx=(10, 0))
        ttk.Entry(toolbar, textvariable=self.repo_search_var, width=16).pack(side=tk.LEFT, padx=4)
        self.auto_var = tk.BooleanVar(value=CFG.get("auto_refresh", True))
        ttk.Checkbutton(toolbar, text="自动刷新", variable=self.auto_var).pack(
            side=tk.RIGHT, padx=8)
        ttk.Button(toolbar, text="⚙ 设置", command=self._open_settings).pack(
            side=tk.RIGHT, padx=2)
        ttk.Button(toolbar, text="⚡ 批量操作", command=self._open_batch_op).pack(
            side=tk.RIGHT, padx=2)
        ttk.Button(toolbar, text="🔄 立即刷新", command=self.refresh,
                   style="Accent.TButton").pack(side=tk.RIGHT, padx=2)

        # 标签页
        self.notebook = ttk.Notebook(self.root)
        self.notebook.pack(fill=tk.BOTH, expand=True, padx=12, pady=(4, 0))
        self._build_monitor_tab(self.notebook)
        self._build_compare_tab(self.notebook)
        self._build_graph_tab(self.notebook)
        self._build_stats_tab(self.notebook)
        self._build_workspace_tab(self.notebook)
        self._build_branches_tab(self.notebook)
        self._build_stash_tab(self.notebook)
        self.notebook.bind("<<NotebookTabChanged>>", self._on_tab_changed)

        # 状态栏
        self.status_var = tk.StringVar(value="就绪")
        ttk.Separator(self.root, orient=tk.HORIZONTAL).pack(fill=tk.X, side=tk.BOTTOM)
        status_bar = tk.Frame(self.root, bg=THEME_PANEL, height=30)
        status_bar.pack(fill=tk.X, side=tk.BOTTOM)
        self.status_dot = tk.Canvas(status_bar, width=10, height=10,
                                     bg=THEME_PANEL, bd=0, highlightthickness=0)
        self.status_dot.create_oval(1, 1, 9, 9, fill="#10B981", outline="")
        self.status_dot.pack(side=tk.LEFT, padx=(12, 5), pady=10)
        tk.Label(status_bar, textvariable=self.status_var, bg=THEME_PANEL,
                 fg=THEME_MUTED, font=(FONT_UI, 9), anchor=tk.W).pack(
            side=tk.LEFT, pady=4)
        self.progress = ttk.Progressbar(status_bar, mode="indeterminate", length=110)
        self.progress.pack(side=tk.RIGHT, padx=(0, 10), pady=9)
        self.clock_var = tk.StringVar(value="")
        tk.Label(status_bar, textvariable=self.clock_var, bg=THEME_PANEL,
                 fg=THEME_MUTED, font=(FONT_UI, 9)).pack(side=tk.RIGHT, padx=14, pady=4)

    def _set_status(self, text, dot="#2BA24C"):
        """统一设置底部状态文字 + 状态点颜色（绿=正常/黄=进行中/红=异常）。"""
        self.status_var.set(text)
        try:
            self.status_dot.delete("all")
            self.status_dot.create_oval(1, 1, 9, 9, fill=dot, outline="")
        except Exception:
            pass

    def _set_busy(self, busy, text=None):
        """git 操作进行中的不确定进度条（避免长任务看起来像卡死）。"""
        if text:
            self._set_status(text, "#E0A100")
        try:
            if busy:
                self.progress.start(12)
            else:
                self.progress.stop()
        except Exception:
            pass

    # ---- 标签页 1：仓库监控 ----
    def _build_monitor_tab(self, notebook):
        tab = ttk.Frame(notebook)
        notebook.add(tab, text="仓库监控")

        pw = ttk.PanedWindow(tab, orient=tk.VERTICAL)
        pw.pack(fill=tk.BOTH, expand=True, padx=12, pady=(0, 8))

        # 仓库状态（圆角卡片 + 彩色状态圆点）
        status_frame = ttk.LabelFrame(pw, text="仓库状态（单击查看提交 · 双击跳转工作台 · 右键更多操作）", padding=(8, 6))
        pw.add(status_frame, weight=0)

        # 概览统计胶囊（点击筛选）
        self.summary_chips = {}
        chip_bar = tk.Frame(status_frame, bg=THEME_BG)
        chip_bar.pack(fill=tk.X, pady=(2, 4))
        self._build_chips(chip_bar)
        for k, chip in self.summary_chips.items():
            chip.set_selected(k == self.summary_key)

        scroll = tk.Frame(status_frame, bg=THEME_BG)
        scroll.pack(fill=tk.BOTH, expand=True)
        _cards_h = min(len(REPOS) * 132 + 12, 520)
        self.status_canvas = tk.Canvas(scroll, bg=THEME_BG, bd=0, highlightthickness=0,
                                       height=_cards_h)
        self.status_scroll = ttk.Scrollbar(scroll, orient=tk.VERTICAL, command=self.status_canvas.yview)
        self.status_canvas.configure(yscrollcommand=self.status_scroll.set)
        self.status_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.status_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        self.cards_frame = tk.Frame(self.status_canvas, bg=THEME_BG)
        self.cards_win = self.status_canvas.create_window((0, 0), window=self.cards_frame, anchor="nw")
        self.cards_frame.bind("<Configure>",
            lambda e: self.status_canvas.configure(scrollregion=self.status_canvas.bbox("all")))
        self.status_canvas.bind("<Configure>",
            lambda e: self.status_canvas.itemconfig(self.cards_win, width=e.width))
        self.repo_cards = {}
        self._rebuild_cards(self._last_info)

        self.repo_menu = Menu(self.root, tearoff=0)
        self.repo_menu.add_command(
            label="📜 查看提交历史",
            command=lambda: self._load_commits(self._active_repo) if self._active_repo else None)
        self.repo_menu.add_command(
            label="🛠 工作台（变更 / 暂存 / 提交）",
            command=lambda: self._open_workspace(self._active_repo) if self._active_repo else None)
        self.repo_menu.add_command(label="📂 在资源管理器打开", command=self._open_current_repo)
        self.repo_menu.add_separator()
        self.repo_menu.add_command(label="🔄 Fetch（拉取远端引用）",
                                   command=lambda: self._repo_action("fetch"))
        self.repo_menu.add_command(label="⬇ Pull（拉取并合并）",
                                   command=lambda: self._repo_action("pull"))
        self.repo_menu.add_command(label="⬆ Push（推送）",
                                   command=lambda: self._repo_action("push"))
        self.repo_menu.add_command(label="🔀 切换分支…", command=self._checkout_dialog)
        self.repo_menu.add_separator()
        self.repo_menu.add_command(label="📊 查看提交图", command=self._show_graph_for_active)
        self.repo_menu.add_command(label="📈 查看统计", command=self._show_stats_for_active)
        self.repo_menu.add_separator()
        self.repo_menu.add_command(label="🔁 刷新状态", command=self.refresh)

        # 提交历史
        commit_frame = ttk.LabelFrame(pw, text="提交历史（双击上方仓库加载）", padding=(10, 6))
        pw.add(commit_frame, weight=1)

        search_row = ttk.Frame(commit_frame)
        search_row.pack(fill=tk.X, pady=(0, 4))
        ttk.Label(search_row, text="🔍 过滤:").pack(side=tk.LEFT)
        self.search_var = tk.StringVar()
        self.search_var.trace_add("write", lambda *a: self._apply_filter())
        self.commit_search = ttk.Entry(search_row, textvariable=self.search_var)
        self.commit_search.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=4)

        ccols = ("hash", "author", "date", "message")
        self.commit_tree = ttk.Treeview(commit_frame, columns=ccols, show="headings", height=12)
        for c, t in [("hash", "Hash"), ("author", "作者"), ("date", "日期"), ("message", "提交信息")]:
            self.commit_tree.heading(c, text=t)
        self.commit_tree.column("hash", width=70, anchor=tk.CENTER)
        self.commit_tree.column("author", width=100, anchor=tk.W)
        self.commit_tree.column("date", width=130, anchor=tk.CENTER)
        self.commit_tree.column("message", width=520, anchor=tk.W)
        self.commit_tree.pack(fill=tk.BOTH, expand=True)
        self.commit_tree.tag_configure("row_alt", background=THEME_ROW_ALT)
        self.commit_tree.tag_configure("row_base", background=THEME_PANEL)
        for _t, _c in COMMIT_TYPE_COLORS.items():
            self.commit_tree.tag_configure(COMMIT_TYPE_TAGS[_t], foreground=_c)
        self.commit_tree.bind("<Double-1>", self._on_commit_dclick)
        self.commit_tree.bind("<Button-3>", self._on_commit_rightclick)

        self.commit_menu = Menu(self.commit_tree, tearoff=0)
        self.commit_menu.add_command(label="🔍 查看完整 diff", command=self._view_diff)
        self.commit_menu.add_command(label="📋 导出文件列表", command=self._export_files)
        self.commit_menu.add_separator()
        self.commit_menu.add_command(label="📋 复制 Hash（短）",
                                     command=lambda: self._copy_hash(True))
        self.commit_menu.add_command(label="📋 复制 Hash（完整）",
                                     command=lambda: self._copy_hash(False))
        self.commit_menu.add_command(label="💬 复制提交信息", command=self._copy_commit_msg)
        self.commit_menu.add_separator()
        self.commit_menu.add_command(label="🍒 Cherry-pick 此提交",
                                     command=self._cherry_pick_selected)
        self.commit_menu.add_command(label="↩️ Revert 此提交",
                                     command=self._revert_selected)
        self.commit_menu.add_command(label="🌿 在此创建分支…",
                                     command=self._branch_from_selected)
        self.commit_menu.add_command(label="🏷 为此提交打标签…",
                                     command=self._tag_selected)

        btn_frame = ttk.Frame(commit_frame)
        btn_frame.pack(fill=tk.X, pady=(6, 0))
        ttk.Button(btn_frame, text="📋 导出文件列表", command=self._export_files).pack(side=tk.LEFT)
        ttk.Button(btn_frame, text="🔍 查看完整 diff", command=self._view_diff).pack(side=tk.LEFT, padx=6)
        self.repo_label = ttk.Label(btn_frame, text="未选择仓库", font=(FONT_UI, 9, "italic"))
        self.repo_label.pack(side=tk.RIGHT)

    # ---- 卡片分组 / 搜索过滤 ----
    def _visible_repos(self):
        g = self.group_var.get()
        kw = self.repo_search_var.get().strip().lower()
        groups = CFG.get("groups", {})
        names = list(REPOS.keys())
        if g != "全部":
            names = [n for n in groups.get(g, []) if n in REPOS]
        if kw:
            names = [n for n in names
                     if kw in n.lower() or kw in REPOS[n].lower()]
        if self.summary_key != "all" and self._last_info:
            names = [n for n in names
                     if self._last_info.get(n, {}).get("tag") == self.summary_key]
        return names

    # ---- 概览胶囊筛选 ----
    CHIP_SPECS = [
        ("all", "全部", "#2F6FED", "ahead"),
        ("clean", "已同步", "#2BA24C", "clean"),
        ("modified", "有改动", "#E0A100", "modified"),
        ("behind", "落后", "#D64545", "behind"),
        ("ahead", "领先", "#2F6FED", "ahead"),
        ("invalid", "无效", "#9AA3B2", "invalid"),
    ]

    def _build_chips(self, master):
        for key, label, color, soft_key in self.CHIP_SPECS:
            chip = StatChip(master, key, label, color,
                            STATUS_SOFT.get(soft_key, THEME_ACCENT_SOFT),
                            self._on_chip_click)
            chip.pack(side=tk.LEFT, padx=(0, 6))
            self.summary_chips[key] = chip

    def _on_chip_click(self, key):
        if self.summary_key == key:
            key = "all"
        self.summary_key = key
        for k, chip in self.summary_chips.items():
            chip.set_selected(k == key)
        self._on_repo_filter()

    def _update_summary(self, info_map):
        counts = {"all": 0, "clean": 0, "modified": 0,
                  "behind": 0, "ahead": 0, "invalid": 0}
        for name, info in info_map.items():
            counts["all"] += 1
            counts[info.get("tag", "invalid")] += 1
        for key, chip in self.summary_chips.items():
            chip.set_count(counts.get(key, 0))

    def _refresh_group_cb(self):
        """刷新分组下拉框的选项（配置变更后调用）"""
        try:
            groups = CFG.get("groups", {})
            self.group_cb.configure(values=["全部"] + list(groups.keys()))
            if self.group_var.get() not in ["全部"] + list(groups.keys()):
                self.group_var.set("全部")
        except Exception:
            pass

    def _on_repo_filter(self):
        if self._last_info is not None:
            self._rebuild_cards(self._last_info)
        elif REPOS:
            self.refresh()  # 数据还没加载时触发刷新

    def _rebuild_cards(self, info_map=None):
        try:
            self.cards_frame
        except Exception:
            return
        for w in self.cards_frame.winfo_children():
            w.destroy()
        self.repo_cards = {}
        visible = self._visible_repos()
        n = len(visible)
        self.status_canvas.configure(height=min(n * 132 + 12, 520) if n else 60)
        if not n:
            tk.Label(self.cards_frame, text="（没有匹配的仓库，请调整分组/搜索）",
                     bg=THEME_BG, fg=THEME_MUTED, font=(FONT_UI, 9)).pack(pady=14)
            return
        for name in visible:
            card = RepoCard(self.cards_frame, name, self._activate_repo)
            card.pack(fill=tk.X, pady=5, padx=2)
            self.repo_cards[name] = card
        self._update_cards(info_map or {})

    def _update_cards(self, info_map):
        # 防御：info 字典可能来自旧版本/测试注入而缺键，切主题重绘时
        # 缺 color 会 KeyError 崩掉整个 UI（回归：切主题偶发闪退/卡死）
        for name, card in self.repo_cards.items():
            info = info_map.get(name) if info_map else None
            if not info or not isinstance(info, dict):
                card.update("#9AA3B2", "未知", "—", 0, 0, 0, "", "")
                continue
            card.update(info.get("color", "#9AA3B2"),
                        info.get("label", "未知"),
                        info.get("branch", "—"),
                        info.get("uncommitted", 0),
                        info.get("ahead", 0),
                        info.get("behind", 0),
                        info.get("last_commit", ""),
                        time_ago(info.get("last_date", "")),
                        info.get("added", 0), info.get("removed", 0))

    # ---- 标签页 2：上线比对 ----
    def _build_compare_tab(self, notebook):
        tab = ttk.Frame(notebook)
        notebook.add(tab, text="上线比对")

        # 比对设置行 1：预设 / 仓库 / 分支
        ctrl = ttk.Frame(tab, padding=(10, 8, 10, 0))
        ctrl.pack(fill=tk.X)
        ttk.Label(ctrl, text="预设:").pack(side=tk.LEFT)
        self.cmp_preset_var = tk.StringVar(value="当前配置")
        self.cmp_preset_cb = ttk.Combobox(ctrl, textvariable=self.cmp_preset_var,
                                          values=["当前配置"] +
                                          [p.get("name", "未命名") for p in CFG.get("presets", [])],
                                          state="readonly", width=10)
        self.cmp_preset_cb.pack(side=tk.LEFT, padx=4)
        self.cmp_preset_cb.bind("<<ComboboxSelected>>", self._on_preset_select)
        ttk.Button(ctrl, text="💾 存为预设", command=self._save_as_preset).pack(side=tk.LEFT, padx=2)
        ttk.Label(ctrl, text="仓库:").pack(side=tk.LEFT, padx=(12, 0))
        self.cmp_repo_var = tk.StringVar(value=COMPARE.get("repo", ""))
        self.cmp_repo_cb = ttk.Combobox(ctrl, textvariable=self.cmp_repo_var,
                                        values=list(REPOS.keys()), state="readonly", width=14)
        self.cmp_repo_cb.pack(side=tk.LEFT, padx=4)
        ttk.Label(ctrl, text="开发分支:").pack(side=tk.LEFT, padx=(12, 0))
        self.cmp_dev_var = tk.StringVar(value=COMPARE.get("dev_branch", ""))
        ttk.Entry(ctrl, textvariable=self.cmp_dev_var, width=10).pack(side=tk.LEFT, padx=4)
        ttk.Label(ctrl, text="生产分支:").pack(side=tk.LEFT, padx=(12, 0))
        self.cmp_prod_var = tk.StringVar(value=COMPARE.get("prod_branch", ""))
        ttk.Entry(ctrl, textvariable=self.cmp_prod_var, width=10).pack(side=tk.LEFT, padx=4)

        # 比对设置行 2：方向 / 自动拉取 / 操作按钮
        ctrl2 = ttk.Frame(tab, padding=(10, 6, 10, 8))
        ctrl2.pack(fill=tk.X)
        ttk.Label(ctrl2, text="方向:").pack(side=tk.LEFT)
        self.cmp_dir_var = tk.StringVar(
            value=CMP_DIRECTIONS.get(COMPARE.get("direction", "dev_to_prod"),
                                     CMP_DIRECTIONS["dev_to_prod"]))
        self.cmp_dir_cb = ttk.Combobox(ctrl2, textvariable=self.cmp_dir_var,
                                       values=list(CMP_DIRECTIONS.values()),
                                       state="readonly", width=20)
        self.cmp_dir_cb.pack(side=tk.LEFT, padx=4)
        self.cmp_autofetch_var = tk.BooleanVar(value=COMPARE.get("auto_fetch", True))
        ttk.Checkbutton(ctrl2, text="自动拉取（比对前先 fetch）",
                        variable=self.cmp_autofetch_var).pack(side=tk.LEFT, padx=(12, 0))
        ttk.Button(ctrl2, text="💾 保存并比对", command=self._save_and_compare,
                   style="Accent.TButton").pack(side=tk.LEFT, padx=(16, 4))
        ttk.Button(ctrl2, text="🔍 立即比对", command=self.compare_now).pack(side=tk.LEFT)

        self.cmp_summary = tk.StringVar(value="未比对")
        ttk.Label(tab, textvariable=self.cmp_summary, relief=tk.SUNKEN, anchor=tk.W).pack(
            fill=tk.X, padx=10, pady=(0, 6))

        # 比对过程日志
        log_frame = ttk.LabelFrame(tab, text="比对过程日志", padding=(8, 5))
        log_frame.pack(fill=tk.X, padx=10, pady=(0, 6))
        self.cmp_log = tk.Text(log_frame, height=6, wrap=tk.WORD,
                               bg=THEME_PANEL, fg=THEME_TEXT, font=(FONT_MONO, 9),
                               relief=tk.FLAT, state=tk.DISABLED, cursor="arrow")
        self.cmp_log_sb = ttk.Scrollbar(log_frame, orient=tk.VERTICAL,
                                        command=self.cmp_log.yview)
        self.cmp_log.configure(yscrollcommand=self.cmp_log_sb.set)
        self.cmp_log_sb.pack(side=tk.RIGHT, fill=tk.Y)
        self.cmp_log.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        pw2 = ttk.PanedWindow(tab, orient=tk.VERTICAL)
        pw2.pack(fill=tk.BOTH, expand=True, padx=10, pady=(0, 8))

        # 待上线提交
        self.cmp_commit_frame = ttk.LabelFrame(pw2, text="待上线提交（dev 有 / prod 无）", padding=(8, 5))
        pw2.add(self.cmp_commit_frame, weight=1)
        cf1 = self.cmp_commit_frame
        self.cmp_commit_tree = ttk.Treeview(cf1, columns=("hash", "author", "date", "message"),
                                            show="headings", height=8)
        for c, t, w in [("hash", "Hash", 70), ("author", "作者", 100),
                        ("date", "日期", 130), ("message", "提交信息", 520)]:
            self.cmp_commit_tree.heading(c, text=t)
            self.cmp_commit_tree.column(c, width=w, anchor=tk.W if c in ("author", "message") else tk.CENTER)
        self.cmp_commit_tree.pack(fill=tk.BOTH, expand=True)
        self.cmp_commit_tree.tag_configure("row_alt", background=THEME_ROW_ALT)
        self.cmp_commit_tree.tag_configure("row_base", background=THEME_PANEL)
        self.cmp_commit_tree.bind("<Double-1>", self._on_cmp_commit_dclick)

        # 变动文件
        cf2 = ttk.LabelFrame(pw2, text="变动文件（双击查看具体 diff）", padding=(8, 5))
        pw2.add(cf2, weight=1)
        self.cmp_file_tree = ttk.Treeview(cf2, columns=("status", "risk"),
                                          show="tree headings", height=8)
        self.cmp_file_tree.heading("#0", text="文件（按目录分组）")
        self.cmp_file_tree.column("#0", width=560, anchor=tk.W)
        self.cmp_file_tree.heading("status", text="状态")
        self.cmp_file_tree.column("status", width=60, anchor=tk.CENTER)
        self.cmp_file_tree.heading("risk", text="风险")
        self.cmp_file_tree.column("risk", width=50, anchor=tk.CENTER)
        self.cmp_file_tree.pack(fill=tk.BOTH, expand=True)
        self.cmp_file_tree.bind("<Double-1>", self._on_cmp_file_dclick)
        self.cmp_file_tree.tag_configure("A", background=TAG_COLORS["A"][0],
                                         foreground=TAG_COLORS["A"][1])
        self.cmp_file_tree.tag_configure("D", background=TAG_COLORS["D"][0],
                                         foreground=TAG_COLORS["D"][1])
        self.cmp_file_tree.tag_configure("M", background=TAG_COLORS["M"][0],
                                         foreground=TAG_COLORS["M"][1])
        self.cmp_file_tree.tag_configure("risk_high", foreground="#D1242F")
        self.cmp_file_tree.tag_configure("risk_low", foreground="#6B7686")
        self.cmp_file_tree.tag_configure("dir_row", foreground=THEME_ACCENT,
                                         font=(FONT_UI, 9, "bold"))

        btn2 = ttk.Frame(tab, padding=(10, 0))
        btn2.pack(fill=tk.X)
        ttk.Button(btn2, text="📥 导出比对结果(CSV)",
                   command=self._export_compare_csv).pack(side=tk.LEFT)
        ttk.Button(btn2, text="📝 导出上线清单(MD)",
                   command=self._export_compare_md).pack(side=tk.LEFT, padx=6)
        ttk.Button(btn2, text="📜 发布历史",
                   command=self._open_release_history).pack(side=tk.LEFT, padx=6)

    # ---- 比对预设 ----
    def _preset_values(self):
        return ["当前配置"] + [p.get("name", "未命名") for p in CFG.get("presets", [])]

    def _refresh_preset_cb(self):
        self.cmp_preset_cb.configure(values=self._preset_values())

    def _save_as_preset(self):
        repo = self.cmp_repo_var.get()
        if not repo:
            messagebox.showwarning("提示", "请先选择仓库")
            return
        name = self._ask_name("预设名称", f"{repo} 上线比对")
        if not name:
            return
        presets = CFG.setdefault("presets", [])
        for p in presets:
            if p.get("name") == name:
                messagebox.showinfo("提示", f"已存在同名预设「{name}」，将覆盖")
                presets.remove(p)
                break
        presets.append({
            "name": name,
            "repo": repo,
            "dev_branch": self.cmp_dev_var.get().strip(),
            "prod_branch": self.cmp_prod_var.get().strip(),
            "direction": next((k for k, v in CMP_DIRECTIONS.items()
                               if v == self.cmp_dir_var.get()), "dev_to_prod"),
            "auto_fetch": self.cmp_autofetch_var.get(),
        })
        save_config(CFG)
        self._refresh_preset_cb()
        self.cmp_preset_var.set(name)
        Toast(self.root, "预设已保存", f"「{name}」已写入 {os.path.basename(CONFIG_PATH)}")

    def _on_preset_select(self, _):
        name = self.cmp_preset_var.get()
        if name == "当前配置":
            self._sync_compare_ui()
            return
        for p in CFG.get("presets", []):
            if p.get("name") == name:
                COMPARE.update({
                    "enabled": True, "repo": p.get("repo", ""),
                    "dev_branch": p.get("dev_branch", ""),
                    "prod_branch": p.get("prod_branch", ""),
                    "direction": p.get("direction", "dev_to_prod"),
                    "auto_fetch": p.get("auto_fetch", True),
                })
                self._sync_compare_ui()
                self._cmp_log(f"已载入预设「{name}」（点「保存并比对」可持久化到磁盘）")
                return

    def _ask_name(self, title, initial):
        dlg = tk.Toplevel(self.root)
        dlg.title(title)
        dlg.configure(bg=THEME_BG)
        dlg.transient(self.root)
        dlg.grab_set()
        dlg.geometry("320x120+%d+%d" % (
            self.root.winfo_rootx() + 200, self.root.winfo_rooty() + 200))
        var = tk.StringVar(value=initial)
        ttk.Entry(dlg, textvariable=var).pack(fill=tk.X, padx=14, pady=(16, 8))
        result = {"v": None}
        def ok():
            result["v"] = var.get().strip()
            dlg.destroy()
        row = ttk.Frame(dlg)
        row.pack(fill=tk.X, padx=14)
        ttk.Button(row, text="确定", style="Accent.TButton", command=ok).pack(side=tk.RIGHT)
        ttk.Button(row, text="取消", command=dlg.destroy).pack(side=tk.RIGHT, padx=6)
        dlg.bind("<Return>", lambda e: ok())
        dlg.wait_window()
        return result["v"]

    # ---- 标签页 3：提交图 ----
    def _build_graph_tab(self, notebook):
        tab = ttk.Frame(notebook)
        notebook.add(tab, text="提交图")

        ctrl = ttk.Frame(tab, padding=(10, 8))
        ctrl.pack(fill=tk.X)
        ttk.Label(ctrl, text="仓库:").pack(side=tk.LEFT)
        self.graph_repo_var = tk.StringVar()
        self.graph_repo_cb = ttk.Combobox(ctrl, textvariable=self.graph_repo_var,
                                          values=list(REPOS.keys()), state="readonly", width=16)
        self.graph_repo_cb.pack(side=tk.LEFT, padx=4)
        self.graph_repo_cb.bind("<<ComboboxSelected>>", lambda e: self._load_graph())
        ttk.Button(ctrl, text="🔄 重绘", command=self._load_graph).pack(side=tk.LEFT, padx=4)
        ttk.Button(ctrl, text="🖼 导出 PNG", command=self._export_graph_png).pack(
            side=tk.LEFT, padx=4)
        ttk.Button(ctrl, text="1:1", command=self._graph_reset_zoom).pack(
            side=tk.LEFT, padx=4)
        ttk.Label(ctrl, text="双击节点看详情 · Ctrl+滚轮缩放", font=(FONT_UI, 9),
                  foreground=THEME_MUTED).pack(side=tk.LEFT, padx=10)
        self.graph_info_var = tk.StringVar(value="")
        ttk.Label(ctrl, textvariable=self.graph_info_var, font=(FONT_UI, 9),
                  foreground=THEME_MUTED).pack(side=tk.RIGHT, padx=4)

        wrap = ttk.Frame(tab)
        wrap.pack(fill=tk.BOTH, expand=True, padx=10, pady=(0, 8))
        self.graph_canvas = tk.Canvas(wrap, bg=THEME_PANEL, bd=0, highlightthickness=0)
        self.graph_vsb = ttk.Scrollbar(wrap, orient=tk.VERTICAL, command=self.graph_canvas.yview)
        self.graph_hsb = ttk.Scrollbar(wrap, orient=tk.HORIZONTAL, command=self.graph_canvas.xview)
        self.graph_canvas.configure(yscrollcommand=self.graph_vsb.set,
                                    xscrollcommand=self.graph_hsb.set)
        self.graph_canvas.grid(row=0, column=0, sticky="nsew")
        self.graph_vsb.grid(row=0, column=1, sticky="ns")
        self.graph_hsb.grid(row=1, column=0, sticky="ew")
        wrap.grid_rowconfigure(0, weight=1)
        wrap.grid_columnconfigure(0, weight=1)
        self.graph_canvas.bind("<Button-1>", self._on_graph_click)
        self.graph_canvas.bind("<Double-1>", self._on_graph_dclick)
        self.graph_canvas.bind("<Motion>", self._on_graph_motion)
        self.graph_canvas.bind("<Leave>", self._on_graph_leave)
        self.graph_canvas.bind("<Control-MouseWheel>", self._on_graph_zoom)
        self.graph_canvas.bind("<Control-Button-4>", self._on_graph_zoom)  # Linux 滚轮上
        self.graph_canvas.bind("<Control-Button-5>", self._on_graph_zoom)  # Linux 滚轮下

    def _show_graph_for_active(self):
        name = self._active_repo or (list(REPOS.keys()) or [None])[0]
        if not name:
            return
        self.graph_repo_var.set(name)
        self.notebook.select(2)
        self._load_graph()

    def _load_graph(self):
        name = self.graph_repo_var.get()
        if not name:
            return
        self.graph_info_var.set(f"正在加载 {name} 的提交图…")
        self._graph_req += 1
        req = self._graph_req
        threading.Thread(target=self._fetch_graph, args=(name, req), daemon=True).start()

    # ---- 提交图导出 PNG ----------------
    def _export_graph_png(self):
        c = self.graph_canvas
        if not c.find_all():
            messagebox.showinfo("提示", "请先加载提交图（选择仓库后会自动绘制）")
            return
        repo = self.graph_repo_var.get() or "repo"
        if not PIL_AVAILABLE:
            # 无 Pillow：降级导出 PostScript（Tk 原生支持）
            save_path = filedialog.asksaveasfilename(
                defaultextension=".ps",
                filetypes=[("PostScript", "*.ps"), ("All", "*.*")],
                initialfile=f"graph_{_safe_file_part(repo)}.ps",
            )
            if not save_path:
                return
            try:
                c.postscript(colormode="color", file=save_path)
            except Exception as e:
                messagebox.showerror("导出失败", str(e))
                return
            messagebox.showinfo(
                "导出成功",
                f"已保存为 PostScript 格式（未安装 Pillow，无法导出 PNG）：\n{save_path}\n\n"
                "安装 Pillow 后即可导出 PNG：pip install pillow")
            return
        from PIL import ImageGrab
        # 把窗口置前再截图，避免抓到他窗口的内容（DPI 已由启动时 SetProcessDpiAwareness 统一）
        self.root.lift()
        self.root.focus_force()
        self.root.update_idletasks()
        x0, y0 = c.winfo_rootx(), c.winfo_rooty()
        w, h = c.winfo_width(), c.winfo_height()
        if w <= 1 or h <= 1:
            messagebox.showinfo("提示", "画布尚未渲染完成，请稍候再试")
            return
        save_path = filedialog.asksaveasfilename(
            defaultextension=".png",
            filetypes=[("PNG 图片", "*.png"), ("All", "*.*")],
            initialfile=f"graph_{_safe_file_part(repo)}_"
                        f"{datetime.now().strftime('%Y%m%d')}.png",
        )
        if not save_path:
            return
        try:
            img = ImageGrab.grab(bbox=(x0, y0, x0 + w, y0 + h))
            img.save(save_path, "PNG")
        except Exception as e:
            # 截图失败（RDP/遮挡等）→ 链式降级为 PostScript 全量导出
            ps_path = os.path.splitext(save_path)[0] + ".ps"
            try:
                c.postscript(colormode="color", file=ps_path)
            except Exception as e2:
                messagebox.showerror(
                    "导出失败",
                    f"PNG 截图失败：{e}\nPostScript 降级也失败：{e2}")
                return
            messagebox.showinfo(
                "导出成功（降级）",
                f"PNG 截图失败（{e}），已降级导出 PostScript：\n{ps_path}")
            return
        messagebox.showinfo(
            "导出成功",
            f"已保存到:\n{save_path}\n（当前为画布可见区域截图，可滚动后再导出其余部分）")

    def _fetch_graph(self, repo_name, req):
        try:
            commits = get_graph_log(REPOS[repo_name])
            refs = get_ref_map(REPOS[repo_name])
            head, _ = git(REPOS[repo_name], "rev-parse", "--abbrev-ref", "HEAD")
            self.root.after(0, self._draw_graph, (commits, refs, head or ""),
                            repo_name, req)
        except Exception as e:
            err = str(e)
            self.root.after(0, lambda: self.graph_info_var.set(f"加载失败: {err}"))

    def _draw_graph(self, data, repo_name, req=None):
        if req is not None:
            if req != self._graph_req:
                return  # 过期结果（期间切换了仓库），丢弃
            self._graph_data = data
            self._graph_repo = repo_name
        commits, refs, head = data
        if not isinstance(refs, dict):
            refs = {}  # 防御：异常 refs(list 等)不至于让主题切换重建 UI 时崩溃
        c = self.graph_canvas
        c.delete("all")
        self._graph_hover = None
        rows, pos = layout_graph(commits)
        if not rows:
            c.create_text(300, 30, text="（该仓库没有提交）", fill=THEME_MUTED, anchor="nw")
            c.configure(scrollregion=(0, 0, 600, 60))
            self.graph_info_var.set(f"{repo_name}：无提交")
            return
        s = getattr(self, "_graph_scale", 1.0)  # Ctrl+滚轮缩放
        LANE_W, ROW_H, NODE_R = 26 * s, 34 * s, 5 * s
        X0, Y0 = 14, 20
        total_lanes = max((r["lane"] for r in rows), default=0) + 1
        total_w = total_lanes * LANE_W + 420
        total_h = len(rows) * ROW_H + 40
        msg_font = max(6, int(9 * s))
        ref_font = max(6, int(7 * s))

        # 作者 → 节点颜色（同一作者同色，GitKraken 风格；边仍用 lane 色表示拓扑）
        author_colors = {}
        for c_ in commits:
            a = c_.get("author", "")
            if a not in author_colors:
                author_colors[a] = LANE_COLORS[len(author_colors) % len(LANE_COLORS)]

        # 边（先画，节点后画覆盖端点）
        for i, r in enumerate(rows):
            commit = r["commit"]
            lane = r["lane"]
            cx = X0 + lane * LANE_W
            cy = Y0 + i * ROW_H
            color = LANE_COLORS[lane % len(LANE_COLORS)]
            for p in commit["parents"]:
                if p not in pos:
                    continue
                pr, pl = pos[p]
                px = X0 + pl * LANE_W
                py = Y0 + pr * ROW_H
                c.create_line(cx, cy, cx, py, fill=color, width=2)
                c.create_line(cx, py, px, py, fill=color, width=2)

        for i, r in enumerate(rows):
            commit = r["commit"]
            lane = r["lane"]
            x = X0 + lane * LANE_W
            y = Y0 + i * ROW_H
            is_head = commit["hash"] == head
            parents = commit.get("parents") or []
            is_merge = len(parents) >= 2
            # HEAD 高亮：节点外圈光晕
            if is_head:
                c.create_oval(x - NODE_R - 3, y - NODE_R - 3, x + NODE_R + 3,
                              y + NODE_R + 3, outline=THEME_ACCENT, width=2)
            ncolor = author_colors.get(commit["author"],
                                       LANE_COLORS[lane % len(LANE_COLORS)])
            node_tags = (f"node:{commit['hash']}",)
            if is_merge:
                # 合并提交：菱形标记（GitKraken 风格），比普通节点略大
                r2 = NODE_R + 3
                c.create_polygon(x, y - r2, x + r2, y, x, y + r2, x - r2, y,
                                 fill=ncolor, outline=THEME_PANEL, width=2,
                                 tags=node_tags)
            else:
                c.create_oval(x - NODE_R, y - NODE_R, x + NODE_R, y + NODE_R,
                              fill=ncolor, outline=THEME_PANEL, width=2,
                              tags=node_tags)
            # 作者首字母头像（节点内白字，一眼区分作者）
            initial = (commit.get("author") or "?")[:1].upper()
            c.create_text(x, y, text=initial, fill="white",
                          font=(FONT_UI, max(5, int(6 * s)), "bold"),
                          tags=node_tags)
            # 引用标注（分支/远程/标签用不同颜色，内联画在提交信息前，可点击）
            ref_list = refs.get(commit["hash"], [])
            if is_head and not ref_list:
                ref_list = [{"name": "HEAD", "kind": "head"}]
            ref_fg = {"branch": THEME_ACCENT, "remote": THEME_MUTED,
                      "tag": TAG_COLORS["M"][1], "head": THEME_ACCENT,
                      "other": THEME_MUTED}
            rfx = total_lanes * LANE_W + 26
            shown = 0
            for ref in ref_list[:3]:
                label = f"[{ref['name']}]"
                c.create_text(rfx, y, text=label, anchor="w",
                              fill=ref_fg.get(ref.get("kind", "other"), THEME_MUTED),
                              font=(FONT_UI, ref_font, "bold"),
                              tags=(f"node:{commit['hash']}",))
                rfx += _font((FONT_UI, ref_font, "bold")).measure(label) + 8
                shown += 1
            if len(ref_list) > shown:
                c.create_text(rfx, y, text=f"+{len(ref_list) - shown}", anchor="w",
                              fill=THEME_MUTED, font=(FONT_UI, ref_font),
                              tags=(f"node:{commit['hash']}",))
                rfx += 26
            msg = commit["message"]
            if len(msg) > 52:
                msg = msg[:51] + "…"
            c.create_text(rfx, y, text=msg, anchor="w", fill=THEME_TEXT,
                          font=(FONT_UI, msg_font), tags=(f"node:{commit['hash']}",))
            # 相对时间（GitKraken 式：信息右侧灰字）
            ago = time_ago(commit.get("date", ""))
            if ago:
                c.create_text(rfx + _font((FONT_UI, msg_font)).measure(msg) + 10,
                              y, text=ago, anchor="w", fill=THEME_MUTED,
                              font=(FONT_UI, ref_font),
                              tags=(f"node:{commit['hash']}",))

        c.configure(scrollregion=(0, 0, total_w, total_h))
        # 行区域表（hover 高亮用）
        self._graph_rows = [(Y0 + i * ROW_H, Y0 + i * ROW_H + ROW_H,
                             r["commit"]["hash"]) for i, r in enumerate(rows)]
        self.graph_info_var.set(
            f"{repo_name}：{len(rows)} 个提交 · 双击节点查看详情 · Ctrl+滚轮缩放")

    def _on_graph_motion(self, event):
        """悬停高亮整行（浅色背景垫底，不遮挡节点与文字）"""
        c = self.graph_canvas
        if not getattr(self, "_graph_rows", None):
            return
        y = event.y
        hover = None
        for (y0, y1, h) in self._graph_rows:
            if y0 <= y <= y1:
                hover = h
                break
        if hover == getattr(self, "_graph_hover", None):
            return
        self._graph_hover = hover
        c.delete("hover_row")
        if hover is None:
            return
        for (y0, y1, h) in self._graph_rows:
            if h == hover:
                c.create_rectangle(0, y0, max(c.winfo_width(), 4000), y1,
                                   fill=THEME_ROW_ALT, outline="",
                                   tags=("hover_row",))
                c.tag_lower("hover_row")
                commit = self._find_graph_commit(self._graph_data[0], hover)
                if commit:
                    self.graph_info_var.set(
                        f"{commit['hash'][:7]} · {commit['author']} · "
                        f"{commit['date']} · {commit['message']}")
                break

    def _on_graph_leave(self, _=None):
        if getattr(self, "_graph_hover", None) is not None:
            self._graph_hover = None
            try:
                self.graph_canvas.delete("hover_row")
            except Exception:
                pass

    @staticmethod
    def _find_graph_commit(commits, h):
        """按 hash 在提交列表中定位提交（提交是含多字段的 dict，必须整体匹配而非解包）"""
        for commit in commits or []:
            if commit.get("hash") == h:
                return commit
        return None

    def _on_graph_click(self, event):
        c = self.graph_canvas
        item = c.find_withtag("current")
        if not item:
            return
        tags = c.gettags(item[0])
        for t in tags:
            if t.startswith("node:"):
                h = t[5:]
                commit = self._find_graph_commit(self._graph_data[0], h)
                if commit:
                    self.graph_info_var.set(
                        f"{commit['hash'][:7]} · {commit['author']} · {commit['date']} · {commit['message']}")
                    self._graph_sel = h
                    return

    def _on_graph_dclick(self, event):
        h = getattr(self, "_graph_sel", None)
        if h and self._graph_repo:
            repo = self._graph_repo
            self._load_diff_async(f"提交详情 - {h[:7]}",
                                  lambda: get_commit_show(REPOS[repo], h))

    def _on_graph_zoom(self, event):
        """Ctrl+滚轮缩放提交图（0.5x ~ 2.5x），重绘并按当前鼠标位置保持视角"""
        d = getattr(event, "delta", 0)
        num = getattr(event, "num", 0)
        if d == 0 and num:
            d = 120 if num == 4 else -120
        if d == 0:
            return "break"
        old = self._graph_scale
        self._graph_scale = min(2.5, max(0.5, old * (1.12 if d > 0 else 1 / 1.12)))
        if self._graph_data:
            self._draw_graph(self._graph_data, self._graph_repo or "")
        return "break"

    def _graph_reset_zoom(self):
        self._graph_scale = 1.0
        if self._graph_data:
            self._draw_graph(self._graph_data, self._graph_repo or "")

    # ---- 标签页 4：统计 ----
    def _build_stats_tab(self, notebook):
        tab = ttk.Frame(notebook)
        notebook.add(tab, text="统计")

        ctrl = ttk.Frame(tab, padding=(10, 8))
        ctrl.pack(fill=tk.X)
        ttk.Label(ctrl, text="仓库:").pack(side=tk.LEFT)
        self.stats_repo_var = tk.StringVar(value="全部仓库")
        self.stats_repo_cb = ttk.Combobox(ctrl, textvariable=self.stats_repo_var,
                                          values=["全部仓库"] + list(REPOS.keys()),
                                          state="readonly", width=20)
        self.stats_repo_cb.pack(side=tk.LEFT, padx=4)
        self.stats_repo_cb.bind("<<ComboboxSelected>>", lambda e: self._load_stats())
        ttk.Label(ctrl, text="近").pack(side=tk.LEFT, padx=(8, 0))
        self.stats_days_var = tk.StringVar(value="30")
        self._last_days = 30               # _parse_days 非法输入的回退值
        # 天数可编辑：预设 14/30/90 之外可直接输入任意天数，回车/刷新即加载
        self.stats_days_cb = ttk.Combobox(ctrl, textvariable=self.stats_days_var,
                                          values=["14", "30", "90"], width=6)
        self.stats_days_cb.pack(side=tk.LEFT, padx=2)
        self.stats_days_cb.bind("<Return>", lambda e: self._load_stats())
        ttk.Label(ctrl, text="天").pack(side=tk.LEFT)
        ttk.Label(ctrl, text="(可输入自定义)", foreground=THEME_MUTED,
                  font=(FONT_UI, 9)).pack(side=tk.LEFT, padx=(2, 0))
        ttk.Button(ctrl, text="🔄 刷新统计", command=self._load_stats).pack(side=tk.LEFT, padx=8)
        ttk.Button(ctrl, text="📥 导出统计(CSV)",
                   command=self._export_stats_csv).pack(side=tk.LEFT, padx=8)
        # 仓库趋势折线：默认显示（全部仓库各一条线）；单仓库视图自动关闭
        self.compare_on_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(ctrl, text="📈 仓库趋势", variable=self.compare_on_var,
                        command=self._on_compare_toggle).pack(side=tk.LEFT, padx=(8, 0))
        # 对比仓库多选过滤（菜单式多选下拉）：默认全部，取消勾选后图表与导出同步排除。
        # 配合图例开关形成两级过滤（过滤=粗粒度范围，图例=细粒度显示）。
        _rnames = list(REPOS.keys())
        ttk.Label(ctrl, text="筛选:").pack(side=tk.LEFT, padx=(10, 2))
        if getattr(self, "_repo_filter_names", None) is None:
            self._repo_filter_names = set(_rnames)
        self._filter_label_var = tk.StringVar(value="")
        self._filter_menu_btn = tk.Menubutton(ctrl, textvariable=self._filter_label_var,
                                              relief="raised", bd=1,
                                              font=(FONT_UI, 9))
        self._filter_menu = tk.Menu(self._filter_menu_btn, tearoff=0)
        self._filter_menu_btn.configure(menu=self._filter_menu)
        self._filter_menu_btn.pack(side=tk.LEFT, padx=2)
        self._repo_filter_vars = {}
        for _rn in _rnames:
            _rv = tk.BooleanVar(value=_rn in self._repo_filter_names)
            self._repo_filter_vars[_rn] = _rv
            self._filter_menu.add_checkbutton(label=_rn, variable=_rv,
                                              command=self._on_filter_toggle)
        self._filter_menu.add_separator()
        self._filter_menu.add_command(label="☑ 全选",
                                      command=lambda: self._set_filter_all(True))
        self._filter_menu.add_command(label="□ 清空",
                                      command=lambda: self._set_filter_all(False))
        self._update_filter_label()
        self.stats_info_var = tk.StringVar(value="")
        ttk.Label(ctrl, textvariable=self.stats_info_var, font=(FONT_UI, 9),
                  foreground=THEME_MUTED).pack(side=tk.RIGHT, padx=4)

        # 第二行：周报功能独立一行，避免工具栏控件挤压
        ctrl2 = ttk.Frame(tab, padding=(10, 0, 10, 6))
        ctrl2.pack(fill=tk.X)
        self.weekly_detail_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(ctrl2, text="🧾 包含提交明细", variable=self.weekly_detail_var).pack(
            side=tk.LEFT)
        self.weekly_csv_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(ctrl2, text="📋 另存每日明细CSV",
                        variable=self.weekly_csv_var).pack(side=tk.LEFT, padx=(8, 0))
        ttk.Button(ctrl2, text="📅 一键生成周报", style="Accent.TButton",
                   command=self._export_weekly_report).pack(side=tk.LEFT, padx=6)

        wrap = ttk.Frame(tab)
        wrap.pack(fill=tk.BOTH, expand=True, padx=10, pady=(0, 8))
        # 垂直滚动容器：画布按内容动态增高（真实字体行高），超窗时可滚动，杜绝挤压
        scroll_canvas = tk.Canvas(wrap, bg=THEME_BG, bd=0, highlightthickness=0)
        vsb = ttk.Scrollbar(wrap, orient=tk.VERTICAL, command=scroll_canvas.yview)
        scroll_canvas.configure(yscrollcommand=vsb.set)
        scroll_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        vsb.pack(side=tk.RIGHT, fill=tk.Y)
        inner = tk.Frame(scroll_canvas, bg=THEME_BG)
        scroll_canvas.create_window((0, 0), window=inner, anchor="nw")
        inner.bind("<Configure>",
                   lambda e: scroll_canvas.configure(scrollregion=scroll_canvas.bbox("all")))
        scroll_canvas.bind("<Configure>",
                           lambda e: scroll_canvas.itemconfig(1, width=e.width))
        self._stats_scroll = scroll_canvas

        # 各画布不 expand：高度由内容决定（_draw_stats 里按真实行高动态设置）
        self.daily_canvas = tk.Canvas(inner, bg=THEME_PANEL, bd=0, highlightthickness=0,
                                      height=250)
        self.daily_canvas.pack(fill=tk.X, pady=(0, 24))
        self.author_canvas = tk.Canvas(inner, bg=THEME_PANEL, bd=0, highlightthickness=0,
                                       height=250)
        self.author_canvas.pack(fill=tk.X)
        # 各仓库逐日提交趋势（默认显示，位于作者排行下方；复选框可关闭）
        self.compare_canvas = tk.Canvas(inner, bg=THEME_PANEL, bd=0,
                                        highlightthickness=0, height=190)
        self.compare_canvas.pack(fill=tk.X, pady=(16, 0))
        self.compare_canvas.bind("<Motion>", self._on_compare_motion)
        self.compare_canvas.bind("<Leave>", self._on_compare_leave)
        self._compare_xs = []

        # 滚轮滚动：统计 tab 滚动本区；提交图 tab 顺带补上垂直滚轮
        def _on_wheel(e):
            if not getattr(self, "notebook", None):
                return
            idx = self.notebook.index(self.notebook.select())
            if idx == 3:
                scroll_canvas.yview_scroll(int(-e.delta / 120), "units")
            elif idx == 2 and getattr(self, "graph_canvas", None):
                self.graph_canvas.yview_scroll(int(-e.delta / 120), "units")
        scroll_canvas.bind_all("<MouseWheel>", _on_wheel)
        # 柱形图交互：悬停提示 + 图例开关（点击仓库 chip 可切换显示/隐藏）
        self.daily_canvas.bind("<Motion>", self._on_stats_motion)
        self.daily_canvas.bind("<Leave>", self._on_stats_leave)
        self.daily_canvas.bind("<Button-1>", self._on_stats_click)
        # 窗口尺寸变化（含初始布局定型）后按新宽度自动重绘，避免图表卡在
        # 过早绘制时的窄画布上（曾导致柱顶数值/长作者名被裁切）；防抖避免拖拽时狂刷
        self.daily_canvas.bind("<Configure>", lambda e: self._on_stats_configure())
        self.author_canvas.bind("<Configure>", lambda e: self._on_stats_configure())
        self._stats_redraw_after = None
        self._daily_bars = []
        self._tooltip_items = []
        self._legend_chips = []
        self._author_items = []
        self._stack_names = None
        self._stack_visible = set()

    def _show_stats_for_active(self):
        name = self._active_repo
        self.stats_repo_var.set(name if name else "全部仓库")
        self.notebook.select(3)
        self._load_stats()

    def _load_stats(self):
        self.stats_info_var.set("统计中…")
        repo = self.stats_repo_var.get()
        # 单仓库视图下仓库趋势无意义：自动取消勾选
        if repo != "全部仓库" and self.compare_on_var.get():
            self.compare_on_var.set(False)
        days = self._parse_days()
        repos = {repo: REPOS[repo]} if repo != "全部仓库" else dict(REPOS)
        self._stats_req += 1
        req = self._stats_req
        threading.Thread(target=self._fetch_stats, args=(repos, days, repo, req),
                         daemon=True).start()

    def _parse_days(self):
        """解析天数输入：支持任意正整数（自定义查询）；非法或超范围自动回退/限幅，
        并把输入框修正为实际生效值，避免用户误以为查询了别的范围。"""
        try:
            v = int(str(self.stats_days_var.get()).strip())
        except Exception:
            v = getattr(self, "_last_days", 30) or 30
        v = max(1, min(v, 3650))
        self._last_days = v
        self.stats_days_var.set(str(v))
        return v

    def _fetch_stats(self, repos, days, repo, req):
        try:
            (by_date, by_author, by_repo_date, by_repo_author,
             by_type, by_repo_type) = get_stats_detailed(repos, days)
            self.root.after(0, self._draw_stats, by_date, by_author,
                            by_repo_date, by_repo_author, by_type,
                            by_repo_type, days, repo, req)
        except Exception as e:
            err = str(e)
            self.root.after(0, lambda: self.stats_info_var.set(f"统计失败: {err}"))

    def _draw_stats(self, by_date, by_author, by_repo_date, by_repo_author,
                    by_type, by_repo_type, days, repo, req=None):
        if req is not None:
            if req != self._stats_req:
                return  # 过期结果（期间切换了仓库/天数），丢弃
            self._stats = (by_date, by_author, by_repo_date, by_repo_author,
                           by_type, by_repo_type, days, repo)
        self.daily_canvas.delete("all")
        self.author_canvas.delete("all")
        self._daily_bars = []
        self._legend_chips = []
        self._author_items = []
        self._hide_tooltip()
        # 多选过滤（仅「全部仓库」视图生效）：图表按勾选仓库预过滤，与图例开关
        # 形成两级过滤——过滤管图表+导出，图例只管显示层
        if repo == "全部仓库":
            fset = getattr(self, "_repo_filter_names", None)
            if fset is not None:
                by_date, by_author, by_repo_date, by_type = apply_repo_filter(
                    by_date, by_author, by_repo_date, by_repo_author,
                    by_repo_type, fset)
        c = self.daily_canvas
        cw = max(c.winfo_width(), 400)
        ch = 240
        # 每日提交柱状图：多仓库时切换为多色堆叠（一眼看出各仓库贡献）
        today = datetime.now().date()
        date_list = [(today - timedelta(days=i)).isoformat()
                     for i in range(days - 1, -1, -1)]
        stacked = bool(by_repo_date) and len(by_repo_date) > 1
        names = sorted(by_repo_date.keys()) if stacked else []
        if stacked:
            if getattr(self, "_stack_names", None) != names:
                self._stack_names = list(names)
                self._stack_visible = set(names)
            visible = self._stack_visible
        else:
            visible = set()
        total_in_window = sum(by_date.get(d, 0) for d in date_list)
        # 堆叠模式下柱顶/比例按“可见仓库”汇总，与图例开关保持一致
        counts = [by_date.get(d, 0) for d in date_list]
        if stacked:
            counts = [sum(by_repo_date[n].get(d, 0) for n in names
                          if n in visible) for d in date_list]
        mx = max(counts) if counts else 0
        mx = max(mx, 1)
        m_l, m_r, m_t, m_b = 46, 10, 44, 30
        # 画布高度按内容（标题 + 网格 + 轴标签）设置，而非固定值
        self.daily_canvas.configure(height=ch + 8)
        bw = (cw - m_l - m_r) / days
        c.create_text(m_l, 12, text=f"近 {days} 天提交量"
                      f"（{'全部仓库' if repo == '全部仓库' else repo}）",
                      anchor="w", fill=THEME_TEXT, font=(FONT_UI, 10, "bold"))
        for gi in range(5):
            gy = m_t + (ch - m_t - m_b) * gi / 4
            val = mx * (1 - gi / 4)
            c.create_line(m_l, gy, cw - m_r, gy, fill=THEME_BORDER, dash=(2, 3))
            c.create_text(m_l - 6, gy, text=str(int(round(val))), anchor="e",
                          fill=THEME_MUTED, font=(FONT_UI, 8))
        # 堆叠图例（右上角右对齐，标准仪表盘布局；与标题按实际文字宽度隔离，
        # 窄窗口自动截断为 +N，绝不重叠；点击 chip 可开关仓库）
        legend_font = tkfont.Font(self.root, family=FONT_UI, size=8)
        if stacked:
            title_txt = f"近 {days} 天提交量" \
                        f"（{'全部仓库' if repo == '全部仓库' else repo}）"
            title_w = _font((FONT_UI, 10, "bold")).measure(title_txt)
            lx = cw - m_r - 8
            for idx in range(len(names) - 1, -1, -1):
                n = names[idx]
                col = LANE_COLORS[idx % len(LANE_COLORS)]
                on = n in visible
                w_n = legend_font.measure(n) + 18
                if lx - w_n < m_l + title_w + 24:  # 与标题宽度隔离，溢出截断
                    c.create_text(lx - 2, 13, text=f"+{idx + 1}…", anchor="e",
                                  fill=THEME_MUTED, font=(FONT_UI, 8))
                    break
                lx -= w_n
                chip = c.create_rectangle(lx, 6, lx + 10, 18,
                                          fill=col if on else THEME_PANEL,
                                          outline=col)
                lbl = c.create_text(lx + 14, 12, text=n, anchor="w",
                                    fill=THEME_TEXT if on else THEME_MUTED,
                                    font=(FONT_UI, 8))
                # 命中矩形收窄 2px 避免相邻 chip 的 4px 重叠区造成误触
                self._legend_chips.append((lx, 4, lx + w_n - 2, 20, n,
                                           chip, lbl))
        for i, d in enumerate(date_list):
            x = m_l + i * bw
            cnt = counts[i]
            detail = None
            seg_top = None
            if stacked and cnt:
                detail = [(n, by_repo_date[n].get(d, 0)) for n in names
                          if n in visible and by_repo_date[n].get(d, 0)]
                y_top = ch - m_b
                for n, sc in detail:
                    h = (ch - m_t - m_b) * sc / mx
                    y0 = y_top - h
                    c.create_rectangle(x + 1, y0, x + bw - 2, y_top,
                                       fill=LANE_COLORS[names.index(n)
                                                        % len(LANE_COLORS)],
                                       outline="")
                    y_top = y0
                seg_top = y_top
            elif cnt:
                h = (ch - m_t - m_b) * cnt / mx
                c.create_rectangle(x + 1, ch - m_b - h, x + bw - 2, ch - m_b,
                                   fill=THEME_ACCENT, outline="")
                seg_top = ch - m_b - h
            if cnt:
                # 柱顶显示数量：柱宽窄(天数多)时缩字号，避免相邻数字糊成一团
                c.create_text(x + bw / 2, seg_top - 2, text=str(cnt),
                              anchor="s", fill=THEME_TEXT,
                              font=(FONT_UI, 8 if bw >= 14 else 7))
                self._daily_bars.append((x + 1, x + bw - 2, d, cnt, detail))
            if i % max(days // 5, 1) == 0 or i == days - 1:
                c.create_text(x + bw / 2, ch - m_b + 12, text=d[5:], anchor="n",
                              fill=THEME_MUTED, font=(FONT_UI, 8))
        # 仓库趋势折线（可选）：勾选后在作者排行下方叠加各仓库逐日提交对比
        if self._compare_enabled():
            if not self.compare_canvas.winfo_manager():
                self.compare_canvas.pack(fill=tk.X, pady=(16, 0))
            self._draw_compare(by_repo_date, days)
        elif self.compare_canvas.winfo_manager():
            self.compare_canvas.pack_forget()
            self._compare_xs = []
        # 作者排行：名字按实际渲染宽度动态右移条形区，杜绝与条形重叠（DPI 下更可靠）；
        # 画布高度与行高按真实字体行高计算，杜绝行间挤压
        ac = self.author_canvas
        acw = max(ac.winfo_width(), 400)
        ac.create_text(46, 12, text="作者提交排行 Top 10", anchor="w",
                       fill=THEME_TEXT, font=(FONT_UI, 10, "bold"))
        top = sorted(by_author.items(), key=lambda x: -x[1])[:10]
        if not top:
            ac.create_text(46, 80, text="（近 {} 天没有提交）".format(days),
                           anchor="w", fill=THEME_MUTED, font=(FONT_UI, 9))
            return
        mx2 = max(v for _, v in top) or 1
        name_font = tkfont.Font(self.root, family=FONT_UI, size=9)
        ls = name_font.metrics("linespace")   # 真实行高（DPI 缩放后），行距不低于它
        # 排行图保持内容大小（行距 = 真实行高），与上方柱状图用固定间距隔开；
        # 不强行拉满可视区，避免作者少时行距过大显得臃肿
        ach = 44 + len(top) * ls + 12
        ac.configure(height=ach)
        row_h = max(ls, (ach - 44) / len(top))
        bar_x, disp = compute_author_layout([n for n, _ in top], acw,
                                            name_font.measure)
        self._author_bar_x = bar_x
        for i, ((name, cnt), disp_name) in enumerate(zip(top, disp)):
            y = 34 + i * row_h
            bar_w = max((acw - bar_x - 130) * cnt / mx2, 2)
            bar_id = ac.create_rectangle(bar_x, y + 4, bar_x + bar_w, y + row_h - 6,
                                         fill=LANE_COLORS[i % len(LANE_COLORS)],
                                         outline="")
            name_id = ac.create_text(6, y + row_h / 2, text=disp_name, anchor="w",
                                     fill=THEME_TEXT, font=(FONT_UI, 9))
            val_id = ac.create_text(bar_x + bar_w + 8, y + row_h / 2, text=str(cnt),
                                    anchor="w", fill=THEME_MUTED, font=(FONT_UI, 9))
            self._author_items.append((bar_id, name_id, val_id))
        # 信息栏用全部仓库的真实总数（开关仓库只影响柱形图展示，不影响统计口径）
        self.stats_info_var.set(
            f"{'全部仓库' if repo == '全部仓库' else repo} 近 {days} 天："
            f"共 {total_in_window} 次提交 · {len(by_author)} 位作者")

    # ---- 统计柱形图交互：悬停提示 + 图例开关 ----------------
    def _on_stats_configure(self):
        """画布尺寸变化后防抖重绘：等 150ms 布局稳定再用最新画布宽度重画。
        数据以 self._stats 为准（无数据时跳过）。"""
        if self._stats_redraw_after is not None:
            try:
                self.root.after_cancel(self._stats_redraw_after)
            except Exception:
                pass
        self._stats_redraw_after = self.root.after(150, self._do_stats_redraw)

    def _do_stats_redraw(self):
        self._stats_redraw_after = None
        # 窗口销毁/退出瞬间定时器可能仍触发：画布已不存在时直接跳过，避免 TclError
        try:
            if not self.daily_canvas.winfo_exists():
                return
        except Exception:
            return
        if self._stats is not None:
            self._draw_stats(*self._stats)

    def _on_stats_motion(self, event):
        try:
            x, y = event.x, event.y
        except Exception:
            return
        for (x0, x1, d, cnt, detail) in self._daily_bars:
            if x0 <= x <= x1:
                self._show_tooltip(self.daily_canvas, x, y,
                                   build_bar_tooltip(d, cnt, detail))
                return
        self._hide_tooltip()

    def _on_stats_leave(self, event):
        self._hide_tooltip()

    def _on_stats_click(self, event):
        if self._stats is None or not self._legend_chips:
            return
        x, y = event.x, event.y
        for (x0, y0, x1, y1, n, chip, lbl) in self._legend_chips:
            if x0 <= x <= x1 and y0 <= y <= y1:
                self._stack_visible.symmetric_difference_update([n])
                # 点击处理器跑在主线程，直接同步重绘（after(0) 会让 smoke/后台
                # 统计线程的绘制回调乱序插入，造成短暂错帧）
                self._draw_stats(*self._stats)
                return

    def _show_tooltip(self, canvas, x, y, body):
        self._hide_tooltip()
        c = canvas
        cw = max(c.winfo_width(), 400)
        ch = max(c.winfo_height(), 190)
        f = tkfont.Font(self.root, family=FONT_UI, size=9)
        lines = body.split("\n")
        ls = f.metrics("linespace")          # 真实行高（中文 UI 字体 ~28px）
        pad = 8                              # 四边内边距
        tw = min(max(f.measure(l) for l in lines) + pad * 2, cw - 8)
        th = ls * len(lines) + pad * 2       # 用真实行高包住所有行
        tx = max(4, min(x + 14, cw - tw - 6))
        ty = max(4, min(y + 10, ch - th - 6))
        box = c.create_rectangle(tx, ty, tx + tw, ty + th,
                                 fill=THEME_ACCENT_SOFT, outline=THEME_ACCENT)
        # 每行一个文本项（各自限宽 tw-2*pad）：行内只裁切不换行，
        # 高度 n*linespace 恒等于实际渲染高度，框一定包住所有内容
        items = [box]
        for i, ln in enumerate(lines):
            items.append(c.create_text(
                tx + pad, ty + pad + i * ls, text=ln, anchor="nw",
                width=tw - pad * 2, fill=THEME_TEXT, font=(FONT_UI, 9)))
        self._tooltip_items = items
        self._tooltip_owner = canvas

    def _hide_tooltip(self, canvas=None):
        c = canvas or getattr(self, "_tooltip_owner", None) or self.daily_canvas
        for i in getattr(self, "_tooltip_items", []) or []:
            try:
                c.delete(i)
            except Exception:
                pass
        self._tooltip_items = []
        self._tooltip_owner = None

    # ---- 仓库趋势折线：绘制 + 悬停 + 开关 ----------------
    def _compare_enabled(self):
        """仓库趋势折线仅在「全部仓库」统计视图下有意义"""
        return (self.compare_on_var.get()
                and self.stats_repo_var.get() == "全部仓库")

    def _on_compare_toggle(self):
        if self._stats is not None:
            self._draw_stats(*self._stats)

    def _draw_compare(self, by_repo_date, days):
        """各仓库逐日提交量趋势：每个仓库一条线（全部仓库默认显示）。"""
        c = self.compare_canvas
        c.delete("all")
        self._compare_xs = []
        by_repo_date = by_repo_date or {}
        names = sorted(by_repo_date.keys())
        cw = max(c.winfo_width(), 400)
        ch = max(c.winfo_height(), 190)
        m_l, m_r, m_t, m_b = 46, 10, 24, 30
        today = datetime.now().date()
        date_list = [(today - timedelta(days=i)).isoformat()
                     for i in range(days - 1, -1, -1)]
        c.create_text(m_l, 12, text=f"各仓库逐日提交趋势（近 {days} 天）",
                      anchor="w", fill=THEME_TEXT, font=(FONT_UI, 10, "bold"))
        if not names:
            c.create_text(46, 40, text="（无提交数据）", anchor="w",
                          fill=THEME_MUTED, font=(FONT_UI, 9))
            return
        mx = max((by_repo_date[n].get(d, 0) for n in names
                  for d in date_list), default=0) or 1
        bw = (cw - m_l - m_r) / days
        for gi in range(5):
            gy = m_t + (ch - m_t - m_b) * gi / 4
            val = mx * (1 - gi / 4)
            c.create_line(m_l, gy, cw - m_r, gy, fill=THEME_BORDER, dash=(2, 3))
            c.create_text(m_l - 6, gy, text=str(int(round(val))), anchor="e",
                          fill=THEME_MUTED, font=(FONT_UI, 8))
        # 图例（右上角，颜色与堆叠图同源）
        leg_font = tkfont.Font(self.root, family=FONT_UI, size=8)
        lx = cw - m_r - 8
        for idx in range(len(names) - 1, -1, -1):
            n = names[idx]
            w_n = leg_font.measure(n) + 26
            lx -= w_n
            if lx < m_l + 170:  # 不与标题区打架，超长名直接省略
                break
            c.create_line(lx, 12, lx + 14, 12,
                          fill=LANE_COLORS[idx % len(LANE_COLORS)], width=2)
            c.create_text(lx + 18, 12, text=n, anchor="w", fill=THEME_TEXT,
                          font=(FONT_UI, 8))

        def _y(v):
            return ch - m_b - (ch - m_t - m_b) * v / mx

        # 每个仓库一条折线（非零日画圆点）
        for idx, n in enumerate(names):
            col = LANE_COLORS[idx % len(LANE_COLORS)]
            seq = [by_repo_date[n].get(d, 0) for d in date_list]
            pts = [(m_l + (i + 0.5) * bw, _y(v)) for i, v in enumerate(seq)]
            c.create_line([p for pt in pts for p in pt], fill=col, width=2,
                          smooth=True)
            for i, v in enumerate(seq):
                if v:
                    x = m_l + (i + 0.5) * bw
                    r = 2.5
                    c.create_oval(x - r, _y(v) - r, x + r, _y(v) + r,
                                  fill=col, outline="")
        for i in range(days):
            if i % max(days // 5, 1) == 0 or i == days - 1:
                x = m_l + (i + 0.5) * bw
                c.create_text(x, ch - m_b + 12, text=date_list[i][5:],
                              anchor="n", fill=THEME_MUTED, font=(FONT_UI, 8))
            # 悬停命中槽位（与柱形图同宽，含 0 值日）
            self._compare_xs.append((m_l + i * bw, m_l + (i + 1) * bw,
                                     date_list[i],
                                     {n: by_repo_date[n].get(date_list[i], 0)
                                      for n in names}))

    def _on_compare_motion(self, event):
        for (x0, x1, d, vals) in self._compare_xs:
            if x0 <= event.x <= x1:
                lines = [f"{d}"] + [f"  {n}: {v}" for n, v in vals.items()]
                self._show_tooltip(self.compare_canvas, event.x, event.y,
                                   "\n".join(lines))
                return
        self._hide_tooltip()

    def _on_compare_leave(self, event):
        self._hide_tooltip()

    # ---- 对比仓库多选过滤（图表 + 导出两级过滤的第一级）----
    def _on_filter_toggle(self):
        self._repo_filter_names = {n for n, v in self._repo_filter_vars.items()
                                   if v.get()}
        self._update_filter_label()
        if self._stats is not None:
            self._draw_stats(*self._stats)

    def _set_filter_all(self, on):
        for v in self._repo_filter_vars.values():
            v.set(bool(on))
        self._on_filter_toggle()

    def _update_filter_label(self):
        total = len(self._repo_filter_vars)
        sel = sum(1 for n in self._repo_filter_vars
                  if n in getattr(self, "_repo_filter_names", set()))
        if total == 0:
            self._filter_label_var.set("筛选: —")
        elif sel == 0:
            self._filter_label_var.set("□ 筛选: 无")
        elif sel == total:
            self._filter_label_var.set(f"☑ 筛选: 全部({total})")
        else:
            self._filter_label_var.set(f"☑ 筛选: {sel}/{total}")

    # ---- 统计导出 CSV ----------------
    def _export_stats_csv(self):
        if not self._stats:
            messagebox.showinfo("提示", "请先刷新统计")
            return
        (by_date, by_author, by_repo_date, by_repo_author,
         by_type, by_repo_type, days, repo) = self._stats
        save_path = filedialog.asksaveasfilename(
            defaultextension=".csv",
            filetypes=[("CSV", "*.csv"), ("All", "*.*")],
            initialfile=f"stats_{_safe_file_part(repo)}_"
                        f"{days}d_{datetime.now().strftime('%Y%m%d')}.csv",
        )
        if not save_path:
            return
        # 导出与图表同口径：勾选过滤的仓库同步排除
        if repo == "全部仓库":
            fset = getattr(self, "_repo_filter_names", None)
            if fset is not None:
                by_date, by_author, by_repo_date, by_type = apply_repo_filter(
                    by_date, by_author, by_repo_date, by_repo_author,
                    by_repo_type, fset)
        with open(save_path, "w", encoding="utf-8-sig", newline="") as f:
            f.write(build_stats_csv(by_date, by_author, days, repo,
                                    by_repo_date, by_type))
        messagebox.showinfo("导出成功", f"已保存到:\n{save_path}")

    # ---- 一键生成周报（Markdown）----------------
    def _export_weekly_report(self):
        repo = self.stats_repo_var.get() or "全部仓库"
        try:
            days = int(self.stats_days_var.get())
        except Exception:
            days = 30
        # 周报与图表同口径：全部仓库视图按多选过滤仓库
        repos = ({repo: REPOS[repo]} if repo != "全部仓库"
                 else filter_repos_by_set(dict(REPOS),
                                          getattr(self, "_repo_filter_names",
                                                  None)))
        if not repos:
            messagebox.showwarning("提示", "没有可统计的仓库")
            return
        include = bool(self.weekly_detail_var.get())
        save_path = filedialog.asksaveasfilename(
            defaultextension=".md",
            filetypes=[("Markdown", "*.md"), ("All", "*.*")],
            initialfile=f"weekly_{_safe_file_part(repo)}_"
                        f"{days}d_{datetime.now().strftime('%Y%m%d')}.md",
        )
        if not save_path:
            return
        csv_path = None
        if self.weekly_csv_var.get():
            csv_path = filedialog.asksaveasfilename(
                defaultextension=".csv",
                filetypes=[("CSV", "*.csv"), ("All", "*.*")],
                initialfile=f"weekly_detail_{_safe_file_part(repo)}_"
                            f"{days}d_{datetime.now().strftime('%Y%m%d')}.csv",
            )
            # 取消 CSV 对话框 → 跳过 CSV，周报照常生成
        # 采集提交在后台线程，避免大仓库卡 UI
        threading.Thread(target=self._do_weekly,
                         args=(repos, days, repo, include, save_path, csv_path),
                         daemon=True).start()
        self._set_busy(True, "正在生成周报…")

    def _do_weekly(self, repos, days, repo, include, save_path, csv_path):
        try:
            commits = get_repo_commits(repos, days)
        except Exception as e:
            err = str(e)  # except 变量离开块后会被清除，先绑定普通局部变量
            self.root.after(0, lambda: (self._set_busy(False),
                                        messagebox.showerror("周报生成失败", err)))
            return
        md = build_weekly_report(commits, repo, days, include)
        # MD 与 CSV 分开写：各自报错，MD 成功但 CSV 失败时不会误报"周报保存失败"
        try:
            with open(save_path, "w", encoding="utf-8") as f:
                f.write(md)
        except Exception as e:
            err = str(e)
            self.root.after(0, lambda: (self._set_busy(False),
                                        messagebox.showerror("周报保存失败", err)))
            return
        extra = ""
        if csv_path:
            try:
                with open(csv_path, "w", encoding="utf-8-sig", newline="") as f:
                    f.write(build_weekly_detail_csv(commits, repo, days))
                extra = f"\n每日明细 CSV: {csv_path}"
            except Exception as e:
                err = str(e)
                self.root.after(0, lambda: (self._set_busy(False),
                                            messagebox.showerror(
                                                "每日明细 CSV 保存失败", err)))
                return
        self.root.after(0, lambda: (self._set_busy(False),
                                    messagebox.showinfo(
                                        "周报已生成",
                                        f"共 {len(commits)} 条提交 · 已保存到:\n{save_path}{extra}")))

    # -------------------- 快捷键 --------------------
    SHORTCUT_HELP = [
        ("F5", "立即刷新所有仓库状态"),
        ("Ctrl+F", "聚焦提交历史搜索框"),
        ("Ctrl+D", "查看选中提交的完整 diff"),
        ("Ctrl+E", "导出选中提交的文件列表"),
        ("Ctrl+1..4", "切换标签页（监控/比对/提交图/统计）"),
        ("Ctrl+Shift+S", "打开设置"),
        ("Ctrl+Shift+G", "查看当前仓库提交图"),
        ("Ctrl+Shift+T", "显示统计面板"),
        ("F1", "显示本帮助"),
    ]

    def _bind_shortcuts(self):
        try:
            self.root.bind_all("<F5>", lambda e: self.refresh())
            self.root.bind_all("<F1>", self._show_shortcuts)
            self.root.bind_all("<Control-f>", self._focus_search)
            self.root.bind_all("<Control-d>", lambda e: self._view_diff())
            self.root.bind_all("<Control-e>", lambda e: self._export_files())
            self.root.bind_all("<Control-Key-1>", lambda e: self.notebook.select(0))
            self.root.bind_all("<Control-Key-2>", lambda e: self.notebook.select(1))
            self.root.bind_all("<Control-Key-3>", lambda e: self.notebook.select(2))
            self.root.bind_all("<Control-Key-4>", lambda e: self.notebook.select(3))
            self.root.bind_all("<Control-Shift-s>", lambda e: self._open_settings())
            self.root.bind_all("<Control-Shift-g>", self._shortcut_graph)
            self.root.bind_all("<Control-Shift-t>", self._shortcut_stats)
        except Exception:
            pass

    def _shortcut_graph(self, _):
        if self._active_repo:
            self.graph_repo_var.set(self._active_repo)
        elif list(REPOS.keys()):
            self.graph_repo_var.set(list(REPOS.keys())[0])
        self.notebook.select(2)
        self._load_graph()

    def _shortcut_stats(self, _):
        if self._active_repo:
            self.stats_repo_var.set(self._active_repo)
        self.notebook.select(3)
        self._load_stats()

    def _show_shortcuts(self, _):
        text = "\n".join(f"{k:<14} {v}" for k, v in self.SHORTCUT_HELP)
        messagebox.showinfo("快捷键", text)

    def _focus_search(self, _):
        try:
            self.commit_search.focus_set()
        except Exception:
            pass

    # -------------------- 退出 --------------------
    def _on_close(self):
        self._exit_app()

    def _exit_app(self):
        self.polling = False
        global _TRAY_ACTIVE, _TRAY_HWND
        _TRAY_ACTIVE = False
        try:
            if _TRAY_HWND:
                import ctypes
                ctypes.windll.user32.PostMessageW(_TRAY_HWND, 0x0012, 0, 0)  # WM_QUIT 唤醒
        except Exception:
            pass
        self.root.after(0, self.root.destroy)

    # -------------------- 托盘交互 --------------------
    def _tray_restore(self):
        try:
            self.root.deiconify()
            self.root.lift()
            self.root.focus_force()
        except Exception:
            pass

    def _tray_popup_menu(self):
        try:
            m = Menu(self.root, tearoff=0)
            m.add_command(label="🖥 显示主窗口", command=self._tray_restore)
            m.add_command(label="⏹ 退出程序", command=self._tray_quit)
            m.tk_popup(self.root.winfo_pointerx(), self.root.winfo_pointery())
        except Exception:
            pass

    def _tray_quit(self):
        if messagebox.askyesno("退出", "确定退出 Git 仓库监控器吗？"):
            self._exit_app()

    def _on_maybe_minimize(self, _=None):
        """窗口被最小化且开启 minimize_to_tray → 隐藏到托盘（可从托盘恢复）"""
        try:
            if self.root.state() == "iconic" and getattr(self, "_tray_enabled", False):
                self.root.withdraw()
                Toast(self.root, "已最小化到托盘", "点击托盘图标可恢复窗口")
        except Exception:
            pass

    # -------------------- 刷新逻辑（后台线程，避免卡 UI）--------------------
    def refresh(self):
        if self._refreshing:
            # 上一轮还没跑完：手动刷新（按钮/F5）不丢弃，跑完补一次
            self._pending_refresh = True
            self._set_status("刷新进行中，已排队补刷…", "#E0A100")
            return
        self._refreshing = True
        self._set_busy(True, "正在刷新…")
        threading.Thread(target=self._fetch_and_render, daemon=True).start()

    def _fetch_and_render(self):
        now = datetime.now().strftime("%H:%M:%S")
        # 自动刷新也读取最新磁盘配置，避免外部改配置后一直用旧快照；
        # 但设置窗口打开时跳过：reload 会整体替换 REPOS 字典，把设置窗里未保存的编辑冲掉
        if not getattr(self, "_settings_open", False):
            reload_config()
        repos = dict(REPOS)  # 快照，避免与 UI 线程并发读取全局 REPOS
        toasts = []
        info_map = {}
        errors = []
        try:
            # 并行探测各仓库状态：互不依赖，串行会累加最慢仓库的耗时；
            # 线程池限并发（仓库很多时避免同时 fork 大量 git 进程）
            results = {n: None for n in repos}

            def _probe(name, path):
                try:
                    st = get_status(path)
                except Exception as e:
                    errors.append(f"{name}: {e}")
                    st = {"invalid": True, "branch": "N/A", "uncommitted": 0,
                          "ahead": 0, "behind": 0, "last_hash": "", "last_commit": "",
                          "last_date": ""}
                results[name] = st

            with ThreadPoolExecutor(max_workers=max(1, min(8, len(repos)))) as ex:
                list(ex.map(lambda np: _probe(*np), repos.items()))

            for name, st in results.items():  # results 按 repos 顺序预置，迭代即仓库顺序
                if not self.first_load:
                    prev_hash = self.known_hash.get(name)
                    prev_unc = self.known_uncommitted.get(name)
                    if prev_hash and prev_hash != st["last_hash"] and st["last_hash"]:
                        toasts.append((name, "检测到新提交！"))
                    elif prev_unc is not None and st["uncommitted"] > prev_unc:
                        toasts.append((name, f"未提交变更 +{st['uncommitted'] - prev_unc}"))

                self.known_hash[name] = st["last_hash"]
                self.known_uncommitted[name] = st["uncommitted"]
                color, label, tag = self._status_style(st)
                info_map[name] = {
                    "color": color, "label": label, "tag": tag,
                    "branch": st["branch"],
                    "uncommitted": st["uncommitted"], "ahead": st["ahead"],
                    "behind": st["behind"], "last_commit": st["last_commit"],
                    "last_date": st.get("last_date", ""),
                }

            # 自动比对：为避免离线/网络环境下 git fetch 挂起（导致"比对中"卡很久），
            # 自动刷新只做本地比对（auto_fetch=False），不触网；用户点"立即比对/保存并比对"
            # 时才按配置拉取最新（auto_fetch 来自配置）。
            cmp_data = None
            if COMPARE.get("enabled") and COMPARE.get("repo") in repos:
                try:
                    cmp_data = compute_compare(repos[COMPARE["repo"]],
                                               COMPARE["dev_branch"], COMPARE["prod_branch"],
                                               COMPARE.get("direction", "dev_to_prod"),
                                               False)
                except Exception as e:
                    errors.append(f"比对失败: {e}")
        except Exception as e:
            errors.append(f"刷新异常: {e}")
        finally:
            self._refreshing = False
            if self._pending_refresh:
                self._pending_refresh = False
                self.root.after(0, self.refresh)  # 补齐被守卫跳过的手动刷新

        gen = self._gen
        self.root.after(0, self._render, info_map, toasts, now, cmp_data,
                        "; ".join(errors), gen)

    def _status_style(self, st):
        if st.get("invalid"):
            return STATUS_STYLE["invalid"]
        if st["uncommitted"] > 0:
            return STATUS_STYLE["modified"]
        if st["behind"] > 0:
            return STATUS_STYLE["behind"]
        if st["ahead"] > 0:
            return STATUS_STYLE["ahead"]
        return STATUS_STYLE["clean"]

    def _render(self, info_map, toasts, now, cmp_data=None, error_msg="", gen=None):
        if gen is not None and gen != self._gen:
            return  # UI 已重建，本次结果作废
        self._last_info = info_map
        visible = self._visible_repos()
        if visible and set(visible) == set(self.repo_cards.keys()):
            self._update_cards(info_map)   # 可见集合没变 → 原地更新，避免周期性刷新重建卡片造成闪烁
        else:
            self._rebuild_cards(info_map)
        self._update_summary(info_map)
        self.first_load = False
        status = f"最后更新 {now}　|　共 {len(REPOS)} 个仓库"
        if error_msg:
            status += f"　|　⚠ {error_msg}"
        self.clock_var.set(now)
        self._set_status(status, "#D64545" if error_msg else "#2BA24C")
        self._set_busy(False)
        for title, msg in toasts:
            notify_sound()
            Toast(self.root, title, msg)
        if cmp_data is not None:
            self._render_compare(cmp_data, notify=True)

    def _background_poll(self):
        while self.polling:
            time.sleep(REFRESH_INTERVAL)
            if self.auto_var.get():
                self.refresh()

    # -------------------- 批量操作（多仓库 fetch / pull） --------------------
    def _open_batch_op(self):
        if not REPOS:
            return
        dlg = tk.Toplevel(self.root)
        dlg.title("批量操作")
        dlg.configure(bg=THEME_BG)
        dlg.geometry("440x400+%d+%d" % (self.root.winfo_rootx() + 200,
                                         self.root.winfo_rooty() + 120))
        ttk.Label(dlg, text="选择仓库（勾选后执行同一操作）:", font=(FONT_UI, 9, "bold"),
                  background=THEME_BG).pack(anchor=tk.W, padx=12, pady=(10, 2))
        vars_map = {}
        for n in REPOS:
            v = tk.BooleanVar(value=True)
            vars_map[n] = v
            ttk.Checkbutton(dlg, text=f"{n}  ·  {REPOS[n]}", variable=v).pack(
                anchor=tk.W, padx=16)
        ttk.Label(dlg, text="操作:", font=(FONT_UI, 9, "bold"),
                  background=THEME_BG).pack(anchor=tk.W, padx=12, pady=(8, 2))
        op_var = tk.StringVar(value="fetch")
        ttk.Radiobutton(dlg, text="Fetch（拉取远程引用，不改动工作区）",
                        variable=op_var, value="fetch").pack(anchor=tk.W, padx=16)
        ttk.Radiobutton(dlg, text="Pull（拉取并合并，可能需要网络）",
                        variable=op_var, value="pull").pack(anchor=tk.W, padx=16)
        result = {"go": False}

        def _go():
            result["go"] = True
            dlg.destroy()

        row = ttk.Frame(dlg)
        row.pack(fill=tk.X, padx=12, pady=12)
        ttk.Button(row, text="执行", style="Accent.TButton", command=_go).pack(side=tk.RIGHT)
        ttk.Button(row, text="取消", command=dlg.destroy).pack(side=tk.RIGHT, padx=6)
        dlg.wait_window()
        if not result["go"]:
            return
        sel = [n for n, v in vars_map.items() if v.get()]
        if not sel:
            messagebox.showwarning("提示", "请至少选择一个仓库")
            return
        op = op_var.get()
        fn = {"fetch": repo_fetch, "pull": repo_pull}[op]
        self._set_busy(True, f"正在对 {len(sel)} 个仓库执行 {op}…")
        threading.Thread(target=self._run_batch, args=(sel, op, fn),
                         daemon=True).start()

    def _run_batch(self, names, op, fn):
        results = []
        for n in names:
            try:
                out, rc = fn(REPOS[n])
                head = (out.splitlines() or [""])[0][:100]
                results.append((n, rc == 0, head))
            except Exception as e:
                results.append((n, False, str(e)))
        self.root.after(0, self._batch_done, op, results)

    def _batch_done(self, op, results):
        self._set_busy(False)
        ok = [r for r in results if r[1]]
        bad = [r for r in results if not r[1]]
        lines = [f"✅ 成功 {len(ok)} 个："]
        lines += [f"  {n}：{m}" for n, _o, m in ok]
        if bad:
            lines += [f"\n❌ 失败 {len(bad)} 个："]
            lines += [f"  {n}：{m}" for n, _o, m in bad]
        messagebox.showinfo(f"批量 {op} 完成", "\n".join(lines))
        self.refresh()

    # -------------------- 仓库卡片交互 --------------------
    def _activate_repo(self, name, right=False, event=None, single=False):
        self._active_repo = name
        if right:
            try:
                self.repo_menu.tk_popup(event.x_root, event.y_root)
            except Exception:
                pass
            return
        if single:
            # 单击 → 提交历史（在监控 tab 展示）
            self._load_commits(name)
            try:
                self.notebook.select(0)
            except Exception:
                pass
            return
        # 双击 → 工作台（跳转到该仓库的工作台）
        self._open_workspace(name)

    def _open_current_repo(self):
        if not self._active_repo:
            return
        open_in_explorer(REPOS[self._active_repo])

    def _load_commits(self, repo_name):
        self.current_repo = repo_name
        self.repo_label.config(text=f"当前: {repo_name}")
        self.status_var.set(f"正在加载 {repo_name} 的提交…")
        self._commits_req += 1
        req = self._commits_req
        threading.Thread(target=self._fetch_commits, args=(repo_name, req),
                         daemon=True).start()

    def _fetch_commits(self, repo_name, req):
        commits = get_commits(REPOS[repo_name])
        self.root.after(0, self._render_commits, commits, req)

    def _render_commits(self, commits, req=None):
        if req is not None and req != self._commits_req:
            return  # 期间又加载了别的仓库/重建过 UI，丢弃过期结果
        if req is None:
            self.all_commits = commits  # 搜索结果不覆盖内存基础列表
        self.commit_tree.delete(*self.commit_tree.get_children())
        for idx, c in enumerate(commits):
            tag = "row_alt" if idx % 2 else "row_base"
            m = COMMIT_PREFIX_RE.match(c["message"] or "")
            if m and m.group(1) in COMMIT_TYPE_TAGS:
                tag = COMMIT_TYPE_TAGS[m.group(1)]  # feat/fix/docs… 整行着色
            self.commit_tree.insert("", tk.END,
                values=(c["hash7"], c["author"], c["date"], c["message"]),
                tags=(c["hash"], tag))
        self.status_var.set(f"已加载 {len(commits)} 条提交")

    def _apply_filter(self):
        kw = self.search_var.get().strip()
        if getattr(self, "_search_after", None) is not None:
            try:
                self.root.after_cancel(self._search_after)
            except Exception:
                pass
            self._search_after = None
        if not kw:
            # 清空搜索 → 恢复内存预加载列表
            self._render_commits(self.all_commits)
            return
        # 防抖 300ms 后做全量 git log --grep 搜索（离线），避免每次击键都起 git 进程
        self._search_after = self.root.after(300, self._do_search, kw)

    def _do_search(self, kw):
        self._search_after = None
        repo = self.current_repo
        if not repo:
            self.status_var.set("请先双击上方仓库加载提交历史，再进行搜索")
            return
        self.status_var.set(f"正在全量搜索「{kw}」…")
        self._commits_req += 1
        req = self._commits_req
        threading.Thread(target=self._fetch_search, args=(repo, kw, req),
                         daemon=True).start()

    def _fetch_search(self, repo, kw, req):
        try:
            commits = search_commits(REPOS[repo], kw)
        except Exception as e:
            err = str(e)
            self.root.after(0, lambda: self.status_var.set(f"搜索失败: {err}"))
            return
        self.root.after(0, self._render_search, commits, kw, req)

    def _render_search(self, commits, kw, req):
        if req != self._commits_req:
            return
        self._render_commits(commits, req)
        self.status_var.set(f"「{kw}」匹配 {len(commits)} 条提交（全量历史）")

    # -------------------- 仓库操作 --------------------
    def _repo_action(self, action):
        name = self._active_repo
        if not name:
            return
        path = REPOS[name]
        if not os.path.isdir(path):
            messagebox.showwarning("提示", f"仓库路径无效：{path}")
            return
        if not messagebox.askyesno("确认操作",
                                   f"确定要对「{name}」执行 git {action} 吗？"):
            return
        self._set_busy(True, f"正在 {action} {name}…")
        threading.Thread(target=self._run_repo_action, args=(name, path, action),
                         daemon=True).start()

    def _run_repo_action(self, name, path, action):
        fn = {"fetch": repo_fetch, "pull": repo_pull, "push": repo_push}[action]
        out, rc = fn(path)
        head = out.splitlines()[0] if out.splitlines() else ""
        if rc == 0:
            msg = (f"{name} {action} 成功" + (f"：{head[:80]}" if head else ""))
            self.root.after(0, lambda: (self._set_busy(False),
                                        self._set_status(msg, "#2BA24C"),
                                        Toast(self.root, f"{action} 完成", msg)))
        else:
            detail = "\n".join(out.splitlines()[-8:])
            self.root.after(0, lambda: (self._set_busy(False),
                                        self._set_status(f"{name} {action} 失败", "#D64545"),
                                        messagebox.showerror(
                                            f"{action} 失败",
                                            f"仓库：{name}\n\n{detail or '（无输出）'}")))

    def _checkout_dialog(self):
        name = self._active_repo
        if not name:
            return
        path = REPOS[name]
        local, remote = get_branches(path)
        if not local and not remote:
            messagebox.showinfo("提示", "该仓库没有可切换的分支")
            return
        dlg = tk.Toplevel(self.root)
        dlg.title(f"切换分支 - {name}")
        dlg.configure(bg=THEME_BG)
        dlg.geometry("380x340+%d+%d" % (self.root.winfo_rootx() + 200,
                                        self.root.winfo_rooty() + 120))
        ttk.Label(dlg, text="本地分支:", font=(FONT_UI, 9, "bold"),
                  background=THEME_BG).pack(anchor=tk.W, padx=12, pady=(10, 2))
        lb = tk.Listbox(dlg, height=6, exportselection=False, bg=THEME_PANEL,
                        fg=THEME_TEXT, selectbackground=THEME_ACCENT_SOFT,
                        selectforeground=THEME_TEXT, highlightthickness=0)
        for b in local:
            lb.insert(tk.END, b)
        lb.pack(fill=tk.X, padx=12)
        ttk.Label(dlg, text="远程分支（选中即创建跟踪分支）:", font=(FONT_UI, 9, "bold"),
                  background=THEME_BG).pack(anchor=tk.W, padx=12, pady=(8, 2))
        rb = tk.Listbox(dlg, height=6, exportselection=False, bg=THEME_PANEL,
                        fg=THEME_TEXT, selectbackground=THEME_ACCENT_SOFT,
                        selectforeground=THEME_TEXT, highlightthickness=0)
        for b in remote:
            rb.insert(tk.END, b)
        rb.pack(fill=tk.X, padx=12)
        result = {"target": None}
        def ok():
            sel = lb.curselection() or rb.curselection()
            box = lb if lb.curselection() else rb
            if not sel:
                return
            result["target"] = box.get(sel[0])
            dlg.destroy()
        row = ttk.Frame(dlg)
        row.pack(fill=tk.X, padx=12, pady=10)
        ttk.Button(row, text="切换", style="Accent.TButton", command=ok).pack(side=tk.RIGHT)
        ttk.Button(row, text="取消", command=dlg.destroy).pack(side=tk.RIGHT, padx=6)
        dlg.wait_window()
        target = result["target"]
        if not target:
            return
        self._set_busy(True, f"正在切换到 {target}…")
        threading.Thread(target=self._run_checkout, args=(name, path, target),
                         daemon=True).start()

    def _run_checkout(self, name, path, target):
        out, rc = repo_checkout(path, target)
        if rc == 0:
            self.root.after(0, lambda: (self._set_busy(False),
                                        self._set_status(f"已切换到 {target}", "#2BA24C"),
                                        Toast(self.root, "切换成功",
                                              f"{name} 已切换到 {target}"),
                                        self.refresh()))
        else:
            detail = "\n".join(out.splitlines()[-8:])
            self.root.after(0, lambda: (self._set_busy(False),
                                        self._set_status("切换失败", "#D64545"),
                                        messagebox.showerror(
                                            "切换失败",
                                            f"仓库：{name}\n目标：{target}\n\n{detail or '（无输出）'}")))

    # -------------------- 右键菜单 --------------------
    def _on_commit_rightclick(self, event):
        row = self.commit_tree.identify_row(event.y)
        if row:
            self.commit_tree.selection_set(row)
            self.commit_menu.tk_popup(event.x_root, event.y_root)

    # -------------------- 提交右键高级操作 --------------------
    def _copy_hash(self, short=True):
        full_hash, vals = self._selected_commit()
        if not full_hash:
            return
        self.root.clipboard_clear()
        self.root.clipboard_append(full_hash[:7] if short else full_hash)
        self._set_status(f"已复制{'短' if short else '完整'} Hash", "#2BA24C")

    def _copy_commit_msg(self):
        full_hash, vals = self._selected_commit()
        if not full_hash:
            return
        self.root.clipboard_clear()
        self.root.clipboard_append(vals[3] if len(vals) > 3 else "")
        self._set_status("已复制提交信息", "#2BA24C")

    def _cherry_pick_selected(self):
        full_hash, vals = self._selected_commit()
        if not full_hash or not self.current_repo:
            return
        if not messagebox.askyesno(
                "Cherry-pick",
                f"将把提交 {vals[0]}「{(vals[3] or '')[:40]}」应用到当前分支：\n\n"
                f"{self.current_repo}\n\n冲突时需要手动解决，确定继续？"):
            return
        self._run_git_op("Cherry-pick",
                         lambda: repo_cherry_pick(REPOS[self.current_repo], full_hash))

    def _revert_selected(self):
        full_hash, vals = self._selected_commit()
        if not full_hash or not self.current_repo:
            return
        if not messagebox.askyesno(
                "Revert",
                f"将生成一个反向提交来回滚 {vals[0]}「{(vals[3] or '')[:40]}」：\n\n"
                f"{self.current_repo}\n\n确定继续？"):
            return
        self._run_git_op("Revert",
                         lambda: repo_revert(REPOS[self.current_repo], full_hash))

    def _branch_from_selected(self):
        full_hash, vals = self._selected_commit()
        if not full_hash or not self.current_repo:
            return
        name = self._ask_name("创建分支", f"branch-{vals[0]}")
        if not name:
            return
        self._run_git_op("创建分支",
                         lambda: repo_create_branch(REPOS[self.current_repo], name, full_hash))

    def _tag_selected(self):
        full_hash, vals = self._selected_commit()
        if not full_hash or not self.current_repo:
            return
        name = self._ask_name("打标签", "v1.0.0")
        if not name:
            return
        self._run_git_op("打标签",
                         lambda: repo_create_tag(REPOS[self.current_repo], name, full_hash))

    def _run_git_op(self, label, fn):
        """通用 git 操作执行器：后台线程 + 进度条 + 结果反馈 + 自动刷新"""
        self._set_busy(True, f"正在{label}…")

        def _work():
            try:
                out, rc = fn()
            except Exception as e:
                out, rc = str(e), 1
            self.root.after(0, self._git_op_done, label, out, rc)

        threading.Thread(target=_work, daemon=True).start()

    def _git_op_done(self, label, out, rc):
        self._set_busy(False)
        if rc == 0:
            head = (out.splitlines() or ["完成"])[0][:80]
            self._set_status(f"{label}成功", "#2BA24C")
            Toast(self.root, f"{label}成功", head)
            self.refresh()
        else:
            detail = "\n".join(out.splitlines()[-6:])
            self._set_status(f"{label}失败", "#D64545")
            messagebox.showerror(f"{label}失败", detail or "（无输出）")

    # -------------------- 分支比对 --------------------
    def _save_and_compare(self):
        repo = self.cmp_repo_var.get()
        if not repo:
            messagebox.showwarning("提示", "请先选择要比对的仓库")
            return
        self._sync_compare_from_ui()
        save_config(CFG)
        self.compare_now()

    # -------------------- 比对过程日志（线程安全的 UI 更新）--------------------
    def _cmp_log(self, msg):
        """后台线程调用：把一行日志投递到主线程显示。"""
        ts = time.strftime("%H:%M:%S")
        self.root.after(0, self._cmp_log_ui, f"[{ts}] {msg}")

    def _cmp_log_ui(self, line):
        self.cmp_log.configure(state=tk.NORMAL)
        self.cmp_log.insert(tk.END, line + "\n")
        self.cmp_log.see(tk.END)
        self.cmp_log.configure(state=tk.DISABLED)

    def cmp_log_clear(self):
        self.cmp_log.configure(state=tk.NORMAL)
        self.cmp_log.delete("1.0", tk.END)
        self.cmp_log.configure(state=tk.DISABLED)

    def _sync_compare_ui(self):
        """把当前内存中的比对配置同步到设置栏控件，避免界面与磁盘配置不一致。"""
        try:
            self.cmp_repo_var.set(COMPARE.get("repo", ""))
            self.cmp_dev_var.set(COMPARE.get("dev_branch", ""))
            self.cmp_prod_var.set(COMPARE.get("prod_branch", ""))
            self.cmp_dir_var.set(CMP_DIRECTIONS.get(COMPARE.get("direction", "dev_to_prod"),
                                                    CMP_DIRECTIONS["dev_to_prod"]))
            self.cmp_autofetch_var.set(COMPARE.get("auto_fetch", True))
        except Exception:
            pass

    def _sync_compare_from_ui(self):
        """把比对设置栏的当前值写入 COMPARE（预设 / 手动编辑立即生效，无需先保存）。"""
        COMPARE["repo"] = self.cmp_repo_var.get()
        COMPARE["dev_branch"] = self.cmp_dev_var.get().strip()
        COMPARE["prod_branch"] = self.cmp_prod_var.get().strip()
        COMPARE["direction"] = next((k for k, v in CMP_DIRECTIONS.items()
                                     if v == self.cmp_dir_var.get()), "dev_to_prod")
        COMPARE["auto_fetch"] = self.cmp_autofetch_var.get()
        COMPARE["enabled"] = bool(COMPARE["repo"])

    def _ui_matches_disk_compare(self):
        """界面比对设置与磁盘配置是否一致（一致才允许读盘刷新外部改动）。
        不一致说明用户刚选了预设或手动改了字段——此时若读盘会把预设覆盖掉。"""
        try:
            d = load_config().get("compare", {})
            return (self.cmp_repo_var.get() == d.get("repo", "")
                    and self.cmp_dev_var.get().strip() == (d.get("dev_branch", "") or "").strip()
                    and self.cmp_prod_var.get().strip() == (d.get("prod_branch", "") or "").strip()
                    and next((k for k, v in CMP_DIRECTIONS.items()
                              if v == self.cmp_dir_var.get()), "dev_to_prod")
                    == d.get("direction", "dev_to_prod")
                    and self.cmp_autofetch_var.get() == d.get("auto_fetch", True))
        except Exception:
            return False

    def compare_now(self):
        if self._cmp_running:
            self._cmp_log("已有比对正在进行，忽略本次点击（避免并发叠加）")
            return  # 已有比对在跑，避免并发叠加导致"比对中"卡死
        # 界面值与磁盘一致 → 读盘以支持外部修改配置；不一致（预设/手动改动）→ 直接采用界面值
        if self._ui_matches_disk_compare():
            reload_config()
            self._sync_compare_ui()
        self._sync_compare_from_ui()
        self.cmp_log_clear()
        if not (COMPARE.get("enabled") and COMPARE.get("repo") in REPOS):
            messagebox.showinfo("提示", "请先在比对设置里选择仓库与分支")
            return
        self._cmp_log(f"配置来源: {CONFIG_PATH}")
        self._cmp_log(f"比对设置: 仓库={COMPARE.get('repo')} 开发={COMPARE.get('dev_branch')} "
                      f"生产={COMPARE.get('prod_branch')} 方向={COMPARE.get('direction')} "
                      f"自动拉取={COMPARE.get('auto_fetch')}")
        if COMPARE.get("dev_branch", "").strip() == COMPARE.get("prod_branch", "").strip():
            messagebox.showerror(
                "配置错误",
                f"开发分支与生产分支被配置成了同一个（{COMPARE.get('dev_branch')}）。\n\n"
                "请打开 git_monitor.json，把 prod_branch 改成实际的生产分支"
                "（如 prod / main），与 dev_branch 区分开——\n"
                "否则比对永远是「待上线 0 · 变动 0」，因为相当于拿分支跟自己比。")
            return
        self._cmp_running = True
        self.first_compare = True  # 手动比对不弹通知
        self.cmp_summary.set("比对中…（拉取最新并比对）")
        self._set_busy(True, "正在比对…")
        self._cmp_log("开始比对，后台线程已启动…")
        threading.Thread(target=self._fetch_compare, daemon=True).start()

    def _fetch_compare(self):
        try:
            data = compute_compare(REPOS[COMPARE["repo"]], COMPARE["dev_branch"],
                                   COMPARE["prod_branch"], COMPARE.get("direction", "dev_to_prod"),
                                   COMPARE.get("auto_fetch", True), progress=self._cmp_log)
            gen = self._gen
            self.root.after(0, self._render_compare, data, False, gen)
        except Exception as e:
            err = str(e)
            self.root.after(0, lambda: self.cmp_summary.set(f"比对异常: {err}"))
            self._cmp_log(f"✗ 比对异常: {err}")
        finally:
            self._cmp_running = False
            self._set_busy(False)

    def _repopulate_compare_trees(self, data):
        """重建 UI 后恢复比对结果表格内容（不触发通知/弹窗）"""
        if not data or not data.get("ok"):
            return
        self.cmp_commit_tree.delete(*self.cmp_commit_tree.get_children())
        self.cmp_file_tree.delete(*self.cmp_file_tree.get_children())
        if data.get("direction") == "prod_to_dev":
            self.cmp_commit_frame.config(text="回滚风险提交（prod 有 / dev 无）")
        else:
            self.cmp_commit_frame.config(text="待上线提交（dev 有 / prod 无）")
        for idx, c in enumerate(data["commits"]):
            self.cmp_commit_tree.insert("", tk.END,
                values=(c["hash7"], c["author"], c["date"], c["message"]),
                tags=(c["hash"], "row_alt" if idx % 2 else "row_base"))
        self._fill_cmp_file_tree(data)

    def _render_compare(self, data, notify=False, gen=None):
        if gen is not None and gen != self._gen:
            return
        self._last_cmp = data
        self.cmp_commit_tree.delete(*self.cmp_commit_tree.get_children())
        self.cmp_file_tree.delete(*self.cmp_file_tree.get_children())

        if not data.get("ok"):
            self.cmp_summary.set(data.get("error", "比对失败").split("\n")[0])
            # 手动比对才弹详细诊断，自动刷新不刷屏
            if not notify:
                messagebox.showerror("比对失败", data.get("error", "比对失败"))
            return

        direction = data.get("direction", "dev_to_prod")
        self.cmp_base = data.get("base", "")
        self.cmp_head = data.get("head", "")

        # 提交列表标题随方向变化
        if direction == "prod_to_dev":
            self.cmp_commit_frame.config(text="回滚风险提交（prod 有 / dev 无）")
            title_prefix = "回滚风险提交"
        else:
            self.cmp_commit_frame.config(text="待上线提交（dev 有 / prod 无）")
            title_prefix = "待上线提交"

        for idx, c in enumerate(data["commits"]):
            self.cmp_commit_tree.insert("", tk.END,
                values=(c["hash7"], c["author"], c["date"], c["message"]),
                tags=(c["hash"], "row_alt" if idx % 2 else "row_base"))
        self._fill_cmp_file_tree(data)

        arrow = " → " if direction == "dev_to_prod" else " ← "
        repo = COMPARE.get("repo", "")
        self.cmp_summary.set(
            f"仓库 {repo} ｜ {_ref_label(data['base'])}{arrow}{_ref_label(data['head'])} ｜ "
            f"{title_prefix}: {len(data['commits'])} · 变动文件: {len(data['files'])}")
        # 比对成功 → 记入本地发布历史（自动刷新与上次结果相同则自动去重）
        try:
            push_release_snapshot(data, repo)
        except Exception:
            pass
        # 若任一侧解析为远程跟踪引用（可能过期），弹一次提醒避免误判
        if data["base"].startswith("refs/remotes/origin/") or \
           data["head"].startswith("refs/remotes/origin/"):
            if not notify:
                messagebox.showwarning(
                    "比对提示",
                    "当前有一侧使用的是 origin 远程跟踪引用（可能未 fetch 最新）。\n"
                    "若刚在本地提交却看不到变化，请确认：\n"
                    "1) 提交是否在「比对设置」所选的仓库目录内；\n"
                    "2) dev_branch / prod_branch 名称是否与本地分支一致；\n"
                    "3) 若为本地分支请先 git checkout 到该分支再提交。")

        if notify:
            cur = {c["hash"] for c in data["commits"]}
            if direction != self.last_cmp_dir:
                # 方向刚切换，静默重置，避免把整批当作"新提交"误报
                self.known_release = cur
                self.last_cmp_dir = direction
            else:
                if not self.first_compare:
                    new = cur - self.known_release
                    if new:
                        notify_sound()
                        Toast(self.root, "上线比对", f"有 {len(new)} 个新提交待发布")
                self.known_release = cur
            self.first_compare = False

    def _load_diff_async(self, title, loader):
        """后台线程加载 diff 文本后回到主线程弹窗，避免大仓库/大提交阻塞 UI。"""
        def _work():
            try:
                text = loader()
            except Exception as e:
                text = f"（加载失败: {e}）"
            self.root.after(0, self._show_diff_window, title, text)
        threading.Thread(target=_work, daemon=True).start()

    def _on_cmp_commit_dclick(self, _):
        sel = self.cmp_commit_tree.selection()
        if not sel:
            return
        full_hash = self.cmp_commit_tree.item(sel[0], "tags")[0]
        repo = COMPARE.get("repo", "")
        self._load_diff_async(f"提交详情 - {full_hash[:7]}",
                              lambda: get_commit_show(REPOS[repo], full_hash))

    def _fill_cmp_file_tree(self, data):
        """按顶层目录分组填充变动文件树；配置文件 / 锁文件自动标高风险。"""
        self.cmp_file_tree.delete(*self.cmp_file_tree.get_children())
        status_map = STATUS_CN
        for top, flist in group_files(data.get("files", [])):
            dir_id = self.cmp_file_tree.insert(
                "", tk.END, text=f"📁 {top}", values=("", f"{len(flist)} 个"),
                open=True, tags=("dir_row",))
            for f in flist:
                letter = f["status"][0] if f["status"] else "?"
                label = status_map.get(letter, letter)
                risk = file_risk(f["path"])
                self.cmp_file_tree.insert(
                    dir_id, tk.END, text=f["path"],
                    values=(label, risk),
                    tags=(letter, "risk_high" if risk == "高" else "risk_low"))

    def _on_cmp_file_dclick(self, _):
        sel = self.cmp_file_tree.selection()
        if not sel:
            return
        item = self.cmp_file_tree.item(sel[0])
        if "dir_row" in (item.get("tags") or ()):
            return  # 目录节点没有 diff
        path = item.get("text", "")
        if not path:
            return
        repo = COMPARE.get("repo", "")
        base, head = self.cmp_base, self.cmp_head
        self._load_diff_async(
            f"文件差异 - {path}",
            lambda: (get_file_diff(REPOS[repo], base, head, path)
                     or "（该文件在两个分支间无文本差异，可能是重命名/二进制文件）"))

    # -------------------- 发布历史（本地比对快照） --------------------
    def _open_release_history(self):
        hist = load_releases()
        if not hist:
            messagebox.showinfo("提示", "还没有发布历史\n\n完成一次上线比对后会自动记录（存于 "
                                "git_monitor_releases.json，纯本地）")
            return
        dlg = tk.Toplevel(self.root)
        dlg.title("发布历史")
        dlg.geometry("860x560")
        dlg.configure(bg=THEME_BG)
        dlg.grid_rowconfigure(1, weight=1)
        dlg.grid_columnconfigure(0, weight=1)

        bar = tk.Frame(dlg, bg=THEME_HEADER, height=42)
        bar.grid(row=0, column=0, sticky="nsew")
        tk.Label(bar, text="📜 发布历史（每次上线比对自动记录）", bg=THEME_HEADER,
                 fg="white", font=(FONT_UI, 12, "bold")).pack(side=tk.LEFT, padx=14, pady=9)
        tk.Label(bar, text="本地文件，不联网", bg=THEME_HEADER, fg=THEME_HEADER_SUB,
                 font=(FONT_UI, 9)).pack(side=tk.RIGHT, padx=14, pady=9)

        body = ttk.PanedWindow(dlg, orient=tk.HORIZONTAL)
        body.grid(row=1, column=0, sticky="nsew", padx=10, pady=8)

        left = ttk.Frame(body)
        body.add(left, weight=1)
        cols = ("time", "repo", "dir", "ncommits", "nfiles")
        tree = ttk.Treeview(left, columns=cols, show="headings", height=16)
        for c, t, w in [("time", "时间", 140), ("repo", "仓库", 120),
                        ("dir", "方向", 90), ("ncommits", "提交", 60),
                        ("nfiles", "文件", 60)]:
            tree.heading(c, text=t)
            tree.column(c, width=w, anchor=tk.CENTER if c in ("ncommits", "nfiles") else tk.W)
        ysb = ttk.Scrollbar(left, orient=tk.VERTICAL, command=tree.yview)
        tree.configure(yscrollcommand=ysb.set)
        tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        ysb.pack(side=tk.RIGHT, fill=tk.Y)

        right = ttk.Frame(body)
        body.add(right, weight=1)
        ttk.Label(right, text="快照详情（提交 + 文件）", font=(FONT_UI, 10, "bold"),
                  foreground=THEME_TEXT).pack(anchor=tk.W, padx=4, pady=(0, 4))
        detail = tk.Text(right, wrap=tk.NONE, font=(FONT_MONO, 9),
                         bg=THEME_PANEL, fg=THEME_TEXT, borderwidth=1,
                         relief="flat", highlightbackground=THEME_BORDER,
                         highlightthickness=1, padx=10, pady=8)
        detail.pack(fill=tk.BOTH, expand=True)
        detail.tag_configure("hdr", foreground=THEME_ACCENT, font=(FONT_UI, 9, "bold"))
        detail.tag_configure("muted", foreground=THEME_MUTED)

        all_entries = []
        for rname, lst in sorted(hist.items()):
            for e in lst:
                all_entries.append((rname, e))
        all_entries.sort(key=lambda x: x[1].get("time", ""), reverse=True)
        for rname, e in all_entries:
            d = e.get("direction", "") == "prod_to_dev"
            tree.insert("", tk.END,
                        values=(e.get("time", ""), rname,
                                "回滚" if d else "上线",
                                e.get("n_commits", 0), e.get("n_files", 0)))

        def _show_detail(_=None):
            sel = tree.selection()
            if not sel:
                return
            idx = tree.index(sel[0])
            rname, e = all_entries[idx]
            detail.configure(state=tk.NORMAL)
            detail.delete("1.0", tk.END)
            detail.insert(tk.END, f"{rname} · {e.get('time', '')}\n", "hdr")
            detail.insert(tk.END, f"方向：{e.get('dev', '')} → {e.get('prod', '')} · "
                                  f"提交 {e.get('n_commits', 0)} · 文件 {e.get('n_files', 0)}\n\n", "muted")
            detail.insert(tk.END, "== 提交 ==\n", "hdr")
            for h in e.get("commits", []):
                detail.insert(tk.END, f"  {h}\n")
            detail.insert(tk.END, "\n== 变动文件 ==\n", "hdr")
            for p in e.get("files", []):
                detail.insert(tk.END, f"  {p}\n")
            detail.configure(state=tk.DISABLED)

        tree.bind("<<TreeviewSelect>>", _show_detail)
        btn_row = ttk.Frame(dlg, padding=(0, 10))
        btn_row.grid(row=2, column=0, sticky="ew")

        def _export_md():
            save_path = filedialog.asksaveasfilename(
                defaultextension=".md",
                filetypes=[("Markdown", "*.md"), ("All", "*.*")],
                initialfile=f"releases_{datetime.now().strftime('%Y%m%d')}.md")
            if not save_path:
                return
            lines = ["# 📜 发布历史\n"]
            for rname, e in all_entries:
                lines.append(f"## {rname} · {e.get('time', '')}")
                lines.append(f"- 方向：{e.get('dev', '')} → {e.get('prod', '')} · "
                             f"提交 {e.get('n_commits', 0)} · 文件 {e.get('n_files', 0)}")
                for h in e.get("commits", []):
                    lines.append(f"  - `{h}`")
                for p in e.get("files", []):
                    lines.append(f"  - {p}")
                lines.append("")
            with open(save_path, "w", encoding="utf-8") as f:
                f.write("\n".join(lines))
            messagebox.showinfo("导出成功", f"已保存到:\n{save_path}")

        def _export_csv():
            save_path = filedialog.asksaveasfilename(
                defaultextension=".csv",
                filetypes=[("CSV", "*.csv"), ("All", "*.*")],
                initialfile=f"releases_{datetime.now().strftime('%Y%m%d')}.csv")
            if not save_path:
                return
            buf = io.StringIO()
            w = csv.writer(buf)
            safe = _csv_safe
            w.writerow(["time", "repo", "dev", "prod", "direction",
                        "n_commits", "n_files"])
            for rname, e in all_entries:
                w.writerow([safe(e.get("time", "")), safe(rname),
                            safe(e.get("dev", "")), safe(e.get("prod", "")),
                            safe(e.get("direction", "")),
                            e.get("n_commits", 0), e.get("n_files", 0)])
            w.writerow([])
            w.writerow(["=== 提交明细 ==="])
            w.writerow(["time", "repo", "hash"])
            for rname, e in all_entries:
                for h in e.get("commits", []):
                    w.writerow([safe(e.get("time", "")), safe(rname), safe(h)])
            with open(save_path, "w", encoding="utf-8-sig", newline="") as f:
                f.write(buf.getvalue())
            messagebox.showinfo("导出成功", f"已保存到:\n{save_path}")

        ttk.Button(btn_row, text="📝 导出全部(MD)", command=_export_md).pack(side=tk.LEFT, padx=4)
        ttk.Button(btn_row, text="📥 导出全部(CSV)", command=_export_csv).pack(side=tk.LEFT, padx=4)
        ttk.Button(btn_row, text="关闭", command=dlg.destroy).pack(side=tk.LEFT, padx=4)

    # -------------------- 导出比对结果 --------------------
    def _export_compare_csv(self):
        data = self._last_cmp
        if not data or not data.get("ok"):
            messagebox.showinfo("提示", "请先完成一次比对")
            return
        save_path = filedialog.asksaveasfilename(
            defaultextension=".csv",
            filetypes=[("CSV", "*.csv"), ("All", "*.*")],
            initialfile=f"compare_{_safe_file_part(COMPARE.get('repo', 'repo'))}_"
                        f"{_safe_file_part(data.get('dev', 'dev'))}"
                        f"_vs_{_safe_file_part(data.get('prod', 'prod'))}.csv",
        )
        if not save_path:
            return
        with open(save_path, "w", encoding="utf-8-sig", newline="") as f:
            w = csv.writer(f)
            safe = _csv_safe
            w.writerow([safe("比对方向"),
                        safe(CMP_DIRECTIONS.get(data.get("direction"), ""))])
            w.writerow([safe("基准"), safe(_ref_label(data.get("base", "")))])
            w.writerow([safe("目标"), safe(_ref_label(data.get("head", "")))])
            w.writerow([])
            w.writerow(["=== 提交 ==="])
            w.writerow(["hash", "author", "date", "message"])
            for c in data["commits"]:
                w.writerow([c["hash7"], safe(c["author"]), c["date"],
                            safe(c["message"])])
            w.writerow([])
            w.writerow([f"=== 变动文件（共 {len(data['files'])} 个）==="])
            w.writerow(["status", "path"])
            status_map = STATUS_CN
            for fi in data["files"]:
                letter = fi["status"][0] if fi["status"] else "?"
                w.writerow([safe(status_map.get(letter, letter)),
                            safe(fi["path"])])
        messagebox.showinfo("导出成功", f"已保存到:\n{save_path}")

    def _export_compare_md(self):
        """导出 Markdown 上线清单（待上线提交 + 变动文件 + 发布说明模板）。"""
        data = self._last_cmp
        if not data or not data.get("ok"):
            messagebox.showinfo("提示", "请先完成一次比对")
            return
        repo = COMPARE.get("repo", "repo")
        save_path = filedialog.asksaveasfilename(
            defaultextension=".md",
            filetypes=[("Markdown", "*.md"), ("All", "*.*")],
            initialfile=f"release_{_safe_file_part(repo)}_"
                        f"{_safe_file_part(data.get('dev', 'dev'))}"
                        f"_vs_{_safe_file_part(data.get('prod', 'prod'))}.md",
        )
        if not save_path:
            return
        md = build_release_md(data, repo)
        with open(save_path, "w", encoding="utf-8") as f:
            f.write(md)
        messagebox.showinfo("导出成功", f"已保存到:\n{save_path}")

    # -------------------- diff 弹窗（共用）--------------------
    def _selected_commit(self):
        sel = self.commit_tree.selection()
        if not sel:
            messagebox.showwarning("提示", "请先选择一个提交")
            return None, None
        item = self.commit_tree.item(sel[0])
        tags = self.commit_tree.item(sel[0], "tags")
        full_hash = tags[0] if tags else item["values"][0]
        return full_hash, item["values"]

    def _on_commit_dclick(self, _):
        self._view_diff()

    def _view_diff(self):
        full_hash, vals = self._selected_commit()
        if not full_hash:
            return
        repo = self.current_repo
        self._load_diff_async(f"提交详情 - {vals[0]}",
                              lambda: get_commit_show(REPOS[repo], full_hash))

    def _parse_diff(self, text):
        """把 unified/git diff 文本切分为：prelude（首个 diff 之前的提交元信息）+ 每个文件的段落。
        每个文件段落含 path / status / adds / dels / lines。"""
        files = []
        prelude = []
        cur = None
        for raw in text.split("\n"):
            if raw.startswith("diff --git "):
                m = re.search(r"diff --git a/(.*?) b/(.*)", raw)
                path = m.group(2) if m else raw
                if path.startswith("b/"):
                    path = path[2:]
                cur = {"path": path, "status": "M", "adds": 0, "dels": 0, "lines": []}
                files.append(cur)
                continue
            if cur is None:
                prelude.append(raw)
                continue
            if raw.startswith("new file"):
                cur["status"] = "A"
            elif raw.startswith("deleted file"):
                cur["status"] = "D"
            elif raw.startswith("rename from") or raw.startswith("rename to"):
                cur["status"] = "R"
            if raw.startswith("+") and not raw.startswith("+++"):
                cur["adds"] += 1
            elif raw.startswith("-") and not raw.startswith("---"):
                cur["dels"] += 1
            cur["lines"].append(raw)
        while prelude and prelude[-1] == "":
            prelude.pop()
        return prelude, files

    def _show_diff_window(self, title, diff_text):
        dlg = tk.Toplevel(self.root)
        dlg.title(title)
        dlg.geometry("1000x670")
        dlg.configure(bg=THEME_BG)
        # Toplevel 全程只用 grid，杜绝 pack/grid 混用导致 TclError
        dlg.grid_rowconfigure(1, weight=1)
        dlg.grid_columnconfigure(0, weight=1)

        # 标题条 + 统计摘要
        bar = tk.Frame(dlg, bg=THEME_HEADER, height=42)
        bar.grid(row=0, column=0, sticky="nsew")
        tk.Label(bar, text=title, bg=THEME_HEADER, fg="white",
                 font=(FONT_UI, 12, "bold")).pack(side=tk.LEFT, padx=14, pady=9)
        self._diff_summary = tk.StringVar(value="")
        tk.Label(bar, textvariable=self._diff_summary, bg=THEME_HEADER, fg=THEME_HEADER_SUB,
                 font=(FONT_UI, 9)).pack(side=tk.RIGHT, padx=14, pady=9)

        # 主体：左侧文件清单 + 右侧差异文本
        body = ttk.PanedWindow(dlg, orient=tk.HORIZONTAL)
        body.grid(row=1, column=0, sticky="nsew", padx=10, pady=8)

        left = ttk.Frame(body)
        body.add(left, weight=0)
        ttk.Label(left, text="变更文件", font=(FONT_UI, 10, "bold"),
                  foreground=THEME_TEXT).pack(anchor=tk.W, padx=4, pady=(0, 4))
        file_tree = ttk.Treeview(left, columns=("plus", "minus"),
                                 show="tree headings", height=28)
        file_tree.heading("#0", text="文件")
        file_tree.column("#0", width=230, anchor=tk.W)
        file_tree.heading("plus", text="+")
        file_tree.column("plus", width=32, anchor=tk.CENTER)
        file_tree.heading("minus", text="−")
        file_tree.column("minus", width=32, anchor=tk.CENTER)
        fscroll = ttk.Scrollbar(left, orient=tk.VERTICAL, command=file_tree.yview)
        file_tree.configure(yscrollcommand=fscroll.set)
        file_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0, 2))
        fscroll.pack(side=tk.RIGHT, fill=tk.Y)
        file_tree.tag_configure("A", foreground=TAG_COLORS["A"][1])
        file_tree.tag_configure("D", foreground=TAG_COLORS["D"][1])
        file_tree.tag_configure("M", foreground=TAG_COLORS["M"][1])
        file_tree.tag_configure("R", foreground=THEME_ACCENT)

        right = ttk.Frame(body)
        body.add(right, weight=1)
        txt = tk.Text(right, wrap=tk.NONE, font=(FONT_MONO, 10),
                      bg=THEME_PANEL, fg=THEME_TEXT, insertbackground=THEME_TEXT,
                      borderwidth=0, relief="flat", padx=14, pady=10,
                      selectbackground=THEME_ACCENT_SOFT, selectforeground=THEME_TEXT)
        ysb = ttk.Scrollbar(right, orient=tk.VERTICAL, command=txt.yview)
        xsb = ttk.Scrollbar(right, orient=tk.HORIZONTAL, command=txt.xview)
        txt.configure(yscrollcommand=ysb.set, xscrollcommand=xsb.set)
        txt.grid(row=0, column=0, sticky="nsew", padx=(0, 4), pady=(0, 4))
        ysb.grid(row=0, column=1, sticky="ns", pady=(0, 4))
        xsb.grid(row=1, column=0, sticky="ew", padx=(0, 4), pady=(0, 4))
        right.grid_rowconfigure(0, weight=1)
        right.grid_columnconfigure(0, weight=1)

        txt.tag_configure("add", foreground=TAG_COLORS["A"][1], background=DIFF_ADD_BG)
        txt.tag_configure("del", foreground=TAG_COLORS["D"][1], background=DIFF_DEL_BG)
        txt.tag_configure("meta", foreground=THEME_MUTED)
        txt.tag_configure("hunk", foreground=THEME_ACCENT, background=DIFF_HUNK_BG)
        txt.tag_configure("filehdr", foreground=THEME_ACCENT, background=THEME_ACCENT_SOFT,
                          font=(FONT_UI, 10, "bold"))
        txt.tag_configure("prelude", foreground=THEME_MUTED, background=DIFF_PRELUDE_BG)

        prelude, files = self._parse_diff(diff_text)
        marks = []
        total_a = total_d = 0
        status_labels = {"A": "新增", "M": "修改", "D": "删除", "R": "重命名", "?": "?"}

        if prelude:
            head = "\n".join(prelude).strip("\n")
            if head:
                txt.insert("end", head + "\n", "prelude")
                txt.insert("end", "\n")

        for fi in files:
            total_a += fi["adds"]
            total_d += fi["dels"]
            header = (f"📄 {fi['path']}   "
                      f"[{status_labels.get(fi['status'], fi['status'])}]   "
                      f"+{fi['adds']} −{fi['dels']}\n")
            txt.insert("end", header, "filehdr")
            idx = txt.index("end-1c")  # 头行插入后再取锚点：文件头能被 see() 滚到可见
            for line in fi["lines"]:
                if line.startswith("+") and not line.startswith("+++"):
                    txt.insert("end", line + "\n", "add")
                elif line.startswith("-") and not line.startswith("---"):
                    txt.insert("end", line + "\n", "del")
                elif line.startswith("@@"):
                    txt.insert("end", line + "\n", "hunk")
                elif line.startswith(("diff --git", "index ", "--- ", "+++ ",
                                      "new file", "deleted file", "rename",
                                      "similarity", "old mode", "new mode",
                                      "Binary", "\\ ")):
                    txt.insert("end", line + "\n", "meta")
                else:
                    txt.insert("end", line + "\n")
            txt.insert("end", "\n")
            marks.append((fi["path"], idx))
            file_tree.insert("", tk.END, text=fi["path"],
                             values=(fi["adds"], fi["dels"]), tags=(fi["status"],))

        if files:
            self._diff_summary.set(f"共 {len(files)} 个文件 · +{total_a} −{total_d}")
        else:
            self._diff_summary.set("无文本差异（可能仅重命名 / 二进制文件）")

        txt.config(state=tk.DISABLED)

        def _goto(event):
            sel = file_tree.selection()
            if not sel:
                return
            path = file_tree.item(sel[0], "text")
            for p, i in marks:
                if p == path:
                    txt.see(i)
                    break

        if file_tree.get_children():
            file_tree.selection_set(file_tree.get_children()[0])
            file_tree.bind("<<TreeviewSelect>>", _goto)

        # 按钮行
        btn_row = ttk.Frame(dlg, padding=(0, 10))
        btn_row.grid(row=2, column=0, sticky="ew")
        ttk.Button(btn_row, text="📄 复制全部", style="Accent.TButton",
                   command=lambda: (dlg.clipboard_clear(),
                                    dlg.clipboard_append(diff_text),
                                    messagebox.showinfo("已复制", "diff 已复制到剪贴板"))).pack(side=tk.LEFT, padx=4)
        ttk.Button(btn_row, text="关闭", command=dlg.destroy).pack(side=tk.LEFT, padx=4)

    # -------------------- 导出文件列表 --------------------
    def _export_files(self):
        full_hash, vals = self._selected_commit()
        if not full_hash:
            return
        repo = self.current_repo
        # 文件列表也是 git 调用，放到后台线程避免大提交时 UI 卡顿
        threading.Thread(target=self._do_export_files, args=(repo, vals, full_hash),
                         daemon=True).start()

    def _do_export_files(self, repo, vals, full_hash):
        try:
            files = get_changed_files(REPOS[repo], full_hash)
        except Exception as e:
            self.root.after(0, lambda: messagebox.showerror("导出失败", str(e)))
            return
        self.root.after(0, self._finish_export_files, repo, vals, full_hash, files)

    def _finish_export_files(self, repo, vals, full_hash, files):
        if not files:
            messagebox.showinfo("提示", "该提交没有文件变更")
            return
        save_path = filedialog.asksaveasfilename(
            defaultextension=".txt",
            filetypes=[("Text", "*.txt"), ("Markdown", "*.md"), ("All", "*.*")],
            initialfile=f"{repo}_{vals[0]}_files.txt",
        )
        if not save_path:
            return
        status_map = STATUS_CN
        with open(save_path, "w", encoding="utf-8") as f:
            f.write(f"仓库:   {repo}\n")
            f.write(f"提交:   {vals[0]}\n")
            f.write(f"作者:   {vals[1]}\n")
            f.write(f"日期:   {vals[2]}\n")
            f.write(f"信息:   {vals[3]}\n")
            f.write(f"{'=' * 60}\n")
            f.write(f"共 {len(files)} 个文件变更:\n\n")
            for fi in files:
                label = status_map.get(fi["status"], fi["status"])
                f.write(f"  [{label}] {fi['path']}\n")
        messagebox.showinfo("导出成功", f"已保存到:\n{save_path}")

    # -------------------- 设置界面 --------------------
    def _open_settings(self):
        dlg = tk.Toplevel(self.root)
        dlg.title("设置 - Git 仓库监控器")
        dlg.geometry("780x600")  # 初始尺寸，内容构建完按实际所需自动适配（见 _open_settings 尾部）
        dlg.minsize(720, 480)
        dlg.configure(bg=THEME_BG)
        dlg.transient(self.root)
        # 设置窗打开期间禁止自动刷新 reload_config（reload 会整体替换 REPOS 字典，
        # 把窗口里未保存的仓库编辑冲掉）；窗口销毁时复位
        self._settings_open = True

        def _on_settings_destroy(e):
            if e.widget is dlg:
                self._settings_open = False
        dlg.bind("<Destroy>", _on_settings_destroy)

        nb = ttk.Notebook(dlg)
        nb.pack(fill=tk.BOTH, expand=True, padx=12, pady=10)

        # --- 常规 ---
        t1 = ttk.Frame(nb)
        nb.add(t1, text="常规")
        f1 = ttk.LabelFrame(t1, text="通用", padding=(12, 8))
        f1.pack(fill=tk.X, padx=8, pady=8)
        row = ttk.Frame(f1)
        row.pack(fill=tk.X, pady=3)
        ttk.Label(row, text="刷新间隔（秒）:").pack(side=tk.LEFT)
        iv = tk.IntVar(value=CFG.get("refresh_interval", 30))
        ttk.Spinbox(row, from_=5, to=600, increment=5, textvariable=iv,
                    width=8).pack(side=tk.LEFT, padx=6)
        auto_v = tk.BooleanVar(value=CFG.get("auto_refresh", True))
        ttk.Checkbutton(row, text="启动时开启自动刷新", variable=auto_v).pack(side=tk.LEFT, padx=12)
        row2 = ttk.Frame(f1)
        row2.pack(fill=tk.X, pady=3)
        ttk.Label(row2, text="主题:").pack(side=tk.LEFT)
        theme_v = tk.StringVar(value=THEME_LABELS.get(CFG.get("theme", "light"), "浅色"))
        theme_cb = ttk.Combobox(row2, textvariable=theme_v,
                                values=list(THEME_LABELS.values()),
                                state="readonly", width=10)
        theme_cb.pack(side=tk.LEFT, padx=6)
        # 选中即切换并持久化；已打开的弹窗（含本设置窗）下次打开才跟随新主题
        theme_cb.bind("<<ComboboxSelected>>",
                      lambda e: self._switch_theme(THEME_KEYS.get(theme_v.get(), "light")))
        ttk.Label(row2, text="（选中立即生效）", font=(FONT_UI, 9),
                  foreground=THEME_MUTED).pack(side=tk.LEFT)
        row3 = ttk.Frame(f1)
        row3.pack(fill=tk.X, pady=3)
        sound_v = tk.BooleanVar(value=CFG.get("sound", True))
        ttk.Checkbutton(row3, text="通知时播放声音（Windows）", variable=sound_v).pack(side=tk.LEFT)
        if not PIL_AVAILABLE:
            ttk.Label(f1, text="⚠ 未安装 Pillow：提交图只能导出 PostScript，导出 PNG 需 pip install pillow",
                      font=(FONT_UI, 9), foreground="#D64545").pack(anchor=tk.W, pady=4)

        # --- 仓库 ---
        t2 = ttk.Frame(nb)
        nb.add(t2, text="仓库")
        f2 = ttk.LabelFrame(t2, text="仓库列表", padding=(8, 6))
        f2.pack(fill=tk.BOTH, expand=True, padx=8, pady=8)
        cols = ("name", "path", "group")
        tree = ttk.Treeview(f2, columns=cols, show="headings", height=8)
        for c, t, w in [("name", "名称", 150), ("path", "路径", 340), ("group", "分组", 100)]:
            tree.heading(c, text=t)
            tree.column(c, width=w)
        tree.pack(fill=tk.BOTH, expand=True, padx=(0, 4), pady=(0, 4))
        groups_map = {}
        for g, names in CFG.get("groups", {}).items():
            for n in names:
                groups_map[n] = g
        for n, p in REPOS.items():
            tree.insert("", tk.END, values=(n, p, groups_map.get(n, "默认")))
        ef = ttk.LabelFrame(t2, text="新增 / 修改仓库", padding=(12, 8))
        ef.pack(fill=tk.X, padx=8, pady=(0, 8))
        r1 = ttk.Frame(ef)
        r1.pack(fill=tk.X, pady=2)
        ttk.Label(r1, text="名称:").pack(side=tk.LEFT)
        e_name = ttk.Entry(r1, width=22)
        e_name.pack(side=tk.LEFT, padx=4)
        ttk.Label(r1, text="路径:").pack(side=tk.LEFT, padx=(8, 0))
        e_path = ttk.Entry(r1, width=40)
        e_path.pack(side=tk.LEFT, padx=4)
        ttk.Label(r1, text="分组:").pack(side=tk.LEFT, padx=(8, 0))
        e_group = ttk.Combobox(r1, values=list(CFG.get("groups", {})) + ["默认"],
                               width=10)
        e_group.set("默认")
        e_group.pack(side=tk.LEFT, padx=4)
        r2 = ttk.Frame(ef)
        r2.pack(fill=tk.X, pady=(6, 0))
        ttk.Button(r2, text="➕ 新增仓库",
                   command=lambda: _add_repo()).pack(side=tk.LEFT)
        ttk.Button(r2, text="✏️ 填入选中（修改）",
                   command=lambda: _fill_selected()).pack(side=tk.LEFT, padx=6)
        ttk.Button(r2, text="🗑 删除选中",
                   command=lambda: _del_repo()).pack(side=tk.LEFT, padx=6)

        def _selected_repo():
            sel = tree.selection()
            return tree.item(sel[0])["values"] if sel else None

        def _fill_selected():
            v = _selected_repo()
            if v:
                e_name.delete(0, tk.END)
                e_name.insert(0, v[0])
                e_path.delete(0, tk.END)
                e_path.insert(0, v[1])
                e_group.set(v[2])

        def _add_repo():
            name = e_name.get().strip()
            path = e_path.get().strip()
            if not name or not path:
                messagebox.showwarning("提示", "名称与路径不能为空")
                return
            path = os.path.normpath(path)
            if not os.path.isdir(path):
                # 离线机器可能有未挂载盘/网络盘：确认后仍可添加
                if not messagebox.askyesno(
                        "路径不存在",
                        f"目录不存在：\n{path}\n\n仍要添加吗？（可能是未挂载的移动盘/网络盘）"):
                    return
            old = _selected_repo()
            if old and old[0] == name:
                REPOS[name] = path
                tree.item(tree.selection()[0], values=(name, path, e_group.get()))
            else:
                REPOS[name] = path
                tree.insert("", tk.END, values=(name, path, e_group.get()))
            g = e_group.get().strip() or "默认"
            CFG.setdefault("groups", {})
            for gname, names in CFG["groups"].items():
                if name in names and gname != g:
                    names.remove(name)
            CFG["groups"].setdefault(g, [])
            if name not in CFG["groups"][g]:
                CFG["groups"][g].append(name)
            e_name.delete(0, tk.END)
            e_path.delete(0, tk.END)

        def _del_repo():
            v = _selected_repo()
            if not v:
                return
            name = v[0]
            REPOS.pop(name, None)
            for gname, names in CFG.get("groups", {}).items():
                if name in names:
                    names.remove(name)
            tree.delete(tree.selection()[0])

        # --- 比对预设 ---
        t3 = ttk.Frame(nb)
        nb.add(t3, text="比对预设")
        f3 = ttk.LabelFrame(t3, text="预设列表", padding=(8, 6))
        f3.pack(fill=tk.BOTH, expand=True, padx=8, pady=8)
        pcols = ("name", "repo", "dev", "prod", "dir")
        ptree = ttk.Treeview(f3, columns=pcols, show="headings", height=6)
        for c, t, w in [("name", "名称", 140), ("repo", "仓库", 140),
                        ("dev", "开发分支", 90), ("prod", "生产分支", 90),
                        ("dir", "方向", 150)]:
            ptree.heading(c, text=t)
            ptree.column(c, width=w)
        ptree.pack(fill=tk.BOTH, expand=True, pady=(0, 4))
        dir_label = {v: k for k, v in CMP_DIRECTIONS.items()}
        for p in CFG.get("presets", []):
            ptree.insert("", tk.END,
                         values=(p.get("name", ""), p.get("repo", ""),
                                 p.get("dev_branch", ""), p.get("prod_branch", ""),
                                 CMP_DIRECTIONS.get(p.get("direction", ""), "")))
        pef = ttk.LabelFrame(t3, text="预设编辑", padding=(12, 8))
        pef.pack(fill=tk.X, padx=8, pady=(0, 8))
        pr = ttk.Frame(pef)
        pr.pack(fill=tk.X, pady=2)
        ttk.Label(pr, text="名称:").pack(side=tk.LEFT)
        p_name = ttk.Entry(pr, width=18)
        p_name.pack(side=tk.LEFT, padx=4)
        ttk.Label(pr, text="仓库:").pack(side=tk.LEFT, padx=(8, 0))
        p_repo = ttk.Combobox(pr, values=list(REPOS.keys()), width=16)
        p_repo.pack(side=tk.LEFT, padx=4)
        ttk.Label(pr, text="开发:").pack(side=tk.LEFT, padx=(8, 0))
        p_dev = ttk.Entry(pr, width=10)
        p_dev.pack(side=tk.LEFT, padx=4)
        ttk.Label(pr, text="生产:").pack(side=tk.LEFT, padx=(8, 0))
        p_prod = ttk.Entry(pr, width=10)
        p_prod.pack(side=tk.LEFT, padx=4)
        ttk.Label(pr, text="方向:").pack(side=tk.LEFT, padx=(8, 0))
        p_dir = ttk.Combobox(pr, values=list(CMP_DIRECTIONS.values()), width=20)
        p_dir.set(CMP_DIRECTIONS["dev_to_prod"])
        p_dir.pack(side=tk.LEFT, padx=4)
        pr2 = ttk.Frame(pef)
        pr2.pack(fill=tk.X, pady=(6, 0))
        ttk.Button(pr2, text="➕ 新增预设", command=lambda: _add_preset()).pack(side=tk.LEFT)
        ttk.Button(pr2, text="✏️ 填入选中", command=lambda: _fill_preset()).pack(side=tk.LEFT, padx=6)
        ttk.Button(pr2, text="🗑 删除选中", command=lambda: _del_preset()).pack(side=tk.LEFT, padx=6)

        def _fill_preset():
            sel = ptree.selection()
            if not sel:
                return
            v = ptree.item(sel[0])["values"]
            p_name.delete(0, tk.END)
            p_name.insert(0, v[0])
            p_repo.set(v[1])
            p_dev.delete(0, tk.END)
            p_dev.insert(0, v[2])
            p_prod.delete(0, tk.END)
            p_prod.insert(0, v[3])
            p_dir.set(v[4])

        def _add_preset():
            name = p_name.get().strip()
            if not name:
                messagebox.showwarning("提示", "预设名称不能为空")
                return
            presets = CFG.setdefault("presets", [])
            for p in presets:
                if p.get("name") == name:
                    presets.remove(p)
                    break
            presets.append({
                "name": name, "repo": p_repo.get(),
                "dev_branch": p_dev.get().strip(),
                "prod_branch": p_prod.get().strip(),
                "direction": next((k for k, v in CMP_DIRECTIONS.items()
                                   if v == p_dir.get()), "dev_to_prod"),
                "auto_fetch": True,
            })
            ptree.delete(*ptree.get_children())
            for p in presets:
                ptree.insert("", tk.END,
                             values=(p.get("name", ""), p.get("repo", ""),
                                     p.get("dev_branch", ""), p.get("prod_branch", ""),
                                     CMP_DIRECTIONS.get(p.get("direction", ""), "")))
            p_name.delete(0, tk.END)

        def _del_preset():
            sel = ptree.selection()
            if not sel:
                return
            name = ptree.item(sel[0])["values"][0]
            presets = CFG.setdefault("presets", [])
            CFG["presets"] = [p for p in presets if p.get("name") != name]
            ptree.delete(sel[0])

        # --- 保存 ---
        btns = ttk.Frame(dlg)
        btns.pack(fill=tk.X, padx=12, pady=(0, 12))
        status = tk.StringVar(value="")

        def _save():
            if iv.get() < 5:
                messagebox.showwarning("提示", "刷新间隔不能小于 5 秒")
                return
            old_theme = CFG.get("theme", "light")
            CFG["refresh_interval"] = int(iv.get())
            CFG["auto_refresh"] = auto_v.get()
            CFG["sound"] = sound_v.get()
            CFG["theme"] = THEME_KEYS.get(theme_v.get(), "light")
            CFG["repos"] = dict(REPOS)
            for g, names in list(CFG.get("groups", {}).items()):
                if not names:
                    del CFG["groups"][g]
            save_config(CFG)
            reload_config()
            dlg.destroy()
            new_theme = CFG.get("theme", "light")
            if new_theme != old_theme:
                apply_theme(new_theme)
            self._rebuild_ui()
            self._refresh_group_cb()
            self.refresh()

        ttk.Button(btns, text="保存", style="Accent.TButton", command=_save).pack(side=tk.RIGHT)
        ttk.Button(btns, text="取消", command=dlg.destroy).pack(side=tk.RIGHT, padx=6)

        # 内容构建完成 → 按实际所需尺寸自适应：高分屏缩放后固定 580 高会截断底部按钮
        dlg.update_idletasks()
        sw, sh = dlg.winfo_screenwidth(), dlg.winfo_screenheight()
        w = min(dlg.winfo_reqwidth() + 8, sw - 40)
        h = min(dlg.winfo_reqheight() + 8, sh - 80)
        dlg.geometry("%dx%d+%d+%d" % (w, h, max(10, (sw - w) // 2),
                                      max(10, (sh - h) // 2)))

    # -------------------- 标签页 5：工作台（单仓库 变更→暂存→提交 一条龙） --------------------
    def _build_workspace_tab(self, notebook):
        tab = ttk.Frame(notebook)
        notebook.add(tab, text="工作台")

        ctrl = ttk.Frame(tab, padding=(10, 8))
        ctrl.pack(fill=tk.X)
        ttk.Label(ctrl, text="仓库:").pack(side=tk.LEFT)
        self.ws_repo_var = tk.StringVar(value=list(REPOS.keys())[0] if REPOS else "")
        self.ws_repo_cb = ttk.Combobox(ctrl, textvariable=self.ws_repo_var,
                                       values=list(REPOS.keys()), state="readonly", width=18)
        self.ws_repo_cb.pack(side=tk.LEFT, padx=4)
        self.ws_repo_cb.bind("<<ComboboxSelected>>", lambda e: self._load_workspace())
        ttk.Button(ctrl, text="🔄 刷新", command=self._load_workspace).pack(side=tk.LEFT, padx=4)
        ttk.Button(ctrl, text="📂 打开文件夹",
                   command=self._open_workspace_dir).pack(side=tk.LEFT, padx=4)
        self.ws_info_var = tk.StringVar(value="选择仓库后查看未提交变更")
        ttk.Label(ctrl, textvariable=self.ws_info_var, font=(FONT_UI, 9),
                  foreground=THEME_MUTED).pack(side=tk.RIGHT, padx=4)

        body = ttk.PanedWindow(tab, orient=tk.HORIZONTAL)
        body.pack(fill=tk.BOTH, expand=True, padx=10, pady=(0, 8))

        left = ttk.Frame(body)
        body.add(left, weight=1)
        op = ttk.Frame(left)
        op.pack(fill=tk.X, pady=(0, 4))
        # 全选复选框
        self.ws_select_all_var = tk.BooleanVar(value=False)
        self.ws_select_all_cb = ttk.Checkbutton(op, text="全选",
                                                 variable=self.ws_select_all_var,
                                                 command=self._ws_toggle_select_all)
        self.ws_select_all_cb.pack(side=tk.LEFT)
        ttk.Button(op, text="➕ 全部暂存",
                   command=lambda: self._ws_stage(None)).pack(side=tk.LEFT, padx=(6, 0))
        ttk.Button(op, text="➖ 全部取消暂存",
                   command=lambda: self._ws_unstage(None)).pack(side=tk.LEFT, padx=6)
        ttk.Button(op, text="🗑 丢弃选中",
                   command=self._ws_discard).pack(side=tk.LEFT, padx=6)
        ttk.Button(op, text="⚠ 放弃所有更改",
                   command=self._ws_discard_all).pack(side=tk.LEFT, padx=6)
        ttk.Button(op, text="🚀 暂存全部+提交", style="Accent.TButton",
                   command=self._ws_stage_all_commit).pack(side=tk.LEFT, padx=6)
        ttk.Button(op, text="✏️ 编辑选中",
                   command=self._ws_edit_selected).pack(side=tk.LEFT, padx=6)
        ttk.Button(op, text="➕ 暂存此文件",
                   command=self._ws_stage_preview_file).pack(side=tk.LEFT, padx=6)
        ttk.Button(op, text="🔍 Blame",
                   command=self._open_blame).pack(side=tk.LEFT, padx=6)
        ttk.Label(op, text="双击 @@ 块 = 只暂存该块",
                  font=(FONT_UI, 9), foreground=THEME_MUTED).pack(side=tk.RIGHT)
        # 列顺序：文件在最左，+ / − 在右；长路径可横向滚动
        cols = ("path", "plus", "minus")
        col_defs = [("path", "文件", 340, tk.W), ("plus", "+", 46, tk.CENTER),
                    ("minus", "−", 46, tk.CENTER)]
        # 对标 VS Code / Fork：已暂存与未暂存分区展示，双击在两者间移动
        self.ws_staged_frame = ttk.LabelFrame(left, text="已暂存（双击=取消暂存）",
                                              padding=(6, 3))
        self.ws_staged_frame.pack(fill=tk.BOTH, expand=True, pady=(0, 6))
        self.ws_tree_staged = ttk.Treeview(self.ws_staged_frame, columns=cols,
                                           show="headings", height=5)
        for c, t, w, anc in col_defs:
            self.ws_tree_staged.heading(c, text=t)
            self.ws_tree_staged.column(c, width=w, anchor=anc)
        _xsb1 = ttk.Scrollbar(self.ws_staged_frame, orient=tk.HORIZONTAL,
                              command=self.ws_tree_staged.xview)
        self.ws_tree_staged.configure(xscrollcommand=_xsb1.set)
        _xsb1.pack(side=tk.BOTTOM, fill=tk.X)
        self.ws_tree_staged.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.ws_tree_staged.bind("<<TreeviewSelect>>", self._on_ws_file_select)
        self.ws_tree_staged.bind("<Double-1>", self._on_ws_file_dclick)

        self.ws_unstaged_frame = ttk.LabelFrame(left, text="未暂存 / 未跟踪（双击=暂存）",
                                                padding=(6, 3))
        self.ws_unstaged_frame.pack(fill=tk.BOTH, expand=True)
        self.ws_tree_unstaged = ttk.Treeview(self.ws_unstaged_frame, columns=cols,
                                             show="headings", height=8)
        for c, t, w, anc in col_defs:
            self.ws_tree_unstaged.heading(c, text=t)
            self.ws_tree_unstaged.column(c, width=w, anchor=anc)
        _xsb2 = ttk.Scrollbar(self.ws_unstaged_frame, orient=tk.HORIZONTAL,
                              command=self.ws_tree_unstaged.xview)
        self.ws_tree_unstaged.configure(xscrollcommand=_xsb2.set)
        _xsb2.pack(side=tk.BOTTOM, fill=tk.X)
        self.ws_tree_unstaged.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.ws_tree_unstaged.bind("<<TreeviewSelect>>", self._on_ws_file_select)
        self.ws_tree_unstaged.bind("<Double-1>", self._on_ws_file_dclick)

        right = ttk.Frame(body)
        body.add(right, weight=1)
        self.ws_diff = tk.Text(right, wrap="none", bg=THEME_PANEL, fg=THEME_TEXT,
                               font=("Consolas", 9), bd=0, highlightthickness=1,
                               highlightbackground=THEME_BORDER, state="disabled")
        self.ws_diff.pack(fill=tk.BOTH, expand=True)
        self.ws_diff.tag_configure("add", foreground=TAG_COLORS["A"][1])
        self.ws_diff.tag_configure("del", foreground=TAG_COLORS["D"][1])
        self.ws_diff.tag_configure("meta", foreground=THEME_MUTED)
        self.ws_diff.tag_configure("hunkline", foreground=THEME_ACCENT,
                                   background=DIFF_HUNK_BG, font=(FONT_MONO, 9, "bold"))
        # 冲突文件行：红底高亮，提示需要手动解决
        self.ws_tree_unstaged.tag_configure(
            "ws_conflict",
            background=STATUS_SOFT.get("behind", "#FDE9E7"),
            foreground=TAG_COLORS["D"][1])
        # 双击 diff 预览区：点在 @@ 块上 → 只暂存该块；其他位置 → 默认编辑器打开
        self.ws_diff.bind("<Double-1>", self._ws_diff_dclick)

        cmt = ttk.LabelFrame(tab, text="提交（只提交已暂存内容）", padding=(10, 8))
        cmt.pack(fill=tk.X, padx=10, pady=(0, 10))
        row1 = ttk.Frame(cmt)
        row1.pack(fill=tk.X)
        ttk.Label(row1, text="前缀:").pack(side=tk.LEFT)
        self.ws_prefix_var = tk.StringVar(value="")
        self.ws_prefix_cb = ttk.Combobox(row1, textvariable=self.ws_prefix_var,
                                         values=COMMIT_PREFIXES, width=10)
        self.ws_prefix_cb.pack(side=tk.LEFT, padx=4)
        self.ws_prefix_cb.bind("<<ComboboxSelected>>",
                               lambda e: self._ws_apply_prefix())
        self.ws_msg_var = tk.StringVar()
        e = ttk.Entry(row1, textvariable=self.ws_msg_var)
        e.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 6))
        e.bind("<Return>", lambda ev: self._ws_commit())
        ttk.Button(row1, text="📝 提交", style="Accent.TButton",
                   command=self._ws_commit).pack(side=tk.RIGHT)
        self.ws_staged_var = tk.StringVar(value="已暂存 0 项")
        ttk.Label(row1, textvariable=self.ws_staged_var, font=(FONT_UI, 9),
                  foreground=THEME_MUTED).pack(side=tk.RIGHT, padx=8)
        row2 = ttk.Frame(cmt)
        row2.pack(fill=tk.X, pady=(4, 0))
        ttk.Label(row2, text="历史:").pack(side=tk.LEFT)
        self.ws_hist_var = tk.StringVar(value="")
        self.ws_hist_cb = ttk.Combobox(row2, textvariable=self.ws_hist_var,
                                       values=self._commit_history(), width=38,
                                       state="readonly")
        self.ws_hist_cb.pack(side=tk.LEFT, padx=4)
        self.ws_hist_cb.bind("<<ComboboxSelected>>",
                             lambda e: self._ws_use_history())
        ttk.Label(row2, text="模板:").pack(side=tk.LEFT, padx=(10, 0))
        self.ws_tpl_var = tk.StringVar(value="")
        self.ws_tpl_cb = ttk.Combobox(row2, textvariable=self.ws_tpl_var,
                                      values=self._commit_templates(), width=26,
                                      state="readonly")
        self.ws_tpl_cb.pack(side=tk.LEFT, padx=4)
        self.ws_tpl_cb.bind("<<ComboboxSelected>>",
                            lambda e: self._ws_use_template())
        ttk.Button(row2, text="💾 存为模板",
                   command=self._ws_save_template).pack(side=tk.LEFT, padx=2)
        ttk.Label(row2, text="{branch}/{date}/{time}/{repo} 自动替换 · Enter 提交",
                  font=(FONT_UI, 9), foreground=THEME_MUTED).pack(side=tk.RIGHT, padx=4)

    def _open_workspace(self, name):
        """跳转到指定仓库的工作台。name 必须是 REPOS 中的仓库名。"""
        self._active_repo = name
        if not getattr(self, "ws_repo_var", None):
            return
        # 确保仓库名有效（防止跳转到默认仓库）
        if name not in REPOS:
            return
        self.ws_repo_var.set(name)
        # 更新工作台下拉框的选项（防止仓库列表变化后找不到）
        if getattr(self, "ws_repo_cb", None):
            self.ws_repo_cb["values"] = list(REPOS.keys())
            self.ws_repo_var.set(name)
        try:
            self.notebook.select(4)  # 工作台是第 5 个 tab（索引 4）
        except Exception:
            return
        self._load_workspace()

    def _open_workspace_dir(self):
        name = self.ws_repo_var.get()
        if name and REPOS.get(name):
            open_in_explorer(REPOS[name])

    def _load_workspace(self):
        name = self.ws_repo_var.get()
        if not name or not getattr(self, "ws_tree_staged", None):
            return
        self.ws_info_var.set(f"正在加载 {name} 的变更…")
        self.ws_tree_staged.delete(*self.ws_tree_staged.get_children())
        self.ws_tree_unstaged.delete(*self.ws_tree_unstaged.get_children())
        self._ws_req += 1
        req = self._ws_req
        threading.Thread(target=self._fetch_workspace, args=(name, req),
                         daemon=True).start()

    def _fetch_workspace(self, name, req):
        try:
            files = get_workspace_status(REPOS[name])
        except Exception as e:
            err = str(e)
            self.root.after(0, lambda: self.ws_info_var.set(f"加载失败: {err}"))
            return
        self.root.after(0, self._render_workspace, files, name, req)

    def _render_workspace(self, files, name, req=None):
        if not getattr(self, "ws_tree_staged", None):
            return
        if req is not None and req != self._ws_req:
            return  # 过期结果（快速切换仓库），丢弃
        self.ws_tree_staged.delete(*self.ws_tree_staged.get_children())
        self.ws_tree_unstaged.delete(*self.ws_tree_unstaged.get_children())
        self._ws_files = files
        for idx, f in enumerate(files):
            vals = (f["path"], f["added"] or "", f["removed"] or "")
            if f["staged"]:
                self.ws_tree_staged.insert("", tk.END, iid=f"s{idx}", values=vals)
            elif f["conflict"]:
                # 冲突文件：红底 + ⚠ 前缀，双击走「手动解决」而非暂存
                self.ws_tree_unstaged.insert(
                    "", tk.END, iid=f"u{idx}",
                    values=("⚠ " + f["path"], f["added"] or "", f["removed"] or ""),
                    tags=("ws_conflict",))
            else:
                self.ws_tree_unstaged.insert("", tk.END, iid=f"u{idx}", values=vals)
        n_staged = sum(1 for f in files if f["staged"])
        n_untracked = sum(1 for f in files if f["untracked"])
        n_conflict = sum(1 for f in files if f["conflict"])
        self.ws_staged_var.set(f"已暂存 {n_staged} 项 / 未暂存 {len(files) - n_staged} 项")
        if not files:
            self.ws_info_var.set(f"{name}：工作区干净，没有未提交变更")
            self._ws_show_text("（工作区干净 ✓）")
            return
        extra = f" · 冲突 {n_conflict}" if n_conflict else ""
        self.ws_info_var.set(f"{name}：{len(files)} 个变更（未跟踪 {n_untracked}）{extra}")
        # 默认预览：优先第一个未暂存文件；没有则预览已暂存第一个
        kids = self.ws_tree_unstaged.get_children() or self.ws_tree_staged.get_children()
        if kids:
            self.ws_tree_unstaged.selection_remove(*self.ws_tree_unstaged.selection())
            self.ws_tree_staged.selection_remove(*self.ws_tree_staged.selection())
            if self.ws_tree_unstaged.exists(kids[0]):
                self.ws_tree_unstaged.selection_set(kids[0])
            else:
                self.ws_tree_staged.selection_set(kids[0])

    def _ws_show_text(self, text):
        self.ws_diff.configure(state="normal")
        self.ws_diff.delete("1.0", tk.END)
        if text.strip() and not text.startswith("（未跟踪"):
            self.ws_diff.insert(tk.END, "（双击 @@ 块可只暂存该块）\n", "meta")
        for line in text.splitlines():
            tag = None
            if line.startswith("+") and not line.startswith("+++"):
                tag = "add"
            elif line.startswith("-") and not line.startswith("---"):
                tag = "del"
            elif line.startswith("@@"):
                tag = "hunkline"
            elif line.startswith(("diff ", "index ", "--- ", "+++ ",
                                  "（", "…", "Not", "Binary")):
                tag = "meta"
            self.ws_diff.insert(tk.END, line + "\n", tag or ())
        self.ws_diff.configure(state="disabled")

    def _ws_diff_dclick(self, event):
        """双击 diff 预览区：点在 @@ 块上 → 只暂存该块；其他位置 → 编辑器打开。"""
        try:
            idx = self.ws_diff.index(f"@{event.x},{event.y}")
        except Exception:
            idx = None
        if idx and "hunkline" in self.ws_diff.tag_names(idx):
            self._ws_stage_hunk_at(idx)
        else:
            self._ws_edit_preview()

    def _hunk_no_at(self, idx):
        """点击位置属于第几个 @@ 块（0 起）；不在任何块上返回 None。"""
        ranges = self.ws_diff.tag_ranges("hunkline")
        for k in range(0, len(ranges), 2):
            if self.ws_diff.compare(ranges[k], "<=", idx) and \
               self.ws_diff.compare(idx, "<=", ranges[k + 1]):
                return k // 2
        return None

    def _ws_stage_hunk_at(self, idx):
        f = getattr(self, "_ws_preview_file", None)
        if not f:
            Toast(self.root, "暂存块", "请先单击选中一个文件")
            return
        if f["staged"]:
            Toast(self.root, "暂存块", "该文件已在暂存区，没有可暂存的块")
            return
        if f["untracked"]:
            Toast(self.root, "暂存块", "未跟踪文件没有 diff 块，请用「暂存此文件」")
            return
        n = self._hunk_no_at(idx)
        if n is None:
            return
        repo = REPOS.get(self.ws_repo_var.get())
        if not repo:
            return
        patch = get_file_patch(repo, f["path"])
        headers, hunks = split_hunks(patch)
        if n >= len(hunks):
            return
        if not messagebox.askyesno(
                "暂存此块",
                f"只暂存 {f['path']} 的第 {n + 1} 个变更块（共 {len(hunks)} 个）？\n\n"
                "该块改动将进入暂存区，其余改动保留在工作区。"):
            return
        self._ws_run("暂存块",
                     lambda: git_apply_cached(repo, "\n".join(headers + [hunks[n]]) + "\n"),
                     f"已暂存 {f['path']} 第 {n + 1} 个变更块")

    def _ws_stage_preview_file(self):
        """➕ 暂存此文件：把当前预览的未暂存文件整体加入暂存区"""
        f = getattr(self, "_ws_preview_file", None)
        if not f:
            Toast(self.root, "暂存文件", "请先单击选中一个文件")
            return
        if f["staged"]:
            Toast(self.root, "暂存文件", "该文件已在暂存区")
            return
        repo = REPOS.get(self.ws_repo_var.get())
        if not repo:
            return
        self._ws_run("暂存文件", lambda: ws_stage(repo, [f["path"]]),
                     f"已暂存 {f['path']}")

    def _open_blame(self):
        """🔍 Blame：对当前预览文件做逐行溯源（GitLens 风格，离线）"""
        f = getattr(self, "_ws_preview_file", None)
        if not f:
            Toast(self.root, "Blame", "请先单击选中一个文件")
            return
        repo = REPOS.get(self.ws_repo_var.get())
        if not repo:
            return
        path, staged = f["path"], f["staged"]
        self._set_busy(True, "正在加载 Blame…")

        def _work():
            try:
                rows = get_blame(repo, path, staged)
            except Exception as e:
                err = str(e)
                self.root.after(0, lambda: (self._set_busy(False),
                                            messagebox.showerror("Blame 失败", err)))
                return
            self.root.after(0, self._show_blame_window, rows, path)

        threading.Thread(target=_work, daemon=True).start()

    def _show_blame_window(self, rows, path):
        self._set_busy(False)
        dlg = tk.Toplevel(self.root)
        dlg.title(f"Blame - {path}")
        dlg.geometry("1000x640")
        dlg.configure(bg=THEME_BG)
        dlg.grid_rowconfigure(1, weight=1)
        dlg.grid_columnconfigure(0, weight=1)
        bar = tk.Frame(dlg, bg=THEME_HEADER, height=42)
        bar.grid(row=0, column=0, sticky="nsew")
        tk.Label(bar, text=f"Blame · {path}", bg=THEME_HEADER, fg="white",
                 font=(FONT_UI, 12, "bold")).pack(side=tk.LEFT, padx=14, pady=9)
        tk.Label(bar, text=f"{len(rows)} 行", bg=THEME_HEADER, fg=THEME_HEADER_SUB,
                 font=(FONT_UI, 9)).pack(side=tk.RIGHT, padx=14, pady=9)
        wrap = ttk.Frame(dlg)
        wrap.grid(row=1, column=0, sticky="nsew", padx=10, pady=8)
        txt = tk.Text(wrap, wrap=tk.NONE, font=(FONT_MONO, 10),
                      bg=THEME_PANEL, fg=THEME_TEXT, insertbackground=THEME_TEXT,
                      borderwidth=0, relief="flat", padx=12, pady=8,
                      selectbackground=THEME_ACCENT_SOFT, selectforeground=THEME_TEXT)
        ysb = ttk.Scrollbar(wrap, orient=tk.VERTICAL, command=txt.yview)
        xsb = ttk.Scrollbar(wrap, orient=tk.HORIZONTAL, command=txt.xview)
        txt.configure(yscrollcommand=ysb.set, xscrollcommand=xsb.set)
        txt.grid(row=0, column=0, sticky="nsew", padx=(0, 4), pady=(0, 4))
        ysb.grid(row=0, column=1, sticky="ns", pady=(0, 4))
        xsb.grid(row=1, column=0, sticky="ew", padx=(0, 4), pady=(0, 4))
        wrap.grid_rowconfigure(0, weight=1)
        wrap.grid_columnconfigure(0, weight=1)
        # 作者 → 颜色（与提交图同色板）
        authors = []
        for r in rows:
            if r["author"] not in authors:
                authors.append(r["author"])
        a_colors = {a: LANE_COLORS[i % len(LANE_COLORS)]
                    for i, a in enumerate(authors)}
        for i, _c in enumerate(a_colors.values()):
            txt.tag_configure(f"blame_{i}", foreground=_c)
        for r in rows:
            ai = authors.index(r["author"])
            txt.insert(tk.END,
                       f"{r['hash'][:7]:<8} {r['author']:<14} {r['date']} "
                       f"{r['line']:>4} │ {r['content']}\n",
                       f"blame_{ai}")
        txt.config(state=tk.DISABLED)
        btn_row = ttk.Frame(dlg, padding=(0, 10))
        btn_row.grid(row=2, column=0, sticky="ew")
        ttk.Button(btn_row, text="关闭", command=dlg.destroy).pack(side=tk.LEFT, padx=4)

    def _sel_ws_files(self, tree=None):
        """选中行对应的文件 dict 列表。tree 指定时只看该表（双击操作），否则汇总两区。"""
        files = getattr(self, "_ws_files", [])
        trees = [tree] if tree is not None else [self.ws_tree_staged,
                                                  self.ws_tree_unstaged]
        out = []
        for t in trees:
            for iid in t.selection():
                if iid and iid[0] in "su":
                    idx = int(iid[1:])
                    if idx < len(files):
                        out.append(files[idx])
        return out

    def _on_ws_file_select(self, _=None):
        files = self._sel_ws_files()
        if not files:
            return
        f = files[0]
        self._ws_preview_file = f  # 当前预览文件：双击 diff 区时用默认编辑器打开它
        repo = REPOS.get(self.ws_repo_var.get())
        if not repo:
            return
        try:
            text = get_worktree_diff(repo, f["path"], f["untracked"],
                                     staged=f["staged"])
        except Exception as e:
            text = f"（加载失败: {e}）"
        self._ws_show_text(text)

    def _on_ws_file_dclick(self, event=None):
        tree = getattr(event, "widget", None) if event else None
        files = self._sel_ws_files(tree)
        if not files:
            return
        repo = REPOS.get(self.ws_repo_var.get())
        if not repo:
            return
        paths = [f["path"] for f in files]
        if files[0].get("conflict"):
            # 冲突文件：双击打开编辑器手动解决（冲突未解决前不能直接暂存）
            Toast(self.root, "冲突文件", "已打开编辑器，请手动解决冲突标记后再刷新工作台")
            self._ws_edit_file(files[0])
            return
        if tree is self.ws_tree_staged:
            # 已暂存区双击 → 取消暂存（回到工作区）
            self._ws_run("取消暂存", lambda: ws_unstage(repo, paths),
                         f"已取消暂存 {len(files)} 个文件")
        else:
            self._ws_run("暂存", lambda: ws_stage(repo, paths),
                         f"已暂存 {len(files)} 个文件")

    def _ws_edit_file(self, f):
        """用系统默认编辑器打开文件（拼接仓库根路径），改完回工作台刷新看状态变化"""
        repo = REPOS.get(self.ws_repo_var.get())
        if not repo or not f:
            return
        fp = os.path.join(repo, f["path"])
        if not os.path.exists(fp):
            Toast(self.root, "打开失败", f"文件不存在：{f['path']}\n可能已被移动或删除")
            return
        if open_with_default_app(fp):
            Toast(self.root, "已用默认编辑器打开", f['path'])
        else:
            Toast(self.root, "打开失败", f"无法调用系统默认编辑器：{f['path']}")

    def _ws_edit_selected(self):
        """✏️ 编辑选中：打开文件列表中第一个选中项"""
        files = self._sel_ws_files()
        if not files:
            Toast(self.root, "编辑", "请先选中要编辑的文件")
            return
        self._ws_edit_file(files[0])

    def _ws_edit_preview(self):
        """双击 diff 预览区：打开当前正在预览的文件"""
        f = getattr(self, "_ws_preview_file", None)
        if not f:
            Toast(self.root, "编辑", "先在左侧单击选中一个文件看差异")
            return
        self._ws_edit_file(f)

    def _ws_run(self, action_label, fn, ok_msg):
        name = self.ws_repo_var.get()
        if not name:
            return
        self._set_busy(True, f"正在{action_label}…")

        def _work():
            try:
                out, rc = fn()
            except Exception as e:
                out, rc = str(e), 1
            self.root.after(0, lambda: self._ws_done(action_label, out, rc, ok_msg))

        threading.Thread(target=_work, daemon=True).start()

    def _ws_done(self, action_label, out, rc, ok_msg):
        self._set_busy(False)
        if rc == 0:
            msg = ok_msg or f"{action_label}成功"
            Toast(self.root, f"{action_label}完成", msg)
            # 提交成功 → 完整提交信息写入历史（去重/上限；定向写盘，不覆盖设置窗未保存的改动）
            if action_label in ("提交", "暂存并提交"):
                cm = (getattr(self, "_last_commit_msg", "") or "").strip()
                if cm:
                    hist = push_commit_history(list(CFG.get("commit_history", [])), cm)
                    CFG["commit_history"] = hist
                    self._persist_cfg_key("commit_history", hist)
                    if getattr(self, "ws_hist_cb", None):
                        self.ws_hist_cb.configure(values=list(hist))
            self.ws_msg_var.set("")
            self._load_workspace()
            self.refresh()
        else:
            detail = "\n".join(out.splitlines()[-6:])
            self.ws_info_var.set(f"{action_label}失败")
            messagebox.showerror(f"{action_label}失败", detail or "（无输出）")

    def _ws_stage(self, paths):
        repo = REPOS.get(self.ws_repo_var.get())
        if not repo:
            return
        if paths is None and not getattr(self, "_ws_files", []):
            Toast(self.root, "暂存", "没有可暂存的变更")
            return
        ok_msg = "已暂存全部变更" if paths is None else f"已暂存 {len(paths)} 个文件"
        self._ws_run("暂存", lambda: ws_stage(repo, paths), ok_msg)

    def _ws_unstage(self, paths):
        repo = REPOS.get(self.ws_repo_var.get())
        if not repo:
            return
        ok_msg = "已取消全部暂存" if paths is None else f"已取消暂存 {len(paths)} 个文件"
        self._ws_run("取消暂存", lambda: ws_unstage(repo, paths), ok_msg)

    def _ws_discard(self):
        files = self._sel_ws_files()
        if not files:
            Toast(self.root, "丢弃", "请先选中要丢弃的文件")
            return
        # 确认弹窗：逐文件显示改动行数，未跟踪文件单独标注「将直接删除」防误删
        title, body = build_discard_confirm_text(files)
        if not messagebox.askyesno(title, body):
            return
        repo = REPOS.get(self.ws_repo_var.get())
        if repo:
            self._ws_run("丢弃", lambda: ws_discard(repo, files),
                         f"已丢弃 {len(files)} 个文件的改动")

    def _ws_toggle_select_all(self):
        """全选/取消全选所有变更文件"""
        select = self.ws_select_all_var.get()
        if select:
            # 全选：选中所有 staged 和 unstaged 文件
            all_iids = list(self.ws_tree_staged.get_children()) + \
                       list(self.ws_tree_unstaged.get_children())
            self.ws_tree_staged.selection_set(self.ws_tree_staged.get_children())
            self.ws_tree_unstaged.selection_set(self.ws_tree_unstaged.get_children())
        else:
            # 取消全选
            self.ws_tree_staged.selection_remove(*self.ws_tree_staged.get_children())
            self.ws_tree_unstaged.selection_remove(*self.ws_tree_unstaged.get_children())
        # 触发选中事件更新预览
        self._on_ws_file_select()

    def _ws_discard_all(self):
        """放弃所有更改：还原所有已修改文件 + 删除所有新建文件"""
        files = getattr(self, "_ws_files", [])
        if not files:
            Toast(self.root, "放弃更改", "没有未提交的更改")
            return
        # 确认弹窗
        title, body = build_discard_confirm_text(files)
        if not messagebox.askyesno(title, body):
            return
        repo = REPOS.get(self.ws_repo_var.get())
        if repo:
            self._ws_run("放弃所有更改", lambda: ws_discard(repo, files),
                         f"已放弃所有更改（{len(files)} 个文件）")

    def _commit_history(self):
        return list(CFG.get("commit_history", []))[:20]

    def _commit_templates(self):
        return list(CFG.get("commit_templates", []))[:20]

    def _persist_cfg_key(self, key, value):
        """定向写盘单个配置键（读盘→只改该键→写回），避免覆盖设置窗未保存的其它改动"""
        try:
            with open(CONFIG_PATH, "r", encoding="utf-8") as f:
                _cfg = json.load(f)
            _cfg[key] = value
            _atomic_write_json(CONFIG_PATH, _cfg)
        except Exception:
            pass

    def _ws_fill_msg(self, msg):
        """把历史/模板内容填入输入框，并同步前缀下拉"""
        if not msg:
            return
        self.ws_msg_var.set(msg)
        m = COMMIT_PREFIX_RE.match(msg)
        if m:
            self.ws_prefix_var.set(m.group(0).strip())

    def _ws_apply_prefix(self):
        """把选中的前缀应用到提交信息（去重/替换，见 apply_commit_prefix）"""
        self.ws_msg_var.set(apply_commit_prefix(self.ws_prefix_var.get().strip(),
                                                self.ws_msg_var.get()))

    def _ws_use_history(self):
        """选中的历史提交信息填入输入框"""
        self._ws_fill_msg(self.ws_hist_var.get())

    def _ws_use_template(self):
        """选中的模板填入输入框"""
        self._ws_fill_msg(self.ws_tpl_var.get())

    def _ws_save_template(self):
        """把当前输入框内容（前缀+正文组合后）存为自定义模板"""
        msg = apply_commit_prefix(self.ws_prefix_var.get().strip(),
                                  self.ws_msg_var.get().strip())
        if not msg or not COMMIT_PREFIX_RE.sub("", msg).strip():
            messagebox.showwarning("提示", "输入框内容为空，先写好提交信息再存为模板")
            return
        tpls = push_commit_history(list(CFG.get("commit_templates", [])), msg)
        CFG["commit_templates"] = tpls
        self._persist_cfg_key("commit_templates", tpls)
        if getattr(self, "ws_tpl_cb", None):
            self.ws_tpl_cb.configure(values=list(tpls))
        Toast(self.root, "模板已保存", f"已保存：{msg[:40]}")

    def _ws_expand_vars(self, msg):
        """提交模板变量展开：{branch}/{date}/{time}/{repo}（离线）"""
        repo = self.ws_repo_var.get()
        branch = ""
        if repo and self._last_info:
            branch = self._last_info.get(repo, {}).get("branch", "")
        if not branch and repo and REPOS.get(repo):
            out, _ = git(REPOS[repo], "rev-parse", "--abbrev-ref", "HEAD")
            branch = out.strip()
        return expand_commit_vars(msg, branch=branch,
                                  date=datetime.now().strftime("%Y-%m-%d"),
                                  time=datetime.now().strftime("%H:%M"),
                                  repo=repo or "")

    def _ws_commit(self):
        msg = apply_commit_prefix(self.ws_prefix_var.get().strip(),
                                  self.ws_msg_var.get().strip())
        msg = self._ws_expand_vars(msg)
        # 光有前缀（如 "fix:"）不算正文，避免产生裸前缀提交
        if not msg or not COMMIT_PREFIX_RE.sub("", msg).strip():
            messagebox.showwarning("提示", "请先填写提交信息正文（光有前缀不算）")
            return
        self._last_commit_msg = msg
        repo = REPOS.get(self.ws_repo_var.get())
        if not repo:
            return
        files = getattr(self, "_ws_files", [])
        n_staged = sum(1 for f in files if f["staged"])
        if n_staged == 0 and not files:
            messagebox.showinfo("提示", "工作区没有可提交的变更")
            return
        if n_staged == 0:
            if not messagebox.askyesno("没有已暂存内容",
                                       "当前没有已暂存的文件，是否暂存全部后一起提交？"):
                return
            self._ws_run("暂存并提交",
                         lambda: (ws_stage(repo), ws_commit(repo, msg))[1],
                         f"已提交：{msg[:40]}")
            return
        self._ws_run("提交", lambda: ws_commit(repo, msg), f"已提交：{msg[:40]}")

    def _ws_stage_all_commit(self):
        """🚀 一键暂存全部并提交：消息优先取输入框（前缀+正文组合），
        为空则用「模板」下拉当前选中的模板，都空则提示。
        一键把当前仓库所有变更（含未跟踪）暂存并提交，配模板下拉快速套用。"""
        msg = apply_commit_prefix(self.ws_prefix_var.get().strip(),
                                  self.ws_msg_var.get().strip())
        if not msg or not COMMIT_PREFIX_RE.sub("", msg).strip():
            # 输入框为空 → 用「模板」下拉选中值，并保留用户已选前缀（与主路径语义一致）
            msg = apply_commit_prefix(self.ws_prefix_var.get().strip(),
                                      (self.ws_tpl_var.get() or "").strip())
        msg = self._ws_expand_vars(msg)
        if not msg or not COMMIT_PREFIX_RE.sub("", msg).strip():
            messagebox.showwarning("提示",
                                   "请先填写提交信息正文，或在「模板」下拉选一个模板")
            return
        repo = REPOS.get(self.ws_repo_var.get())
        if not repo:
            return
        files = getattr(self, "_ws_files", [])
        if not files:
            messagebox.showinfo("提示", "工作区没有可提交的变更")
            return
        self._last_commit_msg = msg
        self._ws_run("暂存并提交",
                     lambda: ws_stage_all_and_commit(repo, msg),
                     f"已暂存全部并提交：{msg[:40]}")

    # -------------------- 标签页 6：分支管理 --------------------
    def _build_branches_tab(self, notebook):
        tab = ttk.Frame(notebook)
        notebook.add(tab, text="分支")

        ctrl = ttk.Frame(tab, padding=(10, 8))
        ctrl.pack(fill=tk.X)
        ttk.Label(ctrl, text="仓库:").pack(side=tk.LEFT)
        self.branch_repo_var = tk.StringVar(value=list(REPOS.keys())[0] if REPOS else "")
        self.branch_repo_cb = ttk.Combobox(ctrl, textvariable=self.branch_repo_var,
                                           values=list(REPOS.keys()), state="readonly", width=18)
        self.branch_repo_cb.pack(side=tk.LEFT, padx=4)
        self.branch_repo_cb.bind("<<ComboboxSelected>>", lambda e: self._load_branches())
        ttk.Button(ctrl, text="🔄 刷新", command=self._load_branches).pack(side=tk.LEFT, padx=4)
        ttk.Button(ctrl, text="🌿 新建分支…", command=self._branch_new).pack(side=tk.LEFT, padx=4)
        ttk.Button(ctrl, text="🔀 切换", command=self._branch_checkout).pack(side=tk.LEFT, padx=4)
        ttk.Button(ctrl, text="🔗 合并到当前", command=self._branch_merge).pack(side=tk.LEFT, padx=4)
        ttk.Button(ctrl, text="✏️ 重命名", command=self._branch_rename).pack(side=tk.LEFT, padx=4)
        ttk.Button(ctrl, text="🗑 删除", command=self._branch_delete).pack(side=tk.LEFT, padx=4)
        self.branch_info_var = tk.StringVar(value="")
        ttk.Label(ctrl, textvariable=self.branch_info_var, font=(FONT_UI, 9),
                  foreground=THEME_MUTED).pack(side=tk.RIGHT, padx=4)

        wrap = ttk.Frame(tab)
        wrap.pack(fill=tk.BOTH, expand=True, padx=10, pady=(0, 8))
        cols = ("name", "kind", "hash", "date", "subject", "ahead", "behind")
        self.branch_tree = ttk.Treeview(wrap, columns=cols, show="headings", height=14)
        for c, t, w, anc in [
                ("name", "分支", 190, tk.W), ("kind", "类型", 50, tk.CENTER),
                ("hash", "最新提交", 80, tk.CENTER), ("date", "日期", 110, tk.CENTER),
                ("subject", "提交信息", 380, tk.W), ("ahead", "领先", 50, tk.CENTER),
                ("behind", "落后", 50, tk.CENTER)]:
            self.branch_tree.heading(c, text=t)
            self.branch_tree.column(c, width=w, anchor=anc)
        ysb = ttk.Scrollbar(wrap, orient=tk.VERTICAL, command=self.branch_tree.yview)
        self.branch_tree.configure(yscrollcommand=ysb.set)
        self.branch_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        ysb.pack(side=tk.RIGHT, fill=tk.Y)
        self.branch_tree.tag_configure("本地", foreground=THEME_ACCENT)
        self.branch_tree.tag_configure("远程", foreground=THEME_MUTED)
        self.branch_tree.bind("<Double-1>", lambda e: self._branch_checkout())

    def _sel_branch(self):
        sel = self.branch_tree.selection()
        if not sel:
            Toast(self.root, "提示", "请先在列表中选择一个分支")
            return None
        return sel[0]

    def _load_branches(self):
        name = self.branch_repo_var.get()
        if not name or not getattr(self, "branch_tree", None):
            return
        self.branch_info_var.set(f"正在加载 {name} 的分支…")
        self._branch_req += 1
        req = self._branch_req
        threading.Thread(target=self._fetch_branches, args=(name, req),
                         daemon=True).start()

    def _fetch_branches(self, name, req):
        try:
            rows = get_branch_overview(REPOS[name])
        except Exception as e:
            err = str(e)
            self.root.after(0, lambda: self.branch_info_var.set(f"加载失败: {err}"))
            return
        self.root.after(0, self._render_branches, rows, name, req)

    def _render_branches(self, rows, name, req):
        if req != self._branch_req:
            return
        self.branch_tree.delete(*self.branch_tree.get_children())
        cur = self._last_info.get(name, {}).get("branch", "") if self._last_info else ""
        for r in rows:
            mark = "● " if (r["kind"] == "本地" and r["name"] == cur) else ""
            self.branch_tree.insert("", tk.END, iid=r["name"],
                                    values=(mark + r["name"], r["kind"], r["hash7"],
                                            r["date"], r["subject"], r["ahead"],
                                            r["behind"]),
                                    tags=(r["kind"],))
        self.branch_info_var.set(f"{name}：{len(rows)} 个分支（● = 当前分支）")

    def _branch_new(self):
        name = self.branch_repo_var.get()
        if not name:
            return
        bname = self._ask_name("新建分支", "feature/xxx")
        if not bname:
            return
        self._run_git_op("新建分支",
                         lambda: repo_create_branch(REPOS[name], bname))

    def _branch_checkout(self):
        b = self._sel_branch()
        if not b:
            return
        name = self.branch_repo_var.get()
        self._run_git_op("切换分支", lambda: repo_checkout(REPOS[name], b))

    def _branch_merge(self):
        b = self._sel_branch()
        if not b:
            return
        name = self.branch_repo_var.get()
        if not messagebox.askyesno("合并分支",
                                   f"将把「{b}」合并到当前分支（{name}），确定继续？"):
            return
        self._run_git_op("合并分支", lambda: repo_merge_branch(REPOS[name], b))

    def _branch_rename(self):
        b = self._sel_branch()
        if not b:
            return
        if b.startswith("origin/"):
            messagebox.showwarning("提示", "远程分支不能直接重命名（请重命名本地分支后推送）")
            return
        name = self.branch_repo_var.get()
        nb = self._ask_name("重命名分支", b)
        if not nb or nb == b:
            return
        self._run_git_op("重命名分支", lambda: repo_rename_branch(REPOS[name], b, nb))

    def _branch_delete(self):
        b = self._sel_branch()
        if not b:
            return
        name = self.branch_repo_var.get()
        cur = self._last_info.get(name, {}).get("branch", "") if self._last_info else ""
        if b == cur:
            messagebox.showwarning("提示", f"「{b}」是当前分支，请先切换到其他分支再删除")
            return
        if b.startswith("origin/"):
            if not messagebox.askyesno(
                    "删除远程分支",
                    f"将执行 git push origin --delete {b[len('origin/'):]}\n\n"
                    "这会删除远程仓库的分支（需要网络），且不可恢复，确定继续？"):
                return
            self._run_git_op("删除远程分支",
                             lambda: git(REPOS[name], "push", "origin",
                                         "--delete", b[len("origin/"):], timeout=90))
        else:
            if not messagebox.askyesno("删除分支",
                                       f"将强制删除本地分支「{b}」（-D，含未合并提交），确定继续？"):
                return
            self._run_git_op("删除分支", lambda: repo_delete_branch(REPOS[name], b))

    # -------------------- 标签页 7：Stash 管理 --------------------
    def _build_stash_tab(self, notebook):
        tab = ttk.Frame(notebook)
        notebook.add(tab, text="Stash")

        ctrl = ttk.Frame(tab, padding=(10, 8))
        ctrl.pack(fill=tk.X)
        ttk.Label(ctrl, text="仓库:").pack(side=tk.LEFT)
        self.stash_repo_var = tk.StringVar(value=list(REPOS.keys())[0] if REPOS else "")
        self.stash_repo_cb = ttk.Combobox(ctrl, textvariable=self.stash_repo_var,
                                          values=list(REPOS.keys()), state="readonly", width=18)
        self.stash_repo_cb.pack(side=tk.LEFT, padx=4)
        self.stash_repo_cb.bind("<<ComboboxSelected>>", lambda e: self._load_stashes())
        ttk.Button(ctrl, text="🔄 刷新", command=self._load_stashes).pack(side=tk.LEFT, padx=4)
        ttk.Button(ctrl, text="💾 保存…", command=self._stash_save).pack(side=tk.LEFT, padx=4)
        ttk.Button(ctrl, text="♻️ 应用", command=self._stash_apply).pack(side=tk.LEFT, padx=4)
        ttk.Button(ctrl, text="🗑 删除", command=self._stash_drop).pack(side=tk.LEFT, padx=4)
        ttk.Label(ctrl, text="双击 = 查看内容", font=(FONT_UI, 9),
                  foreground=THEME_MUTED).pack(side=tk.RIGHT, padx=4)
        self.stash_info_var = tk.StringVar(value="")
        ttk.Label(ctrl, textvariable=self.stash_info_var, font=(FONT_UI, 9),
                  foreground=THEME_MUTED).pack(side=tk.RIGHT, padx=8)

        wrap = ttk.Frame(tab)
        wrap.pack(fill=tk.BOTH, expand=True, padx=10, pady=(0, 8))
        cols = ("ref", "msg", "date")
        self.stash_tree = ttk.Treeview(wrap, columns=cols, show="headings", height=14)
        for c, t, w, anc in [("ref", "引用", 110, tk.W), ("msg", "说明", 560, tk.W),
                             ("date", "时间", 130, tk.CENTER)]:
            self.stash_tree.heading(c, text=t)
            self.stash_tree.column(c, width=w, anchor=anc)
        ysb = ttk.Scrollbar(wrap, orient=tk.VERTICAL, command=self.stash_tree.yview)
        self.stash_tree.configure(yscrollcommand=ysb.set)
        self.stash_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        ysb.pack(side=tk.RIGHT, fill=tk.Y)
        self.stash_tree.tag_configure("stash_row", foreground=THEME_TEXT)
        self.stash_tree.bind("<Double-1>", lambda e: self._stash_show())

    def _sel_stash(self):
        sel = self.stash_tree.selection()
        if not sel:
            Toast(self.root, "提示", "请先在列表中选择一个 stash")
            return None
        return self.stash_tree.item(sel[0])["values"][0]

    def _load_stashes(self):
        name = self.stash_repo_var.get()
        if not name or not getattr(self, "stash_tree", None):
            return
        self.stash_info_var.set(f"正在加载 {name} 的 stash…")
        self._stash_req += 1
        req = self._stash_req
        threading.Thread(target=self._fetch_stashes, args=(name, req),
                         daemon=True).start()

    def _fetch_stashes(self, name, req):
        try:
            rows = get_stash_list(REPOS[name])
        except Exception as e:
            err = str(e)
            self.root.after(0, lambda: self.stash_info_var.set(f"加载失败: {err}"))
            return
        self.root.after(0, self._render_stashes, rows, name, req)

    def _render_stashes(self, rows, name, req):
        if req != self._stash_req:
            return
        self.stash_tree.delete(*self.stash_tree.get_children())
        for r in rows:
            self.stash_tree.insert("", tk.END,
                                   values=(r["ref"], r["msg"], r["date"]),
                                   tags=("stash_row",))
        self.stash_info_var.set(f"{name}：{len(rows)} 个 stash")

    def _stash_save(self):
        name = self.stash_repo_var.get()
        if not name:
            return
        msg = self._ask_name("保存 Stash", "WIP 临时保存")
        if not msg:
            return
        self._run_git_op("保存 Stash", lambda: stash_save(REPOS[name], msg))

    def _stash_apply(self):
        ref = self._sel_stash()
        if not ref:
            return
        name = self.stash_repo_var.get()
        if not messagebox.askyesno("应用 Stash",
                                   f"将把 {ref} 的改动恢复到工作区（保留 stash 本身），确定继续？"):
            return
        self._run_git_op("应用 Stash", lambda: stash_apply(REPOS[name], ref))

    def _stash_drop(self):
        ref = self._sel_stash()
        if not ref:
            return
        name = self.stash_repo_var.get()
        if not messagebox.askyesno("删除 Stash",
                                   f"将永久删除 {ref}，其内容不可恢复，确定继续？"):
            return
        self._run_git_op("删除 Stash", lambda: stash_drop(REPOS[name], ref))

    def _stash_show(self):
        ref = self._sel_stash()
        if not ref:
            return
        name = self.stash_repo_var.get()
        self._load_diff_async(f"Stash 内容 - {ref}",
                              lambda: stash_show(REPOS[name], ref) or "（该 stash 无文本差异）")

    # -------------------- 标签页切换 --------------------
    def _on_tab_changed(self, _):
        idx = self.notebook.index(self.notebook.select())
        if idx == 2:  # 提交图
            if not self.graph_repo_var.get() and REPOS:
                self.graph_repo_var.set(list(REPOS.keys())[0])
                self._load_graph()
        elif idx == 3:  # 统计
            if not self._stats:
                self._load_stats()
        elif idx == 4:  # 工作台
            if not getattr(self, "ws_tree_staged", None):
                return
            if self.ws_repo_var.get() and not self.ws_tree_unstaged.get_children() \
                    and not self.ws_tree_staged.get_children():
                # 打开工作台时优先自动选中"有未提交变更"的仓库, 避免默认第一个仓库
                # 一片空白(改的是别的仓库时), 让用户误以为功能失效
                _dirty = pick_ws_repo(getattr(self, "_last_info", None),
                                      list(REPOS.keys()))
                if _dirty and _dirty != self.ws_repo_var.get():
                    self.ws_repo_var.set(_dirty)
                self._load_workspace()
        elif idx == 5:  # 分支
            if not getattr(self, "branch_tree", None):
                return
            if self.branch_repo_var.get() and not self.branch_tree.get_children():
                self._load_branches()
        elif idx == 6:  # Stash
            if not getattr(self, "stash_tree", None):
                return
            if self.stash_repo_var.get() and not self.stash_tree.get_children():
                self._load_stashes()


# ============================================================
# 入口
# ============================================================
def _draw_app_icon():
    """程序图标（蓝底圆角方块 + 白色分支图形）→ PIL RGBA 图。
    窗口图标与托盘图标共用，保证两处一致。"""
    img = Image.new("RGBA", (32, 32), (0, 0, 0, 0))
    d = ImageDraw.Draw(img)
    d.rounded_rectangle([2, 2, 30, 30], radius=7, fill="#2F6FED")
    d.ellipse([13, 7, 19, 13], fill="white")
    d.line([16, 13, 16, 22], fill="white", width=2)
    d.line([16, 22, 24, 24], fill="white", width=2)
    return img


def make_window_icon():
    """用 PIL 生成应用图标（无 PIL 时返回 None）"""
    if not PIL_AVAILABLE:
        return None
    try:
        from PIL import ImageTk
        return ImageTk.PhotoImage(_draw_app_icon())
    except Exception:
        return None


def _make_tray_icon():
    """生成托盘 HICON：PIL 图 → ICO 数据 → CreateIconFromResourceEx。
    与窗口图标同款图形；无 PIL 或失败时返回 0（调用方降级用系统默认图标）。"""
    if not PIL_AVAILABLE:
        return 0
    try:
        import io as _io
        import struct as _struct
        import ctypes as _ct
        buf = _io.BytesIO()
        _draw_app_icon().save(buf, format="ICO", sizes=[(32, 32)])
        data = buf.getvalue()
        count = _struct.unpack_from("<H", data, 4)[0]
        if not count:
            return 0
        size = _struct.unpack_from("<I", data, 6 + 16 * 0 + 8)[0]
        off = _struct.unpack_from("<I", data, 6 + 16 * 0 + 12)[0]
        icon_bits = data[off:off + size]
        _ct.windll.user32.CreateIconFromResourceEx.restype = _ct.c_void_p
        raw = _ct.create_string_buffer(icon_bits)
        h = _ct.windll.user32.CreateIconFromResourceEx(
            _ct.cast(raw, _ct.c_void_p), len(icon_bits), True,
            0x00030000, 0, 0, 0)
        return h or 0
    except Exception:
        return 0


def main():
    if not TK_AVAILABLE:
        sys.stderr.write(
            "错误：本机未安装 tkinter（桌面 GUI 所需）。\n"
            "请安装 Tk 后重试；若仅需 Web 服务，请改用 git_web.py。\n")
        sys.exit(1)
    # 高 DPI 感知：否则高分屏下界面模糊
    if os.name == "nt":
        try:
            import ctypes
            ctypes.windll.shcore.SetProcessDpiAwareness(1)
        except Exception:
            pass
    root = tk.Tk()
    icon = make_window_icon()
    if icon:
        root.iconphoto(True, icon)
    app = GitMonitorApp(root)
    root.protocol("WM_DELETE_WINDOW", app._on_close)
    root.mainloop()


if __name__ == "__main__":
    main()
