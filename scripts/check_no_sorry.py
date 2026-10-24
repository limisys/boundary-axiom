#!/usr/bin/env python3
"""check_no_sorry.py —— 剥离注释后检查 `sorry` / `admit` / `axiom`，并统计声明数。

用法：
    python3 scripts/check_no_sorry.py --root lean
    python3 scripts/check_no_sorry.py --root vendor/CausModel
    python3 scripts/check_no_sorry.py --root . --recursive

规则与 `counts.py` 基本一致（本脚本另外剔除字符串内容，计数仅作旁证；官方数字以 `counts.py` 为准）：
  剥离可嵌套块注释 `/- … -/`、行注释 `--` 与字符串后，
  thm/lem = `^\\s*(noncomputable|private|protected)* (theorem|lemma)`
  def/str = 同前缀的 `(def|abbrev|structure|instance)`
退出码：0 = 无违规；1 = 有违规或读不到文件。
"""
import argparse
import re
from pathlib import Path

BAD = ("sorry", "admit", "axiom")
THM = r"^\s*(?:noncomputable\s+|private\s+|protected\s+)*(?:theorem|lemma)\s"
DEF = r"^\s*(?:noncomputable\s+|private\s+|protected\s+)*(?:def|abbrev|structure|instance)\s"
SKIP_DIRS = {"build", ".lake", ".git", "__pycache__"}


def strip_comments(src: str) -> str:
    """删除嵌套块注释、行注释；字符串内容也剔除，避免注释/字符串里的词误报。"""
    out, i, n = [], 0, len(src)
    while i < n:
        if src.startswith("/-", i):
            depth, i = 1, i + 2
            while i < n and depth:
                if src.startswith("/-", i):
                    depth, i = depth + 1, i + 2
                elif src.startswith("-/", i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
        elif src.startswith("--", i):
            j = src.find("\n", i)
            i = n if j < 0 else j
        elif src[i] == '"':
            i += 1
            while i < n:
                if src[i] == "\\":
                    i += 2
                    continue
                if src[i] == '"':
                    i += 1
                    break
                i += 1
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


def lean_files(root: Path, recursive: bool):
    it = root.rglob("*.lean") if recursive else root.glob("*.lean")
    for p in sorted(it):
        if p.name.startswith("."):
            continue
        if any(part in SKIP_DIRS for part in p.parts):
            continue
        yield p


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default="lean")
    ap.add_argument("--recursive", action="store_true")
    ap.add_argument("--exclude", action="append", default=[], help="按文件名排除")
    args = ap.parse_args()

    root = Path(args.root)
    if not root.is_dir():
        print(f"FAIL 目录不存在：{root}")
        return 1
    files = [p for p in lean_files(root, args.recursive) if p.name not in set(args.exclude)]
    if not files:
        print(f"FAIL {root} 下没有 .lean 文件")
        return 1

    bad, total_t, total_d = [], 0, 0
    for p in files:
        code = strip_comments(p.read_text(encoding="utf-8"))
        t = len(re.findall(THM, code, re.M))
        d = len(re.findall(DEF, code, re.M))
        total_t += t
        total_d += d
        hits = [w for w in BAD if re.search(r"(?<![\w.])" + w + r"(?![\w])", code)]
        if hits:
            bad.append((str(p), hits))
        print(f"{str(p):52s} thm/lem={t:3d} def/str={d:2d} 违规={hits or '无'}")

    print(f"{'合计':52s} thm/lem={total_t:3d} def/str={total_d:2d} 文件={len(files)}")
    if bad:
        print("!! 违规：", bad)
        return 1
    print("0 sorry / 0 axiom —— 通过")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
