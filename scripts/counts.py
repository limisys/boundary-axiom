#!/usr/bin/env python3
"""counts.py —— 统一仓单一计数真源：按作用域分报，输出 JSON，可 --check。

计数规则（与 check_no_sorry.py 完全一致，刻意不改，以便与已发表数字逐位对齐）：
  剥离可嵌套块注释 /- -/ 与 -- 行注释后，
  thm/lem = ^\\s*(noncomputable|private|protected)* (theorem|lemma) 的行数
  def/str = 同前缀的 (def|abbrev|structure|instance) 行数

作用域（同一批源件，四种口径）：
  all                 全部 56 件 —— 统一仓审计体（B 线 55 ＋ A 线 BoundaryTheory 1）
  b_line              55 件 —— 正典 53 ＋ BoundaryReportIdentity ＋ ReportCountermodels
  a_module             1 件 —— BoundaryTheory（论文 A 的硬证据模块）
  paper_b_canonical   53 件 —— 论文 B 正文所引「正典树」（不含两件同一性文件与 A 模块）

用法：
  python3 scripts/counts.py --root lean --out data/counts.json --check docs/counts.json
"""
import argparse
import json
import re
import sys
from pathlib import Path

THM = r"^\s*(?:noncomputable\s+|private\s+|protected\s+)*(?:theorem|lemma)\s"
DEF = r"^\s*(?:noncomputable\s+|private\s+|protected\s+)*(?:def|abbrev|structure|instance)\s"
A_MODULE = "BoundaryTheory.lean"
IDENTITY = {"BoundaryReportIdentity.lean", "ReportCountermodels.lean"}


def strip_comments(src: str) -> str:
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
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


def count_one(p: Path):
    code = strip_comments(p.read_text(encoding="utf-8"))
    return {
        "file": p.name,
        "theorem_or_lemma": len(re.findall(THM, code, re.M)),
        "def_or_struct": len(re.findall(DEF, code, re.M)),
    }


def summarize(rows):
    return {
        "files": len(rows),
        "thm_lem": sum(r["theorem_or_lemma"] for r in rows),
        "def": sum(r["def_or_struct"] for r in rows),
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default="lean")
    ap.add_argument("--out")
    ap.add_argument("--check")
    args = ap.parse_args()

    root = Path(args.root)
    files = sorted(p for p in root.glob("*.lean") if not p.name.startswith("."))
    if not files:
        print(f"FAIL {root} 下没有 .lean 文件")
        return 1

    rows = [count_one(p) for p in files]
    by_name = {r["file"]: r for r in rows}
    result = {
        "all": summarize(rows),
        "b_line": summarize([r for r in rows if r["file"] != A_MODULE]),
        "a_module": summarize([r for r in rows if r["file"] == A_MODULE]),
        "paper_b_canonical": summarize(
            [r for r in rows if r["file"] != A_MODULE and r["file"] not in IDENTITY]
        ),
        "method": (
            "strip nested /- -/ and -- comments, then count declarations with the same "
            "regex as check_no_sorry.py; archive/ is not under lean/ and is not counted"
        ),
        "note": (
            "统一仓全部 56 件；四作用域由同一批源件切出，不是四套互相矛盾的数。"
            "论文 B 引用 paper_b_canonical=417/77/53；B 线全量 434/83/55；"
            "A 模块 33/7/1；统一审计体 467/90/56。"
        ),
        "files": rows,
    }

    if args.out:
        Path(args.out).parent.mkdir(parents=True, exist_ok=True)
        Path(args.out).write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

    ok = True
    if args.check:
        exp = json.loads(Path(args.check).read_text(encoding="utf-8"))
        for scope in ("all", "b_line", "a_module", "paper_b_canonical"):
            for key in ("files", "thm_lem", "def"):
                got, want = result[scope][key], exp[scope][key]
                status = "ok" if got == want else "MISMATCH"
                if got != want:
                    ok = False
                print(f"{scope}.{key}: {got} (expected {want}) {status}")
    else:
        print(json.dumps({k: result[k] for k in ("all", "b_line", "a_module", "paper_b_canonical")},
                         ensure_ascii=False, indent=2))

    print("PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
