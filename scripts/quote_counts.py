#!/usr/bin/env python3
"""quote_counts.py —— 从 data/counts.json 生成对外可引用的唯一数字串。

论文、README、公开仓回填都从本脚本取数，禁止手抄。
用法：python3 scripts/quote_counts.py [--json]
"""
import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LABELS = {
    "all": "统一仓审计体（B 线 55 + A 模块 1）",
    "b_line": "B 线全量（正典 53 + 同一性 2）",
    "a_module": "A 模块 BoundaryTheory",
    "paper_b_canonical": "论文 B 正典树（不含同一性与 A 模块）",
}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()
    data = json.loads((ROOT / "data" / "counts.json").read_text(encoding="utf-8"))
    if args.json:
        print(json.dumps({k: data[k] for k in LABELS}, ensure_ascii=False, indent=2))
        return 0
    for key, label in LABELS.items():
        s = data[key]
        print(f"{label}: {s['files']} 文件 / {s['thm_lem']} thm/lem / {s['def']} def")
    print("\n论文 B 正文引用口径：417 / 77 / 53")
    print("论文 A 引用口径：+33 / 7 / 1（A 模块）")
    print("全审计体引用口径：467 / 90 / 56")
    print("禁止写法：把 450/84/54 或 434/84/55 当作统一仓总数。")
    return 0


if __name__ == "__main__":
    sys.exit(main())
