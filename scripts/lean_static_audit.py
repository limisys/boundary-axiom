#!/usr/bin/env python3
"""lean_static_audit.py —— 逐文件静态审计（剥离注释后计数），输出 JSON。

用法：python3 scripts/lean_static_audit.py --root lean [--exclude FILE ...] --out data/lean_static_audit.json
"""
import argparse
import json
import re
from pathlib import Path

THM = re.compile(r"^[ \t]*(?:noncomputable[ \t]+|private[ \t]+|protected[ \t]+)*(?:theorem|lemma)[ \t]", re.M)
DEF = re.compile(r"^[ \t]*(?:noncomputable[ \t]+|private[ \t]+|protected[ \t]+)*(?:def|abbrev|structure|instance)[ \t]", re.M)
BAD = ("sorry", "admit", "axiom")


def mask_comments(src: str) -> str:
    out = list(src)
    i, n = 0, len(src)
    while i < n:
        if src.startswith("/-", i):
            depth = 1
            out[i] = out[i + 1] = " "
            i += 2
            while i < n and depth:
                if src.startswith("/-", i):
                    depth += 1; out[i] = out[i + 1] = " "; i += 2
                elif src.startswith("-/", i):
                    depth -= 1; out[i] = out[i + 1] = " "; i += 2
                else:
                    if src[i] != "\n":
                        out[i] = " "
                    i += 1
        elif src.startswith("--", i):
            while i < n and src[i] != "\n":
                out[i] = " "; i += 1
        else:
            i += 1
    return "".join(out)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default="lean")
    ap.add_argument("--exclude", action="append", default=[])
    ap.add_argument("--out", default="data/lean_static_audit.json")
    args = ap.parse_args()

    root = Path(args.root)
    files = sorted(p for p in root.glob("*.lean") if p.name not in set(args.exclude or []))
    rows = []
    for p in files:
        code = mask_comments(p.read_text(encoding="utf-8"))
        rows.append({
            "file": p.name,
            "theorem_or_lemma": len(THM.findall(code)),
            "def_or_struct": len(DEF.findall(code)),
            "violations": [w for w in BAD if re.search(r"(?<![\w.])" + w + r"(?![\w])", code)],
        })
    out = {
        "root": str(root),
        "files": len(rows),
        "thm_lem": sum(r["theorem_or_lemma"] for r in rows),
        "def": sum(r["def_or_struct"] for r in rows),
        "violations": [r for r in rows if r["violations"]],
        "rows": rows,
    }
    Path(args.out).parent.mkdir(parents=True, exist_ok=True)
    Path(args.out).write_text(json.dumps(out, ensure_ascii=False, indent=2), encoding="utf-8")
    print(json.dumps({k: out[k] for k in ("root", "files", "thm_lem", "def")}, ensure_ascii=False))
    print("PASS" if not out["violations"] else f"FAIL {out['violations']}")
    return 0 if not out["violations"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
