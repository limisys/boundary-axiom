#!/usr/bin/env python3
"""claim_index.py —— 把 claims.yaml 的每条 formalized 主张解析到 Lean 声明。

用法：python3 scripts/claim_index.py --root lean --claims docs/claims.yaml \
        --out data/claim_index.json [--check]
--check：任一 formalized 主张的定理找不到 → 非零退出。
"""
import argparse
import json
import re
import sys
from pathlib import Path

import yaml

DECL = re.compile(
    r"^[ \t]*(?:noncomputable[ \t]+|private[ \t]+|protected[ \t]+)*"
    r"(?:theorem|lemma|def|abbrev|structure|instance)[ \t]+([A-Za-z_][A-Za-z0-9_']*)",
    re.M,
)


def mask_comments(src: str) -> str:
    """Replace comment characters with spaces, preserving length and newlines,
    so that regex offsets map back to raw-file line numbers."""
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
                    if src[i] != "\n": out[i] = " "
                    i += 1
        elif src.startswith("--", i):
            while i < n and src[i] != "\n":
                out[i] = " "; i += 1
        else:
            i += 1
    return "".join(out)


def build_index(root: Path):
    index = {}
    for p in sorted(root.glob("*.lean")):
        code = mask_comments(p.read_text(encoding="utf-8"))
        for m in DECL.finditer(code):
            name = m.group(1)
            line = code[: m.start()].count("\n") + 1
            index.setdefault(name, []).append({"file": p.name, "line": line})
    return index


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default="lean")
    ap.add_argument("--claims", default="docs/claims.yaml")
    ap.add_argument("--out")
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()

    root = Path(args.root)
    claims = yaml.safe_load(Path(args.claims).read_text(encoding="utf-8"))["claims"]
    index = build_index(root)

    rows, missing = [], []
    for c in claims:
        should = c.get("state") == "formalized"
        names = [n.strip() for n in str(c.get("theorem") or "").split(",") if n.strip()]
        for full in names:
            short = full.split(".")[-1]
            hits = index.get(short)
            if hits:
                rows.append({"claim": c["id"], "theorem": full, "resolved": hits[0]})
            elif should:
                missing.append((c["id"], full))

    out = {
        "claims_file": args.claims,
        "formalized_claims": sum(1 for c in claims if c.get("state") == "formalized"),
        "resolved": rows,
        "missing": [{"claim": cid, "theorem": t} for cid, t in missing],
    }
    if args.out:
        Path(args.out).parent.mkdir(parents=True, exist_ok=True)
        Path(args.out).write_text(json.dumps(out, ensure_ascii=False, indent=2), encoding="utf-8")

    for r in rows:
        print(f"{r['claim']:5s} {r['theorem']:55s} -> {r['resolved']['file']}:{r['resolved']['line']}")
    if missing:
        print("MISSING:", missing)
        return 1
    print(f"PASS {len(rows)} theorem references resolved")
    return 0


if __name__ == "__main__":
    sys.exit(main())
