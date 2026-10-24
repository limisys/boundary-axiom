#!/usr/bin/env python3
"""Deterministic tree Merkle root over a directory.

Definition (v1.1.1)
-------------------
Leaf   L_f = SHA256( b"file" || 0x00 || relpath_utf8 || 0x00 || sha256_hex(content) )
Node       = SHA256( L_i || L_{i+1} ); an odd tail node pairs with itself.
Order      = relpath sorted by UTF-8 bytes (equivalent to LC_ALL=C sort).
Excluded   = ".git" plus any path given after --exclude.

Usage:
    python3 scripts/tree_merkle.py <dir> [--exclude rel/path ...]

Prints one line: the root as lowercase hex.
"""
import hashlib
import os
import sys


def sha(b: bytes) -> bytes:
    return hashlib.sha256(b).digest()


def collect(root: str, excludes) -> list:
    out = []
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d != ".git"]
        for fn in filenames:
            full = os.path.join(dirpath, fn)
            rel = os.path.relpath(full, root).replace(os.sep, "/")
            if any(rel == e or rel.startswith(e + "/") for e in excludes):
                continue
            out.append(rel)
    return sorted(out, key=lambda s: s.encode("utf-8"))


def leaf(root: str, rel: str) -> bytes:
    with open(os.path.join(root, rel), "rb") as fh:
        h = hashlib.sha256(fh.read()).hexdigest().encode()
    return sha(b"file\x00" + rel.encode("utf-8") + b"\x00" + h)


def merkle(leaves) -> str:
    if not leaves:
        raise SystemExit("tree_merkle: no files to hash")
    level = list(leaves)
    while len(level) > 1:
        nxt = []
        for i in range(0, len(level), 2):
            a = level[i]
            b = level[i + 1] if i + 1 < len(level) else level[i]
            nxt.append(sha(a + b))
        level = nxt
    return level[0].hex()


def main(argv) -> int:
    if len(argv) < 2:
        print(__doc__)
        return 2
    root = argv[1]
    excludes = []
    if "--exclude" in argv:
        excludes = argv[argv.index("--exclude") + 1:]
    files = collect(root, excludes)
    print(merkle([leaf(root, r) for r in files]))
    print(f"files={len(files)}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
