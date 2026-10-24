#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""audit_cited_names.py —— **被引定理名存在性审计**（第 144 轮 · DSH）

**为什么需要它**：既有脚本检查的是"文件里有没有 `sorry`／`axiom`"（`check_no_sorry.py`）、
"一篇稿件的计数是否与开发体一致"（`verify_manuscript_counts.py`）、
"**某一篇**稿件的主张索引是否可定位"（`verify_claim_index.py`）、"引文是否越级"（`verify_citations.py`）。
**没有一条**检查：**散落在几十篇研究记录里的 `Module.theorem` 形式引用，是否真的存在于源码。**
而本线对外材料的承重结构正是「某条主张 ↔ 某个机检名」——引用一个不存在的定理名是最贵的错误。

**索引范围（三处，缺一则误报）**：
  1. `--lean-dir`（默认本仓 `lean/`）的开发体；
  2. `--caus`（默认本仓 `vendor/CausModel`）的**冻结范畴层**——`CausModel.*` 在此；
  3. **mathlib 白名单**（外部库不索引，用已知命名空间前缀排除，避免把 mathlib 名字误报为"不存在"）。

**判定**：只把"**裸名也不在任何一处源码里**"判为 ❌；把"裸名在、限定前缀未见"判为 🟡（人工看）。

用法：
    python3 audit_cited_names.py <被引文件或目录> [...] [--lean-dir=DIR] [--caus=DIR]
退出码：0 = 无 ❌；1 = 有 ❌。
"""
import re, sys, os, glob

DECL = re.compile(r'^\s*(?:noncomputable\s+|private\s+|protected\s+)*'
                  r'(?:theorem|lemma|def|abbrev|structure|instance)\s+([A-Za-z_][\w\'.]*)', re.M)
NS = re.compile(r'^\s*namespace\s+([A-Za-z_][\w.]*)', re.M)
CITED = re.compile(r'\b([A-Z][A-Za-z0-9_]*\.[a-z][A-Za-z0-9_\']*)\b')

# 外部库命名空间：不索引，直接放行（避免误报）
MATHLIB_NS = {
    'Adjunction', 'Asymptotics', 'Filter', 'Finset', 'GaloisConnection', 'ClosureOperator',
    'EventuallyEq', 'IntegrableAtFilter', 'LocallyIntegrable', 'Set', 'Real', 'Nat', 'Int',
    'Order', 'Icc', 'Monotone', 'Metric', 'Continuous', 'Measurable', 'Fintype', 'List',
    'Function', 'Subtype', 'Equiv', 'CategoryTheory', 'TopologicalSpace', 'Filter', 'ENNReal',
}
# 明显不是定理的（文件名／URL／路径）
FILEISH = re.compile(r'\.(lean|olean|ilean|md|txt|html|py|m|json|yaml|yml|mat|tgz|atom|log|csv|tsv|pdf|tex|sh|toml)$')

# **审计记录里"故意引用错误名"的白名单**：审计件必须能写出它查出的错名，否则无法留痕。
# 这些名字**经核实不存在**，此处放行**仅**为了避免"审计件因记录错误而被自己的工具判失败"。
# 新增白名单必须附：错名 + 正确名 + 查出它的审计件编号。
KNOWN_BAD_QUOTED = {
    'ClosureGauge.c':          '正确名 SharpnessClosure.c（`139` 查出）',
    'RelaxRobust.recovery_time': '正确名 LevelDynamics.recovery_time（`139` 查出）',
}


def strip_comments(s: str) -> str:
    out, i, depth = [], 0, 0
    while i < len(s):
        if depth == 0 and s.startswith('/-', i):
            depth += 1; i += 2; continue
        if depth == 0 and s.startswith('--', i):
            j = s.find('\n', i); i = len(s) if j < 0 else j; continue
        if depth > 0:
            if s.startswith('/-', i):
                depth += 1; i += 2; continue
            if s.startswith('-/', i):
                depth -= 1; i += 2; continue
            i += 1; continue
        out.append(s[i]); i += 1
    return ''.join(out)


def index_dir(d, full, bare):
    n_files = 0
    for f in glob.glob(os.path.join(d, '**', '*.lean'), recursive=True):
        if os.path.basename(f).startswith('.'):
            continue          # 隐藏件（如 .DimensionAlgebra_v1_failed.lean）不入索引
        n_files += 1
        code = strip_comments(open(f, encoding='utf-8').read())
        nss = NS.findall(code)
        for n in DECL.findall(code):
            bare.add(n.split('.')[-1])
            full.add(n)
            for ns in nss:
                full.add(ns + '.' + n)
    return n_files


def main() -> int:
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    here = os.path.dirname(os.path.abspath(__file__))
    root = os.path.dirname(here)
    lean_dir = next((a.split('=', 1)[1] for a in sys.argv[1:] if a.startswith('--lean-dir=')),
                    os.path.join(root, 'lean'))
    caus = next((a.split('=', 1)[1] for a in sys.argv[1:] if a.startswith('--caus=')),
                os.path.join(root, 'vendor', 'CausModel'))
    extra = [a.split('=', 1)[1] for a in sys.argv[1:] if a.startswith('--extra=')]
    if not args:
        print(__doc__); return 2

    full, bare = set(), set()
    n1 = index_dir(lean_dir, full, bare)
    n2 = index_dir(caus, full, bare) if os.path.isdir(caus) else 0
    n3 = sum(index_dir(d, full, bare) for d in extra if os.path.isdir(d))
    print(f'索引：开发体 {n1} 文件 ＋ 冻结范畴层 {n2} 文件 ＋ 外部源 {n3} 文件 '
          f'⇒ 限定名 {len(full)} / 裸名 {len(bare)}\n')

    targets = []
    for a in args:
        targets += (sorted(glob.glob(os.path.join(a, '**', '*.md'), recursive=True))
                    if os.path.isdir(a) else [a])

    missing, soft = {}, {}
    for t in targets:
        try:
            txt = open(t, encoding='utf-8').read()
        except OSError:
            continue
        for m in set(CITED.findall(txt)):
            ns = m.split('.')[0]
            if ns in MATHLIB_NS or FILEISH.search(m) or m in KNOWN_BAD_QUOTED:
                continue
            if m in full:
                continue
            (soft if m.split('.')[-1] in bare else missing).setdefault(m, set()).add(os.path.basename(t))

    print(f'扫描 {len(targets)} 个文件\n')
    print(f'❌ 完全找不到（裸名也不在开发体／范畴层）: {len(missing)}')
    for k in sorted(missing):
        print(f'   {k:48s} ← {", ".join(sorted(missing[k])[:3])}')
    print(f'\n🟡 裸名存在、限定前缀未在源码出现（多为跨文件命名空间写法，人工看）: {len(soft)}')
    for k in sorted(soft):
        print(f'   {k:48s} ← {", ".join(sorted(soft[k])[:3])}')
    return 1 if missing else 0


if __name__ == '__main__':
    sys.exit(main())
