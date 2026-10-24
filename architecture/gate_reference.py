#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
gate_reference.py —— 边界—自报联合提交协议的有限状态参考实现（v1.1）

只依赖 Python 标准库。它做四件事：
  1. 在有限 Ω 上枚举子集，构造闭包算子、Moore 族、报告算子；
  2. 实现一致性 Gate（R1–R5, R7）与原子提交；
  3. 跑 13 个协议测试（正例、各类拒绝、崩溃、动作闸门、玩具机）；
  4. 在 3 状态玩具机上展示：规范族 Fix(c_I) 是 Moore 族、可被接受；
     逐状态阈值族不是 Moore 族、被 REVIEW。

注意：这是参考实现，不是 Lean 证明，也不是对真实 agent 的验证。
"""

from __future__ import annotations

import itertools
from dataclasses import dataclass
from typing import Callable, Dict, FrozenSet, Iterable, List, Optional, Set, Tuple

SetF = FrozenSet[str]
Family = FrozenSet[SetF]
Closure = Callable[[SetF], SetF]


# ─────────────────────────────────────────────────────────────────────────────
# 一 · 有限集合工具
# ─────────────────────────────────────────────────────────────────────────────

def subsets(universe: Iterable[str]) -> List[SetF]:
    items = tuple(universe)
    out: List[SetF] = []
    for r in range(len(items) + 1):
        for combo in itertools.combinations(items, r):
            out.append(frozenset(combo))
    return out


def is_closure(C: Closure, universe: Iterable[str]) -> bool:
    """扩张、单调、幂等。"""
    subs = subsets(universe)
    for S in subs:
        if not S <= C(S):
            return False
    for S in subs:
        for T in subs:
            if S <= T and not C(S) <= C(T):
                return False
    return all(C(C(S)) == C(S) for S in subs)


def is_moore(R: Family, universe: Iterable[str]) -> bool:
    """Moore 族：含 Ω，且对二元交封闭（有限 Ω 下等价于对任意交封闭）。"""
    top = frozenset(universe)
    if top not in R:
        return False
    for A in R:
        for B in R:
            if (A & B) not in R:
                return False
    return True


def rep_closed(R: Family, S: SetF, universe: Iterable[str]) -> SetF:
    """c_R(S) = ⋂{T ⊇ S : T ∈ R}；空族取 Ω。"""
    fam = [T for T in R if S <= T]
    if not fam:
        return frozenset(universe)
    out = fam[0]
    for T in fam[1:]:
        out = out & T
    return out


def closure_from_interventions(interventions: Iterable[Dict[str, str]],
                               universe: Iterable[str]) -> Closure:
    maps = tuple(interventions)
    subs = subsets(universe)

    def invariant(S: SetF) -> bool:
        return all(frozenset(m[x] for x in S) <= S for m in maps)

    def C(S: SetF) -> SetF:
        fam = [T for T in subs if S <= T and invariant(T)]
        out = fam[0]
        for T in fam[1:]:
            out = out & T
        return out

    return C


def fix_family(C: Closure, universe: Iterable[str]) -> Family:
    return frozenset(S for S in subsets(universe) if C(S) == S)


# ─────────────────────────────────────────────────────────────────────────────
# 二 · Bundle、Gate、Store
# ─────────────────────────────────────────────────────────────────────────────

@dataclass(frozen=True)
class Bundle:
    version: int
    state: SetF
    C: Closure
    R: Family
    report: SetF
    evidence_version: int
    certificate_ok: bool
    parent: Optional[str]


@dataclass(frozen=True)
class Verdict:
    accepted: bool
    codes: Tuple[str, ...]
    reason: str


def gate(bundle: Bundle, universe: Iterable[str], head: Optional[str]) -> Verdict:
    codes: List[str] = []
    if not is_closure(bundle.C, universe):
        codes.append("R1:not-a-closure-operator")
    if not is_moore(bundle.R, universe):
        codes.append("R2:not-a-moore-family")
    if any(rep_closed(bundle.R, S, universe) != bundle.C(S) for S in subsets(universe)):
        codes.append("R3:c_R != C")
    if bundle.report not in bundle.R:
        codes.append("R4:report-not-in-R")
    if bundle.evidence_version != bundle.version or not bundle.certificate_ok:
        codes.append("R5:version-or-evidence-mismatch")
    if bundle.parent != head:
        codes.append("R7:parent-mismatch")

    if not codes:
        return Verdict(True, (), "ACCEPT")
    # R2 / R5 是“前件/证据不足” → REVIEW；其余是结构非法 → REJECT
    review_only = all(c.startswith(("R2:", "R5:")) for c in codes)
    return Verdict(False, tuple(codes), "REVIEW" if review_only else "REJECT")


def gate_candidates(candidates: List[Bundle], universe: Iterable[str],
                    head: Optional[str]) -> Verdict:
    """R6 wrapper: exactly one candidate. Zero/multiple -> REVIEW."""
    if len(candidates) != 1:
        return Verdict(False, ("R6:candidate-count",), "REVIEW")
    return gate(candidates[0], universe, head)


class Store:
    def __init__(self) -> None:
        self.head: Optional[str] = None
        self.committed: Dict[int, Bundle] = {}
        self._next_hash = 0

    def _hash(self) -> str:
        self._next_hash += 1
        return f"h{self._next_hash:04d}"

    def commit(self, bundle: Bundle, universe: Iterable[str]) -> Verdict:
        v = gate(bundle, universe, self.head)
        if not v.accepted:
            return v
        # 事务：先构造新快照，成功后一次性替换 head
        new_head = self._hash()
        new_committed = dict(self.committed)
        new_committed[bundle.version] = bundle
        self.committed = new_committed
        self.head = new_head
        return v

    def crash_commit(self, bundle: Bundle, universe: Iterable[str]) -> None:
        """模拟提交事务在写入前失败：head 与 committed 都不变。"""
        v = gate(bundle, universe, self.head)
        if not v.accepted:
            return
        raise RuntimeError("simulated crash before atomic swap")


def action_gate(action: Dict[str, object], bundle: Bundle) -> str:
    if action.get("required_version") != bundle.version:
        return "DENY:stale-action"
    if not bundle.certificate_ok:
        return "DENY:no-certificate"
    target = action.get("target")
    if not isinstance(target, frozenset):
        return "DENY:bad-target"
    if not target <= bundle.C(bundle.state):
        return "DENY:leaves-boundary"
    return "ALLOW"


# ─────────────────────────────────────────────────────────────────────────────
# 三 · 测试
# ─────────────────────────────────────────────────────────────────────────────

def main() -> int:
    passed = 0
    total = 0

    def check(name: str, cond: bool, detail: str = "") -> None:
        nonlocal passed, total
        total += 1
        if cond:
            passed += 1
            print(f"  PASS  {name}")
        else:
            print(f"  FAIL  {name}  {detail}")

    # ── 3.1 正例：Ω={a,b}，R={∅,{a},{a,b}}（Moore）
    U2 = ("a", "b")
    R2 = frozenset({frozenset(), frozenset({"a"}), frozenset({"a", "b"})})
    C2 = lambda S: rep_closed(R2, S, U2)
    store = Store()
    good = Bundle(1, frozenset({"a"}), C2, R2, frozenset({"a"}), 1, True, store.head)
    v = store.commit(good, U2)
    check("G1 positive bundle ACCEPT + commit", v.accepted and store.head is not None, str(v))
    check("G1 R is Moore and c_R=C", is_moore(R2, U2) and is_closure(C2, U2))

    # ── 3.2 R2：非 Moore（缺 Ω）
    R_bad = frozenset({frozenset(), frozenset({"a"})})
    C_bad = lambda S: rep_closed(R_bad, S, U2)
    b2 = Bundle(2, frozenset({"a"}), C_bad, R_bad, frozenset({"a"}), 2, True, store.head)
    v2 = gate(b2, U2, store.head)
    check("G2 non-Moore -> REVIEW(R2)", (not v2.accepted) and any(c.startswith("R2") for c in v2.codes), str(v2))

    # ── 3.3 R1：C 不是闭包算子（常值 ∅）
    C_bad1: Closure = lambda S: frozenset()
    b3 = Bundle(3, frozenset({"a"}), C_bad1, R2, frozenset({"a"}), 3, True, store.head)
    v3 = gate(b3, U2, store.head)
    check("G3 non-closure -> REJECT(R1)", (not v3.accepted) and any(c.startswith("R1") for c in v3.codes), str(v3))

    # ── 3.4 R3：C 是闭包算子但 c_R != C（恒等）
    C_id: Closure = lambda S: S
    b4 = Bundle(4, frozenset({"a"}), C_id, R2, frozenset({"a"}), 4, True, store.head)
    v4 = gate(b4, U2, store.head)
    check("G4 c_R != C -> REJECT(R3)", (not v4.accepted) and any(c.startswith("R3") for c in v4.codes), str(v4))

    # ── 3.5 R4：report 不在 R
    b5 = Bundle(5, frozenset({"a"}), C2, R2, frozenset({"b"}), 5, True, store.head)
    v5 = gate(b5, U2, store.head)
    check("G5 report outside R -> REJECT(R4)", (not v5.accepted) and any(c.startswith("R4") for c in v5.codes), str(v5))

    # ── 3.6 R5：证据版本不一致
    b6 = Bundle(6, frozenset({"a"}), C2, R2, frozenset({"a"}), 5, True, store.head)
    v6 = gate(b6, U2, store.head)
    check("G6 version mismatch -> REVIEW(R5)", (not v6.accepted) and any(c.startswith("R5") for c in v6.codes), str(v6))

    # ── 3.7 R7：父哈希不匹配
    b7 = Bundle(7, frozenset({"a"}), C2, R2, frozenset({"a"}), 7, True, "deadbeef")
    v7 = gate(b7, U2, store.head)
    check("G7 parent mismatch -> REJECT(R7)", (not v7.accepted) and any(c.startswith("R7") for c in v7.codes), str(v7))

    # ── 3.7b R6：候选数不是 1 -> REVIEW
    v6a = gate_candidates([], U2, None)
    v6b = gate_candidates([good, good], U2, None)
    v6c = gate_candidates([good], U2, None)
    check("G7b R6 zero/multiple -> REVIEW, one -> ACCEPT",
          (not v6a.accepted) and any(c.startswith("R6") for c in v6a.codes)
          and (not v6b.accepted) and any(c.startswith("R6") for c in v6b.codes)
          and v6c.accepted,
          f"{v6a}/{v6b}/{v6c}")

    # ── 3.8 崩溃注入：提交前失败，head 不变
    before = store.head
    b8 = Bundle(8, frozenset({"a"}), C2, R2, frozenset({"a"}), 8, True, before)
    try:
        store.crash_commit(b8, U2)
    except RuntimeError:
        pass
    check("G8 crash -> no partial commit", store.head == before and 8 not in store.committed)

    # ── 3.9 动作闸门
    allowed = action_gate({"required_version": good.version, "target": frozenset({"a"})}, good)
    stale = action_gate({"required_version": 999, "target": frozenset({"a"})}, good)
    outside = action_gate({"required_version": good.version, "target": frozenset({"b"})}, good)
    check("G9 action gate ALLOW/DENY", allowed == "ALLOW" and stale.startswith("DENY") and outside.startswith("DENY"),
          f"{allowed}/{stale}/{outside}")

    # ── 3.10 3 状态玩具机：规范族 Moore；阈值族非 Moore
    STATES = ("self", "external", "unknown")
    INTERVENTIONS = [
        {"self": "self", "external": "external", "unknown": "unknown"},
        {"self": "unknown", "external": "unknown", "unknown": "unknown"},
        {"self": "external", "external": "external", "unknown": "unknown"},
        {"self": "unknown", "external": "unknown", "unknown": "unknown"},
    ]
    C = closure_from_interventions(INTERVENTIONS, STATES)
    Fix = fix_family(C, STATES)
    top = frozenset(STATES)
    threshold = frozenset({frozenset(), frozenset({"self"})})

    toy_store = Store()
    b_fix = Bundle(1, frozenset({"self"}), C, Fix, C(frozenset({"self"})), 1, True, toy_store.head)
    v_fix = gate(b_fix, STATES, toy_store.head)
    b_thr = Bundle(1, frozenset({"self"}), C, threshold, frozenset({"self"}), 1, True, toy_store.head)
    v_thr = gate(b_thr, STATES, toy_store.head)

    check("G10 canon Fix(c_I) is Moore and ACCEPT",
          is_moore(Fix, STATES) and v_fix.accepted, f"moore={is_moore(Fix, STATES)} verdict={v_fix}")
    check("G11 threshold family is not Moore -> REVIEW",
          (not is_moore(threshold, STATES)) and (not v_thr.accepted) and any(c.startswith("R2") for c in v_thr.codes),
          str(v_thr))
    check("G12 threshold Fix(c_R) = threshold ∪ {Ω}",
          fix_family(lambda S: rep_closed(threshold, S, STATES), STATES) == threshold | {top})

    print(f"\nRESULT: {passed}/{total} protocol tests passed")
    print(f"PASS: {passed}/{total} protocol tests" if passed == total else "FAIL")
    return 0 if passed == total else 1


if __name__ == "__main__":
    raise SystemExit(main())
