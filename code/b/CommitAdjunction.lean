/-
  Copyright 2026 Xueqiang Gao (高学强) · ORCID 0009-0008-3821-3454
  Licensed under the Apache License, Version 2.0 (see LICENSE).
  Original publication source: caseos.cn/research — https://caseos.cn/research/
  First public release 2026-10-09; formal publication 2026-10-20.
  Part of the B-line canonical subset (group 2): 53 files / 417 theorems+lemmas / 77 definitions.
  Attribution header added at publication; proof bodies unchanged.
-/

/-
CommitAdjunction.lean —— `commit` **来自一个伴随**（第 66 轮）

**动机**：第 65 轮（附录 H）自己标出最大的未接之处：
本纲领的芯外闭包 $c=\texttt{commit}$ 只证了**幂等**且 $b$ **不增**，
**未证它来自伴随**——而论文 §3.1 的边界定义是 $\partial=(\mathrm{Fix}(c),b)$，其中 $c=G\circ F$ 由**伴随**诱导。
本轮补上：给出一个**偏序**，使 `commit` 成为该偏序上的**闭包算子**，
于是 Mathlib 的 `ClosureOperator.gi` 直接给出**伴随（Galois 插入）**，
且 `ClosureOperator.closureOperator_gi_self` 给出 $(G\circ F)=c$。

**顺带得到变分结构**（这是靶心 3 的对接点）：

  · **`b_eq_pU_add_two_min`**  $b(x)=p_U(x)+2\min(p_S,p_N)$ —— $b$ 的**新写法**；
  · **`b_antitone`**            $x\preceq y\Rightarrow b(y)\le b(x)$ —— $b$ 是"沉淀序"上的**反单调势**；
  · **`b_min_on_fix`**          在 $\mathrm{Fix}(c)$ 上 $b=p_U$，且这是该序类上的**最小值**。

**一句话**：$b$ 是沉淀序上的一个**势**，被闭包算子 $c$ **单调降低**，且恰在 $\mathrm{Fix}(c)$ 取到下确界 $p_U$。
这把值层的 $b$ 与范畴层的 $\mathrm{Fix}(c)$ **在同一台机器上**接了起来。

0 `sorry` / 0 `axiom`。
-/
import FieldClosure

open scoped Real

namespace CommitAdjunction

open ThreeComponent FieldClosure

/-! ## 一 · "沉淀序"：$p_U$ 相同、表态结果相同，且少数侧更小者为大 -/

/-- **沉淀序**：`x ≼ y` 读作"`y` 比 `x` 更沉淀"。 -/
def SettlesTo (x y : Field) : Prop :=
  x.pU = y.pU ∧ commit x = commit y ∧ min y.pS y.pN ≤ min x.pS x.pN

instance : PartialOrder Field where
  le := SettlesTo
  le_refl := fun x => ⟨rfl, rfl, le_rfl⟩
  le_trans := fun x y z hxy hyz =>
    ⟨hxy.1.trans hyz.1, hxy.2.1.trans hyz.2.1, (hyz.2.2).trans (hxy.2.2)⟩
  le_antisymm := by
    intro x y hxy hyx
    obtain ⟨hu, hc, hm⟩ := hxy
    obtain ⟨hu', hc', hm'⟩ := hyx
    have hmin : min x.pS x.pN = min y.pS y.pN := le_antisymm hm' hm
    have hs : x.pS + x.pN = y.pS + y.pN := by linarith [x.sum, y.sum, hu]
    have hS : (commit x).pS = (commit y).pS := by rw [hc]
    have hN : (commit x).pN = (commit y).pN := by rw [hc]
    obtain ⟨hdx, -⟩ := commit_data x
    obtain ⟨hdy, -⟩ := commit_data y
    rcases hdx with ⟨hlex, eSx, eNx⟩ | ⟨hltx, eSx, eNx⟩ <;>
      rcases hdy with ⟨hley, eSy, eNy⟩ | ⟨hlty, eSy, eNy⟩
    · -- 两支都是"多数 = S"：少数侧 `pN = min`
      have hmx : min x.pS x.pN = x.pN := min_eq_right hlex
      have hmy : min y.pS y.pN = y.pN := min_eq_right hley
      refine Field.ext ?_ ?_ ?_
      · linarith [hs, hmin, hmx, hmy]
      · linarith [hmin, hmx, hmy]
      · linarith [hu]
    · -- x 支 1、y 支 2：两侧和都为零，故同为 `(0,0,pU)`
      have h1 : x.pS + x.pN = 0 := by linarith [hS, eSx, eSy]
      have h2 : y.pS + y.pN = 0 := by linarith [hN, eNx, eNy]
      refine Field.ext ?_ ?_ ?_
      · linarith [h1, h2, x.hS, x.hN, y.hS, y.hN]
      · linarith [h1, h2, x.hS, x.hN, y.hS, y.hN]
      · linarith [hu]
    · -- x 支 2、y 支 1（对称）
      have h1 : x.pS + x.pN = 0 := by linarith [hN, eNx, eNy]
      have h2 : y.pS + y.pN = 0 := by linarith [hS, eSx, eSy]
      refine Field.ext ?_ ?_ ?_
      · linarith [h1, h2, x.hS, x.hN, y.hS, y.hN]
      · linarith [h1, h2, x.hS, x.hN, y.hS, y.hN]
      · linarith [hu]
    · -- 两支都是"多数 = N"：少数侧 `pS = min`
      have hmx : min x.pS x.pN = x.pS := min_eq_left hltx.le
      have hmy : min y.pS y.pN = y.pS := min_eq_left hlty.le
      refine Field.ext ?_ ?_ ?_
      · linarith [hmin, hmx, hmy]
      · linarith [hs, hmin, hmx, hmy]
      · linarith [hu]

/-! ## 二 · `commit` 是闭包算子 -/

/-- 表态后少数侧归零，故两者的较小者为 `0`。 -/
theorem min_commit (x : Field) : min (commit x).pS (commit x).pN = 0 := by
  obtain ⟨hd, -⟩ := commit_data x
  rcases hd with ⟨-, eS, eN⟩ | ⟨-, eS, eN⟩
  · rw [eS, eN, min_eq_right (by linarith [x.hS, x.hN])]
  · rw [eS, eN, min_eq_left (by linarith [x.hS, x.hN])]

/-- **扩张**：`x ≼ commit x`。 -/
theorem le_commit (x : Field) : x ≤ commit x :=
  ⟨(pU_commit x).symm, (commit_idem x).symm, by
    rw [min_commit x]; exact le_min x.hS x.hN⟩

/-- **单调**。 -/
theorem commit_mono {x y : Field} (h : x ≤ y) : commit x ≤ commit y := by
  obtain ⟨hu, hc, -⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [pU_commit, pU_commit, hu]
  · rw [commit_idem, commit_idem, hc]
  · rw [min_commit y, min_commit x]

/-- **`commit` 是 `Field` 上的闭包算子**（该序下）。 -/
noncomputable def commitClosure : ClosureOperator Field where
  toFun := commit
  monotone' := fun _ _ h => commit_mono h
  le_closure' := le_commit
  idempotent' := commit_idem

/-- **（主结果）`commit` 来自一个伴随**：闭包算子 `c` 与其不动点子类型之间有 Galois 插入
（即 $F\dashv G$），且 $G\circ F=c$。 -/
theorem commit_from_adjunction :
    ∃ (β : Type) (_ : PartialOrder β) (F : Field → β) (G : β → Field),
      GaloisConnection F G ∧ ∀ x : Field, G (F x) = commit x := by
  refine ⟨commitClosure.Closeds, inferInstance, commitClosure.toCloseds, (↑), ?_, ?_⟩
  · exact commitClosure.gi.gc
  · intro x
    rfl

/-- 上述伴随**复合回来的闭包算子恰是 `commit`**（即 $G\circ F=c$）。 -/
theorem commit_closure_composite :
    (commitClosure.gi.gc).closureOperator.toFun = commit := rfl

/-! ## 三 · 变分结构：`b` 是新序上的**反单调势** -/

/-- **（新写法）** $b(x)=p_U(x)+2\min(p_S,p_N)$。 -/
theorem b_eq_pU_add_two_min (x : Field) : b x = x.pU + 2 * min x.pS x.pN := by
  have h : b x - x.pU = 2 * min x.pS x.pN := by
    simpa [twoSided] using b_sub_pU_eq_two_min x
  linarith

/-- **反单调**：更沉淀 ⇒ 边界隶属度更小。 -/
theorem b_antitone {x y : Field} (h : x ≤ y) : b y ≤ b x := by
  obtain ⟨hu, -, hm⟩ := h
  rw [b_eq_pU_add_two_min y, b_eq_pU_add_two_min x, hu]
  linarith

/-- **闭包下降**（反单调的直接推论）。 -/
theorem b_commit_le' (x : Field) : b (commit x) ≤ b x := b_antitone (le_commit x)

/-- **势的最小值恰在不动点取到**：在 `Fix(c)` 上 $b=p_U$，且 $p_U$ 是该序类上的下确界。 -/
theorem b_min_on_fix {x : Field} (hx : commit x = x) : b x = x.pU := fix_b_eq_pU hx

/-- **收官**：$b$ 沿沉淀序**反单调**，且其值域的下界 $p_U$ **恰在** $\mathrm{Fix}(c)$ 上取到；
而 $\mathrm{Fix}(c)$ 恰是**单向归属**。值层的 $b$ 与范畴层的 $\mathrm{Fix}(c)$ 由此接在同一台机器上。 -/
theorem b_is_potential_for_closure :
    (∀ x : Field, b (commit x) ≤ b x)
    ∧ (∀ x : Field, commit x = x → b x = x.pU)
    ∧ (∀ x : Field, commit x = x ↔ x.pS = 0 ∨ x.pN = 0) :=
  ⟨b_commit_le', fun _ hx => b_min_on_fix hx, fix_iff_oneSided⟩

end CommitAdjunction
