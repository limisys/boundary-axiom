/-
  Copyright 2026 Xueqiang Gao (高学强) · ORCID 0009-0008-3821-3454
  Licensed under the Apache License, Version 2.0 (see LICENSE).
  Original publication source: caseos.cn/research — https://caseos.cn/research/
  First public release 2026-10-09; formal publication 2026-10-20.
  Part of the B-line canonical subset (group 2): 53 files / 417 theorems+lemmas / 77 definitions.
  Attribution header added at publication; proof bodies unchanged.
-/

/-
LanguageStrict.lean —— §5 那条对照的**严格性判据**（第 76 轮）

**动机**：论文 §5 的可检验对照目前只写成**弱不等式**：
"干预族扩充 ⇒ 刚性面收缩、模糊区扩大"。严谨读者立刻会问：
**什么时候严格？**——而弱不等式**不能被证伪**（相等也满足它），所以这条对照目前**还不是一条可检验的预言**。

本轮给出**严格性判据**：把"严格"归结为一条**具体的见证**。

**主结果**（设 $c_1\le c_2$ 逐点）：

  · **`rigid_ssubset_iff`**  $\mathrm{Fix}(c_2)\subsetneq\mathrm{Fix}(c_1)$
    $\iff$ **存在** $x$ 使"$c_1$ 已决而 $c_2$ 未决"（$c_1x=x\ \wedge\ c_2x\ne x$）；
  · **`fuzzy_ssubset_iff`**  同一见证 $\iff$ 模糊区**严格**扩大；
  · **`no_witness_iff_fuzzy_eq`** **不存在**见证 $\iff$ 两族的模糊区**完全相同**
    （即**对照在经验上落空**）；
  · **`fuzzy_card_lt_iff`**（有限状态空间） 基数**严格**增大 $\iff$ 存在该见证。

**所以 §5 的可证伪形式是**：
> 在语言密集域中存在一个状态，**身体干预把它判定为已决，而语言干预不**——
> 若这样的状态**不存在**，则"语言已进入判据"在本框架内**落空**。

这比"模糊区更大"**强得多**：它给出了一个**具体的、可去数一数的**目标，而不是一个不等式。

0 `sorry` / 0 `axiom`。复用 `LanguageInterventions` 的 `fixedPoints_antitone`（不重复声明）。
-/
import LanguageInterventions

open ClosureOperator

namespace LanguageStrict

open LanguageInterventions

variable {α : Type*}

/-- **见证**：一个状态，被 $c_1$ 判定为已决，却被 $c_2$ 推得更远。 -/
def Witness (c₁ c₂ : α → α) : Prop := ∃ x : α, c₁ x = x ∧ c₂ x ≠ x

/-- **（主结果一）** 刚性面**严格**收缩 $\iff$ 存在见证。 -/
theorem rigid_ssubset_iff [PartialOrder α] (c₁ c₂ : ClosureOperator α)
    (h : ∀ x, c₁ x ≤ c₂ x) :
    {x : α | c₂ x = x} ⊂ {x : α | c₁ x = x} ↔ Witness c₁ c₂ := by
  constructor
  · intro hss
    rw [Set.ssubset_iff_exists] at hss
    obtain ⟨-, x, hxt, hxs⟩ := hss
    exact ⟨x, hxt, by simpa using hxs⟩
  · rintro ⟨x, h1, h2⟩
    rw [Set.ssubset_iff_exists]
    exact ⟨fun y hy => fixedPoints_antitone c₁ c₂ h hy, x, h1, by simpa using h2⟩

/-- **（主结果二）** 模糊区**严格**扩大 $\iff$ 存在同一个见证。 -/
theorem fuzzy_ssubset_iff [PartialOrder α] (c₁ c₂ : ClosureOperator α)
    (h : ∀ x, c₁ x ≤ c₂ x) :
    {x : α | c₁ x ≠ x} ⊂ {x : α | c₂ x ≠ x} ↔ Witness c₁ c₂ := by
  constructor
  · intro hss
    rw [Set.ssubset_iff_exists] at hss
    obtain ⟨-, x, hxt, hxs⟩ := hss
    exact ⟨x, by simpa using hxs, hxt⟩
  · rintro ⟨x, h1, h2⟩
    rw [Set.ssubset_iff_exists]
    refine ⟨?_, x, h2, ?_⟩
    · intro y hy
      simp only [Set.mem_ofPred_eq] at hy ⊢
      intro hy2
      exact hy (fixedPoints_antitone c₁ c₂ h hy2)
    · simp only [Set.mem_ofPred_eq]; exact fun hh => hh h1

/-- **（主结果三 · 对照落空判据）** **不存在**见证 $\iff$ 两族的模糊区**完全相同**。
即：若没有"身体已决而语言未决"的状态，则 §5 的对照**在经验上落空**。 -/
theorem no_witness_iff_fuzzy_eq [PartialOrder α] (c₁ c₂ : ClosureOperator α)
    (h : ∀ x, c₁ x ≤ c₂ x) :
    (¬ Witness c₁ c₂) ↔ {x : α | c₁ x ≠ x} = {x : α | c₂ x ≠ x} := by
  constructor
  · intro hno
    ext y
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro hy hy2
      exact hy (fixedPoints_antitone c₁ c₂ h hy2)
    · intro hy hy1
      exact hno ⟨y, hy1, hy⟩
  · rintro heq ⟨x, h1, h2⟩
    have hne : c₁ x ≠ x := by
      have hmem : x ∈ ({y : α | c₁ y ≠ y} : Set α) := by rw [heq]; exact h2
      exact hmem
    exact hne h1

/-- **（主结果四 · 有限情形）** 模糊区的**基数严格增大** $\iff$ 存在见证。
——这使 §5 的对照成为一条**可数出来**的预言。 -/
theorem fuzzy_card_lt_iff [Fintype α] [PartialOrder α] [DecidableEq α]
    (c₁ c₂ : ClosureOperator α) (h : ∀ x, c₁ x ≤ c₂ x) :
    (Finset.univ.filter (fun x => c₁ x ≠ x)).card
        < (Finset.univ.filter (fun x => c₂ x ≠ x)).card
      ↔ Witness c₁ c₂ := by
  constructor
  · intro hlt
    by_contra hno
    have heq : Finset.univ.filter (fun x => c₁ x ≠ x)
        = Finset.univ.filter (fun x => c₂ x ≠ x) := by
      apply Finset.ext
      intro x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h1 h2
        exact h1 (fixedPoints_antitone c₁ c₂ h h2)
      · intro h2 h1
        exact hno ⟨x, h1, h2⟩
    rw [heq] at hlt
    exact absurd hlt (lt_irrefl _)
  · rintro ⟨x, h1, h2⟩
    have hsub : Finset.univ.filter (fun y => c₁ y ≠ y)
        ⊆ Finset.univ.filter (fun y => c₂ y ≠ y) := by
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      intro hy2
      exact hy (fixedPoints_antitone c₁ c₂ h hy2)
    have hne : Finset.univ.filter (fun y => c₁ y ≠ y)
        ≠ Finset.univ.filter (fun y => c₂ y ≠ y) := by
      intro heq
      have hx2 : x ∈ Finset.univ.filter (fun y => c₂ y ≠ y) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h2
      have hx1 : x ∈ Finset.univ.filter (fun y => c₁ y ≠ y) := by rw [heq]; exact hx2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx1
      exact hx1 h1
    exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)

/-- **（收官）** §5 的**可证伪形式**：两族的刚性面/模糊区**严格**分离，
当且仅当存在一个"身体已决而语言未决"的状态。 -/
theorem contrast_is_sharp [PartialOrder α] (c₁ c₂ : ClosureOperator α)
    (h : ∀ x, c₁ x ≤ c₂ x) :
    (Witness c₁ c₂)
      ↔ ({x : α | c₂ x = x} ⊂ {x : α | c₁ x = x}
        ∧ {x : α | c₁ x ≠ x} ⊂ {x : α | c₂ x ≠ x}) :=
  ⟨fun hw => ⟨(rigid_ssubset_iff c₁ c₂ h).mpr hw, (fuzzy_ssubset_iff c₁ c₂ h).mpr hw⟩,
   fun ⟨hr, _⟩ => (rigid_ssubset_iff c₁ c₂ h).mp hr⟩

end LanguageStrict
