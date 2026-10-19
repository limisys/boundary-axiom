/-
  Copyright 2026 Xueqiang Gao (高学强) · ORCID 0009-0008-3821-3454
  Licensed under the Apache License, Version 2.0 (see LICENSE).
  Original publication source: caseos.cn/research — https://caseos.cn/research/
  First public release 2026-10-09; formal publication 2026-10-20.
  Part of the B-line canonical subset (group 2): 53 files / 417 theorems+lemmas / 77 definitions.
  Attribution header added at publication; proof bodies unchanged.
-/

/-
ComparabilityMatters.lean —— 那两条判据**共享的隐含假设**，及去掉它的反例（第 81 轮）

**动机**：第 80 轮发现纲领面向经验的两条最硬的断言共享同一个谓词：

  · **§5（语言线）**：见证＝"**身体已决而语言未决**"；
  · **推论 C（$\\sigma$ 线）**：判别＝"**旧闭包未决而新闭包已决**"。

两者都归结为 `rigid_ssubset_iff`，而该定理有一条**显式假设**：$c_1\\le c_2$ **逐点**
（一族比另一族推得更远）。该假设在 §5 里**写明了**（语言族扩充身体族）；
但在**推论 C 的文字表述**里**只隐含**（"新极性"默认推得**更多**）。

本轮问：**去掉这条假设会怎样？** 答案：**两条判据都不再成立**，且以最尖锐的方式失效——
`Witness` 可以**同时**在两个方向成立。

**结果**（在 `Set (Fin 2)` 上取 $c_1X=X\\cup\\{0\\}$、$c_2X=X\\cup\\{1\\}$）：

  · `fix_c₁`／`fix_c₂`   不动点集分别为 $\\{X:\\{0\\}\\subseteq X\\}$ 与 $\\{X:\\{1\\}\\subseteq X\\}$；
  · **`fix_incomparable`** 两个不动点集**互不包含**；
  · **`witness_both_ways`** `Witness c₁ c₂` **且** `Witness c₂ c₁` **同时成立**；
  · **`comparability_essential`** 故：**没有可比性，`Witness` 就不再"指出哪一族更大"**——
    而"哪一族更大"正是两条判据要判定的东西。

**结论**：§5 与推论 C 的判据**必须写明可比性**；§5 已写明，**推论 C 应补上**。

0 `sorry` / 0 `axiom`。
-/
import LanguageStrict
import LocusVsBoundary

open scoped Real

namespace ComparabilityMatters

open LanguageStrict

/-! ## 一 · 两个"互不包含"的闭包算子 -/

/-- `c₁ X = X ∪ {0}`（把 `0` 补进去）。 -/
noncomputable def c₁ : ClosureOperator (Set (Fin 2)) where
  toFun X := X ∪ ({0} : Set (Fin 2))
  monotone' := fun _ _ h => Set.union_subset_union h subset_rfl
  le_closure' := fun X => Set.subset_union_left
  idempotent' := fun X => by
    show X ∪ {0} ∪ {0} = X ∪ {0}
    rw [Set.union_assoc, Set.union_self]

/-- `c₂ X = X ∪ {1}`（把 `1` 补进去）。 -/
noncomputable def c₂ : ClosureOperator (Set (Fin 2)) where
  toFun X := X ∪ ({1} : Set (Fin 2))
  monotone' := fun _ _ h => Set.union_subset_union h subset_rfl
  le_closure' := fun X => Set.subset_union_left
  idempotent' := fun X => by
    show X ∪ {1} ∪ {1} = X ∪ {1}
    rw [Set.union_assoc, Set.union_self]

theorem fix_c₁ :
    LocusVsBoundary.Fix c₁ = {X : Set (Fin 2) | ({0} : Set (Fin 2)) ⊆ X} := by
  ext X
  simp only [LocusVsBoundary.Fix, Set.mem_ofPred_eq]
  change X ∪ ({0} : Set (Fin 2)) = X ↔ ({0} : Set (Fin 2)) ⊆ X
  exact Set.union_eq_left

theorem fix_c₂ :
    LocusVsBoundary.Fix c₂ = {X : Set (Fin 2) | ({1} : Set (Fin 2)) ⊆ X} := by
  ext X
  simp only [LocusVsBoundary.Fix, Set.mem_ofPred_eq]
  change X ∪ ({1} : Set (Fin 2)) = X ↔ ({1} : Set (Fin 2)) ⊆ X
  exact Set.union_eq_left

/-- **（互不包含）** 两个不动点集**互不包含**。 -/
theorem fix_incomparable :
    ¬ (LocusVsBoundary.Fix c₁ ⊂ LocusVsBoundary.Fix c₂)
      ∧ ¬ (LocusVsBoundary.Fix c₂ ⊂ LocusVsBoundary.Fix c₁) := by
  constructor
  · intro h
    have hmem : ({0} : Set (Fin 2)) ∈ LocusVsBoundary.Fix c₁ := by
      rw [fix_c₁]; simp
    have hnot : ({0} : Set (Fin 2)) ∉ LocusVsBoundary.Fix c₂ := by
      rw [fix_c₂]
      intro hh
      have h1 : (1 : Fin 2) ∈ ({0} : Set (Fin 2)) := hh (by simp)
      simp at h1
    exact hnot (h.1 hmem)
  · intro h
    have hmem : ({1} : Set (Fin 2)) ∈ LocusVsBoundary.Fix c₂ := by
      rw [fix_c₂]; simp
    have hnot : ({1} : Set (Fin 2)) ∉ LocusVsBoundary.Fix c₁ := by
      rw [fix_c₁]
      intro hh
      have h1 : (0 : Fin 2) ∈ ({1} : Set (Fin 2)) := hh (by simp)
      simp at h1
    exact hnot (h.1 hmem)

/-- **（两个方向同时成立）** `Witness c₁ c₂` 与 `Witness c₂ c₁` **同时为真**——
见证**不再指示"哪一族更大"**。 -/
theorem witness_both_ways : Witness c₁ c₂ ∧ Witness c₂ c₁ := by
  constructor
  · refine ⟨{0}, ?_, ?_⟩
    · show ({0} : Set (Fin 2)) ∪ {0} = {0}
      rw [Set.union_self]
    · intro h
      have h1 : ({0} : Set (Fin 2)) ∪ {1} = {0} := h
      have h2 : (1 : Fin 2) ∈ ({0} : Set (Fin 2)) := by
        rw [← h1]; simp
      simp at h2
  · refine ⟨{1}, ?_, ?_⟩
    · show ({1} : Set (Fin 2)) ∪ {1} = {1}
      rw [Set.union_self]
    · intro h
      have h1 : ({1} : Set (Fin 2)) ∪ {0} = {1} := h
      have h2 : (0 : Fin 2) ∈ ({1} : Set (Fin 2)) := by
        rw [← h1]; simp
      simp at h2

/-! ## 二 · 收官：可比性是**必需的** -/

/-- **（可比性必需）** 去掉逐点可比假设后，两条判据所依赖的等价**不再成立**：
此处 `Witness` 两个方向都为真，而两个"严格包含"**都为假**。
故 §5 与推论 C 的判据**必须写明可比性**；§5 已写明，**推论 C 应补上**。 -/
theorem comparability_essential :
    Witness c₁ c₂ ∧ Witness c₂ c₁
      ∧ ¬ (LocusVsBoundary.Fix c₁ ⊂ LocusVsBoundary.Fix c₂)
      ∧ ¬ (LocusVsBoundary.Fix c₂ ⊂ LocusVsBoundary.Fix c₁) :=
  ⟨witness_both_ways.1, witness_both_ways.2, fix_incomparable.1, fix_incomparable.2⟩

/-- 两个算子本身也**互不支配**（`c₁ ≰ c₂` 且 `c₂ ≰ c₁`）。 -/
theorem operators_incomparable :
    ¬ (∀ X, c₁ X ≤ c₂ X) ∧ ¬ (∀ X, c₂ X ≤ c₁ X) := by
  constructor
  · intro h
    have h1 : (0 : Fin 2) ∈ c₁ ({1} : Set (Fin 2)) := by
      show (0 : Fin 2) ∈ ({1} : Set (Fin 2)) ∪ {0}
      simp
    have h2 : (0 : Fin 2) ∉ c₂ ({1} : Set (Fin 2)) := by
      show (0 : Fin 2) ∉ ({1} : Set (Fin 2)) ∪ {1}
      simp
    exact h2 (h ({1} : Set (Fin 2)) h1)
  · intro h
    have h1 : (1 : Fin 2) ∈ c₂ ({0} : Set (Fin 2)) := by
      show (1 : Fin 2) ∈ ({0} : Set (Fin 2)) ∪ {1}
      simp
    have h2 : (1 : Fin 2) ∉ c₁ ({0} : Set (Fin 2)) := by
      show (1 : Fin 2) ∉ ({0} : Set (Fin 2)) ∪ {0}
      simp
    exact h2 (h ({0} : Set (Fin 2)) h1)

end ComparabilityMatters
