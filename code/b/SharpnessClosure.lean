/-
  Copyright 2026 Xueqiang Gao (高学强) · ORCID 0009-0008-3821-3454
  Licensed under the Apache License, Version 2.0 (see LICENSE).
  Original publication source: caseos.cn/research — https://caseos.cn/research/
  First public release 2026-10-09; formal publication 2026-10-20.
  Part of the B-line canonical subset (group 2): 53 files / 417 theorems+lemmas / 77 definitions.
  Attribution header added at publication; proof bodies unchanged.
-/

/-
SharpnessClosure.lean —— **值层的锐度 κ 进入范畴层的闭包算子**（第 70 轮）

**动机**：靶心 3 是"范畴层（Fix(c)、障碍类）与值层（c₀,α,C_F,C₀）逐项对接"。
前几轮做到了：两层共存不冲突、伴有两面同构、芯外闭包来自伴随。
**但值层的参数从未进入 c**——本轮补这一哩。

**做法**：在状态线 ℝ 上，对锐度 `κ>0`、中心 `μ`、水平常数 `w≥0` 定义

  `c κ μ w z` ＝ `z`（若 `z ≤ μ - w/κ`）；`μ + w/κ`（若 `μ - w/κ < z < μ + w/κ`）；`z`（若 `μ + w/κ ≤ z`）

即"**把模糊带压到其右端点**"。

**本轮结果**：

  · `isClosure_c`       `c κ μ w` 是闭包算子（扩张／单调／幂等）；
  · `fix_c`             `Fix (c κ μ w) = {z | z ≤ μ - w/κ ∨ μ + w/κ ≤ z}`（**两条尾**）；
  · `fix_c_eq_decided`（接缝）取 `w = L θ`，则 `Fix (c κ μ (L θ)) = {x | b κ μ x ≤ θ}`
    —— **范畴层的不动点集恰是可解芯的"已决集"**；
  · `fix_mono_in_kappa`  `κ₁ ≤ κ₂ ⇒ Fix (c κ₁) ⊆ Fix (c κ₂)` —— **锐度越大，刚性面越大**；
  · 由值层 κ★ = π√(α/(3c₀))，**c₀,α 由此进入 c**：临界锐度是族中一员。

本文件不含未完成证明（检查脚本 `check_no_sorry.py` 会剥掉注释后再搜关键词）。
复用第 60 轮的 `LogisticCore.L`／`T6_complement` 与第 67 轮的 `IsClosure`／`Fix`。
-/
import LogisticCore
import LocusVsBoundary

open scoped Real

namespace SharpnessClosure

open LogisticCore LocusVsBoundary

/-- **按锐度参数化的闭包算子**：把模糊带压到右端点。 -/
noncomputable def c (κ μ w : ℝ) (z : ℝ) : ℝ :=
  if z ≤ μ - w / κ then z else if z < μ + w / κ then μ + w / κ else z

/-- 扩张性。 -/
theorem le_c (κ μ w z : ℝ) (_hκ : 0 < κ) (_hw : 0 ≤ w) : z ≤ c κ μ w z := by
  unfold c
  by_cases h1 : z ≤ μ - w / κ
  · rw [if_pos h1]
  · rw [if_neg h1]
    by_cases h2 : z < μ + w / κ
    · rw [if_pos h2]; linarith
    · rw [if_neg h2]

/-- **三歧**：`c z` 只可能是 `z` 或右端点。 -/
theorem c_eq (κ μ w z : ℝ) (_hκ : 0 < κ) (_hw : 0 ≤ w) :
    c κ μ w z = z ∨ c κ μ w z = μ + w / κ := by
  unfold c
  by_cases h1 : z ≤ μ - w / κ
  · left; rw [if_pos h1]
  · rw [if_neg h1]
    by_cases h2 : z < μ + w / κ
    · right; rw [if_pos h2]
    · left; rw [if_neg h2]

/-- 右端点是不动点（`w = 0` 时带退化，故分情形）。 -/
theorem c_fixpt_right (κ μ w : ℝ) (_hκ : 0 < κ) (_hw : 0 ≤ w) :
    c κ μ w (μ + w / κ) = μ + w / κ := by
  unfold c
  by_cases h1 : μ + w / κ ≤ μ - w / κ
  · rw [if_pos h1]
  · rw [if_neg h1]
    by_cases h2 : μ + w / κ < μ + w / κ
    · rw [if_pos h2]
    · rw [if_neg h2]

/-- 幂等性。 -/
theorem c_idem (κ μ w z : ℝ) (hκ : 0 < κ) (hw : 0 ≤ w) :
    c κ μ w (c κ μ w z) = c κ μ w z := by
  rcases c_eq κ μ w z hκ hw with h | h
  · rw [h]; exact h
  · rw [h, c_fixpt_right κ μ w hκ hw]

/-- 单调性。 -/
theorem monotone_c (κ μ w : ℝ) (hκ : 0 < κ) (hw : 0 ≤ w) : Monotone (c κ μ w) := by
  have hwk : 0 ≤ w / κ := div_nonneg hw hκ.le
  intro z₁ z₂ hz
  unfold c
  by_cases h1 : z₁ ≤ μ - w / κ
  · rw [if_pos h1]
    by_cases g1 : z₂ ≤ μ - w / κ
    · rw [if_pos g1]; exact hz
    · rw [if_neg g1]
      by_cases g2 : z₂ < μ + w / κ
      · rw [if_pos g2]; linarith
      · rw [if_neg g2]; exact hz
  · rw [if_neg h1]
    by_cases h2 : z₁ < μ + w / κ
    · rw [if_pos h2]
      by_cases g1 : z₂ ≤ μ - w / κ
      · rw [if_pos g1]; linarith
      · rw [if_neg g1]
        by_cases g2 : z₂ < μ + w / κ
        · rw [if_pos g2]
        · rw [if_neg g2]; linarith
    · rw [if_neg h2]
      have hz₁ : μ + w / κ ≤ z₁ := le_of_not_gt h2
      by_cases g1 : z₂ ≤ μ - w / κ
      · rw [if_pos g1]; linarith
      · rw [if_neg g1]
        by_cases g2 : z₂ < μ + w / κ
        · rw [if_pos g2]; linarith
        · rw [if_neg g2]; exact hz

/-- **（结果一）** `c κ μ w` 是闭包算子。 -/
theorem isClosure_c (κ μ w : ℝ) (hκ : 0 < κ) (hw : 0 ≤ w) : IsClosure (c κ μ w) :=
  ⟨fun z => le_c κ μ w z hκ hw, fun _ _ h => monotone_c κ μ w hκ hw h,
    fun z => c_idem κ μ w z hκ hw⟩

/-- **（结果二）** 不动点集＝**两条尾**。 -/
theorem fix_c (κ μ w : ℝ) (hκ : 0 < κ) (hw : 0 ≤ w) :
    LocusVsBoundary.Fix (c κ μ w) = {z : ℝ | z ≤ μ - w / κ ∨ μ + w / κ ≤ z} := by
  have hwk : 0 ≤ w / κ := div_nonneg hw hκ.le
  ext z
  simp only [LocusVsBoundary.Fix, Set.mem_ofPred_eq]
  constructor
  · intro h
    unfold c at h
    by_cases h1 : z ≤ μ - w / κ
    · exact Or.inl h1
    · rw [if_neg h1] at h
      by_cases h2 : z < μ + w / κ
      · rw [if_pos h2] at h
        exact absurd h.symm (ne_of_lt h2)
      · exact Or.inr (le_of_not_gt h2)
  · rintro (h1 | h1)
    · unfold c; rw [if_pos h1]
    · unfold c
      by_cases g1 : z ≤ μ - w / κ
      · rw [if_pos g1]
      · rw [if_neg g1, if_neg (not_lt.mpr h1)]

/-- 两条尾 $\iff$ 带外。 -/
theorem tail_iff (κ μ w z : ℝ) (hκ : 0 < κ) (_hw : 0 ≤ w) :
    (z ≤ μ - w / κ ∨ μ + w / κ ≤ z) ↔ w ≤ |κ * (z - μ)| := by
  have hk : |κ * (z - μ)| = κ * |z - μ| := by rw [abs_mul, abs_of_pos hκ]
  have hκw : κ * (w / κ) = w := by field_simp
  rw [hk]
  constructor
  · rintro (h | h)
    · have h' : w / κ ≤ μ - z := by linarith
      have h2 : w / κ ≤ |z - μ| := h'.trans (by
        have : μ - z = -(z - μ) := by ring
        rw [this]; exact neg_le_abs _)
      nlinarith [h2, hκ, hκw]
    · have h' : w / κ ≤ z - μ := by linarith
      have h2 : w / κ ≤ |z - μ| := h'.trans (le_abs_self _)
      nlinarith [h2, hκ, hκw]
  · intro h
    have h' : w / κ ≤ |z - μ| := by
      rw [div_le_iff₀ hκ]; linarith
    rcases lt_or_ge (z - μ) 0 with hneg | hpos
    · left
      rw [abs_of_neg hneg] at h'
      linarith
    · right
      rw [abs_of_nonneg hpos] at h'
      linarith

/-- **（接缝）** 取 `w = L θ`，范畴层的刚性面**恰是**可解芯的已决集。 -/
theorem fix_c_eq_decided (κ μ θ : ℝ) (hκ : 0 < κ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    LocusVsBoundary.Fix (c κ μ (L θ)) = {x : ℝ | b κ μ x ≤ θ} := by
  have hw : 0 ≤ L θ := (L_pos hθ0 hθ1).le
  rw [fix_c κ μ (L θ) hκ hw]
  ext x
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, T6_complement κ μ x θ hκ hθ0 hθ1]
  exact tail_iff κ μ (L θ) x hκ hw

/-- **（锐度单调）** 锐度越大，刚性面越大。 -/
theorem fix_mono_in_kappa (κ₁ κ₂ μ w : ℝ) (h1 : 0 < κ₁) (h2 : 0 < κ₂) (hw : 0 ≤ w)
    (hκ : κ₁ ≤ κ₂) : LocusVsBoundary.Fix (c κ₁ μ w) ⊆ LocusVsBoundary.Fix (c κ₂ μ w) := by
  intro z hz
  rw [fix_c κ₁ μ w h1 hw] at hz
  rw [fix_c κ₂ μ w h2 hw]
  have hdiv : w / κ₂ ≤ w / κ₁ := by
    rw [div_le_div_iff₀ h2 h1]; nlinarith
  rcases hz with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

/-- **（收官）** 三层打包：`c` 是闭包算子；其不动点集＝已决集；且随锐度**单调增大**。 -/
theorem sharpness_enters_closure :
    (∀ (κ μ w : ℝ), 0 < κ → 0 ≤ w → IsClosure (c κ μ w))
    ∧ (∀ (κ μ θ : ℝ), 0 < κ → 0 < θ → θ < 1 →
        LocusVsBoundary.Fix (c κ μ (L θ)) = {x : ℝ | b κ μ x ≤ θ})
    ∧ (∀ (κ₁ κ₂ μ w : ℝ), 0 < κ₁ → 0 < κ₂ → 0 ≤ w → κ₁ ≤ κ₂ →
        LocusVsBoundary.Fix (c κ₁ μ w) ⊆ LocusVsBoundary.Fix (c κ₂ μ w)) :=
  ⟨fun κ μ w hκ hw => isClosure_c κ μ w hκ hw,
   fun κ μ θ hκ hθ0 hθ1 => fix_c_eq_decided κ μ θ hκ hθ0 hθ1,
   fun κ₁ κ₂ μ w h1 h2 hw hκ => fix_mono_in_kappa κ₁ κ₂ μ w h1 h2 hw hκ⟩

end SharpnessClosure
