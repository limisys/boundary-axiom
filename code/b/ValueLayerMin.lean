/-
  Copyright 2026 Xueqiang Gao (高学强) · ORCID 0009-0008-3821-3454
  Licensed under the Apache License, Version 2.0 (see LICENSE).
  Original publication source: caseos.cn/research — https://caseos.cn/research/
  First public release 2026-10-09; formal publication 2026-10-20.
  Part of the B-line canonical subset (group 2): 53 files / 417 theorems+lemmas / 77 definitions.
  Attribution header added at publication; proof bodies unchanged.
-/

/-
ValueLayerMin.lean —— κ★ 是**全局最小**（不只是临界点），外加值层两端极限的 ε–δ 形式（第 62 轮）

**动机**：论文把 κ★ 称作 "least-action sharpness"，但**冻结值层只证了临界性**
（`deriv_V_kappaStar`），**从未证明它是全局最小**——严谨读者第一个会问的正是这一点。
本件补上：

  · **`V_global_min`**  `V(κ★) ≤ V(κ)` 对一切 `κ > 0`（用 AM–GM，**不用微积分**）；
  · **`V_eq_min_iff`** 等号**只在** `κ = κ★` 成立（严格唯一）；
  · **`deriv_zero_iff`** 临界点**唯一**（把冻结层的"存在"升级为"唯一"）；
  · **`V_gt_near_zero`**／**`V_gt_atTop`** 两端极限的 **ε–δ 形式**（论文 §7 列为未证的
    "the two limits in the value layer's own terms (analytic, ε–δ)"）。

**为什么用 ε–δ 而不 `Filter.Tendsto`**：论文 §7 的原话就是 ε–δ；且显式常数
（`δ = A/max(M,1)`、`K = max 1 (M/c₀)`）对读者更可核查。两者等价，此处选可核查者。

0 `sorry` / 0 `axiom`。依赖冻结值层 `BoundaryTheory` 与本纲领 `ValueLayerExtension`（**均未改动其一行**）。
-/
import BoundaryTheory
import ValueLayerExtension

open scoped Real

namespace ValueLayerMin

/-- 不确定项系数 `A(α) = απ²/3`，使 `V = c₀κ + A/κ`。 -/
noncomputable def A (α : ℝ) : ℝ := α * Real.pi ^ 2 / 3

theorem A_pos {α : ℝ} (hα : 0 < α) : 0 < A α := by
  unfold A; positivity

theorem A_nonneg {α : ℝ} (hα : 0 ≤ α) : 0 ≤ A α := by
  unfold A; positivity

/-! ## 一 · 代数辅助（把重复的根式运算集中一次） -/

/-- `c₀·√(A/c₀) = √(c₀·A)`（`c₀ > 0`）。 -/
theorem c_mul_sqrt {c₀ A : ℝ} (hc₀ : 0 < c₀) (hA : 0 ≤ A) :
    c₀ * Real.sqrt (A / c₀) = Real.sqrt (c₀ * A) := by
  rw [← Real.sqrt_sq (show (0:ℝ) ≤ c₀ * Real.sqrt (A / c₀) by positivity)]
  congr 1
  rw [mul_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ A / c₀)]
  field_simp

/-- `A / √(A/c₀) = √(c₀·A)`（`c₀ > 0`，与上一条对偶）。 -/
theorem div_sqrt {c₀ A : ℝ} (hc₀ : 0 < c₀) (hA : 0 < A) :
    A / Real.sqrt (A / c₀) = Real.sqrt (c₀ * A) := by
  have hs : Real.sqrt (A / c₀) ≠ 0 := (Real.sqrt_pos.mpr (div_pos hA hc₀)).ne'
  rw [div_eq_iff hs, ← c_mul_sqrt hc₀ hA.le, mul_assoc,
    Real.mul_self_sqrt (by positivity : (0:ℝ) ≤ A / c₀)]
  field_simp

/-! ## 二 · AM–GM 核（不做微积分） -/

/-- **AM–GM**：`c₀κ + A/κ ≥ 2√(c₀A)`。证明用完全平方。 -/
theorem amgm {c₀ A : ℝ} (hc₀ : 0 < c₀) (hA : 0 ≤ A) {κ : ℝ} (hκ : 0 < κ) :
    2 * Real.sqrt (c₀ * A) ≤ c₀ * κ + A / κ := by
  have h1 : 0 ≤ (Real.sqrt (c₀ * κ) - Real.sqrt (A / κ)) ^ 2 := sq_nonneg _
  have h2 : Real.sqrt (c₀ * κ) ^ 2 = c₀ * κ := Real.sq_sqrt (by positivity)
  have h3 : Real.sqrt (A / κ) ^ 2 = A / κ := Real.sq_sqrt (by positivity)
  have h4 : Real.sqrt (c₀ * A) = Real.sqrt (c₀ * κ) * Real.sqrt (A / κ) := by
    rw [← Real.sqrt_mul (show (0:ℝ) ≤ c₀ * κ by positivity)]
    congr 1
    field_simp
  nlinarith [h1, h2, h3, h4, Real.sqrt_nonneg (c₀ * κ), Real.sqrt_nonneg (A / κ)]

/-- **AM–GM 等号情形**：等号 ⟺ `κ = √(A/c₀)`。 -/
theorem amgm_eq_iff {c₀ A : ℝ} (hc₀ : 0 < c₀) (hA : 0 < A) {κ : ℝ} (hκ : 0 < κ) :
    c₀ * κ + A / κ = 2 * Real.sqrt (c₀ * A) ↔ κ = Real.sqrt (A / c₀) := by
  constructor
  · intro h
    have h4 : Real.sqrt (c₀ * A) = Real.sqrt (c₀ * κ) * Real.sqrt (A / κ) := by
      rw [← Real.sqrt_mul (show (0:ℝ) ≤ c₀ * κ by positivity)]
      congr 1
      field_simp
    have h2 : Real.sqrt (c₀ * κ) ^ 2 = c₀ * κ := Real.sq_sqrt (by positivity)
    have h3 : Real.sqrt (A / κ) ^ 2 = A / κ := Real.sq_sqrt (by positivity)
    have hsq : (Real.sqrt (c₀ * κ) - Real.sqrt (A / κ)) ^ 2 = 0 := by
      nlinarith [h2, h3, h4, h]
    have heq : Real.sqrt (c₀ * κ) = Real.sqrt (A / κ) := by
      have := sq_eq_zero_iff.mp hsq
      linarith
    have hval : c₀ * κ = A / κ := (Real.sqrt_inj (by positivity) (by positivity)).mp heq
    have hk2 : κ ^ 2 = A / c₀ := by
      field_simp at hval ⊢
      nlinarith [hval]
    rw [← Real.sqrt_sq hκ.le, hk2]
  · intro h
    rw [h, c_mul_sqrt hc₀ hA.le, div_sqrt hc₀ hA]
    ring

/-! ## 三 · κ★ = √(A/c₀)，与 `A = c₀κ★²` -/

/-- κ★ 就是 `√(A/c₀)`（冻结层用的是 `π√(α/(3c₀))` 形式，两者相等）。 -/
theorem kappaStar_eq_sqrt {c₀ α : ℝ} (hc₀ : 0 < c₀) (hα : 0 ≤ α) :
    BoundaryTheory.kappaStar c₀ α = Real.sqrt (A α / c₀) := by
  have hL : 0 ≤ BoundaryTheory.kappaStar c₀ α := by
    unfold BoundaryTheory.kappaStar
    positivity
  rw [← Real.sqrt_sq hL]
  congr 1
  rw [BoundaryTheory.kappaStar_sq hc₀ hα]
  unfold A
  field_simp

/-- `A = c₀κ★²`（`κ★` 平衡身份的代数形式；此处直接列出以备引用）。 -/
theorem A_eq_c_mul_kappaStar_sq {c₀ α : ℝ} (hc₀ : 0 < c₀) (hα : 0 ≤ α) :
    A α = c₀ * (BoundaryTheory.kappaStar c₀ α) ^ 2 := by
  rw [BoundaryTheory.kappaStar_sq hc₀ hα]
  unfold A
  field_simp

/-- `V(κ★) = 2√(c₀A)`。 -/
theorem V_kappaStar {c₀ α : ℝ} (hc₀ : 0 < c₀) (hα : 0 < α) :
    BoundaryTheory.V c₀ α (BoundaryTheory.kappaStar c₀ α) = 2 * Real.sqrt (c₀ * A α) := by
  have hA : 0 < A α := A_pos hα
  have hV : BoundaryTheory.V c₀ α (BoundaryTheory.kappaStar c₀ α)
      = c₀ * BoundaryTheory.kappaStar c₀ α + A α / BoundaryTheory.kappaStar c₀ α := rfl
  rw [hV, kappaStar_eq_sqrt hc₀ hα.le, c_mul_sqrt hc₀ hA.le, div_sqrt hc₀ hA]
  ring

/-! ## 四 · 主结果：全局最小、唯一性、临界点唯一 -/

/-- **（主定理）** `κ★` 是 `V` 在 `κ > 0` 上的**全局最小点**——而不只是驻点。 -/
theorem V_global_min (c₀ α κ : ℝ) (hc₀ : 0 < c₀) (hα : 0 < α) (hκ : 0 < κ) :
    BoundaryTheory.V c₀ α (BoundaryTheory.kappaStar c₀ α) ≤ BoundaryTheory.V c₀ α κ := by
  rw [V_kappaStar hc₀ hα]
  have hV : BoundaryTheory.V c₀ α κ = c₀ * κ + A α / κ := rfl
  rw [hV]
  exact amgm hc₀ (A_nonneg hα.le) hκ

/-- **等号唯一**：`V` 在 `κ>0` 上取到最小值**当且仅当** `κ = κ★`。 -/
theorem V_eq_min_iff (c₀ α κ : ℝ) (hc₀ : 0 < c₀) (hα : 0 < α) (hκ : 0 < κ) :
    BoundaryTheory.V c₀ α κ = BoundaryTheory.V c₀ α (BoundaryTheory.kappaStar c₀ α) ↔
      κ = BoundaryTheory.kappaStar c₀ α := by
  have hA : 0 < A α := A_pos hα
  rw [V_kappaStar hc₀ hα, kappaStar_eq_sqrt hc₀ hα.le]
  have hV : BoundaryTheory.V c₀ α κ = c₀ * κ + A α / κ := rfl
  rw [hV]
  exact amgm_eq_iff hc₀ hA hκ

/-- **临界点唯一**：`V'(κ) = 0 ↔ κ = κ★`（冻结层只证了 `κ★` 处导数为零）。 -/
theorem deriv_zero_iff (c₀ α κ : ℝ) (hc₀ : 0 < c₀) (hα : 0 < α) (hκ : 0 < κ) :
    deriv (fun κ : ℝ => BoundaryTheory.V c₀ α κ) κ = 0 ↔ κ = BoundaryTheory.kappaStar c₀ α := by
  have hd : deriv (fun κ : ℝ => BoundaryTheory.V c₀ α κ) κ
      = c₀ - α * Real.pi ^ 2 / (3 * κ ^ 2) := ValueLayerExtension.deriv_V_eq c₀ α κ hκ.ne'
  rw [hd, kappaStar_eq_sqrt hc₀ hα.le]
  constructor
  · intro h
    have hk2 : κ ^ 2 = A α / c₀ := by
      have hAdef : A α = α * Real.pi ^ 2 / 3 := rfl
      rw [hAdef]
      field_simp at h ⊢
      nlinarith [h]
    rw [← Real.sqrt_sq hκ.le, hk2]
  · intro h
    have hA : 0 < A α := A_pos hα
    rw [h, Real.sq_sqrt (div_nonneg hA.le hc₀.le)]
    unfold A
    field_simp
    ring

/-! ## 五 · 两端极限（ε–δ 形式，即论文 §7 所列的两条） -/

/-- **左端**：`κ → 0⁺` 时 `V → +∞`。显式 `δ = A/max(M,1)`。 -/
theorem V_gt_near_zero (c₀ α : ℝ) (hc₀ : 0 < c₀) (hα : 0 < α) :
    ∀ M : ℝ, ∃ δ > 0, ∀ κ : ℝ, 0 < κ → κ < δ → M ≤ BoundaryTheory.V c₀ α κ := by
  intro M
  have hA : 0 < A α := A_pos hα
  refine ⟨A α / max M 1, div_pos hA (lt_of_lt_of_le one_pos (le_max_right M 1)), ?_⟩
  intro κ hκ hκδ
  have hAM : M ≤ max M 1 := le_max_left _ _
  have hmaxpos : (0:ℝ) < max M 1 := lt_of_lt_of_le one_pos (le_max_right M 1)
  have h1 : κ * max M 1 < A α := (lt_div_iff₀ hmaxpos).mp hκδ
  have h2 : max M 1 * κ < A α := by linarith
  have hlt : max M 1 < A α / κ := (lt_div_iff₀ hκ).mpr h2
  have hAM' : M ≤ A α / κ := by linarith
  have hV : BoundaryTheory.V c₀ α κ = c₀ * κ + A α / κ := rfl
  rw [hV]
  nlinarith [hAM', mul_pos hc₀ hκ]

/-- **右端**：`κ → +∞` 时 `V → +∞`。显式 `K = max 1 (M/c₀)`。 -/
theorem V_gt_atTop (c₀ α : ℝ) (hc₀ : 0 < c₀) (hα : 0 < α) :
    ∀ M : ℝ, ∃ K : ℝ, ∀ κ : ℝ, K ≤ κ → M ≤ BoundaryTheory.V c₀ α κ := by
  intro M
  have hA : 0 ≤ A α := A_nonneg hα.le
  refine ⟨max 1 (M / c₀), ?_⟩
  intro κ hκ
  have h1 : (1:ℝ) ≤ max 1 (M / c₀) := le_max_left _ _
  have h2 : M / c₀ ≤ max 1 (M / c₀) := le_max_right _ _
  have hκpos : 0 < κ := lt_of_lt_of_le one_pos (le_trans h1 hκ)
  have hdiv : 0 ≤ A α / κ := div_nonneg hA hκpos.le
  have hcκ : M ≤ c₀ * κ := by
    have hthis : c₀ * (M / c₀) = M := by field_simp
    nlinarith [h2, hκ, hc₀, hthis]
  have hV : BoundaryTheory.V c₀ α κ = c₀ * κ + A α / κ := rfl
  rw [hV]
  linarith

end ValueLayerMin
