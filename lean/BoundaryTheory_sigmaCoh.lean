/-
BoundaryTheory_sigmaCoh.lean
============================

σ_coh（范畴层凝聚度）的序论部分 —— 由第 43/44/46 轮的数值与 Z3 结果提升为 **Lean 机器证明**。

设定（第 43/44 轮件）：
    F(t) := p(|u| ≤ t)                    —— |u| 的分布函数
    已决 ⇔ |u| ≥ L(θ₀)/κ ，故 σ_coh(κ) = 1 − F(L/κ)， L>0
假设只有 CDF 的定义性性质： (A1) 0 ≤ F(t) ≤ 1 ；(A2) Monotone F

对应件：`凝聚度的阈值与局部比不可互推_20261006.md`（第 44 轮）及其第 46 轮补记。
-/

import Mathlib

noncomputable section

open scoped Real Topology

namespace BoundaryTheory

/-- 凝聚度：已决状态所占比例的模型量，σ_coh(κ) = 1 − F(L/κ)。 -/
def sigmaCoh (F : ℝ → ℝ) (L : ℝ) (κ : ℝ) : ℝ := 1 - F (L / κ)

/-! ## M1 · 单调性（第 46 轮 M1 的 Lean 版） -/

theorem sigmaCoh_mono (F : ℝ → ℝ) (hF : Monotone F) (L : ℝ) (hL : 0 < L)
    {κ₁ κ₂ : ℝ} (h1 : 0 < κ₁) (h : κ₁ ≤ κ₂) :
    sigmaCoh F L κ₁ ≤ sigmaCoh F L κ₂ := by
  unfold sigmaCoh
  have hdiv : L / κ₂ ≤ L / κ₁ := by
    have hrec : 1 / κ₂ ≤ 1 / κ₁ := one_div_le_one_div_of_le h1 h
    calc L / κ₂ = L * (1 / κ₂) := by ring
      _ ≤ L * (1 / κ₁) := mul_le_mul_of_nonneg_left hrec (le_of_lt hL)
      _ = L / κ₁ := by ring
  linarith [hF hdiv]

/-! ## M2 · 临界（或任一点）严格性：模糊带有正质量 ⇒ 未完成 -/

theorem sigmaCoh_lt_one (F : ℝ → ℝ) (L : ℝ) (κ : ℝ) (h : 0 < F (L / κ)) :
    sigmaCoh F L κ < 1 := by
  unfold sigmaCoh; linarith

/-- M2b · 反向：凝聚完成 ⇒ 模糊带无质量。 -/
theorem sigmaCoh_eq_one_iff (F : ℝ → ℝ) (L : ℝ) (κ : ℝ) :
    sigmaCoh F L κ = 1 ↔ F (L / κ) = 0 := by
  unfold sigmaCoh
  constructor <;> intro h <;> linarith

/-! ## M4 · 值域：σ_coh ∈ [0,1] -/

theorem sigmaCoh_mem_Icc (F : ℝ → ℝ) (L : ℝ) (κ : ℝ)
    (h0 : 0 ≤ F (L / κ)) (h1 : F (L / κ) ≤ 1) :
    sigmaCoh F L κ ∈ Set.Icc (0 : ℝ) 1 := by
  unfold sigmaCoh
  exact ⟨by linarith, by linarith⟩

/-! ## M3 · σ_coh 依赖状态分布（不是任何"与分布无关的量"的函数）

取 L = 1, κ = 2/5 ⇒ L/κ = 5/2。两组**都是合法 CDF** 的阶梯函数：
    F₁: |u| 集中于 2  ⇒ F₁(5/2) = 1 ⇒ σ_coh = 0
    F₂: |u| 集中于 3  ⇒ F₂(5/2) = 0 ⇒ σ_coh = 1
故同一 κ（从而同一 σ_mech）下 σ_coh 可不同。 -/

def Fmass2 : ℝ → ℝ := fun t => if t < 2 then 0 else 1
def Fmass3 : ℝ → ℝ := fun t => if t < 3 then 0 else 1

theorem Fmass2_mono : Monotone Fmass2 := by
  intro a b hab
  unfold Fmass2
  split_ifs with h1 h2
  · norm_num
  · norm_num
  · linarith
  · norm_num

theorem Fmass3_mono : Monotone Fmass3 := by
  intro a b hab
  unfold Fmass3
  split_ifs with h1 h2
  · norm_num
  · norm_num
  · linarith
  · norm_num

theorem sigmaCoh_depends_on_distribution :
    sigmaCoh Fmass2 1 (2 / 5) ≠ sigmaCoh Fmass3 1 (2 / 5) := by
  unfold sigmaCoh Fmass2 Fmass3
  norm_num

/-! ## L1/L2 · 两端极限（第 49 轮：由"带假设的陈述"升为 Lean 定理）

L1：F(t) → 1 (t → +∞) ⇒ σ_coh(κ) → 0 (κ → 0⁺)
L2：F 在 0 处连续，F(0)=0（无原子） ⇒ σ_coh(κ) → 1 (κ → +∞)
两条都只用到：κ ↦ L/κ 的极限性（`tendsto_inv_nhdsGT_zero` / `tendsto_inv_atTop_zero`）
与 CDF 的两端假设。 -/

theorem sigmaCoh_tendsto_zero (F : ℝ → ℝ) (L : ℝ) (hL : 0 < L)
    (hF : Filter.Tendsto F Filter.atTop (𝓝 1)) :
    Filter.Tendsto (fun κ : ℝ => sigmaCoh F L κ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h1 : Filter.Tendsto (fun κ : ℝ => L / κ) (𝓝[>] (0 : ℝ)) Filter.atTop := by
    have h := (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).const_mul_atTop hL
    simpa [div_eq_mul_inv] using h
  have h3 := hF.comp h1
  have h4 : Filter.Tendsto (fun κ : ℝ => (1 : ℝ) - F (L / κ)) (𝓝[>] (0 : ℝ)) (𝓝 (1 - 1)) :=
    tendsto_const_nhds.sub h3
  simpa [sigmaCoh] using h4

theorem sigmaCoh_tendsto_one (F : ℝ → ℝ) (L : ℝ) (hL : 0 < L)
    (hF : Filter.Tendsto F (𝓝 (0 : ℝ)) (𝓝 0)) :
    Filter.Tendsto (fun κ : ℝ => sigmaCoh F L κ) Filter.atTop (𝓝 1) := by
  have h2 : Filter.Tendsto (fun κ : ℝ => L / κ) Filter.atTop (𝓝 (0 : ℝ)) := by
    have h := (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul L
    simpa [div_eq_mul_inv] using h
  have h3 := hF.comp h2
  have h4 : Filter.Tendsto (fun κ : ℝ => (1 : ℝ) - F (L / κ)) Filter.atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub h3
  simpa [sigmaCoh] using h4

end BoundaryTheory
