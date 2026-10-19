/-
  Copyright 2026 Xueqiang Gao (高学强) · ORCID 0009-0008-3821-3454
  Licensed under the Apache License, Version 2.0 (see LICENSE).
  Original publication source: caseos.cn/research — https://caseos.cn/research/
  First public release 2026-10-09; formal publication 2026-10-20.
  Part of the B-line canonical subset (group 2): 53 files / 417 theorems+lemmas / 77 definitions.
  Attribution header added at publication; proof bodies unchanged.
-/

/-
ContinuousSemigroupExp.lean —— **连续时间的缺口补上：连续半群 ⇒ 指数**（第 140 轮）

**令源**：第 135 轮把"几何形状"归约为**两条可检验对称性**，并如实标注
"**连续时间上**'$\\rho$ 连续且半群 $\\Rightarrow\\rho(t)=e^{-ct}$'**未形式化**（本件只做整数步）"。
本件把那一条补上：

> **若 $\\rho:\\mathbb R\\to\\mathbb R$ 满足（i）半群性 $\\rho(s+t)=\\rho(s)\\rho(t)$，（ii）处处为正，（iii）连续，
> 则 $\\rho(t)=e^{\\,t\\ln\\rho(1)}$——即形状被**唯一**钉死为指数。**

**结果（机检）**：
  · `continuous_additive_linear`：**连续加性 $\\Rightarrow$ 线性**（$L(t)=t\\,L(1)$）；
  · `continuous_semigroup_exp`（**主结果**）：连续正半群 $\\Rightarrow\\rho(t)=e^{t\\ln\\rho(1)}$；
  · `halving_rate`：$\\rho(1)=1/2\\Rightarrow\\rho(t)=e^{-(\\ln2)t}$（与第 129／130／135 轮同一支）；
  · `continuous_shape_certificate`：打包。

**⇒ 缺口更新**：第 135 轮"只做整数步"的限制**解除**；"为何几何"的缺口**只剩**"为何 (S1)／(S2) 成立"。

0 `sorry` / `0 axiom`。
-/
import Mathlib

open scoped Real

namespace ContinuousSemigroupExp

/-- **（连续加性 ⇒ 线性）** 若 $L$ 加性且连续，则 $L(t)=t\\,L(1)$。 -/
theorem continuous_additive_linear (L : ℝ → ℝ)
    (hadd : ∀ s t : ℝ, L (s + t) = L s + L t) (hcont : Continuous L) :
    ∀ t : ℝ, L t = t * L 1 := by
  have h0 : L 0 = 0 := by
    have h := hadd 0 0
    simp only [add_zero] at h
    linarith
  let F : ℝ →+ ℝ := { toFun := L, map_zero' := h0, map_add' := hadd }
  have hrat : ∀ q : ℚ, L (q : ℝ) = (q : ℝ) * L 1 := by
    intro q
    have h1 : F ((q : ℚ) • (1 : ℝ)) = (q : ℚ) • F 1 := map_rat_smul F q 1
    have h2 : (q : ℚ) • (1 : ℝ) = (q : ℝ) := by simp
    have h3 : (q : ℚ) • F 1 = (q : ℝ) * L 1 := by
      rw [Rat.smul_def]
      simp [F]
    rw [h2, h3] at h1
    simpa [F] using h1
  -- 目标集合是闭集，且包含 $\\mathbb Q$ 的像 ⇒ 包含其闭包 = 全空间
  have hclosed : IsClosed {x : ℝ | L x = x * L 1} :=
    isClosed_eq hcont (continuous_id.mul continuous_const)
  have hsub : Set.range ((↑) : ℚ → ℝ) ⊆ {x : ℝ | L x = x * L 1} := by
    rintro x ⟨q, rfl⟩
    exact hrat q
  intro t
  exact closure_minimal hsub hclosed (by
    rw [Rat.denseRange_cast.closure_range]
    trivial)

/-- **（主结果 · 连续半群 ⇒ 指数）** -/
theorem continuous_semigroup_exp (ρ : ℝ → ℝ)
    (hmul : ∀ s t : ℝ, ρ (s + t) = ρ s * ρ t)
    (hpos : ∀ t : ℝ, 0 < ρ t) (hcont : Continuous ρ) :
    ∀ t : ℝ, ρ t = Real.exp (t * Real.log (ρ 1)) := by
  let L : ℝ → ℝ := fun t => Real.log (ρ t)
  have hadd : ∀ s t : ℝ, L (s + t) = L s + L t := by
    intro s t
    simp only [L]
    rw [hmul s t, Real.log_mul (ne_of_gt (hpos s)) (ne_of_gt (hpos t))]
  have hcontL : Continuous L := hcont.log (fun t => ne_of_gt (hpos t))
  have hlin := continuous_additive_linear L hadd hcontL
  intro t
  have ht : Real.log (ρ t) = t * Real.log (ρ 1) := by
    have := hlin t
    simpa [L] using this
  rw [← ht, Real.exp_log (hpos t)]

/-- **（速率形式）** $\\rho(1)=1/2\\Rightarrow\\rho(t)=e^{-(\\ln 2)t}$（与 129／130／135 轮同一支）。 -/
theorem halving_rate (ρ : ℝ → ℝ)
    (hmul : ∀ s t : ℝ, ρ (s + t) = ρ s * ρ t)
    (hpos : ∀ t : ℝ, 0 < ρ t) (hcont : Continuous ρ) (hhalf : ρ 1 = 1 / 2) :
    ∀ t : ℝ, ρ t = Real.exp (-(Real.log 2) * t) := by
  intro t
  rw [continuous_semigroup_exp ρ hmul hpos hcont t, hhalf]
  have hlog : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  rw [hlog]
  ring_nf

/-- **（连续形状证书）** 连续加性 ⇒ 线性 · **连续正半群 ⇒ 指数** · $\\rho(1)=1/2\\Rightarrow$ 半衰期形式。 -/
theorem continuous_shape_certificate :
    (∀ L : ℝ → ℝ, (∀ s t : ℝ, L (s + t) = L s + L t) → Continuous L →
        ∀ t : ℝ, L t = t * L 1) ∧
      (∀ ρ : ℝ → ℝ, (∀ s t : ℝ, ρ (s + t) = ρ s * ρ t) → (∀ t : ℝ, 0 < ρ t) →
        Continuous ρ → ∀ t : ℝ, ρ t = Real.exp (t * Real.log (ρ 1))) ∧
      (∀ ρ : ℝ → ℝ, (∀ s t : ℝ, ρ (s + t) = ρ s * ρ t) → (∀ t : ℝ, 0 < ρ t) →
        Continuous ρ → ρ 1 = 1 / 2 → ∀ t : ℝ, ρ t = Real.exp (-(Real.log 2) * t)) :=
  ⟨fun L hadd hcont => continuous_additive_linear L hadd hcont,
    fun ρ hmul hpos hcont => continuous_semigroup_exp ρ hmul hpos hcont,
    fun ρ hmul hpos hcont hhalf => halving_rate ρ hmul hpos hcont hhalf⟩

end ContinuousSemigroupExp
