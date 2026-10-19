/-
  Copyright 2026 Xueqiang Gao (高学强) · ORCID 0009-0008-3821-3454
  Licensed under the Apache License, Version 2.0 (see LICENSE).
  Original publication source: caseos.cn/research — https://caseos.cn/research/
  First public release 2026-10-09; formal publication 2026-10-20.
  Part of the B-line canonical subset (group 2): 53 files / 417 theorems+lemmas / 77 definitions.
  Attribution header added at publication; proof bodies unchanged.
-/

/-
DescriptionLayer.lean —— **描述层 $L$ 是"导出的且唯一"，不是另一条假设**（第 123 轮）

**背景**：前提审计（第 112 轮）把「**宽度—阈值关系 $w=L(\\theta)$**」列为**假设**（P2），
理由是"它由核与二值熵在模型内得出，**仍以 P1（logistic 核）为前提**"。
本件把这个档位**再精确一层**：

> **给定核 $b$，任何使"水平集恒等式"成立的翻译函数 $g$ 都必等于 $L$。**
> ⇒ **$L$ 不是独立假设，而是被核唯一决定的量**；剩下的假设只有**核的形式**（P1）。

**结果（机检）**：
  · `L_satisfies_identity`：$L$ 本身满足水平集恒等式（非空性）；
  · `description_layer_forced`（**主结果**）：任何满足该恒等式的 $g$，在 $(0,1)$ 上**必等于 $L$**；
  · `description_layer_unique`：两个这样的 $g$ 互相一致；
  · `description_layer_certificate`：打包。

**⚠ 不声称的**：**不声称核的 logistic 形式是导出的**——它仍是**建模假设（P1）**；
本件只说明：**在核已给的条件下，"描述层"不是外加的假设**。

0 `sorry` / `0 axiom`。
-/
import LogisticCore

open scoped Real

namespace DescriptionLayer

open LogisticCore

/-- **（非空性）** $L$ 本身满足水平集恒等式：$b_{\\kappa,\\mu}(x)\\le\\theta\\iff L\\theta\\le|\\kappa(x-\\mu)|$。 -/
theorem L_satisfies_identity (κ μ x θ : ℝ) (hκ : 0 < κ) (h0 : 0 < θ) (h1 : θ < 1) :
    (b κ μ x ≤ θ) ↔ L θ ≤ |κ * (x - μ)| :=
  T6_complement κ μ x θ hκ h0 h1

/-- **（主结果 · 描述层被核决定）**
任何使水平集恒等式成立的"水平—宽度翻译" $g$，在 $(0,1)$ 上**必等于 $L$**。 -/
theorem description_layer_forced (g : ℝ → ℝ)
    (hg : ∀ κ μ x θ : ℝ, 0 < κ → 0 < θ → θ < 1 →
      (b κ μ x ≤ θ ↔ g θ ≤ |κ * (x - μ)|)) :
    ∀ θ : ℝ, 0 < θ → θ < 1 → g θ = L θ := by
  intro θ h0 h1
  have hL : 0 < L θ := L_pos h0 h1
  -- 取 κ=1, μ=0：两个阈值给出同一族尾集 ⇒ 阈值相等
  have key : ∀ x : ℝ, L θ ≤ |x| ↔ g θ ≤ |x| := by
    intro x
    have h1' := hg 1 0 x θ one_pos h0 h1
    have h2 := T6_complement 1 0 x θ one_pos h0 h1
    rw [h2] at h1'
    simpa using h1'
  have hc : 0 ≤ g θ := by
    by_contra hcon
    have hneg : g θ < 0 := not_le.mp hcon
    have h := (key 0).mpr (by simpa using le_of_lt hneg)
    simp only [abs_zero] at h
    linarith
  have hle : L θ ≤ g θ := by
    have h := (key (g θ)).mpr (le_of_eq (abs_of_nonneg hc).symm)
    rwa [abs_of_nonneg hc] at h
  have hge : g θ ≤ L θ := by
    have h := (key (L θ)).mp (le_of_eq (abs_of_pos hL).symm)
    rwa [abs_of_pos hL] at h
  linarith

/-- **（唯一性）** 两个满足恒等式的翻译在 $(0,1)$ 上互相一致。 -/
theorem description_layer_unique (g g' : ℝ → ℝ)
    (hg : ∀ κ μ x θ : ℝ, 0 < κ → 0 < θ → θ < 1 →
      (b κ μ x ≤ θ ↔ g θ ≤ |κ * (x - μ)|))
    (hg' : ∀ κ μ x θ : ℝ, 0 < κ → 0 < θ → θ < 1 →
      (b κ μ x ≤ θ ↔ g' θ ≤ |κ * (x - μ)|)) :
    ∀ θ : ℝ, 0 < θ → θ < 1 → g θ = g' θ := by
  intro θ h0 h1
  rw [description_layer_forced g hg θ h0 h1, description_layer_forced g' hg' θ h0 h1]

/-- **（描述层证书）** 一次打包：$L$ 满足恒等式 · 任何翻译被 $L$ 唯一决定 · 两个翻译一致。 -/
theorem description_layer_certificate :
    (∀ κ μ x θ : ℝ, 0 < κ → 0 < θ → θ < 1 →
        ((b κ μ x ≤ θ) ↔ L θ ≤ |κ * (x - μ)|)) ∧
      (∀ g : ℝ → ℝ,
        (∀ κ μ x θ : ℝ, 0 < κ → 0 < θ → θ < 1 →
          (b κ μ x ≤ θ ↔ g θ ≤ |κ * (x - μ)|)) →
        ∀ θ : ℝ, 0 < θ → θ < 1 → g θ = L θ) ∧
      (∀ g g' : ℝ → ℝ,
        (∀ κ μ x θ : ℝ, 0 < κ → 0 < θ → θ < 1 →
          (b κ μ x ≤ θ ↔ g θ ≤ |κ * (x - μ)|)) →
        (∀ κ μ x θ : ℝ, 0 < κ → 0 < θ → θ < 1 →
          (b κ μ x ≤ θ ↔ g' θ ≤ |κ * (x - μ)|)) →
        ∀ θ : ℝ, 0 < θ → θ < 1 → g θ = g' θ) :=
  ⟨fun κ μ x θ hκ h0 h1 => L_satisfies_identity κ μ x θ hκ h0 h1,
    fun g hg θ h0 h1 => description_layer_forced g hg θ h0 h1,
    fun g g' hg hg' θ h0 h1 => description_layer_unique g g' hg hg' θ h0 h1⟩

end DescriptionLayer
