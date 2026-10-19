/-
  Copyright 2026 Xueqiang Gao (高学强) · ORCID 0009-0008-3821-3454
  Licensed under the Apache License, Version 2.0 (see LICENSE).
  Original publication source: caseos.cn/research — https://caseos.cn/research/
  First public release 2026-10-09; formal publication 2026-10-20.
  Part of the B-line canonical subset (group 2): 53 files / 417 theorems+lemmas / 77 definitions.
  Attribution header added at publication; proof bodies unchanged.
-/

/-
KernelCalibration.lean —— **唯一那条假设的精确形式：校准恒等式**（第 126 轮）

**背景**：第 123 轮之后，纲领的**假设清单只剩一条**：**核的形式**（logistic）。
本件把这条假设**写成一条恒等式**，并证明它与核的形式**等价**：

> **校准恒等式**：**距离＝归属强度的对数几率**，即 $L\\big(b_{\\kappa,\\mu}(\\mu+d/\\kappa)\\big)=d$（$d\\ge0$），
> 其中 $L(\\theta)=\\ln\\frac{2-\\theta}{\\theta}$。
> **任何满足该恒等式的核，必是 logistic 核**（故这条恒等式**就是**那条假设的全部内容）。

**结果（机检）**：
  · `b_eq_thetaOf_abs`：核的闭式 $b_{\\kappa,\\mu}(x)=\\theta\\big(|\\kappa(x-\\mu)|\\big)$（即"水平函数读距离"）；
  · `calibrated_actual`：**实际核满足校准恒等式**（$L\\,b=d$）；
  · `calibrated_unique`（**主结果**）：**任何校准核必等于 logistic 核**；
  · `calibration_iff_logistic`：该恒等式与核的形式**等价**；
  · `calibration_certificate`：打包。

**⇒ 这条把"假设"变成"一条可核对的恒等式"**：
- 它**没有**消除假设（核仍是我们选的）；
- 但它把假设**压到不能再小**，并**给出可证伪形态**：若测到的归属强度与距离的关系**不满足** $L\\,b=d$，则该核（因而整套模型）**不成立**。

0 `sorry` / `0 axiom`。
-/
import LogisticCore
import ReadoutExistence

open scoped Real

namespace KernelCalibration

open LogisticCore
open ReadoutExistence (thetaOf L_thetaOf thetaOf_mem L_injOn)

/-- **（核的闭式）** $b_{\\kappa,\\mu}(x)=\\theta\\big(|\\kappa(x-\\mu)|\\big)$：核就是"水平函数读距离"。 -/
theorem b_eq_thetaOf_abs (κ μ x : ℝ) :
    b κ μ x = thetaOf |κ * (x - μ)| := by
  rw [T1_stable_form]
  unfold sig thetaOf
  rw [neg_neg]
  ring

/-- **（实际核是校准的）** 距离＝对数几率：$L\\big(b_{\\kappa,\\mu}(\\mu+d/\\kappa)\\big)=d$（$d\\ge0$）。 -/
theorem calibrated_actual (κ μ d : ℝ) (hκ : 0 < κ) (hd : 0 ≤ d) :
    L (b κ μ (μ + d / κ)) = d := by
  rw [b_eq_thetaOf_abs]
  have h : |κ * ((μ + d / κ) - μ)| = d := by
    have h1 : κ * ((μ + d / κ) - μ) = d := by
      field_simp
      ring
    rw [h1, abs_of_nonneg hd]
  rw [h, L_thetaOf]

/-- **（主结果）** **任何校准核（在 $d>0$ 上）必是 logistic 核**。 -/
theorem calibrated_unique (φ : ℝ → ℝ)
    (hb : ∀ d : ℝ, 0 < d → 0 < φ d ∧ φ d < 1)
    (hcal : ∀ d : ℝ, 0 < d → L (φ d) = d) :
    ∀ d : ℝ, 0 < d → φ d = thetaOf d := by
  intro d hd
  have hm1 : φ d ∈ Set.Ioo (0 : ℝ) 1 := Set.mem_Ioo.mpr ⟨(hb d hd).1, (hb d hd).2⟩
  have hm2 : thetaOf d ∈ Set.Ioo (0 : ℝ) 1 := thetaOf_mem hd
  exact L_injOn hm1 hm2 (by rw [hcal d hd, L_thetaOf])

/-- **（等价形式）** 在 $d>0$ 上：**校准恒等式 $\iff$ 核的值就是水平函数**。 -/
theorem calibration_iff_logistic (φ : ℝ → ℝ)
    (hb : ∀ d : ℝ, 0 < d → 0 < φ d ∧ φ d < 1) :
    (∀ d : ℝ, 0 < d → L (φ d) = d) ↔ (∀ d : ℝ, 0 < d → φ d = thetaOf d) := by
  constructor
  · intro hcal d hd
    exact calibrated_unique φ hb hcal d hd
  · intro hval d hd
    rw [hval d hd, L_thetaOf]

/-- **（校准证书）** 核的闭式（含中心 $b=1$）· 实际核校准 · 校准唯一（⇒ 假设＝一条恒等式）· 等价形式。 -/
theorem calibration_certificate :
    (∀ κ μ x : ℝ, b κ μ x = thetaOf |κ * (x - μ)|) ∧
      (∀ κ μ d : ℝ, 0 < κ → 0 < d → L (b κ μ (μ + d / κ)) = d) ∧
      (∀ φ : ℝ → ℝ, (∀ d : ℝ, 0 < d → 0 < φ d ∧ φ d < 1) →
        (∀ d : ℝ, 0 < d → L (φ d) = d) → ∀ d : ℝ, 0 < d → φ d = thetaOf d) ∧
      (∀ φ : ℝ → ℝ, (∀ d : ℝ, 0 < d → 0 < φ d ∧ φ d < 1) →
        ((∀ d : ℝ, 0 < d → L (φ d) = d) ↔ (∀ d : ℝ, 0 < d → φ d = thetaOf d))) :=
  ⟨fun κ μ x => b_eq_thetaOf_abs κ μ x,
    fun κ μ d hκ hd => calibrated_actual κ μ d hκ hd.le,
    fun φ hb hcal d hd => calibrated_unique φ hb hcal d hd,
    fun φ hb => calibration_iff_logistic φ hb⟩

end KernelCalibration
