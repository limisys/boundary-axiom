/-
  Copyright 2026 Xueqiang Gao (高学强) · ORCID 0009-0008-3821-3454
  Licensed under the Apache License, Version 2.0 (see LICENSE).
  Original publication source: caseos.cn/research — https://caseos.cn/research/
  First public release 2026-10-09; formal publication 2026-10-20.
  Part of the B-line canonical subset (group 2): 53 files / 417 theorems+lemmas / 77 definitions.
  Attribution header added at publication; proof bodies unchanged.
-/

/-
CalibrationProtocol.lean —— **校准核对的最小协议：两点即可否证核的形式**（第 127 轮）

**令源**：第 126 轮把唯一假设写成**校准恒等式** $L\\big(\\varphi(d)\\big)=d$（距离＝归属强度的对数几率）。
本件把它变成**实验上最小的核对设计**：

> **只要在同一被试内取两个不同距离上的归属强度读数：
> 若两处强度相同 ⇒ 核的形式不成立（模型死）；若强度严格随距离下降且落在校准曲线上 ⇒ 核通过。**

**结果（机检）**：
  · `calibration_injective`：校准 ⇒ 强度对距离**单射**（同强度必同距离）；
  · `calibration_antitone`：校准 ⇒ 强度**严格随距离下降**；
  · `two_point_falsifier`（**主结果**）：两个不同距离上强度相同 ⇒ **不校准**（核的形式被否证）；
  · `two_point_test`：**两点核对**的完整判据（正反两面）；
  · `protocol_certificate`：打包。

**⚠ 本件不做任何测量**：它只把"该测什么、怎么判"写成定理；数据仍须实验。

0 `sorry` / `0 axiom`。
-/
import KernelCalibration
import ReadoutDynamics

open scoped Real

namespace CalibrationProtocol

open LogisticCore (L)
open ReadoutExistence (thetaOf)
open KernelCalibration (calibrated_unique calibration_iff_logistic)

/-- **（校准 ⇒ 单射）** 同一强度不可能出现在两个不同距离上。 -/
theorem calibration_injective (φ : ℝ → ℝ)
    (hb : ∀ d : ℝ, 0 < d → 0 < φ d ∧ φ d < 1)
    (hcal : ∀ d : ℝ, 0 < d → L (φ d) = d) :
    ∀ d₁ d₂ : ℝ, 0 < d₁ → 0 < d₂ → φ d₁ = φ d₂ → d₁ = d₂ := by
  intro d₁ d₂ h1 h2 heq
  have h1' : L (φ d₁) = d₁ := hcal d₁ h1
  have h2' : L (φ d₂) = d₂ := hcal d₂ h2
  rw [heq] at h1'
  exact h1'.symm.trans h2'

/-- **（校准 ⇒ 严格下降）** 强度随距离**严格下降**。 -/
theorem calibration_antitone (φ : ℝ → ℝ)
    (hb : ∀ d : ℝ, 0 < d → 0 < φ d ∧ φ d < 1)
    (hcal : ∀ d : ℝ, 0 < d → L (φ d) = d) :
    ∀ d₁ d₂ : ℝ, 0 < d₁ → d₁ < d₂ → φ d₂ < φ d₁ := by
  intro d₁ d₂ h1 hlt
  have h2 : 0 < d₂ := lt_trans h1 hlt
  have e1 : φ d₁ = thetaOf d₁ := calibrated_unique φ hb hcal d₁ h1
  have e2 : φ d₂ = thetaOf d₂ := calibrated_unique φ hb hcal d₂ h2
  rw [e1, e2]
  exact ReadoutDynamics.thetaOf_lt_thetaOf hlt

/-- **（主结果 · 两点否证）** 两个**不同距离**上强度**相同** ⇒ **核的形式不成立**。 -/
theorem two_point_falsifier (φ : ℝ → ℝ)
    (hb : ∀ d : ℝ, 0 < d → 0 < φ d ∧ φ d < 1)
    (d₁ d₂ : ℝ) (h1 : 0 < d₁) (h2 : 0 < d₂) (hne : d₁ ≠ d₂) (heq : φ d₁ = φ d₂) :
    ¬ (∀ d : ℝ, 0 < d → L (φ d) = d) := by
  intro hcal
  exact hne (calibration_injective φ hb hcal d₁ d₂ h1 h2 heq)

/-- **（两点核对 · 正反两面）** 校准 $\iff$ 每点都落在水平函数上（故两点即可判）。 -/
theorem two_point_test (φ : ℝ → ℝ)
    (hb : ∀ d : ℝ, 0 < d → 0 < φ d ∧ φ d < 1) :
    (∀ d : ℝ, 0 < d → L (φ d) = d) ↔ (∀ d : ℝ, 0 < d → φ d = thetaOf d) :=
  calibration_iff_logistic φ hb

/-- **（协议证书）** 单射 · 严格下降 · 两点否证 · 两点核对（正反两面）。 -/
theorem protocol_certificate :
    (∀ φ : ℝ → ℝ, (∀ d : ℝ, 0 < d → 0 < φ d ∧ φ d < 1) →
      (∀ d : ℝ, 0 < d → L (φ d) = d) →
      ∀ d₁ d₂ : ℝ, 0 < d₁ → 0 < d₂ → φ d₁ = φ d₂ → d₁ = d₂) ∧
      (∀ φ : ℝ → ℝ, (∀ d : ℝ, 0 < d → 0 < φ d ∧ φ d < 1) →
        (∀ d : ℝ, 0 < d → L (φ d) = d) →
        ∀ d₁ d₂ : ℝ, 0 < d₁ → d₁ < d₂ → φ d₂ < φ d₁) ∧
      (∀ φ : ℝ → ℝ, (∀ d : ℝ, 0 < d → 0 < φ d ∧ φ d < 1) →
        ∀ d₁ d₂ : ℝ, 0 < d₁ → 0 < d₂ → d₁ ≠ d₂ → φ d₁ = φ d₂ →
          ¬ (∀ d : ℝ, 0 < d → L (φ d) = d)) ∧
      (∀ φ : ℝ → ℝ, (∀ d : ℝ, 0 < d → 0 < φ d ∧ φ d < 1) →
        ((∀ d : ℝ, 0 < d → L (φ d) = d) ↔ (∀ d : ℝ, 0 < d → φ d = thetaOf d))) :=
  ⟨fun φ hb hcal => calibration_injective φ hb hcal,
    fun φ hb hcal => calibration_antitone φ hb hcal,
    fun φ hb d₁ d₂ h1 h2 hne heq => two_point_falsifier φ hb d₁ d₂ h1 h2 hne heq,
    fun φ hb => two_point_test φ hb⟩

end CalibrationProtocol
