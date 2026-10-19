/-
  Copyright 2026 Xueqiang Gao (高学强) · ORCID 0009-0008-3821-3454
  Licensed under the Apache License, Version 2.0 (see LICENSE).
  Original publication source: caseos.cn/research — https://caseos.cn/research/
  First public release 2026-10-09; formal publication 2026-10-20.
  Part of the B-line canonical subset (group 2): 53 files / 417 theorems+lemmas / 77 definitions.
  Attribution header added at publication; proof bodies unchanged.
-/

/-
TimeScaleInvariance.lean —— **"步 ↔ 秒"不必假设：时间常数是可测的**（第 130 轮）

**令源**：第 129 轮把维持律的形状定为指数（半衰期＝1 个**模型时间单位**），并声明
**"步 ↔ 秒"的换算仍未做**。本件把它**消解**为一次测量：

> 对**任意**初始偏差，同一对时刻上的**偏差比**是**同一个数**（不含初始偏差、且绝对单位相消）；
> 其对数对时间差**线性**，斜率就是速率 $c$。⇒ **$c$（因而 $\\tau=\\ln 2/c$）由曲线形状本身测出**，
> **不需要**先假定模型时间与实验时间的换算。

**结果（机检）**：
  · `wOfRate`：一般速率的指数包络 $w(t)=1+(w_0-1)e^{-ct}$；
  · `ratio_eq`（**主结果**）：$\\dfrac{w(t_1)-1}{w(t_2)-1}=e^{-c(t_1-t_2)}$——**与 $w_0$ 无关**；
  · `ratio_indep_of_deviation`：不同初始偏差给出**同一个比**；
  · `log_ratio_linear`：比的对数对时间差**线性**，斜率 $=-c$ ⇒ **$c$ 可估**；
  · `half_life_eq`：半衰期 $=\\dfrac{\\ln 2}{c}$（故 $\\tau$ 也是可估的）；
  · `time_scale_certificate`：打包。

**⇒ 结论**：**"步 ↔ 秒"不是待补的假设，而是可测参数**；模型可证伪的内容**全部是无量纲的**（比值与线性）。

0 `sorry` / `0 axiom`。
-/
import ContinuousRelaxation

open scoped Real

namespace TimeScaleInvariance

open ReadoutExistence (thetaOf)
open Falsifiers (thetaStar_sub_le)
open ContinuousRelaxation (wOf)

/-- **一般速率的指数包络（声明）**：$w(t)=1+(w_0-1)e^{-ct}$。 -/
noncomputable def wOfRate (c w₀ t : ℝ) : ℝ := 1 + (w₀ - 1) * Real.exp (-(c * t))

/-- **（与第 129 轮相容）** $c=\\ln 2$ 时回到 129 轮的包络。 -/
theorem wOfRate_log_two_eq (w₀ t : ℝ) : wOfRate (Real.log 2) w₀ t = wOf w₀ t := by
  unfold wOfRate wOf
  ring_nf

/-- **（主结果 · 偏差比与初始偏差无关）**
$\\dfrac{w(t_1)-1}{w(t_2)-1}=e^{-c(t_1-t_2)}$（$w_0>1$；绝对单位在比值中相消）。 -/
theorem ratio_eq {c w₀ t₁ t₂ : ℝ} (hc : 0 < c) (hw : 1 < w₀) :
    (wOfRate c w₀ t₁ - 1) / (wOfRate c w₀ t₂ - 1) = Real.exp (-(c * (t₁ - t₂))) := by
  have hw0 : 0 < w₀ - 1 := by linarith
  have h1 : wOfRate c w₀ t₁ - 1 = (w₀ - 1) * Real.exp (-(c * t₁)) := by
    unfold wOfRate; ring
  have h2 : wOfRate c w₀ t₂ - 1 = (w₀ - 1) * Real.exp (-(c * t₂)) := by
    unfold wOfRate; ring
  have h2ne : (w₀ - 1) * Real.exp (-(c * t₂)) ≠ 0 :=
    mul_ne_zero hw0.ne' (Real.exp_ne_zero _)
  rw [h1, h2, mul_div_mul_left _ _ hw0.ne']
  rw [← Real.exp_sub]
  congr 1
  ring

/-- **（不同初始偏差给出同一个比）**。 -/
theorem ratio_indep_of_deviation {c w₀ w₀' t₁ t₂ : ℝ} (hc : 0 < c) (hw : 1 < w₀)
    (hw' : 1 < w₀') :
    (wOfRate c w₀ t₁ - 1) / (wOfRate c w₀ t₂ - 1)
      = (wOfRate c w₀' t₁ - 1) / (wOfRate c w₀' t₂ - 1) := by
  rw [ratio_eq hc hw, ratio_eq hc hw']

/-- **（比的线性 ⇒ 速率可估）** 比的对数对时间差**线性**，斜率 $=-c$。 -/
theorem log_ratio_linear {c w₀ t₁ t₂ : ℝ} (hc : 0 < c) (hw : 1 < w₀) :
    Real.log ((wOfRate c w₀ t₁ - 1) / (wOfRate c w₀ t₂ - 1)) = -(c * (t₁ - t₂)) := by
  rw [ratio_eq hc hw, Real.log_exp]

/-- **（半衰期）** 经过 $\\dfrac{\\ln 2}{c}$ 后偏差减半。 -/
theorem half_life_eq {c w₀ t : ℝ} (hc : 0 < c) :
    wOfRate c w₀ (t + Real.log 2 / c) - 1 = (wOfRate c w₀ t - 1) / 2 := by
  have hcne : c ≠ 0 := hc.ne'
  have harg : -(c * (t + Real.log 2 / c)) = -(c * t) + (-(Real.log 2)) := by
    field_simp
    ring
  have hexp2 : Real.exp (-(Real.log 2)) = 1 / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hexp : Real.exp (-(c * (t + Real.log 2 / c))) = Real.exp (-(c * t)) / 2 := by
    rw [harg, Real.exp_add, hexp2]
    ring
  unfold wOfRate
  rw [hexp]
  ring

/-- **（时间尺度证书）** 与 129 轮相容 · **偏差比与 $w_0$ 无关** · 对数线性（速率可估） · 半衰期 $=\\ln 2/c$。 -/
theorem time_scale_certificate :
    (∀ w₀ t : ℝ, wOfRate (Real.log 2) w₀ t = wOf w₀ t) ∧
      (∀ c w₀ t₁ t₂ : ℝ, 0 < c → 1 < w₀ →
        (wOfRate c w₀ t₁ - 1) / (wOfRate c w₀ t₂ - 1) = Real.exp (-(c * (t₁ - t₂)))) ∧
      (∀ c w₀ w₀' t₁ t₂ : ℝ, 0 < c → 1 < w₀ → 1 < w₀' →
        (wOfRate c w₀ t₁ - 1) / (wOfRate c w₀ t₂ - 1)
          = (wOfRate c w₀' t₁ - 1) / (wOfRate c w₀' t₂ - 1)) ∧
      (∀ c w₀ t₁ t₂ : ℝ, 0 < c → 1 < w₀ →
        Real.log ((wOfRate c w₀ t₁ - 1) / (wOfRate c w₀ t₂ - 1)) = -(c * (t₁ - t₂))) ∧
      (∀ c w₀ t : ℝ, 0 < c →
        wOfRate c w₀ (t + Real.log 2 / c) - 1 = (wOfRate c w₀ t - 1) / 2) :=
  ⟨fun w₀ t => wOfRate_log_two_eq w₀ t,
    fun c w₀ t₁ t₂ hc hw => ratio_eq hc hw,
    fun c w₀ w₀' t₁ t₂ hc hw hw' => ratio_indep_of_deviation hc hw hw',
    fun c w₀ t₁ t₂ hc hw => log_ratio_linear hc hw,
    fun c w₀ t hc => half_life_eq hc⟩

end TimeScaleInvariance
