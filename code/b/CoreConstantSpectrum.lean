/-
  Copyright 2026 Xueqiang Gao (高学强) · ORCID 0009-0008-3821-3454
  Licensed under the Apache License, Version 2.0 (see LICENSE).
  Original publication source: caseos.cn/research — https://caseos.cn/research/
  First public release 2026-10-09; formal publication 2026-10-20.
  Part of the B-line canonical subset (group 2): 53 files / 417 theorems+lemmas / 77 definitions.
  Attribution header added at publication; proof bodies unchanged.
-/

/-
CoreConstantSpectrum.lean —— 核心常数 `C_F` 的**频谱三分**与一处**值域陷阱**（第 87 轮）

**动机**：冻结范畴层 §5.2 的核谱表并列五行：

  | logistic | π²/3 | 机检 |
  | tanh     | π²/6 | 与 logistic 同轨（重标度） |
  | probit Φ | 1.8064 | 真正不同的形状（数值，非机检） |
  | Cauchy   | **发散** | 重尾 |
  | Heaviside| **0** | 零宽度 |

**此前只有 logistic／tanh 行被机检**（第 69 轮），cauchy 与 heaviside 两行只是散文。
本轮把这两行也做成定理，并顺带发现一处**值域陷阱**：

  `coreConstant : (ℝ → ℝ) → ℝ` 用的是 **Bochner 积分**，而 Bochner 积分对不可积函数
  **按约定取 0**（`integral_undef`）。于是

  · Heaviside（零宽度） → `0`；
  · Cauchy（重尾发散） → **也是 `0`**。

  **两行在 ℝ 值下塌成同一个数。** 只有把 `C_F` 的余定义域换成 `ℝ≥0∞`，
  两行才分开：`0` 对 `⊤`。这与靶心 1 的 σ 两义**同型**——不是记号问题，是**类型问题**。

**本轮结果**（0 `sorry` / 0 `axiom`）：

  · `cauchy_tail`：$x\ge2$ 时 $h(F_{\mathrm{Cauchy}}x)\ge\frac{1}{2\pi x}$（重尾的定量形式）；
  · `cauchy_not_integrable`：`¬ Integrable (entropyDensity cauchy)`（借 Mathlib `not_integrableOn_Ioi_inv`）；
  · `cauchy_coreConstant`：`coreConstant cauchy = 0`（发散被 ℝ 值**吞掉**）；
  · `cauchy_lintegral_eq_top`：`∫⁻ ofReal (entropyDensity cauchy) = ⊤`（换值域后可见）；
  · `heaviside_coreConstant` / `heaviside_lintegral`：零宽度行两值域下皆为 `0`；
  · `spectrum_separates_only_in_ennreal`：**打包对照**——ℝ 值下两行相等，ℝ≥0∞ 值下不等。

-/
import BoundaryBridge_layers
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

open scoped Real ENNReal
open MeasureTheory Set

namespace CoreConstantSpectrum

open CausModel

/-! ## 一 · 两个核 -/

/-- 零宽度核（Heaviside）。 -/
noncomputable def heaviside (z : ℝ) : ℝ := if z < 0 then 0 else 1

/-- Cauchy 核（标准 Cauchy 分布函数 $z\mapsto\frac12+\frac{\arctan z}{\pi}$）。 -/
noncomputable def cauchy (z : ℝ) : ℝ := 1 / 2 + Real.arctan z / Real.pi

/-! ## 二 · 熵密度的结构：二值熵 = 两个 `negMulLog` 之和 -/

/-- $h(p)=-\!p\log p-(1-p)\log(1-p)=\mathrm{negMulLog}\,p+\mathrm{negMulLog}(1-p)$。 -/
lemma hbin_eq_negMulLog (p : ℝ) : hbin p = Real.negMulLog p + Real.negMulLog (1 - p) := by
  unfold hbin Real.negMulLog
  ring

/-- $p\in[0,1]\Rightarrow h(p)\ge0$。**注意**：$h$ 不是"正值函数"，
它靠 $p$ 与 $1-p$ **两项各自**非负。 -/
lemma hbin_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : 0 ≤ hbin p := by
  rw [hbin_eq_negMulLog]
  exact add_nonneg (Real.negMulLog_nonneg h0 h1)
    (Real.negMulLog_nonneg (by linarith) (by linarith))

/-- `h` 可测（**只需可测，不需连续**：$h$ 在 $0$ 处并不连续）。 -/
lemma measurable_hbin : Measurable hbin := by
  unfold hbin
  fun_prop

/-! ## 三 · arctan 的两端夹逼（本轮的定量工具） -/

/-- $\arctan t\le t$（$t\ge0$）：由 $\arctan t\le\tan(\arctan t)=t$。 -/
lemma arctan_le_self {t : ℝ} (h0 : 0 ≤ t) : Real.arctan t ≤ t := by
  have h := Real.le_tan (Real.arctan_nonneg.mpr h0) (Real.arctan_lt_pi_div_two t)
  rwa [Real.tan_arctan] at h

/-- $\frac t2\le\arctan t$（$0\le t\le1$）：由 $\sin(\arctan t)=\frac{t}{\sqrt{1+t^2}}$、
$\sin s\le s$ 与 $\sqrt{1+t^2}\le2$。 -/
lemma half_le_arctan {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : t / 2 ≤ Real.arctan t := by
  have hsin : t / Real.sqrt (1 + t ^ 2) ≤ Real.arctan t := by
    have h := Real.sin_le (Real.arctan_nonneg.mpr h0)
    rwa [Real.sin_arctan] at h
  have h4 : (1 + t ^ 2 : ℝ) ≤ 4 := by nlinarith
  have hsq : Real.sqrt (1 + t ^ 2) ≤ 2 := by
    have h := Real.sqrt_le_sqrt h4
    rwa [show Real.sqrt (4 : ℝ) = 2 by norm_num] at h
  have hpos : 0 < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  have hle : 1 / 2 ≤ 1 / Real.sqrt (1 + t ^ 2) :=
    one_div_le_one_div_of_le hpos hsq
  calc t / 2 = t * (1 / 2) := by ring
    _ ≤ t * (1 / Real.sqrt (1 + t ^ 2)) := mul_le_mul_of_nonneg_left hle h0
    _ = t / Real.sqrt (1 + t ^ 2) := by ring
    _ ≤ Real.arctan t := hsin

/-! ## 四 · Cauchy 核落在 $(0,1)$ 内 -/

lemma cauchy_pos (x : ℝ) : 0 < cauchy x := by
  have h := Real.neg_pi_div_two_lt_arctan x
  have hpi := Real.pi_pos
  have : -(1 / 2 : ℝ) < Real.arctan x / Real.pi := by
    rw [lt_div_iff₀ hpi]
    nlinarith
  unfold cauchy
  linarith

lemma cauchy_lt_one (x : ℝ) : cauchy x < 1 := by
  have h := Real.arctan_lt_pi_div_two x
  have hpi := Real.pi_pos
  have : Real.arctan x / Real.pi < (1 / 2 : ℝ) := by
    rw [div_lt_iff₀ hpi]
    nlinarith
  unfold cauchy
  linarith

/-- $1-\text{cauchy}(x)=\arctan(x^{-1})/\pi$（$x>0$）。
**这是"重尾"的解析身份**：尾部质量恰好是倒数的 arctan。 -/
lemma one_sub_cauchy {x : ℝ} (hx : 0 < x) :
    1 - cauchy x = Real.arctan x⁻¹ / Real.pi := by
  unfold cauchy
  rw [Real.arctan_inv_of_pos hx]
  field_simp
  ring

/-! ## 五 · 重尾的定量下界 -/

/-- **（重尾下界）** $x\ge2\Rightarrow h(F_{\mathrm{Cauchy}}x)\ge\frac{1}{2\pi x}$。 -/
lemma cauchy_tail {x : ℝ} (hx : 2 ≤ x) :
    (1 / (2 * Real.pi)) * x⁻¹ ≤ hbin (cauchy x) := by
  have hx0 : 0 < x := by linarith
  have hxinv0 : 0 ≤ x⁻¹ := inv_nonneg.mpr hx0.le
  have hxinv1 : x⁻¹ ≤ 1 := by
    have h : 1 / x ≤ 1 / (1 : ℝ) := one_div_le_one_div_of_le zero_lt_one (by linarith)
    simpa using h
  have hp0 : 0 ≤ cauchy x := (cauchy_pos x).le
  have hp1 : cauchy x ≤ 1 := (cauchy_lt_one x).le
  -- 记 u = 1 - cauchy x
  have hcomp := one_sub_cauchy hx0
  have hu0 : 0 < Real.arctan x⁻¹ / Real.pi :=
    div_pos (Real.arctan_pos.mpr (inv_pos.mpr hx0)) Real.pi_pos
  have hpi := Real.pi_pos
  have hxinv_half : x⁻¹ ≤ (1 : ℝ) / 2 := by
    have h : 1 / x ≤ 1 / (2 : ℝ) := one_div_le_one_div_of_le (by norm_num) hx
    simpa [one_div] using h
  -- 下界：1/(2πx) ≤ u
  have hlow : (1 / (2 * Real.pi)) * x⁻¹ ≤ Real.arctan x⁻¹ / Real.pi := by
    have h2 := half_le_arctan hxinv0 hxinv1
    calc (1 / (2 * Real.pi)) * x⁻¹ = (x⁻¹ / 2) / Real.pi := by field_simp
      _ ≤ Real.arctan x⁻¹ / Real.pi := div_le_div_of_nonneg_right h2 hpi.le
  -- 上界：u ≤ 1/(2π) ≤ exp(-1)，故 -log u ≥ 1
  have hu_le : Real.arctan x⁻¹ / Real.pi ≤ 1 / (2 * Real.pi) := by
    have h2 := arctan_le_self hxinv0
    calc Real.arctan x⁻¹ / Real.pi ≤ x⁻¹ / Real.pi := div_le_div_of_nonneg_right h2 hpi.le
      _ ≤ ((1 : ℝ) / 2) / Real.pi := div_le_div_of_nonneg_right hxinv_half hpi.le
      _ = 1 / (2 * Real.pi) := by field_simp
  have hsix : 1 / (2 * Real.pi) ≤ 1 / 6 := by
    have h : (6 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    exact one_div_le_one_div_of_le (by norm_num) h
  have hexp : 1 / (2 * Real.pi) ≤ Real.exp (-1) := by
    have h3 : (1 : ℝ) / 3 ≤ Real.exp (-1) := by
      rw [Real.exp_neg]
      simpa using one_div_le_one_div_of_le (Real.exp_pos 1)
        (le_of_lt Real.exp_one_lt_three)
    have h13 : 1 / (2 * Real.pi) ≤ 1 / 3 :=
      one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 3) (by nlinarith [Real.pi_gt_three])
    linarith
  have hlog : Real.log (Real.arctan x⁻¹ / Real.pi) ≤ -1 :=
    (Real.log_le_iff_le_exp hu0).mpr (le_trans hu_le hexp)
  have hnm : Real.arctan x⁻¹ / Real.pi ≤ Real.negMulLog (Real.arctan x⁻¹ / Real.pi) := by
    have h := hu0.le
    rw [Real.negMulLog]
    nlinarith [mul_le_mul_of_nonneg_left (by linarith : (1:ℝ) ≤ -Real.log (Real.arctan x⁻¹ / Real.pi)) h]
  calc (1 / (2 * Real.pi)) * x⁻¹
      ≤ Real.arctan x⁻¹ / Real.pi := hlow
    _ ≤ Real.negMulLog (Real.arctan x⁻¹ / Real.pi) := hnm
    _ = Real.negMulLog (1 - cauchy x) := by rw [hcomp]
    _ ≤ hbin (cauchy x) := by
        rw [hbin_eq_negMulLog]
        have := Real.negMulLog_nonneg hp0 hp1
        linarith

/-! ## 六 · Cauchy 行的核心常数**发散**（= 不可积） -/

/-- **（Cauchy 行：发散）** $\int h(F_{\mathrm{Cauchy}})$ 不可积。
由 §五 的定量下界与 Mathlib 的 `not_integrableOn_Ioi_inv` 直接夹出。 -/
theorem cauchy_not_integrable : ¬ Integrable (entropyDensity cauchy) := by
  intro h
  have hsmall : Integrable (fun x : ℝ => (1 / (2 * Real.pi)) * x⁻¹)
      (volume.restrict (Ioi (2 : ℝ))) := by
    refine Integrable.mono' (h.integrableOn (s := Ioi (2 : ℝ))) ?_ ?_
    · exact (measurable_const.mul measurable_inv).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx2 : (2 : ℝ) ≤ x := (mem_Ioi.mp hx).le
      have hb := cauchy_tail hx2
      have hnn : 0 ≤ (1 / (2 * Real.pi)) * x⁻¹ := by
        have : 0 < x := by linarith
        positivity
      rw [Real.norm_of_nonneg hnn]
      simpa [entropyDensity] using hb
  have hInv : IntegrableOn (fun x : ℝ => x⁻¹) (Ioi (2 : ℝ)) := by
    have h2 := hsmall.const_mul (2 * Real.pi)
    have h3 : (fun x : ℝ => (2 * Real.pi) * ((1 / (2 * Real.pi)) * x⁻¹)) = fun x => x⁻¹ := by
      funext x
      field_simp
    rwa [h3] at h2
  exact not_integrableOn_Ioi_inv (a := (2 : ℝ)) hInv

/-- **（ℝ 值把发散吞掉）** 不可积 ⇒ 冻结件的 `coreConstant` 按 Bochner 约定返回 `0`。 -/
theorem coreConstant_eq_zero_of_not_integrable {F : ℝ → ℝ}
    (h : ¬ Integrable (entropyDensity F)) : coreConstant F = 0 := by
  unfold coreConstant
  exact MeasureTheory.integral_undef h

/-- **（Cauchy 行在 ℝ 值下）** `coreConstant cauchy = 0`——**发散被读成零**。 -/
theorem cauchy_coreConstant : coreConstant cauchy = 0 :=
  coreConstant_eq_zero_of_not_integrable cauchy_not_integrable

/-- **（换值域后可见）** 在 `ℝ≥0∞` 值下 Cauchy 行是 `⊤`。 -/
theorem cauchy_lintegral_eq_top :
    ∫⁻ z, ENNReal.ofReal (entropyDensity cauchy z) = ⊤ := by
  have hne : ¬ (∫⁻ z, ENNReal.ofReal (entropyDensity cauchy z) ≠ ⊤) := by
    rw [lintegral_ofReal_ne_top_iff_integrable]
    · exact cauchy_not_integrable
    · exact (measurable_hbin.comp (measurable_const.add
        (Real.measurable_arctan.div_const _))).aestronglyMeasurable
    · filter_upwards with x
      exact hbin_nonneg (cauchy_pos x).le (cauchy_lt_one x).le
  exact not_not.mp hne

/-! ## 七 · Heaviside 行：零宽度 -/

/-- 零宽度核的熵密度**逐点为零**（$h(0)=h(1)=0$）。 -/
lemma hbin_heaviside (z : ℝ) : hbin (heaviside z) = 0 := by
  unfold heaviside
  split_ifs with h
  · simp [hbin]
  · simp [hbin]

/-- **（Heaviside 行在 ℝ 值下）** `coreConstant heaviside = 0`。 -/
theorem heaviside_coreConstant : coreConstant heaviside = 0 := by
  unfold coreConstant entropyDensity
  have : (fun z => hbin (heaviside z)) = fun _ => (0 : ℝ) := funext hbin_heaviside
  rw [this]
  simp

/-- **（Heaviside 行在 ℝ≥0∞ 值下）** 仍是 `0`。 -/
theorem heaviside_lintegral :
    ∫⁻ z, ENNReal.ofReal (entropyDensity heaviside z) = 0 := by
  have : (fun z => ENNReal.ofReal (hbin (heaviside z))) = fun _ => (0 : ℝ≥0∞) := by
    funext z
    rw [hbin_heaviside]
    simp
  rw [show (fun z => ENNReal.ofReal (entropyDensity heaviside z))
      = fun _ => (0 : ℝ≥0∞) from this]
  simp

/-! ## 八 · 收官：**两行只在新值域下分开** -/

/-- **（值域陷阱 · 主结果）** 冻结件 `coreConstant : (ℝ→ℝ) → ℝ` 把
「零宽度」与「重尾发散」**读成同一个数**：两行皆为 `0`。
只有换成 `ℝ≥0∞` 值，「发散」才显现为 `⊤`，两行才分开。

⇒ 核谱表的"发散"一栏**不是** ℝ 值 `coreConstant` 的取值，而是**另一个余定义域**下的取值。
这与靶心 1 的 σ 两义**同型**：不是记号问题，是**类型问题**。 -/
theorem spectrum_separates_only_in_ennreal :
    coreConstant cauchy = coreConstant heaviside ∧
      coreConstant cauchy = 0 ∧ coreConstant heaviside = 0 ∧
      (∫⁻ z, ENNReal.ofReal (entropyDensity heaviside z)) = 0 ∧
      (∫⁻ z, ENNReal.ofReal (entropyDensity cauchy z)) = ⊤ :=
  ⟨by rw [cauchy_coreConstant, heaviside_coreConstant], cauchy_coreConstant,
    heaviside_coreConstant, heaviside_lintegral, cauchy_lintegral_eq_top⟩

end CoreConstantSpectrum
