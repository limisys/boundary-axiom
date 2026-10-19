/-
  Copyright 2026 Xueqiang Gao (高学强) · ORCID 0009-0008-3821-3454
  Licensed under the Apache License, Version 2.0 (see LICENSE).
  Original publication source: caseos.cn/research — https://caseos.cn/research/
  First public release 2026-10-09; formal publication 2026-10-20.
  Part of the B-line canonical subset (group 2): 53 files / 417 theorems+lemmas / 77 definitions.
  Attribution header added at publication; proof bodies unchanged.
-/

/-
GaugeNoGo.lean —— **T-θ‴-2/3：把规范作用写在"已定义"的读出上；并把"水平定不出"写成定理与反例**（第 114 轮）

**背景**：第 113 轮（S1）把"读出映射"定义成类 $\\mathcal R$，其**实质门槛是 K2（规范不变）**；
但 K2 此前只有自然语言表述（"须由规范不变的数据定义"）。本件把它**形式化**，并顺手检验
纲领此前关于"水平层定不出"的**论证**在形式层里究竟成立到什么程度——**结果有两条是更正**。

**本件机检七件事**：

1. `gaugeInv_iff_ratioForm`：**规范不变 $\\iff$ 只依赖比值 $w/\\kappa$**（K2 的精确形式）；
2. `closure_gaugeInv`：闭包族本身规范不变（`ClosureGauge.c_scale` 的泛函形式）；
3. `closure_normal_form`：$c_{\\kappa,\\mu,w}=c_{1,\\mu,w/\\kappa}$（**闭包只知道比值**）；
4. `level_free`：**同一尺度下有多个合法水平** ⇒ 值层数据**定不出**水平（"自由参数"这一半，可证）；
5. `level_changes_decided_set`：换水平**真的换掉**已决集（故 4 不是空话）；
6. **⚠ 更正（`gaugeInv_and_level_sensitive`）**：**存在规范不变且对水平敏感的泛函**——
   只要把**内禀尺度** $\\kappa^\\star$ 当常数用：$f(\\kappa,w)=\\theta\\!\\left(\\kappa^\\star\\cdot\\frac{w}{\\kappa}\\right)$。
   ⇒ **"规范方向"本身并不能证明水平定不出**；此前那句"连续量库整体看不见 $\\theta$"**不是由规范方向推出的**。
7. **⚠ 更正（`unitRead_gaugeInv_level_blind`）**：`unitRead` **规范不变、且完全不依赖 $w$**
   ⇒ 它**对水平是盲的**，故它**不能**充当"系统对自身水平的读出"；它能充当的是
   **"把读出值当作水平"这一约定的输入**（与 `SelfReferenceLevel.recip_self_consistent_iff` 合起来才给出 $\\theta^\\star$）。

**仍然未证**：**T-no-go 的强形式**——"任何由**连续量库整体**定义的内禀泛函都定不出 $\\theta$"。
本件只证明了**值层数据定不出水平**（自由参数形式）并**否掉了"靠规范方向就能证"这条捷径**。

0 `sorry` / 0 `axiom`。
-/
import ClosureGauge
import SharpnessClosure
import ReadoutExistence
import UnitReading

open scoped Real

namespace GaugeNoGo

open ClosureGauge SharpnessClosure ReadoutExistence LocusVsBoundary
open LogisticCore

/-- **规范不变（泛函版）**：对重标定 $(\\kappa,w)\\mapsto(t\\kappa,tw)$（$t>0$）取值不变。 -/
def GaugeInv (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ t κ w : ℝ, 0 < t → 0 < κ → f (t * κ) (t * w) = f κ w

/-- **（1 · K2 的精确形式）** 规范不变 $\\iff$ 该泛函**只依赖比值** $w/\\kappa$。 -/
theorem gaugeInv_iff_ratioForm (f : ℝ → ℝ → ℝ) :
    GaugeInv f ↔ ∃ g : ℝ → ℝ, ∀ κ w : ℝ, 0 < κ → f κ w = g (w / κ) := by
  constructor
  · intro h
    refine ⟨fun r => f 1 r, ?_⟩
    intro κ w hκ
    have h1 := h (1 / κ) κ w (by positivity) hκ
    have h2 : (1 / κ) * κ = 1 := by field_simp
    have h3 : (1 / κ) * w = w / κ := by rw [one_div, div_eq_inv_mul]
    rw [h2, h3] at h1
    exact h1.symm
  · rintro ⟨g, hg⟩ t κ w ht hκ
    rw [hg (t * κ) (t * w) (by positivity), hg κ w hκ]
    congr 1
    exact mul_div_mul_left w κ ht.ne'

/-- **（2）** 闭包族本身规范不变（`c_scale` 的泛函形式，逐点表述）。 -/
theorem closure_gaugeInv (μ z : ℝ) : GaugeInv (fun κ w => c κ μ w z) := by
  intro t κ w ht hκ
  exact ClosureGauge.c_scale κ μ w z ht

/-- **（3）** 闭包**只知道比值**：$c_{\\kappa,\\mu,w}=c_{1,\\mu,w/\\kappa}$。 -/
theorem closure_normal_form (κ μ w : ℝ) (hκ : 0 < κ) :
    c 1 μ (w / κ) = c κ μ w := by
  funext z
  have h := ClosureGauge.c_ratio κ 1 μ w z hκ one_pos
  have h3 : ((1 : ℝ) / κ) * w = w / κ := by rw [one_div, div_eq_inv_mul]
  rwa [h3] at h

/-- **（4 · 自由参数）** 同一尺度 $(\\kappa,\\mu)$ 下，至少有两个**不同**水平给出**合法闭包**。 -/
theorem level_free (κ μ : ℝ) (hκ : 0 < κ) :
    ∃ θ₁ θ₂ : ℝ, (0 < θ₁ ∧ θ₁ < 1) ∧ (0 < θ₂ ∧ θ₂ < 1) ∧ θ₁ ≠ θ₂ ∧
      IsClosure (c κ μ (L θ₁)) ∧ IsClosure (c κ μ (L θ₂)) := by
  refine ⟨1 / 4, 3 / 4, ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩,
    by norm_num, ?_, ?_⟩
  · exact isClosure_c κ μ (L (1 / 4)) hκ (le_of_lt (L_pos (by norm_num) (by norm_num)))
  · exact isClosure_c κ μ (L (3 / 4)) hκ (le_of_lt (L_pos (by norm_num) (by norm_num)))

/-- **（5）** 换水平**真的换掉**已决集（故 4 不是空话）：
取两尾之间的中点作见证——它在 $\theta=3/4$ 的已决集内，却**不在** $\theta=1/4$ 的已决集内。 -/
theorem level_changes_decided_set (κ μ : ℝ) (hκ : 0 < κ) :
    Fix (c κ μ (L (1 / 4))) ≠ Fix (c κ μ (L (3 / 4))) := by
  intro hfix
  have hw1 : 0 < L (1 / 4) := L_pos (by norm_num) (by norm_num)
  have hw2 : 0 < L (3 / 4) := L_pos (by norm_num) (by norm_num)
  have hlt : L (3 / 4) < L (1 / 4) := by
    unfold L
    apply Real.log_lt_log (by norm_num)
    norm_num
  set a : ℝ := L (1 / 4) / κ with ha
  set b : ℝ := L (3 / 4) / κ with hb
  have hapos : 0 < a := by rw [ha]; exact div_pos hw1 hκ
  have hbpos : 0 < b := by rw [hb]; exact div_pos hw2 hκ
  have hba : b < a := by rw [ha, hb]; exact div_lt_div_of_pos_right hlt hκ
  set z : ℝ := μ + (a + b) / 2 with hz
  have hmem2 : z ∈ Fix (c κ μ (L (3 / 4))) := by
    rw [ClosureGauge.fix_ratio_form κ μ (L (3 / 4)) hκ (le_of_lt hw2), Set.mem_ofPred_eq]
    right
    rw [hz, hb]
    linarith
  have hmem1 : z ∈ Fix (c κ μ (L (1 / 4))) := by
    rw [hfix]
    exact hmem2
  rw [ClosureGauge.fix_ratio_form κ μ (L (1 / 4)) hκ (le_of_lt hw1), Set.mem_ofPred_eq] at hmem1
  rcases hmem1 with h | h
  · rw [hz] at h
    linarith
  · rw [hz, ha, hb] at h
    have hba' : L (3 / 4) / κ < L (1 / 4) / κ := div_lt_div_of_pos_right hlt hκ
    linarith

/-- **（6 · 更正）** **存在规范不变且对水平敏感的泛函**：把**内禀尺度** $\\kappa^\\star$ 当常数用即可。
⇒ "规范方向"**本身**不能证明水平定不出。 -/
theorem gaugeInv_and_level_sensitive (κstar : ℝ) (hκ : 0 < κstar) :
    GaugeInv (fun κ w => thetaOf (κstar * (w / κ))) ∧
      (fun κ w => thetaOf (κstar * (w / κ))) κstar (L (1 / 4)) ≠
        (fun κ w => thetaOf (κstar * (w / κ))) κstar (L (3 / 4)) := by
  constructor
  · intro t κ w ht hκ
    show thetaOf (κstar * ((t * w) / (t * κ))) = thetaOf (κstar * (w / κ))
    rw [mul_div_mul_left w κ ht.ne']
  · show thetaOf (κstar * (L (1 / 4) / κstar)) ≠ thetaOf (κstar * (L (3 / 4) / κstar))
    have h1 : κstar * (L (1 / 4) / κstar) = L (1 / 4) := by field_simp
    have h2 : κstar * (L (3 / 4) / κstar) = L (3 / 4) := by field_simp
    rw [h1, h2, thetaOf_L (by norm_num) (by norm_num),
      thetaOf_L (by norm_num) (by norm_num)]
    norm_num

/-- **（7 · 更正）** `unitRead` **规范不变**、且**完全不依赖 $w$** ⇒ **对水平是盲的**。
故它不能充当"系统对自身水平的读出"；它只能是"把读出值当作水平"这一**约定**的输入。 -/
theorem unitRead_gaugeInv_level_blind (μ : ℝ) :
    GaugeInv (fun κ _w => UnitReading.unitRead κ μ) ∧
      (∀ κ κ' w w' : ℝ, 0 < κ → 0 < κ' →
        (fun κ _w => UnitReading.unitRead κ μ) κ w =
          (fun κ _w => UnitReading.unitRead κ μ) κ' w') := by
  constructor
  · intro t κ w ht hκ
    exact (UnitReading.unitRead_scale_center_invariant κ (t * κ) μ μ hκ (by positivity)).symm
  · intro κ κ' w w' hκ hκ'
    exact UnitReading.unitRead_scale_center_invariant κ κ' μ μ hκ hκ'

/-- **（T-θ‴-2/3 证书）** 一次打包：K2 的精确形式 · 闭包规范不变 · 闭包只知道比值 ·
值层定不出水平（自由参数）· 换水平换已决集 · **规范不变仍可对水平敏感** · **`unitRead` 对水平盲**。 -/
theorem t_theta_2_certificate (μ κstar z : ℝ) (hκ : 0 < κstar) :
    (∀ f : ℝ → ℝ → ℝ, GaugeInv f ↔ ∃ g : ℝ → ℝ, ∀ κ w : ℝ, 0 < κ → f κ w = g (w / κ)) ∧
      GaugeInv (fun κ w => c κ μ w z) ∧
      (∀ κ w : ℝ, 0 < κ → c 1 μ (w / κ) = c κ μ w) ∧
      (∃ θ₁ θ₂ : ℝ, (0 < θ₁ ∧ θ₁ < 1) ∧ (0 < θ₂ ∧ θ₂ < 1) ∧ θ₁ ≠ θ₂ ∧
        IsClosure (c κstar μ (L θ₁)) ∧ IsClosure (c κstar μ (L θ₂))) ∧
      Fix (c κstar μ (L (1 / 4))) ≠ Fix (c κstar μ (L (3 / 4))) ∧
      GaugeInv (fun κ w => thetaOf (κstar * (w / κ))) ∧
      GaugeInv (fun κ _w => UnitReading.unitRead κ μ) :=
  ⟨gaugeInv_iff_ratioForm, closure_gaugeInv μ z, fun _ _ hκ => closure_normal_form _ _ _ hκ,
    level_free κstar μ hκ, level_changes_decided_set κstar μ hκ,
    (gaugeInv_and_level_sensitive κstar hκ).1, (unitRead_gaugeInv_level_blind μ).1⟩

end GaugeNoGo
