/-
SelfReferenceLevel.lean —— T-θ′（自指路线）的第一步：**水平的自洽不动点**（第 104 轮）

**背景**：候选 F（边界 ≅ 判据）被判为**规范依赖同构**（第 101／102 轮）；
`ClosureGauge.c_scale` 又证明**闭包只依赖比值 w/κ** ⇒ 极小化定出**尺度**（κ★），定不出**水平**（w，等价 θ）。
第 102／103 轮给出：四条自然路线全败，**唯一存活＝自指路线 T-θ′**。

**本件的做法（把"自指"落到一个具体方程）**：
V 的两项是**互为倒数**的两个代价（$c_0\kappa$ 与 $\alpha C_F/\kappa$，平衡点是"量与它的倒数"的相持）。
把**同一个对偶**用在**判据自己的水平**上：要求**宽度与它自己的倒数相持**，即

$$\text{（T-θ′）}\qquad L(\theta)=\frac{1}{L(\theta)},\qquad L(\theta)=\ln\frac{2-\theta}{\theta}.$$

**结果（本件机检）**：
  · `L_eq_one_iff`：$L(\theta)=1\iff\theta=\dfrac{2}{1+e}$；
  · `recip_self_consistent_iff`：**自洽方程 $L=1/L$ 有且只有这一个解**；
  · `fixpoint_admissible`：该不动点落在允许区间 $(0,1)$ 内。

**诚实标注**：**"把同一对偶用在水平上"是我们的建模选择**（铁律 2）——本件证明的是"给定该选择，解唯一且可算"，
**不是**"水平必然如此"。它的落空条件见数学件 `尺度已定水平未定…` 的姊妹篇。

0 `sorry` / 0 `axiom`。
-/
import SharpnessClosure
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped Real

namespace SelfReferenceLevel

open LogisticCore

/-- **（水平方程的解）** $L(\theta)=1\iff\theta=\dfrac{2}{1+e}$（$0<\theta<1$）。 -/
theorem L_eq_one_iff {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) :
    L θ = 1 ↔ θ = 2 / (1 + Real.exp 1) := by
  have hx : 0 < (2 - θ) / θ := div_pos (by linarith) h0
  have he : (1 + Real.exp 1) ≠ 0 := by positivity
  constructor
  · intro h
    have h2 : (2 - θ) / θ = Real.exp 1 := by
      have := congrArg Real.exp h
      rwa [L, Real.exp_log hx] at this
    have h3 : 2 - θ = θ * Real.exp 1 := by
      field_simp at h2
      linarith
    rw [eq_div_iff he]
    linarith
  · intro h
    subst h
    rw [L]
    have hratio : (2 - 2 / (1 + Real.exp 1)) / (2 / (1 + Real.exp 1)) = Real.exp 1 := by
      field_simp
      ring
    rw [hratio, Real.log_exp]

/-- **（T-θ′ 主结果）** 自洽方程 $L(\theta)=\dfrac{1}{L(\theta)}$ **有且只有**一个解 $\theta=\dfrac{2}{1+e}$。 -/
theorem recip_self_consistent_iff {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) :
    L θ = 1 / L θ ↔ θ = 2 / (1 + Real.exp 1) := by
  have hL : 0 < L θ := L_pos h0 h1
  have hiff : L θ = 1 / L θ ↔ L θ = 1 := by
    rw [eq_div_iff hL.ne']
    constructor
    · intro h
      have h2 : (L θ - 1) * (L θ + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp h2 with h3 | h3
      · linarith
      · linarith
    · intro h
      rw [h]
      norm_num
  rw [hiff, L_eq_one_iff h0 h1]

/-- **（不动点可容许）** $\dfrac{2}{1+e}$ 落在判据的允许区间 $(0,1)$ 内。 -/
theorem fixpoint_admissible :
    0 < 2 / (1 + Real.exp 1) ∧ 2 / (1 + Real.exp 1) < 1 := by
  have he1 : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
  constructor
  · positivity
  · rw [div_lt_one (by positivity)]
    linarith

end SelfReferenceLevel
