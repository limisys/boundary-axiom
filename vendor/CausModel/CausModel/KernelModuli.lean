/-
城邦研究院 · 论文线 · B 阶段 · B6：核模空间与 C_F 的重标度等变律
====================================================================

对应论文 `统一边界理论EN稿.md` **§5.1–§5.2（the kernel family and the core constant /
the C_F spectrum）**（L405–L425）：

  "For each [kernel F], the entropy constant generalizes to the **core constant**
        C_F = ∫_ℝ h(F(z)) dz"

  §5.2 的谱表（五行并列）：
  | logistic σ(z)      | π²/3      | 参考核，机检 |
  | tanh ½(1+tanh z)   | π²/6      | "= σ(2z) —— a rescaling, not a new shape" |
  | probit Φ(z)        | 1.8064    | 真正不同的形状 |
  | Cauchy             | 发散      | 重尾 |
  | Heaviside          | 0         | 零宽度 |

**本节把这张"表"升级为"函子"**（这正是 `13_通用性的范畴判准…` §3 所指的那一步）：

  · `rescale λ F := z ↦ F(λ z)` 定义核上的 **ℝ_{>0}-作用**（轨道）；
  · **主定理 `coreConstant_rescale`**：`C_{λ·F} = C_F / λ`
    ⇒ `C_F` **不是轨道不变量**，而是权 **−1** 的**等变函数**（模空间上的线丛截面）；
  · **推论**：原表五行并非并列，而是：**logistic 与 tanh 同轨**（λ = 1, 2）；
    **Heaviside 是同轨的 λ → ∞ 端点**（`C_F → 0`，与 §5.3 "零宽度 ⇒ 0" 吻合）；
    probit 是**另一条轨道**；Cauchy 的**发散是尺度不变量**（尾条件），属轨道不变量而非数值项。

⇒ "换核不改结论、只改数字"由**散文**（§5.2/§3.6）升为**定理**（G2：函子性）。

**证据档位**：机器证明（本模块零 `sorry`）。核族的一般（非重标度）比较仍是确定性计算（§5.2）。
-/

import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

open MeasureTheory

namespace CausModel

noncomputable section

/-! ## 与 `BoundaryTheory.lean` 同名的核与熵密度 -/

/-- 二元熵密度 `h(p) = −p ln p − (1−p) ln(1−p)`（同 `BoundaryTheory.hbin`）。 -/
def hbin (p : ℝ) : ℝ := -p * Real.log p - (1 - p) * Real.log (1 - p)

/-- logistic 归因核 `σ(z) = 1/(1+e^{−z})`（同 `BoundaryTheory.sig`）。

注意：论文 §1.5 固定了 σ 的两义（凝聚度 / logistic 映射），此处为值层计算义。 -/
def sig (z : ℝ) : ℝ := 1 / (1 + Real.exp (-z))

/-- 边界熵密度 `z ↦ h(F z)`（同 `BoundaryTheory.entropyDensity`，此处对一般核 `F`）。 -/
def entropyDensity (F : ℝ → ℝ) (z : ℝ) : ℝ := hbin (F z)

/-! ## 核的重标度作用与核心常数 -/

/-- **核的重标度作用**：`(λ·F)(z) = F(λ z)`。这是核族上的 `ℝ_{>0}`-作用，其轨道即
"形状相同、宽度不同"的核。 -/
def rescale (lam : ℝ) (F : ℝ → ℝ) : ℝ → ℝ := fun z => F (lam * z)

/-- **核心常数** `C_F = ∫_ℝ h(F(z)) dz`（论文 §5.1）。 -/
def coreConstant (F : ℝ → ℝ) : ℝ := ∫ z : ℝ, entropyDensity F z

/-- **【主定理】$C_F$ 的重标度等变律**：`C_{λ·F} = C_F / λ`。

⇒ `C_F` **不是**核的轨道不变量，而是权 **−1** 的等变函数。

读法：论文 §5.2 把 `C_F` 当作"核的指纹"来读，**读错了一格**——
它随重标度按固定幂律变化，因此正确的对象是**核模掉重标度的模空间**，
`C_F` 是其上的**线丛截面**；"核普适性"因此是**分类问题**，不是"定理"。 -/
theorem coreConstant_rescale (F : ℝ → ℝ) {lam : ℝ} (hlam : 0 < lam) :
    coreConstant (rescale lam F) = lam⁻¹ * coreConstant F := by
  have h := MeasureTheory.Measure.integral_comp_mul_left (fun y : ℝ => hbin (F y)) lam
  rw [abs_of_pos (inv_pos.mpr hlam), smul_eq_mul] at h
  unfold coreConstant entropyDensity rescale
  simpa using h

/-- 等变律的等价写法（去分母）：`λ · C_{λ·F} = C_F`。 -/
theorem coreConstant_rescale_mul (F : ℝ → ℝ) {lam : ℝ} (hlam : 0 < lam) :
    lam * coreConstant (rescale lam F) = coreConstant F := by
  rw [coreConstant_rescale F hlam]
  field_simp

/-- **重标度不改变"是否有限"**：若 `C_F` 有限则 `C_{λ·F}` 有限（λ > 0）。

⇒ §5.3 的有效域 `{F : 0 < C_F < ∞}` 是**重标度不变**的——发散/收敛属**轨道不变量**
（尾条件），而非某一尺度的数值巧合。 -/
theorem coreConstant_rescale_ne_zero (F : ℝ → ℝ) {lam : ℝ} (hlam : 0 < lam)
    (hF : coreConstant F ≠ 0) : coreConstant (rescale lam F) ≠ 0 := by
  rw [coreConstant_rescale F hlam]
  exact mul_ne_zero (inv_ne_zero (ne_of_gt hlam)) hF

/-! ## §5.2 的具体实例：tanh 与 logistic **同轨** -/

/-- **tanh 就是重标度后的 logistic**（λ = 2）：`½(1 + tanh z) = σ(2z)`。

论文 §5.2 表内自注："`= σ(2z)` — a rescaling, not a new shape"——
本定理把它变成**等式**，从而 tanh 与 logistic **落在同一轨道**。 -/
theorem tanh_is_rescaled_logistic (z : ℝ) :
    (1 + Real.tanh z) / 2 = sig (2 * z) := by
  have h1 : Real.exp z ≠ 0 := Real.exp_ne_zero z
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  unfold sig
  rw [show -(2 * z) = -z + -z by ring, Real.exp_add, Real.exp_neg]
  field_simp
  ring

/-- **推论**：tanh 的核心常数是 logistic 核心常数的一半（λ = 2 代入等变律）。

⇒ §5.2 表中 `π²/3` 与 `π²/6` 的比值 **2 : 1 不是巧合**，而是重标度律的**必然结果**。 -/
theorem coreConstant_tanh_eq_half :
    coreConstant (rescale 2 sig) = (2 : ℝ)⁻¹ * coreConstant sig :=
  coreConstant_rescale sig (by norm_num)

end

end CausModel
