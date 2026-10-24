/-
LogisticCore.lean —— 可解芯七条的 Lean 化（第 60 轮）

对应件：`03-数学形式化/边界对_可解芯与饱和桥指数更正_20261006.md` §三（T1–T7）。
该件原先只有数值/`decimal` 验证（`scripts/verify_boundary_pair_core.py`），P4 档位为 ✗。
本件把**可 Lean 化的部分**送进 P4。

可解芯（论文定义 2.2／2.3）：
    p_S(x) = σ(κ(x−μ)),  p_N(x) = 1 − p_S(x),  b(x) = 1 − |p_S(x) − p_N(x)| ∈ [0,1]

本件证明：
  · **T1** 稳定形式 `b = 2σ(−|z|)`（`z = κ(x−μ)`）——数值稳定，无灾难性相消；
  · **T2** 水平集 `θ ≤ b ↔ |x−μ| ≤ L(θ)/κ`，`L(θ) = ln((2−θ)/θ)`；**端点处 `b` 恰为 `θ`**（精确，非近似）；
  · **T3** 宽度标度：`θ ≤ b ↔ |κ(x−μ)| ≤ L(θ)`——**与 κ 无关**，即 `w·κ = 2L`（"宽度严格 ∝ 1/κ"的机检形式）；
  · **T4** 第 42 轮操作性定义**不可用**：`0 < b` **对一切 x 成立** ⇒ `{b>0} = Ω` ⇒ `μ({b>0}) = μ(Ω)`，该定义只给常数 0；
  · **T6** 互补：`Fix(c) = {b ≤ θ₀} = {|κ(x−μ)| ≥ L(θ₀)}`（**两条尾**），与脊 `{x = μ}` 不相交；
  · **T7** 芯的三成分限制：`p_S + p_N = 1`（`p_U ≡ 0`）——这是**边界**，不是结论。

**故意不证明 T5**：T5（饱和桥指数 1/2）已在第 44 轮被**作废**
（无闭式桥；见 `凝聚度的阈值与局部比不可互推_20261006.md`）。
把已作废命题 Lean 化会把三态记错，故此处**留空并注明**。
T5 的前提问题（σ_coh 必须先有口径：宽度比／面积比／阈值比）是待裁定的 (i) 号事项。

0 `sorry` / 0 `axiom`。编译：见 `build_lean_all.sh`。
-/
import Mathlib

open scoped Real

namespace LogisticCore

/-! ## 一 · 逻辑斯蒂函数与三条基础引理 -/

/-- 逻辑斯蒂函数 `σ(z) = 1/(1+e^{−z})`。 -/
noncomputable def sig (z : ℝ) : ℝ := 1 / (1 + Real.exp (-z))

theorem sig_pos (z : ℝ) : 0 < sig z := by
  unfold sig
  positivity

theorem sig_lt_one (z : ℝ) : sig z < 1 := by
  unfold sig
  rw [div_lt_one (by positivity)]
  linarith [Real.exp_pos (-z)]

/-- `σ(−z) = 1 − σ(z)`（互补对称）。 -/
theorem sig_neg (z : ℝ) : sig (-z) = 1 - sig z := by
  unfold sig
  rw [neg_neg]
  have hden : (1 + Real.exp (-z)) ≠ 0 := by positivity
  have hmul : Real.exp z * Real.exp (-z) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  field_simp
  nlinarith [hmul]

/-- `2σ(z) − 1 = (e^z − 1)/(e^z + 1)`（双曲正切形式，用于取绝对值）。 -/
theorem two_sig_sub_one (z : ℝ) : 2 * sig z - 1 = (Real.exp z - 1) / (Real.exp z + 1) := by
  unfold sig
  have hden : (1 + Real.exp (-z)) ≠ 0 := by positivity
  have hden2 : (Real.exp z + 1) ≠ 0 := by positivity
  have hmul : Real.exp z * Real.exp (-z) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  field_simp
  nlinarith [hmul]

/-! ## 二 · T1 稳定形式 -/

/-- 辅助：`f(z) = (e^z − 1)/(e^z + 1)` 是奇函数。 -/
private theorem f_odd (z : ℝ) :
    (Real.exp (-z) - 1) / (Real.exp (-z) + 1)
      = -((Real.exp z - 1) / (Real.exp z + 1)) := by
  have h1 : (Real.exp (-z) + 1) ≠ 0 := by positivity
  have h2 : (Real.exp z + 1) ≠ 0 := by positivity
  have hmul : Real.exp z * Real.exp (-z) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  field_simp
  nlinarith [hmul]

/-- 辅助：`f` 在 `z ≥ 0` 上非负。 -/
private theorem f_nonneg {z : ℝ} (h : 0 ≤ z) :
    0 ≤ (Real.exp z - 1) / (Real.exp z + 1) := by
  apply div_nonneg _ (by positivity)
  have h1 : (1:ℝ) ≤ Real.exp z := by
    have h2 := Real.exp_le_exp.mpr h
    rwa [Real.exp_zero] at h2
  linarith

/-- 辅助：`|2σ(z) − 1| = (e^{|z|} − 1)/(e^{|z|} + 1)`。 -/
private theorem abs_two_sig_sub_one (z : ℝ) :
    |2 * sig z - 1| = (Real.exp |z| - 1) / (Real.exp |z| + 1) := by
  rw [two_sig_sub_one]
  by_cases h : 0 ≤ z
  · rw [abs_of_nonneg (f_nonneg h), abs_of_nonneg h]
  · have hz : z < 0 := lt_of_not_ge h
    have hfz : (Real.exp z - 1) / (Real.exp z + 1) ≤ 0 := by
      have h1 : (0:ℝ) ≤ (Real.exp (-z) - 1) / (Real.exp (-z) + 1) := f_nonneg (by linarith)
      rw [f_odd z] at h1
      linarith
    rw [abs_of_nonpos hfz, abs_of_neg hz, f_odd]

/-- 边界隶属度 `b(x) = 1 − |p_S(x) − p_N(x)|`（定义 2.2；`p_N = 1 − p_S`）。 -/
noncomputable def b (κ μ x : ℝ) : ℝ := 1 - |2 * sig (κ * (x - μ)) - 1|

/-- **T1（稳定形式）**：`b(x) = 2σ(−|κ(x−μ)|)`。
左式在大 `|z|` 时有灾难性相消，右式数值稳定——两者**恒等**。 -/
theorem T1_stable_form (κ μ x : ℝ) :
    b κ μ x = 2 * sig (-(|κ * (x - μ)|)) := by
  unfold b
  rw [abs_two_sig_sub_one]
  unfold sig
  rw [neg_neg]
  have hden : (Real.exp |κ * (x - μ)| + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- 隶属度**处处为正**（T4 的代数内容；见下）。 -/
theorem b_pos (κ μ x : ℝ) : 0 < b κ μ x := by
  rw [T1_stable_form]
  have := sig_pos (-(|κ * (x - μ)|))
  linarith

/-! ## 三 · T2/T3 水平集与宽度标度 -/

/-- 水平集常数 `L(θ) = ln((2−θ)/θ)`。 -/
noncomputable def L (θ : ℝ) : ℝ := Real.log ((2 - θ) / θ)

theorem L_pos {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) : 0 < L θ := by
  unfold L
  apply Real.log_pos
  rw [lt_div_iff₀ hθ0]
  linarith

/-- **T3（宽度标度，精确）**：`θ ≤ b(x) ⟺ |κ(x−μ)| ≤ L(θ)`。
右式**不含 κ**，即模糊宽度满足 `w·κ = 2L(θ)`——"宽度严格 ∝ 1/κ"的机检形式。 -/
theorem T3_width_scaling (κ μ x θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    θ ≤ b κ μ x ↔ |κ * (x - μ)| ≤ L θ := by
  have hx : 0 < (2 - θ) / θ := div_pos (by linarith) hθ0
  rw [T1_stable_form, L]
  unfold sig
  rw [neg_neg]
  rw [show (2 * (1 / (1 + Real.exp |κ * (x - μ)|)))
        = 2 / (1 + Real.exp |κ * (x - μ)|) by ring]
  rw [le_div_iff₀ (by positivity : (0:ℝ) < 1 + Real.exp |κ * (x - μ)|)]
  rw [show θ * (1 + Real.exp |κ * (x - μ)|) ≤ 2
        ↔ Real.exp |κ * (x - μ)| ≤ (2 - θ) / θ by
        rw [le_div_iff₀ hθ0]
        constructor <;> intro h <;> linarith]
  exact (Real.le_log_iff_exp_le hx).symm

/-- **T2（水平集）**：`{x : b(x) ≥ θ} = [μ − L(θ)/κ, μ + L(θ)/κ]`。 -/
theorem T2_level_set (κ μ x θ : ℝ) (hκ : 0 < κ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    θ ≤ b κ μ x ↔ |x - μ| ≤ L θ / κ := by
  rw [T3_width_scaling κ μ x θ hθ0 hθ1, abs_mul, abs_of_pos hκ, le_div_iff₀ hκ]
  ring_nf

/-- **T6（互补）**：`Fix(c) = {x : b(x) ≤ θ} = {x : L(θ) ≤ |κ(x−μ)|}`，即**两条尾**
（深"我"与深"非我"）；脊 `∂S = {x = μ}` 不在其中。

**注意（本轮修正）**：T6 **不能**由 T3 取否得到——T3 是 `θ ≤ b ↔ |z| ≤ L`，
取否只给**严格**命题 `b < θ ↔ L < |z|`，而 T6 需要**非严格**的 `b ≤ θ ↔ L ≤ |z|`。
故此处直接做代数（`Real.log_le_iff_le_exp`），不绕道 T3。 -/
theorem T6_complement (κ μ x θ : ℝ) (_hκ : 0 < κ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    b κ μ x ≤ θ ↔ L θ ≤ |κ * (x - μ)| := by
  have hx : 0 < (2 - θ) / θ := div_pos (by linarith) hθ0
  rw [T1_stable_form, L]
  unfold sig
  rw [neg_neg]
  rw [show (2 * (1 / (1 + Real.exp |κ * (x - μ)|)))
        = 2 / (1 + Real.exp |κ * (x - μ)|) by ring]
  rw [div_le_iff₀ (by positivity : (0:ℝ) < 1 + Real.exp |κ * (x - μ)|)]
  rw [show 2 ≤ θ * (1 + Real.exp |κ * (x - μ)|)
        ↔ (2 - θ) / θ ≤ Real.exp |κ * (x - μ)| by
        rw [div_le_iff₀ hθ0]
        constructor <;> intro h <;> linarith]
  exact (Real.log_le_iff_le_exp hx).symm

/-- **T2 端点（精确，非数值近似）**：`b(μ + L(θ)/κ) = θ`。 -/
theorem T2_endpoint (κ μ θ : ℝ) (hκ : 0 < κ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    b κ μ (μ + L θ / κ) = θ := by
  have hL := L_pos hθ0 hθ1
  have hsub : μ + L θ / κ - μ = L θ / κ := by ring
  have habs : |μ + L θ / κ - μ| = L θ / κ := by
    rw [hsub, abs_of_nonneg (div_nonneg (le_of_lt hL) (le_of_lt hκ))]
  refine le_antisymm ?_ ((T2_level_set κ μ (μ + L θ / κ) θ hκ hθ0 hθ1).mpr (le_of_eq habs))
  rw [T6_complement κ μ (μ + L θ / κ) θ hκ hθ0 hθ1]
  rw [hsub, abs_mul, abs_of_pos hκ, abs_of_nonneg (div_nonneg (le_of_lt hL) (le_of_lt hκ))]
  rw [mul_div_cancel₀ _ hκ.ne']

/-! ## 四 · T4 与 T7：两条**限制**（不是结果，是边界） -/

/-- **T4（第 42 轮操作性定义不可用）**：`0 < b(x)` 对**一切** `x` 成立，
故 `{x : b(x) > 0} = Ω`，第 42 轮的 `σ_coh := 1 − μ({b>0})/μ(Ω)` 在任何有限测度空间上恒为常数 0，
**该定义作废**（不是"取值很大"，而是"不携带信息"）。 -/
theorem T4_operational_unusable (κ μ x : ℝ) : 0 < b κ μ x :=
  b_pos κ μ x

/-- **T7（芯的边界）**：芯上 `p_S + p_N = 1`，即 `p_U ≡ 0`。
芯上的"模糊"由**隶属度亏空 b** 承担，**不是**"不确定概率"；三成分场 `(p_S,p_N,p_U)` 未被芯行使。 -/
theorem T7_no_third_component (z : ℝ) : sig z + (1 - sig z) = 1 := by
  ring

end LogisticCore
