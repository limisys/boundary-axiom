/-
城邦研究院 · 论文线 · C 阶段 · R2：核轨道的显式不变量
=========================================================

**目标**：证明 §5.2 五行核谱表**不是一个平铺的表**，而是一个**有不变量的分类**——
从而把 C4（"不存在单一万有核"）从数值观察升为**定理**。

**不变量**：`I(F) := C_F · F'(0)`。

重标度 `(λ·F)(z) = F(λz)` 下：
  · `C_{λ·F} = C_F / λ`（B6 的 `coreConstant_rescale`）；
  · `(λ·F)'(0) = λ · F'(0)`（链式法则）。
⇒ **`I` 在重标度下不变** ⇒ `I` 是核轨道的**分类不变量**。

数值（确定性计算，非机检）：
  · logistic σ：`I = (π²/3)·(1/4) = π²/12 ≈ 0.822467`
  · tanh `= σ(2z)`：`I = (π²/6)·(1/2) = π²/12` ✅ 同轨
  · probit Φ：`I = 1.806395 × 0.398942 ≈ 0.720647` ⚠️ **异轨**

⇒ **logistic 轨道 ≠ probit 轨道 ⇒ 不存在单一万有核 ⇒ G4 在核层为假。**

**证据档位**：本模块的不变性为机器证明；上表数值为确定性计算。

**R2b 增补（零浮点负定理）**：上表对 probit 的判异依赖 `C_Φ` 的**数值积分**。
模块末尾另给一条**完全机检、零浮点**的判异证法（`plateau_not_in_sig_orbit`）：
严格单调性与"平坦带"在正重标度下互不转化。⇒ "不存在单一万有核"因此至少有一个
**不含数值成分的可引负定理**，不再整体悬挂在浮点比较之上。
-/

import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import CausModel.KernelModuli

open MeasureTheory

namespace CausModel

noncomputable section

/-- **核的轨道不变量** `I(F) = C_F · F'(0)`。

由 `C_F` 的权 −1 等变律与 `F'(0)` 的权 +1 齐次性相乘得到：
两因子在重标度下反向变化，乘积不变。 -/
def orbitInvariant (F : ℝ → ℝ) : ℝ := coreConstant F * deriv F 0

/-- **重标度下导数的变换律**：`(λ·F)'(0) = λ · F'(0)`（链式法则）。

（Lean 的 `deriv` 在不可导处回落到 0，故本引理**无需可导性假设**。） -/
theorem deriv_rescale (F : ℝ → ℝ) (lam : ℝ) :
    deriv (rescale lam F) 0 = lam * deriv F 0 := by
  unfold rescale
  rw [deriv_comp_mul_left]
  simp

/-- **【主定理】轨道不变性**：`I(λ·F) = I(F)`（λ > 0）。

⇒ `I` 无法区分同一轨道内的核（logistic / tanh / 任意重标度），
   **但能区分不同轨道**（logistic vs probit）。
   这就是"核普适性是一个**分类问题**，不是一条定理"的机器可证内核。 -/
theorem orbitInvariant_rescale (F : ℝ → ℝ) {lam : ℝ} (hlam : 0 < lam) :
    orbitInvariant (rescale lam F) = orbitInvariant F := by
  unfold orbitInvariant
  rw [coreConstant_rescale F hlam, deriv_rescale F lam]
  field_simp

/-- **轨道的分类不变量**：同轨道 ⇒ 同不变量。

逆否用法：`I(F) ≠ I(G)` ⇒ `F` 与 `G` **不同轨** ⇒ **不存在把它们联系起来的重标度**，
因而**不存在单一万有核**（C4 / G4 在核层为假）。 -/
theorem ne_orbitInvariant_of_ne {F G : ℝ → ℝ}
    (h : orbitInvariant F ≠ orbitInvariant G) :
    ¬ ∃ lam : ℝ, 0 < lam ∧ G = rescale lam F := by
  rintro ⟨lam, hlam, rfl⟩
  exact h (orbitInvariant_rescale F hlam).symm

/-- **轨道不变量的等价判据**：两个核同轨 ⟺ 它们的 `(C_F, F'(0))` 成比例且比例为正，
等价地 `I` 相等（在非退化情形）。

此处给出正向的一半（机器可证的部分）。 -/
theorem orbitInvariant_eq_of_same_orbit {F G : ℝ → ℝ} {lam : ℝ} (hlam : 0 < lam)
    (hG : G = rescale lam F) : orbitInvariant G = orbitInvariant F := by
  rw [hG, orbitInvariant_rescale F hlam]

/-! ## R2b：零浮点的可引负定理 —— 平坦核不在 logistic 轨道内

上文把 C4/G4 的反例（logistic vs probit）建立在 `I(F) = C_F · F'(0)` 的**数值比较**上：
`I(σ) ≈ 0.822467 ≠ 0.720647 ≈ I(Φ)`。该比较的两个数值都是**确定性计算**（非机检）——
因为 `C_Φ = ∫ h(Φ z) dz` 的严格上下界不在当前 Mathlib 之内，这条判异**无法**仅靠机检闭合。

本节给出一条**完全机检、零浮点**的替代判异，使"不存在单一万有核"至少有一个
不含任何数值成分的**可引负定理**：

  · `sig` 即 Mathlib 的 `Real.sigmoid`，故**严格单调**（`Real.sigmoid_strictMono`）；
  · 定义**平坦核** `plateau`：在中心带 `[-1/2, 1/2]` 上恒为 `1/2`（连续、单调、值域 ⊆ [0,1]）；
  · 正重标度**保持**"非严格单调"——`F` 的平坦带经 `z ↦ z/lam` 缩放后仍是一条平坦带；
  · 而重标度**保持**严格单调。故 `plateau` 无论怎样重标度都不可能等于 `sig`。

⇒ **`plateau` 与 logistic 核不同轨**，且此结论**不含任何浮点比较**。
-/

/-- **logistic 核就是 Mathlib 的 `Real.sigmoid`**（值层计算义）。

这座桥使 KernelModuli 的 `sig` 直接继承 Mathlib 已证的严格单调性、连续性与导数公式，
无需在本工程内重复证明。 -/
theorem sig_eq_sigmoid : sig = Real.sigmoid := by
  funext z
  simp [sig, Real.sigmoid, one_div]

/-- logistic 核**严格单调**（由 Mathlib 的 `Real.sigmoid_strictMono` 转移）。 -/
theorem strictMono_sig : StrictMono sig := by
  rw [sig_eq_sigmoid]
  exact Real.sigmoid_strictMono

/-- logistic 核在中心的斜率：`σ'(0) = 1/4`（机检，取代原先的数值读数）。 -/
theorem deriv_sig_zero : deriv sig 0 = 1 / 4 := by
  rw [sig_eq_sigmoid, Real.deriv_sigmoid]
  norm_num [Real.sigmoid]

/-- **平坦核**：中心带 `[-1/2, 1/2]` 上恒为 `1/2` 的连续单调核。

它是"零浮点判异"的见证核：与 logistic 核的区别不在数值大小，而在**形状的定性类型**
（有无平坦带），而形状类型在正重标度下不变。 -/
def plateau (z : ℝ) : ℝ :=
  min (1 / 2) (max 0 (z + 1)) + min (1 / 2) (max 0 (z - 1 / 2))

/-- 平坦核单调不减（两个饱和斜坡之和）。 -/
theorem monotone_plateau : Monotone plateau := by
  intro a b hab
  have h1 : max 0 (a + 1) ≤ max 0 (b + 1) := max_le_max le_rfl (by linarith)
  have h2 : min (1 / 2 : ℝ) (max 0 (a + 1)) ≤ min (1 / 2) (max 0 (b + 1)) :=
    min_le_min le_rfl h1
  have h3 : max 0 (a - 1 / 2) ≤ max 0 (b - 1 / 2) := max_le_max le_rfl (by linarith)
  have h4 : min (1 / 2 : ℝ) (max 0 (a - 1 / 2)) ≤ min (1 / 2) (max 0 (b - 1 / 2)) :=
    min_le_min le_rfl h3
  unfold plateau
  linarith

/-- 平坦核取值落在 `[0, 1]`（故它是合法的归因核值域）。 -/
theorem plateau_mem_Icc (z : ℝ) : plateau z ∈ Set.Icc (0 : ℝ) 1 := by
  rw [Set.mem_Icc]
  have h1 : 0 ≤ min (1 / 2 : ℝ) (max 0 (z + 1)) := le_min (by norm_num) (le_max_left _ _)
  have h2 : min (1 / 2 : ℝ) (max 0 (z + 1)) ≤ 1 / 2 := min_le_left _ _
  have h3 : 0 ≤ min (1 / 2 : ℝ) (max 0 (z - 1 / 2)) := le_min (by norm_num) (le_max_left _ _)
  have h4 : min (1 / 2 : ℝ) (max 0 (z - 1 / 2)) ≤ 1 / 2 := min_le_left _ _
  unfold plateau
  constructor <;> linarith

/-- 平坦核的中心带：`plateau (-1/2) = plateau (1/2) = 1/2`。 -/
theorem plateau_neg_half : plateau (-(1 / 2)) = 1 / 2 := by norm_num [plateau]

theorem plateau_pos_half : plateau (1 / 2) = 1 / 2 := by norm_num [plateau]

/-- **平坦核不严格单调**：它在 `[-1/2, 1/2]` 上取常值。 -/
theorem plateau_not_strictMono : ¬ StrictMono plateau := by
  intro h
  have := h (by norm_num : -(1 / 2 : ℝ) < 1 / 2)
  rw [plateau_neg_half, plateau_pos_half] at this
  exact lt_irrefl _ this

/-- **正重标度保持"非严格单调"**：若 `F` 有一条平坦带，则 `rescale lam F`（λ > 0）
也有一条平坦带，故不可能严格单调。

这是判异定理的唯一"几何"环节：平坦带在 `z ↦ lam * z` 下被缩放到 `z ↦ z / lam`，
但**不会消失**。 -/
theorem not_strictMono_rescale {F : ℝ → ℝ} (h : ¬ StrictMono F) {lam : ℝ}
    (hlam : 0 < lam) : ¬ StrictMono (rescale lam F) := by
  intro hG
  refine h fun a b hab => ?_
  have h' : a / lam < b / lam := (div_lt_div_iff_of_pos_right hlam).mpr hab
  have h1 : lam * (a / lam) = a := by
    rw [← mul_div_assoc, mul_div_cancel_left₀ a (ne_of_gt hlam)]
  have h2 : lam * (b / lam) = b := by
    rw [← mul_div_assoc, mul_div_cancel_left₀ b (ne_of_gt hlam)]
  have := hG h'
  simpa [rescale, h1, h2] using this

/-- **【可引负定理 · 零浮点】平坦核不可重标度为 logistic 核。**

不存在 `lam > 0` 使 `σ = rescale lam plateau`。证明只用到两件事：
`sig` 严格单调（Mathlib），而任何正重标度后的 `plateau` 都不严格单调（本模块）。

⇒ 这是 C4 / G4 在核层的**不含数值成分**的反例：它与 probit 反例并列，
前者机检、后者为确定性计算，两者的证据档位在论文中分别标注。 -/
theorem plateau_not_in_sig_orbit :
    ¬ ∃ lam : ℝ, 0 < lam ∧ sig = rescale lam plateau := by
  rintro ⟨lam, hlam, h⟩
  have hmono : StrictMono (rescale lam plateau) := h ▸ strictMono_sig
  exact not_strictMono_rescale plateau_not_strictMono hlam hmono

/-- **正重标度保持严格单调**（与 `not_strictMono_rescale` 对偶）。 -/
theorem strictMono_rescale {F : ℝ → ℝ} (h : StrictMono F) {lam : ℝ} (hlam : 0 < lam) :
    StrictMono (rescale lam F) := by
  intro a b hab
  exact h (mul_lt_mul_of_pos_left hab hlam)

/-- 判异的对称形式：`plateau` 不在 logistic 核的轨道内，两个方向都排除。

（重标度关系是自反的且在 λ > 0 下可逆，故 `sig = rescale lam plateau` 与
`plateau = rescale (1/lam) sig` 等价；此处把两个方向都写成定理，便于逐条引用。） -/
theorem plateau_ne_sig_orbit_both :
    (¬ ∃ lam : ℝ, 0 < lam ∧ sig = rescale lam plateau) ∧
    (¬ ∃ lam : ℝ, 0 < lam ∧ plateau = rescale lam sig) := by
  refine ⟨plateau_not_in_sig_orbit, ?_⟩
  rintro ⟨lam, hlam, h⟩
  have hmono : StrictMono plateau := h.symm ▸ strictMono_rescale strictMono_sig hlam
  exact plateau_not_strictMono hmono

end

end CausModel
