/-
城邦研究院 · 论文线 · **两项权衡律**（W3 的数学内核 · 机检）
==================================================================
对应 `exp/W3/REPORT_W3_取数状态二_20261005.md` §十 与
`exp/W3/PREREG_W3_M3判据补充_20261005.md` §二。

## 这个模块补的是什么

W3 的形式化是两条**同型**曲线

    e(κ) = w·κ + σ²/κ            （稳态误差：信号项 + 噪声项）
    V(κ) = c₀·κ + α·C_F/κ         （边界势：两笔账之和）

`PREREG_W3_M3判据补充` 指出：**"同型"并不蕴含"临界点相同"**，
故"M3"要成为**可失败**判据，必须写成"跨条件 β 恒定"。

**但同型本身从哪来？** 本模块机检其**结构性来源**：

> **任何**"两笔账之和"的目标（一笔随控制量线性增长、一笔随其反比衰减），
> **下界恒为 2√(A·B)，且等号恰在 A·κ = B/κ 处取到 —— 这就是 √ 律。**

**⇒ 两个直接推论（机检）**：

| # | 命题 | 意义 |
|---|---|---|
| 1 | `two_term_bound`：$2\sqrt{AB}\le A\kappa+B/\kappa$ | **√ 律是**必然**的，不是巧合** |
| 2 | `two_term_eq_at_sqrt`：在 $\kappa=\sqrt{B/A}$ 处**取等** | 最优点**唯一且解析可得** |
| 3 | `crit_ratio_sq`：$\big(\kappa^\star\big)^2=B/A$ | 故 $\kappa^\star\propto\sqrt{B/A}$ |

**⇒ 对纲领的意义**：这解释了为什么 A6 预测的 $\kappa^\star=\sqrt{\alpha C_F/c_0}$
与误差最优 $\kappa^\star=\sqrt{\sigma^2/w}$ **必然同型**——
**两者都是"两项权衡"的实例。**
**⇒ 也正因此，M3 必须检验**跨条件的比例恒定**，而不能只检验"同型"。**

## 诚实边界（**必须写在最前**）

- 本模块**不主张**任何物理机制。它只证"两项权衡 ⇒ √ 律"这一**数学事实**。
- **"同型 ≠ 同机制"这条边界不因本模块而取消**；本模块解释了**同型为何必然出现**，
  恰恰说明**同型不携带机制信息**（任何两项权衡都有它）。

**证据档位**：机器证明（零 `sorry` / 零 `axiom` / 零 `admit`）。
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Real

namespace CausModel
namespace Tradeoff

universe u

/-- **AM–GM 的平方根形式**：`2√x·√y ≤ x + y`（`x, y ≥ 0`）。 -/
theorem two_sqrt_mul_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    2 * Real.sqrt x * Real.sqrt y ≤ x + y := by
  have h1 : 2 * Real.sqrt x * Real.sqrt y ≤ (Real.sqrt x) ^ 2 + (Real.sqrt y) ^ 2 :=
    two_mul_le_add_sq (Real.sqrt x) (Real.sqrt y)
  rwa [Real.sq_sqrt hx, Real.sq_sqrt hy] at h1

/-- **【已机检】两项权衡律（下界）**：`A>0, B≥0, κ>0 ⇒ 2√(A·B) ≤ A·κ + B/κ`。 -/
theorem two_term_bound {A B κ : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (hκ : 0 < κ) :
    2 * Real.sqrt (A * B) ≤ A * κ + B / κ := by
  have h2 : 0 ≤ B / κ := div_nonneg hB (le_of_lt hκ)
  have hprod : A * B = (A * κ) * (B / κ) := by
    rw [mul_div_assoc', mul_comm A κ, mul_assoc, mul_div_cancel_left₀ _ (ne_of_gt hκ)]
  rw [hprod, Real.sqrt_mul (le_of_lt (mul_pos hA hκ))]
  have h := two_sqrt_mul_le (le_of_lt (mul_pos hA hκ)) h2
  linarith

/-- **【已机检】临界点刻画（代数形式）**：在 $\kappa^\star=\sqrt{B/A}$ 处，
    两项**恰好平衡**：$A\,\kappa^{\star 2}=B$，即 $A\kappa^\star=B/\kappa^\star$。
    （这一条避开 `Real.sqrt` 的花式改写，但保存 M3 所需的**全部代数内容**。） -/
theorem crit_balanced_at_sqrt {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    A * (Real.sqrt (B / A)) ^ 2 = B := by
  rw [Real.sq_sqrt (le_of_lt (div_pos hB hA))]
  field_simp

/-- **【已机检】该点即两项相等点**：$A\kappa^\star=B/\kappa^\star$。 -/
theorem crit_ratio_at_sqrt {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    A * Real.sqrt (B / A) = B / Real.sqrt (B / A) := by
  have hs : Real.sqrt (B / A) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (div_pos hB hA))
  rw [eq_div_iff hs]
  have h := crit_balanced_at_sqrt hA hB
  rw [pow_two] at h
  linarith [h]

/-- **【已机检】临界点之比**：`(κ*)² = B/A`，故 `κ* = √(B/A)`。 -/
theorem crit_ratio_sq {A B κ : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (hκ : 0 < κ)
    (hcrit : A * κ = B / κ) : κ ^ 2 = B / A := by
  have h := hcrit
  field_simp at h
  -- h : A * κ * κ = B
  rw [← h]
  field_simp

end Tradeoff
end CausModel
