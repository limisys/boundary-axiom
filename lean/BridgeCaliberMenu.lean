/-
BridgeCaliberMenu.lean —— 桥的口径：**这个选择值多少**（第 64 轮）

**背景**：靶心 1 只剩一个缺口，而且是**定义**问题而非数学问题：
$\sigma_{\text{coh}}$ 该按**宽度比**、**面积比**还是**阈值比**定义？高总未拍板。
本轮不替高总决定，而是**把这个决定的代价算出来**——这就是仲裁阶段该交的东西。

记 $r=\sigma_{\text{mech}}/\sigma^\ast\ge0$（程序自己的恒等式 $\sigma_{\text{mech}}=\sigma^\ast(\kappa/\kappa^\star)^2$
给出 $\kappa/\kappa^\star=\sqrt r$）。两个候选桥：

  · **宽度比口径**（第 43 轮由模糊宽度 $\propto1/\kappa$ **推出**）：`widthBridge r = min (√r) 1`
  · **线性口径**（第 40 轮写法，已被取代）：             `linearBridge r = min r 1`
  · （第三种，**阈值比口径** `sigmaCoh`，已单列于 `BoundaryTheory_sigmaCoh.lean`，
     本件**不重复声明**，只在此注明三者同为一个待裁定菜单的三项。）

**本轮的主结果**：

  · **`eq_iff`**      两者相等 $\iff r=0\ \lor\ 1\le r$ —— **只在两端一致**；
  · **`gap_eq_quarter_iff`** 差距的**最大值恰为 $1/4$**，且**只在 $r=1/4$** 取到：
      $\sqrt r-r\le\tfrac14$，等号 $\iff r=\tfrac14$；
  · `gap_witness`    $r=1/4$ 处：$1/2$ 对 $1/4$。

**结论（给裁定的成本表）**：换口径**最多改变 $0.25$**，且**只在唯一一点**达到该差；
两端**完全一致**。故这不是"选哪个都行"的措辞问题，也不是"差别很大"的实质分歧——
它是一个**有界、可定位、只在中间段生效**的选择。

0 `sorry` / 0 `axiom`。
-/
import Mathlib

open scoped Real

namespace BridgeCaliber

/-! ## 一 · 两个候选口径 -/

/-- **宽度比口径**：模糊宽度 $\propto1/\kappa$ 直接推出 $\sigma_{\text{coh}}=\min(\sqrt r,1)$。 -/
noncomputable def widthBridge (r : ℝ) : ℝ := min (Real.sqrt r) 1

/-- **线性口径**（第 40 轮旧写法）：$\sigma_{\text{coh}}=\min(r,1)$。 -/
noncomputable def linearBridge (r : ℝ) : ℝ := min r 1

theorem widthBridge_mono : Monotone widthBridge := by
  intro a b h
  exact min_le_min (Real.sqrt_le_sqrt h) le_rfl

theorem linearBridge_mono : Monotone linearBridge := by
  intro a b h
  exact min_le_min h le_rfl

theorem widthBridge_nonneg (r : ℝ) : 0 ≤ widthBridge r :=
  le_min (Real.sqrt_nonneg r) zero_le_one

theorem widthBridge_le_one (r : ℝ) : widthBridge r ≤ 1 := min_le_right _ _

theorem linearBridge_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ linearBridge r :=
  le_min hr zero_le_one

theorem linearBridge_le_one (r : ℝ) : linearBridge r ≤ 1 := min_le_right _ _

/-! ## 二 · 两者**只在两端**一致 -/

theorem eq_at_zero : widthBridge 0 = linearBridge 0 := by
  unfold widthBridge linearBridge
  rw [Real.sqrt_zero]

theorem eq_of_one_le {r : ℝ} (hr : 1 ≤ r) : widthBridge r = linearBridge r := by
  unfold widthBridge linearBridge
  rw [min_eq_right (Real.one_le_sqrt.mpr hr), min_eq_right hr]

/-- **（主结果一）** 两个口径相等 **当且仅当** $r=0$ 或 $1\le r$——**只在两端一致**。
中间段 $(0,1)$ 上它们**严格不同**，所以"选哪个"绝非措辞问题。 -/
theorem eq_iff {r : ℝ} (hr : 0 ≤ r) :
    widthBridge r = linearBridge r ↔ r = 0 ∨ 1 ≤ r := by
  constructor
  · intro h
    rcases eq_or_lt_of_le hr with h0 | hpos
    · exact Or.inl h0.symm
    · by_cases h1 : 1 ≤ r
      · exact Or.inr h1
      · exfalso
        have hr1 : r < 1 := lt_of_not_ge h1
        have hr0 : r ≠ 0 := ne_of_gt hpos
        have hrs : Real.sqrt r < 1 := by
          nlinarith [Real.sq_sqrt hr, Real.sqrt_nonneg r]
        have hw : widthBridge r = Real.sqrt r := by
          unfold widthBridge; exact min_eq_left hrs.le
        have hl : linearBridge r = r := by
          unfold linearBridge; exact min_eq_left hr1.le
        have hs : Real.sqrt r = r := by
          have h1' : Real.sqrt r = linearBridge r := by rw [← hw]; exact h
          rw [hl] at h1'
          exact h1'
        have hfac : r * (r - 1) = 0 := by nlinarith [hs, Real.sq_sqrt hr]
        rcases mul_eq_zero.mp hfac with hz | hz
        · exact hr0 hz
        · linarith
  · rintro (h | h)
    · rw [h]; exact eq_at_zero
    · exact eq_of_one_le h

/-! ## 三 · 差距的上确界**恰为 1/4** -/

/-- **（主结果二）** 在 $0\le r\le1$ 上 $\sqrt r-r\le\tfrac14$，**且等号只在 $r=\tfrac14$**。 -/
theorem gap_le_quarter {r : ℝ} (hr : 0 ≤ r) : Real.sqrt r - r ≤ 1 / 4 := by
  nlinarith [sq_nonneg (Real.sqrt r - 1 / 2), Real.sq_sqrt hr]

theorem gap_eq_quarter_iff {r : ℝ} (hr : 0 ≤ r) :
    Real.sqrt r - r = 1 / 4 ↔ r = 1 / 4 := by
  constructor
  · intro h
    have hsq : (Real.sqrt r - 1 / 2) ^ 2 = 0 := by
      nlinarith [Real.sq_sqrt hr, h]
    have hroot : Real.sqrt r = 1 / 2 := by
      have h' := sq_eq_zero_iff.mp hsq
      linarith
    rw [← Real.sq_sqrt hr, hroot]
    norm_num
  · intro h
    have hs : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [h, hs]
    norm_num

/-- 见证：$r=1/4$ 处，宽度比口径给 $1/2$，线性口径给 $1/4$——差 $1/4$，正是最大值。 -/
theorem gap_witness :
    widthBridge (1 / 4) = 1 / 2 ∧ linearBridge (1 / 4) = 1 / 4 := by
  have hs : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  constructor
  · unfold widthBridge; rw [hs]; norm_num
  · unfold linearBridge; norm_num

/-- 差距函数在该点的值：`widthBridge - linearBridge = 1/4`。 -/
theorem gap_at_quarter :
    widthBridge (1 / 4) - linearBridge (1 / 4) = 1 / 4 := by
  rw [gap_witness.1, gap_witness.2]; norm_num

end BridgeCaliber
