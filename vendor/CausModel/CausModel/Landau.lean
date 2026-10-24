/-
城邦研究院 · 论文线 · B 阶段扩展 · §3.3 Landau 分歧的**标准数学重述**
======================================================================

**背景（风险评估 R-1 / 裁定 D3-§3.3）**

论文 §3.3（L265–L275）原文把 Landau 分歧读作 "**splitting of limits**"：

  "*Categorical reading:* at `r = 0` the minimal-object set splits from a one-point set
   into a two-point set — **a limit that fails to be preserved** at the critical parameter:
   a **splitting of limits**."

**问题**：该节**没有给出任何图**。范畴学中"极限不被保持"须先指定一个图（函子 `J → C`）与
其锥；**没有图就没有极限**，因此"证明它交换 / 不被保持"**不是良定义的任务**。

**裁定**：不做高阶范畴硬写（mathlib 无 2-极限 API，且该陈述非标准）；改为**标准数学的诚实重述**：

  临界轨迹 `Crit = {(r, φ) : ∂_φ V_r(φ) = 0}` 到控制参数 `r` 的投影是**分歧覆盖**：
  · `r < 0`：纤维 1 点（`φ = 0`）；
  · `r > 0`：纤维 3 点（`φ = 0, ±√(r/2)`）；
  · `r = 0`：**分支点**。

这保留了原稿的全部直觉（"结构在临界处一分为二"），但用的是**标准语言**（分歧覆盖 / 分支点），
且**可机检**——即本模块。

**证据档位**：机器证明（本模块零 `sorry`）。
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace CausModel

noncomputable section

/-- 论文 §3.3 的 Landau 势：`V(φ; r) = −r φ² + φ⁴`。 -/
def landau (r φ : ℝ) : ℝ := -r * φ ^ 2 + φ ^ 4

/-- 临界方程 `∂_φ V = 0`，写成多项式形式 `−2rφ + 4φ³ = 0`。 -/
def landauCritical (r φ : ℝ) : Prop := -2 * r * φ + 4 * φ ^ 3 = 0

/-- 临界方程因式分解：`−2rφ + 4φ³ = 2φ(2φ² − r)`。 -/
theorem landau_critical_factor (r φ : ℝ) :
    -2 * r * φ + 4 * φ ^ 3 = 2 * φ * (2 * φ ^ 2 - r) := by
  ring

/-- **临界轨迹的显式分解**：`Crit = {φ = 0} ∪ {φ² = r/2}`。

这是原稿 "splitting of limits" 想要的**真实数学内容**：临界集在 `r = 0` 处由一条直线
与一条抛物线相交而成——**分歧覆盖的分支点**，而非范畴学意义的极限。 -/
theorem landau_critical_iff (r φ : ℝ) :
    landauCritical r φ ↔ φ = 0 ∨ φ ^ 2 = r / 2 := by
  unfold landauCritical
  rw [landau_critical_factor]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h1
    · exact Or.inl (by linarith)
    · right; linarith
  · rintro (h | h)
    · rw [h]; ring
    · rw [h]; ring

/-- **次临界（r ≤ 0）：纤维为单点**。 -/
theorem landau_fiber_singleton {r φ : ℝ} (hr : r ≤ 0)
    (h : landauCritical r φ) : φ = 0 := by
  rcases (landau_critical_iff r φ).mp h with h0 | h2
  · exact h0
  · have hle : φ ^ 2 ≤ 0 := by rw [h2]; linarith
    exact sq_eq_zero_iff.mp (le_antisymm hle (sq_nonneg φ))

/-- **超临界（r > 0）：纤维为三点** `φ = 0, ±√(r/2)`。

⇒ 纤维数在 `r = 0` 处由 **1 跳为 3** —— 这就是"分歧"的精确含义。 -/
theorem landau_fiber_three {r : ℝ} (hr : 0 < r) :
    landauCritical r 0 ∧
    landauCritical r (Real.sqrt (r / 2)) ∧
    landauCritical r (-Real.sqrt (r / 2)) ∧
    Real.sqrt (r / 2) ≠ 0 ∧
    Real.sqrt (r / 2) ≠ -Real.sqrt (r / 2) ∧
    (0 : ℝ) ≠ -Real.sqrt (r / 2) := by
  have h2 : (0 : ℝ) < r / 2 := by linarith
  have hsq : Real.sqrt (r / 2) ^ 2 = r / 2 := Real.sq_sqrt h2.le
  have hpos : 0 < Real.sqrt (r / 2) := Real.sqrt_pos.mpr h2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [landau_critical_iff]; exact Or.inl rfl
  · rw [landau_critical_iff]; right; rw [hsq]
  · rw [landau_critical_iff]; right
    rw [neg_sq, hsq]
  · exact ne_of_gt hpos
  · intro h
    have : (0:ℝ) < Real.sqrt (r/2) := hpos
    linarith
  · intro h
    have : (0:ℝ) < Real.sqrt (r/2) := hpos
    linarith

/-- **分支点唯一性**：纤维数发生变化只可能发生在 `r = 0`。

⇒ `r = 0` 是投影 `Crit → ℝ` 的**唯一分支点**。 -/
theorem landau_branch_point_unique {r : ℝ} (hr : r ≠ 0) :
    (∀ φ, landauCritical r φ → φ = 0) ∨
      (∃ φ₁ φ₂ : ℝ, φ₁ ≠ 0 ∧ φ₂ ≠ 0 ∧ φ₁ ≠ φ₂ ∧
        landauCritical r φ₁ ∧ landauCritical r φ₂) := by
  rcases lt_or_gt_of_ne hr with hlt | hgt
  · left
    intro φ h
    rcases (landau_critical_iff r φ).mp h with h0 | h2
    · exact h0
    · have hle : φ ^ 2 ≤ 0 := by rw [h2]; linarith
      exact sq_eq_zero_iff.mp (le_antisymm hle (sq_nonneg φ))
  · right
    have h2 : (0:ℝ) < r / 2 := by linarith
    have hpos : 0 < Real.sqrt (r / 2) := Real.sqrt_pos.mpr h2
    refine ⟨Real.sqrt (r/2), -Real.sqrt (r/2), ne_of_gt hpos, ?_, ?_, ?_, ?_⟩
    · intro h; have := hpos; linarith
    · intro h; have := hpos; linarith
    · rw [landau_critical_iff]; right; exact Real.sq_sqrt h2.le
    · rw [landau_critical_iff]; right; rw [neg_sq, Real.sq_sqrt h2.le]

end

end CausModel
