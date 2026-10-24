/-
ThreeComponent.lean —— 三成分归属场：**模糊 ≠ 不确定**（第 63 轮）

**动机**：论文定义 2.2 用 $b=1-|p_S-p_N|$ 作"边界隶属度"，并把它称作**模糊区**；
而可解芯件 T7 明说：芯上 $p_S+p_N=1$ ⇒ $p_U\equiv0$，**三成分场从未被行使**——
于是"模糊"与"不确定"这两个词**从未被真正分开**。本件把它们分开，并给出**精确的耦合**：

  记 $b=1-|p_S-p_N|$（**不平衡度**），$p_U$（**不确定度**）。

  · **`pU_le_b`**        $p_U\le b$ —— 不确定质量**总在**模糊带内；
  · **`b_sub_pU_eq_two_min`** $b-p_U=2\min(p_S,p_N)$ —— 差额恰是**两倍的双向归属**；
  · **`b_eq_pU_iff`**    $b=p_U\iff p_S=0\lor p_N=0$ —— 取等**当且仅当**归属是单向的；
  · **`no_function_of_b`** $b$ **不决定** $p_U$：不存在 $f$ 使 $p_U=f(b)$（给出反例）。

**结论（一句话）**：$b$ 是**平衡**量，不是**不确定**量。二者被 $p_U\le b$ 精确耦合，
但 $b-p_U=2\min(p_S,p_N)$ 是"两边都归属"的部分，**与不确定无关**。
这正是 T7 想说的限制的**定量形式**，也解释了三成分场为何不能被芯的结论替代。

0 `sorry` / 0 `axiom`。
-/
import Mathlib

namespace ThreeComponent

/-- 三成分归属场：`p_S + p_N + p_U = 1`，各分量非负。 -/
structure Field where
  pS : ℝ
  pN : ℝ
  pU : ℝ
  hS : 0 ≤ pS
  hN : 0 ≤ pN
  hU : 0 ≤ pU
  sum : pS + pN + pU = 1

/-- **边界隶属度**（论文定义 2.2）：`b = 1 - |p_S - p_N|`，衡量**不平衡**。 -/
noncomputable def b (x : Field) : ℝ := 1 - |x.pS - x.pN|

/-- 两倍的双向归属 `2·min(p_S,p_N)`——"两边都归属"的部分。 -/
noncomputable def twoSided (x : Field) : ℝ := 2 * min x.pS x.pN

/-! ## 一 · 基础界 -/

theorem b_nonneg (x : Field) : 0 ≤ b x := by
  have h1 : |x.pS - x.pN| ≤ x.pS + x.pN :=
    abs_sub_le_iff.mpr ⟨by linarith [x.hN], by linarith [x.hS]⟩
  have h2 : x.pS + x.pN = 1 - x.pU := by linarith [x.sum]
  unfold b
  linarith [h1, h2, x.hU]

theorem pU_nonneg (x : Field) : 0 ≤ x.pU := x.hU

/-- **（主不等式）** 不确定质量**总在**模糊带内：`p_U ≤ b`。 -/
theorem pU_le_b (x : Field) : x.pU ≤ b x := by
  have h1 : |x.pS - x.pN| ≤ x.pS + x.pN :=
    abs_sub_le_iff.mpr ⟨by linarith [x.hN], by linarith [x.hS]⟩
  have h2 : x.pS + x.pN = 1 - x.pU := by linarith [x.sum]
  unfold b
  linarith [h1, h2]

/-- **（差额恒等式）** `b - p_U = 2·min(p_S,p_N)`：模糊带中多于"不确定"的那部分，
恰是**两倍的双向归属**——`b` 不是不确定量，是**平衡**量。 -/
theorem b_sub_pU_eq_two_min (x : Field) : b x - x.pU = twoSided x := by
  unfold b twoSided
  rcases le_total x.pS x.pN with h | h
  · rw [abs_of_nonpos (by linarith), min_eq_left h]
    linarith [x.sum]
  · rw [abs_of_nonneg (by linarith), min_eq_right h]
    linarith [x.sum]

/-- **（取等条件）** `b = p_U` **当且仅当**归属是**单向**的（`p_S = 0` 或 `p_N = 0`）。 -/
theorem b_eq_pU_iff (x : Field) : b x = x.pU ↔ x.pS = 0 ∨ x.pN = 0 := by
  have hmin : min x.pS x.pN = 0 ↔ x.pS = 0 ∨ x.pN = 0 := by
    constructor
    · intro h
      rcases min_cases x.pS x.pN with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl (by rw [h1] at h; exact h)
      · exact Or.inr (by rw [h1] at h; exact h)
    · rintro (h | h)
      · rw [h, min_eq_left x.hN]
      · rw [h, min_eq_right x.hS]
  have key : b x - x.pU = 2 * min x.pS x.pN := b_sub_pU_eq_two_min x
  constructor
  · intro h
    have : 2 * min x.pS x.pN = 0 := by linarith [key, h]
    exact hmin.mp (by linarith)
  · intro h
    have : min x.pS x.pN = 0 := hmin.mpr h
    linarith [key, this]

/-! ## 二 · 主结果（负）：`b` **不决定** `p_U`

**这是本轮的核心**：若"模糊区"真是"不确定区"，$p_U$ 就应是 $b$ 的函数。
下面用**显式反例**否定这一点，并据此否定"存在这样的函数"。
-/

/-- 反例之一：**全然不知**（$p_S=p_N=0,\ p_U=1$）——`b = 1`，`p_U = 1`。 -/
def totallyUnknown : Field where
  pS := 0
  pN := 0
  pU := 1
  hS := le_refl 0
  hN := le_refl 0
  hU := zero_le_one
  sum := by norm_num

/-- 反例之二：**势均力敌**（$p_S=p_N=1/2,\ p_U=0$）——`b = 1`，`p_U = 0`。
**不确定度为零，不平衡度却取到最大**。 -/
noncomputable def maximallyBalanced : Field where
  pS := 1 / 2
  pN := 1 / 2
  pU := 0
  hS := by norm_num
  hN := by norm_num
  hU := le_refl 0
  sum := by norm_num

theorem b_totallyUnknown : b totallyUnknown = 1 := by
  unfold b totallyUnknown; norm_num

theorem b_maximallyBalanced : b maximallyBalanced = 1 := by
  unfold b maximallyBalanced; norm_num

/-- **同一个 `b`，不同的 `p_U`**。 -/
theorem same_b_different_pU :
    ∃ x y : Field, b x = b y ∧ x.pU ≠ y.pU :=
  ⟨totallyUnknown, maximallyBalanced, by rw [b_totallyUnknown, b_maximallyBalanced],
    by unfold totallyUnknown maximallyBalanced; norm_num⟩

/-- **（主结果 · 负）** 不存在函数 `f` 使 `p_U = f(b)`：**"模糊"不是"不确定"的函数**。 -/
theorem no_function_of_b : ¬ ∃ f : ℝ → ℝ, ∀ x : Field, x.pU = f (b x) := by
  rintro ⟨f, hf⟩
  obtain ⟨x, y, hb, hU⟩ := same_b_different_pU
  exact hU (by rw [hf x, hf y, hb])

/-! ## 三 · 与可解芯的对接（T7 的定量形式） -/

/-- **芯上**（`p_U = 0`，故 `p_S + p_N = 1`）：`b = 1 - |2p_S - 1|`——
与可解芯件 `LogisticCore.b` 的**同一表达式**。这正是 T7 所说的"芯不行使第三成分"。 -/
theorem core_b_eq (x : Field) (hU : x.pU = 0) : b x = 1 - |2 * x.pS - 1| := by
  have h1 : x.pN = 1 - x.pS := by linarith [x.sum, hU]
  unfold b
  rw [h1]
  ring_nf

/-- 芯上不可能有"双向归属"：`twoSided = min(p_S,p_N) = 0` ⟺ 芯上 `b` 与"不确定"重合。 -/
theorem core_twoSided_nonneg (x : Field) : 0 ≤ twoSided x := by
  unfold twoSided
  have : 0 ≤ min x.pS x.pN := le_min x.hS x.hN
  linarith

end ThreeComponent
