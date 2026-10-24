/-
城邦研究院 · 论文线 · C 阶段核心 · 模型类与"形式被迫"的真值
=================================================================

**本模块回答一个问题**：`V(κ) = c₀κ + αC_F/κ` 的形式，是**被公理决定的**，
还是**被选定的**？——即论文 §2.3 那句 "*Why this form is forced* is a structural
claim, **not a theorem**" 的真值。

**答案（本模块证明）**：**一半已定，一半需要补一条此前没写下的公理。**

| 成分 | 由什么决定 | 定理名 |
|---|---|---|
| 熵项 `αC_F/κ` | 核 + **重标度等变律** | `boundaryEntropy_eq`（T1） |
| 维护项 | 仅凭范畴层公理：**不受任何约束** | `maintenance_unconstrained`（T2） |
| 维护项（补 A7 后） | **加性 + 连续 ⇒ 线性** ⇒ 必为 `c₀κ` | `maintenance_linear_of_additive`（T3） |
| 常数 `c₀` | 仍是尺度自由度（由规范条件 σ*=1 固定） | `maintenance_scale_free`（T4） |

**⇒ 加上 A7 之后，`V` 的形式完全由公理决定，只剩尺度/规范自由度。**
这比论文的 "the form is forced" **更强、也更诚实**：形式确实是定的，
但定它的是**一条此前没有写下的公理**——而这条公理（维护成本的加性）本身是自然的、可陈述的。

**新公理 A7（维护成本的加性）**：互不相交的两个子系统的维护成本之和，等于联合系统的维护成本；
即维护成本是锐度上的**加性泛函**。等价地：维护是一种**可加的可观测代价**。

**证据档位**：机器证明（本模块零 `sorry`）。
-/

import Mathlib.Topology.Instances.RealVectorSpace
import CausModel.KernelModuli

open MeasureTheory

namespace CausModel

noncomputable section

/-! ## T1 · 熵侧典范性：`H = C_F/κ` 是定理（不是选择） -/

/-- **边界熵**：锐度 `κ` 下核的熵积分。

建模同一化（**界定性**，即"锐度"一词的含义）：锐度 `κ` 通过**核重标度** `z ↦ κz` 实现——
边界越锐，归因核越陡，其模糊宽度 `~1/κ`。 -/
def boundaryEntropy (κ : ℝ) (F : ℝ → ℝ) : ℝ := coreConstant (rescale κ F)

/-- **【T1】熵项是定理**：`H(κ) = C_F/κ`。

⇒ 论文 §2.4 的 `H = C_F/κ` **不是建模选择**，而是 B6 的重标度等变律
（`coreConstant_rescale`）在"锐度 = 核重标度"这一界定性同一化下的**直接推论**。

这也正是 `09_…总表` 与 W7 所指的"`1/κ` 项可由可积性 + 量纲事实得证"的**机器可证形式**。 -/
theorem boundaryEntropy_eq (F : ℝ → ℝ) {κ : ℝ} (hκ : 0 < κ) :
    boundaryEntropy κ F = coreConstant F / κ := by
  unfold boundaryEntropy
  rw [coreConstant_rescale F hκ]
  ring

/-- **T1 系**：熵项随锐度按 `1/κ` 衰减 —— 原稿写作"the sharper the boundary,
the less entropy it carries"，此处为等式。 -/
theorem boundaryEntropy_antitone {F : ℝ → ℝ} (hF : 0 < coreConstant F)
    {κ₁ κ₂ : ℝ} (h₁ : 0 < κ₁) (h₁₂ : κ₁ ≤ κ₂) :
    boundaryEntropy κ₂ F ≤ boundaryEntropy κ₁ F := by
  rw [boundaryEntropy_eq F h₁, boundaryEntropy_eq F (lt_of_lt_of_le h₁ h₁₂)]
  exact div_le_div_of_nonneg_left hF.le h₁ (by linarith)

/-! ## T3 · 维护侧：补上 A7，形式**是被迫的** -/

/-- **【T3 核心】维护成本的线性定理**。

**A7（加性）+ 连续 ⇒ ℝ-线性 ⇒ 维护项必形如 `c₀κ`。**

这一步把论文的 "the form is forced" 从**假主张**变成**真定理**：
代价是补一条此前缺失的公理——维护成本的**加性**（互不相交子系统的代价可加）。
数学内核是 `map_real_smul`（连续加性映射在 ℝ-向量空间之间自动 ℝ-线性）。

⇒ **论文不必再说"形式被迫"而不给证明；它只需写下 A7，然后引用本定理。** -/
theorem maintenance_linear_of_additive (M : ℝ →+ ℝ) (hM : Continuous M) (κ : ℝ) :
    M κ = κ * M 1 := by
  have h := map_real_smul M hM κ (1 : ℝ)
  simpa using h

/-- **T3 系**：线性维护项就是论文的 `c₀κ`（取 `c₀ := M 1`）。 -/
theorem maintenance_eq_coefficient (M : ℝ →+ ℝ) (hM : Continuous M) (κ : ℝ) :
    M κ = M 1 * κ := by
  rw [maintenance_linear_of_additive M hM κ]; ring

/-! ## T2 / T4 · 非范畴性与残留尺度自由度 -/

/-- **【T2】范畴层公理不约束维护项**：存在两个不同的合法维护泛函。

⇒ 只凭 §1–§3 的公理，"维护项是什么"**完全自由**；这正是原稿 "the form is forced"
**不成立**的精确含义，也是 C3b 负定理的内核。 -/
theorem maintenance_unconstrained :
    ∃ M₁ M₂ : ℝ →+ ℝ, Continuous M₁ ∧ Continuous M₂ ∧ M₁ ≠ M₂ := by
  refine ⟨0, AddMonoidHom.id ℝ, continuous_const, continuous_id, ?_⟩
  intro h
  have := congr_fun (congr_arg DFunLike.coe h) 1
  simpa using this

/-- **【T4】补 A7 之后仍残留的尺度自由度**：`c₀` 不被加性公理决定。

⇒ 论文 §3.2 把 `σ* = 1` 列为**"gauge value"（规范值）**是**正确的**：
它不是推论，而是固定尺度 `c₀` 与 `α/C₀` 关系的**规范条件**。
本定理把这一层级区分固化为可机检事实。 -/
theorem maintenance_scale_free :
    ∃ M₁ M₂ : ℝ →+ ℝ, Continuous M₁ ∧ Continuous M₂ ∧
      (∀ κ, M₁ κ = 1 * κ) ∧ (∀ κ, M₂ κ = 2 * κ) ∧ M₁ 1 ≠ M₂ 1 := by
  refine ⟨AddMonoidHom.id ℝ, AddMonoidHom.mulLeft 2,
    continuous_id, continuous_const.mul continuous_id, ?_, ?_, ?_⟩
  · intro κ; simp
  · intro κ; rfl
  · norm_num

end

end CausModel
