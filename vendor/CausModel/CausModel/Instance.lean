/-
城邦研究院 · 论文线 · 非空性见证：一个具体的凝聚与边界
=========================================================

**目的**：证明 §1–§3 的框架**不是空话**——存在一个具体的、可写下来的模型，
其中凝聚是闭包算子、边界是不动点，且边界**既非空集也非全集**（有真实内容）。

**实例**：两个状态的干预系统 `Bool = {false, true}`。"核心态" `true` 一旦被归因，
其因果后果迫使整个状态空间被归因（凝聚 = 因果闭包）：

    c(S) = S ∪ { x | true ∈ S }

（用 `{x | true ∈ S}` 而非条件分支书写，从而**无需可判定性**，纯集合代数可证。）

⇒ 边界 = `{∅, {false}, univ}` ⊂ `𝒫(Bool)`，严格介于两端之间。

本模块直接以函数形式给出闭包，避免结构强制转换带来的表述噪音；
`ClosureOperator` 版本见 `causalClosure`。

**证据档位**：机器证明（本模块零 `sorry`）。
-/

import CausModel.Boundary
import Mathlib.Order.Closure

namespace CausModel

noncomputable section

/-- **因果凝聚的底层函数** `c(S) = S ∪ {x | true ∈ S}`。

读法：`true` 是"自我"的核心；一旦某结构承认了它，因果后果迫使它承认全部。 -/
def causalClosureFun (S : Set Bool) : Set Bool := S ∪ {_x : Bool | true ∈ S}

/-- 边界的直接判据：**凝聚的不动点**（Def 1.4 的"干预不再改变归因"）。 -/
def IsStable (S : Set Bool) : Prop := causalClosureFun S = S

/-- 凝聚单调。 -/
theorem causalClosureFun_mono : Monotone causalClosureFun := by
  intro S T hST x hx
  rcases hx with hx | hx
  · exact Or.inl (hST hx)
  · exact Or.inr (hST hx)

/-- 凝聚扩张（任何结构都被其凝聚包住）。 -/
theorem causalClosureFun_extensive (S : Set Bool) : S ⊆ causalClosureFun S :=
  fun _ hx => Or.inl hx

/-- **凝聚幂等**（"再凝聚一次不再改变" = §2.1 的 "when further intervention changes
nothing in attribution"）。 -/
theorem causalClosureFun_idem (S : Set Bool) :
    causalClosureFun (causalClosureFun S) = causalClosureFun S := by
  have hP : {x : Bool | true ∈ causalClosureFun S} = {_x : Bool | true ∈ S} := by
    ext x
    constructor
    · intro h
      rcases h with h | h
      · exact h
      · exact h
    · intro h
      exact Or.inr h
  show (S ∪ {_x : Bool | true ∈ S}) ∪ {x : Bool | true ∈ causalClosureFun S}
      = S ∪ {_x : Bool | true ∈ S}
  rw [hP, Set.union_assoc, Set.union_self]

/-- 幂等的 `⊆` 形式（供 `ClosureOperator.mk'` 使用）。 -/
theorem causalClosureFun_idem_le (S : Set Bool) :
    causalClosureFun (causalClosureFun S) ⊆ causalClosureFun S :=
  (causalClosureFun_idem S).le

/-- **具体的因果凝聚**，作为闭包算子（论文 §1.3 的 `Cohesion` 的一个实例）。 -/
def causalClosure : ClosureOperator (Set Bool) :=
  ClosureOperator.mk' causalClosureFun causalClosureFun_mono
    causalClosureFun_extensive causalClosureFun_idem_le

/-! ## 边界的具体成员 -/

/-- 空集在边界上（无归因 ⇒ 无边界内容）。 -/
theorem empty_isStable : IsStable (∅ : Set Bool) := by
  unfold IsStable causalClosureFun
  ext x
  simp

/-- 全集在边界上（完全凝聚 ⇒ 已完成）。 -/
theorem univ_isStable : IsStable (Set.univ : Set Bool) := by
  unfold IsStable causalClosureFun
  ext x
  simp

/-- `{false}` 在边界上（不含核心态 ⇒ 凝聚不动）。 -/
theorem singleton_false_isStable : IsStable ({false} : Set Bool) := by
  unfold IsStable causalClosureFun
  ext x
  simp

/-- **`{true}` 不在边界上**：它含核心态却被凝聚扩张 ⇒ 边界是**真子集**，框架非平凡。 -/
theorem singleton_true_not_isStable : ¬ IsStable ({true} : Set Bool) := by
  unfold IsStable causalClosureFun
  intro h
  have hfalse : false ∈ ({true} : Set Bool) ∪ {_x : Bool | true ∈ ({true} : Set Bool)} := by
    exact Or.inr rfl
  rw [h] at hfalse
  simp at hfalse

/-- **`{true}` 的凝聚是把整个状态空间拉进来**（最小违反项的具体见证）。 -/
theorem defect_witness : causalClosureFun ({true} : Set Bool) = Set.univ := by
  unfold causalClosureFun
  ext x
  constructor
  · intro _; exact Set.mem_univ x
  · intro _
    exact Or.inr rfl

/-- **边界严格介于两端之间**：既有闭集，又有非闭集。 -/
theorem boundary_proper :
    (∃ S : Set Bool, IsStable S) ∧ (∃ S : Set Bool, ¬ IsStable S) :=
  ⟨⟨∅, empty_isStable⟩, ⟨{true}, singleton_true_not_isStable⟩⟩

end

end CausModel
