/-
LanguageInterventions.lean —— 「干预类越大 ⇒ 刚性面越小」的形式化（第 57 轮）

**动机**：论文引言（`论文线/38_引言_自我非我边界与语言_20261006.md`）写下了一条可检验的对照：
  · 在语言已深度介入的判定域，**语言类干预**对边界的作用应大于身体类；
  · 在语言介入较浅的域，该大小关系应反转或消失。
本文件给出这条对照的**形式内核**：把"干预类的大小"与"刚性面的大小"之间的关系证成定理。

**读法**：`c : ClosureOperator α` 是"给定一族干预 R，把归属推到稳定值"的凝聚算子；
`c.IsClosed x`（即 `c x = x`）表示 **x 已决**（刚性面的元素）。干预越多 ⇒ 越多的状态会被推动 ⇒
凝聚算子越大（逐点） ⇒ **已决集（刚性面）越小**，未决（模糊区）越大。

结论（`fixedPoints_antitone`）：`(∀ x, c₁ x ≤ c₂ x) → c₂.IsClosed x → c₁.IsClosed x`。
即 **刚性面单调收缩**：语言干预带来更多干预 ⇒ 语言域的刚性面 ⊆ 身体域的刚性面 ⇒ 模糊区更大 ⇒
对外部干预更敏感。这正是引言那条对照的形式内容。

状态：在 Lean 4.33.0 + Mathlib 上编译通过（exit 0，无 sorry / axiom）。
-/

import Mathlib

open ClosureOperator

namespace LanguageInterventions

variable {α : Type*}

/-- **L1（刚性面单调收缩）**：若凝聚 `c₂` 逐点不小于 `c₁`（= 干预更多、推得更远），
则 `c₂` 的已决集（刚性面）**包含于** `c₁` 的已决集。 -/
theorem fixedPoints_antitone [PartialOrder α] (c₁ c₂ : ClosureOperator α)
    (h : ∀ x, c₁ x ≤ c₂ x) {x : α} (hx : c₂ x = x) : c₁ x = x := by
  refine le_antisymm ?_ (c₁.le_closure x)
  calc c₁ x ≤ c₂ x := h x
    _ = x := hx

/-- **L2**：同一条的 `IsClosed` 写法（供后续按谓词使用）。 -/
theorem closed_antitone [PartialOrder α] (c₁ c₂ : ClosureOperator α)
    (h : ∀ x, c₁ x ≤ c₂ x) {x : α} (hx : c₂.IsClosed x) : c₁.IsClosed x := by
  rw [ClosureOperator.isClosed_iff] at hx ⊢
  exact fixedPoints_antitone c₁ c₂ h hx

/-- **L3（模糊区单调增大，有限型）**：在有限状态空间上，未决元素（模糊区）的**基数**随干预增多而**不减**。
这是引言里"语言域的模糊区更大"的机检形式（有限情形）。 -/
theorem fuzzy_card_mono [Fintype α] [PartialOrder α] [DecidableEq α]
    (c₁ c₂ : ClosureOperator α) (h : ∀ x, c₁ x ≤ c₂ x) :
    (Finset.univ.filter (fun x => c₁ x ≠ x)).card
      ≤ (Finset.univ.filter (fun x => c₂ x ≠ x)).card := by
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  intro hx2
  exact hx (fixedPoints_antitone c₁ c₂ h hx2)

/-- **L4（等号情形）**：若两个凝聚算子逐点相等，则刚性面相同（L1 的等号方向）。 -/
theorem fixedPoints_congr [PartialOrder α] (c₁ c₂ : ClosureOperator α)
    (h₁ : ∀ x, c₁ x ≤ c₂ x) (h₂ : ∀ x, c₂ x ≤ c₁ x) {x : α} :
    c₁.IsClosed x ↔ c₂.IsClosed x := by
  constructor
  · intro hx
    rw [ClosureOperator.isClosed_iff] at hx ⊢
    exact fixedPoints_antitone c₂ c₁ h₂ hx
  · intro hx
    rw [ClosureOperator.isClosed_iff] at hx ⊢
    exact fixedPoints_antitone c₁ c₂ h₁ hx

end LanguageInterventions
