/-
ReportCountermodels.lean —— **报告族反例**（第 69 轮 · A-2）

**动机**：`BoundaryReportIdentity.lean` 证了
  · `rep_eq_iff_closureOperator_eq`（**向上封闭**类内：$R=R'\iff c_R=c_{R'}$）；
  · `report_eq_fix_iff`（**向上封闭** $R$：$R=\mathrm{Fix}(c_I)\iff c_R=c_I$）。

**机器（`exp/自指边界机/`）跑出两件事，本件定住**已能完全机检**的部分**：

  · **`repClosed_subset_fix`（定理 B）** $R\subseteq\mathrm{Fix}(c_R)$——**无条件**，已证；
  · **`nonUpClosed_not_canonical`（反例二）** 存在**非**向上封闭的 $R$ 使 $R\neq\mathrm{Fix}(c_R)$——已证。

**⚠ 未完成（按纪律照记，**不塞半成品**）**：

  · **定理 A·规范族** $\mathrm{cl}^{\mathrm{Fix}(c_R)}=\mathrm{cl}^{R}$（**无条件**版）——
    **机器（`exp/自指边界机/` 判据 6）已否定其无条件版**：$\mathrm{Fix}(c_I)$ 不向上封闭；
    正确版本须带**向上封闭**前提（与 `report_eq_fix_iff` 同前提）。Lean 形式化未写出；
  · **反例一**"两个不同（其一向上封闭）的报告族同算子"——机器**未找到**这样的族，
    故**本轮不主张**（见 `exp/自指边界机/RESULT.md` §三）。

0 `sorry` / 0 `axiom`。**复用** `BoundaryReportIdentity`。
-/
import Mathlib
import BoundaryReportIdentity

set_option linter.unusedVariables false

namespace ReportCountermodels

open LocusVsBoundary
open ClosureFromInterventions
open BoundaryReportIdentity

variable {Ω : Type*}

/-! ## 一 · 定理 B：报告族含于闭元族 -/

/-- **（定理 B）**报告族含于它自己生成的算子的闭元族。**无条件**。 -/
theorem repClosed_subset_fix (R : Report Ω) : R ⊆ Fix (repClosed R) :=
  fun _ hT => repClosed_eq_self_of_mem hT

/-! ## 二 · 反例二：非向上封闭族不是自己的规范代表（`Fin 2`）

> 说明：本轮**只收这一条**反例——它是"账本/规范代表"那一半的直接证据，且能完整机检。
> 反例一（同算子不同族）与定理 A 见本件头部 ⚠ 栏。 -/

/-- 报告族 $R=\mathcal P(\mathrm{Fin}\,2)\setminus\{\varnothing\}$（写成 `Set.univ \ {∅}`）。 -/
def RnoEmpty : Report (Fin 2) := Set.univ \ {∅}

theorem RnoEmpty_not_upClosed : ¬ UpClosed RnoEmpty := by
  intro h
  exact absurd h.1 (by simp [RnoEmpty])

/-- `∅` 是 `c_R` 的闭元：族里每个成员都含 `{0}` 与 `{1}` 不相容，故交为空。 -/
theorem RnoEmpty_closed_empty : repClosed RnoEmpty (∅ : Set (Fin 2)) = ∅ := by
  have hmem0 : ({0} : Set (Fin 2)) ∈ RnoEmpty :=
    ⟨Set.mem_univ _, by intro hc; exact absurd (hc ▸ Set.mem_singleton (0 : Fin 2)) (by simp)⟩
  have hmem1 : ({1} : Set (Fin 2)) ∈ RnoEmpty :=
    ⟨Set.mem_univ _, by intro hc; exact absurd (hc ▸ Set.mem_singleton (1 : Fin 2)) (by simp)⟩
  apply le_antisymm
  · intro x hx
    have hx0 : x ∈ ({0} : Set (Fin 2)) :=
      Set.mem_sInter.mp hx ({0} : Set (Fin 2))
        (show (∅ : Set (Fin 2)) ⊆ ({0} : Set (Fin 2)) ∧ ({0} : Set (Fin 2)) ∈ RnoEmpty from
          ⟨by intro y hy; exact absurd hy (by simp), hmem0⟩)
    have hx1 : x ∈ ({1} : Set (Fin 2)) :=
      Set.mem_sInter.mp hx ({1} : Set (Fin 2))
        (show (∅ : Set (Fin 2)) ⊆ ({1} : Set (Fin 2)) ∧ ({1} : Set (Fin 2)) ∈ RnoEmpty from
          ⟨by intro y hy; exact absurd hy (by simp), hmem1⟩)
    rw [Set.mem_singleton_iff] at hx0 hx1
    exact absurd (hx0 ▸ hx1) (by decide)
  · exact subset_repClosed _ ∅

/-- **（反例二）** 存在**非**向上封闭的报告族，它不是自己生成的算子的闭元族。
**故"报告族 = 边界所判定的闭集族"不是自动成立的**：必须取规范代表。 -/
theorem nonUpClosed_not_canonical :
    ∃ (R : Report (Fin 2)), ¬ UpClosed R ∧ R ≠ Fix (repClosed R) := by
  refine ⟨RnoEmpty, RnoEmpty_not_upClosed, ?_⟩
  intro h
  have hmem : (∅ : Set (Fin 2)) ∈ RnoEmpty := by
    rw [h]
    exact RnoEmpty_closed_empty
  exact absurd (Set.mem_diff _ |>.mp hmem).2 (by simp)

end ReportCountermodels
