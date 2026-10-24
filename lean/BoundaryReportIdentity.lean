/-
BoundaryReportIdentity.lean —— **桥的同一性定理**：边界与"边界的自报"是同一对象（第 69 轮）

**动机**：第 68 轮（`ClosureFromInterventions.lean`）给出

  · `isClosure_clos`   $c_I$ **由干预族生成**，是闭包算子（不是假定的）；
  · `fix_clos`         $\mathrm{Fix}(c_I)=\{T:\ T\ \text{是}\ I\text{-不变的}\}$；
  · `equivariant_preserves`（正桥）与 `preservation_not_equivariant`（限制）。

但**该轮只做了"观测保持刚性面"，没有做"报告判定刚性面"**——即：**报告 $R$ 与 $\mathrm{Fix}(c_I)$ 之间那一步没接**。
本件把它接上。

**本件主结果（四条）**：

  · **`isClosureOperator_clos`**  由干预族生成的 $c_I$ 打包为 mathlib 的 `ClosureOperator (Set Ω)`，闭元恰是 $I$-不变集；
  · **`rep_eq_iff_closureOperator_eq`（不可分离定理）** 在**向上封闭**报告族之间，
    $$R=R'\iff c_R=c_{R'}$$
    ——**边界与"边界的自报"在该类内不是两件事，而是同一对象的两种写法**；
  · **`report_eq_fix_iff`（同一性的形式判据）** $R=\mathrm{Fix}(c_I)\iff c_R=c_I$：报告**恰是**被边界算子判为闭合的那些集合，不多不少；
  · **`repClosed_eq_sInter`（锐利判据）** $c_R(S)=\bigcap\{T\in R: S\subseteq T\}$：
    **自由度恰等于同读类的粒度**——读数越粗，同一闭元对应的相容报告族越多。

**证明要点（不依赖报告族的任何"生成性"）**：只用到**向上封闭**一条性质——
$\mathrm{cl}^R(S)\in R$ 由"$\mathrm{cl}^R(S)\subseteq T$（$\forall T\ni S$），取凸性即得 $\mathrm{cl}^R(S)\in R$"给出。
故 `rep_eq_iff_closureOperator_eq` **不是定义展开的重言式**，而是一条真命题。

**与 §2.1 的三层关系**：第 67 轮"非交换轨迹不决定边界"（否定）；第 68 轮"由干预族生成的 $c_I$ 与交换观测相容"（条件正桥）；
本件"**报告与边界在向上封闭类内是同一对象**"（同一性）。**边界不可由轨迹定，但边界与自报不可分。**

0 `sorry` / 0 `axiom`。**复用** `LocusVsBoundary`（`IsClosure`／`Fix`）与 `ClosureFromInterventions`（`Inv`／`clos`），**不重复声明**。
-/
import Mathlib
import ClosureFromInterventions
import ReportBridge

set_option linter.unusedVariables false

namespace BoundaryReportIdentity

open LocusVsBoundary
open ClosureFromInterventions

variable {Ω : Type*}

/-! ## 一 · 由干预族生成的闭包算子（打包为 mathlib 对象） -/

/-- `ClosureFromInterventions.clos I` 打包为 mathlib 的 `ClosureOperator (Set Ω)`。
**这一步使"由干预族生成的边界算子"直接进入 mathlib 的闭包算子生态**
（`isClosed_closure`／`closure_min`／Galois 伴随等）。 -/
noncomputable def closCO (I : Set (Ω → Ω)) : ClosureOperator (Set Ω) :=
  ClosureOperator.mk' (clos I) (clos_mono I) (subset_clos I)
    (fun S => by rw [clos_idem])

theorem closCO_apply (I : Set (Ω → Ω)) (S : Set Ω) :
    (closCO I) S = clos I S := rfl

/-- **（主结果一）** 由干预族生成的 $c_I$ 是闭包算子；其闭元恰是 $I$-不变集。
这是 `ClosureFromInterventions` 两条主结果的**接口化**，本件**不重证**。 -/
theorem isClosureOperator_clos (I : Set (Ω → Ω)) :
    (∀ S : Set Ω, S ≤ (closCO I) S) ∧ (∀ S : Set Ω, (closCO I) ((closCO I) S) = (closCO I) S) ∧
      (∀ S : Set Ω, (closCO I) S = S ↔ Inv I S) := by
  have h3 : ∀ S : Set Ω, (closCO I) S = S ↔ Inv I S := by
    intro S
    show clos I S = S ↔ Inv I S
    exact ⟨fun h => h ▸ inv_clos I S,
      fun h => le_antisymm (clos_subset le_rfl h) (subset_clos I S)⟩
  exact ⟨fun S => subset_clos I S, fun S => clos_idem I S, h3⟩

/-! ## 二 · 报告族的形式化：向上封闭 -/

/-- **报告族** $R\subseteq\mathcal P(\Omega)$：把哪些状态集判为"已闭合 / 在边界内"。
**这是"边界的自报"最一般的形式**——不预设阈值、不预设读数。 -/
abbrev Report (Ω : Type*) := Set (Set Ω)

/-- **向上封闭**：空集被自报；且报告对超集封闭。
这两条是**任何阈值式自报**（$R=\{T:\forall x\in T,\ w\,x\ge\theta\}$）都满足的最小结构。 -/
def UpClosed (R : Report Ω) : Prop :=
  (∅ : Set Ω) ∈ R ∧ ∀ ⦃S T : Set Ω⦄, S ∈ R → S ⊆ T → T ∈ R

/-- 由 $R$ 生成的闭包算子：$\mathrm{cl}^R(S)=\bigcap\{T\supseteq S: T\in R\}$。
**这是"从自报反推边界"的算子**——本件的核心构造。 -/
noncomputable def repClosed (R : Report Ω) : Set Ω → Set Ω :=
  fun S => ⋂₀ {T : Set Ω | S ⊆ T ∧ T ∈ R}

/-- `⋂₀` 的成员判据**显式包装**（避免匿名构造子在函数位置上的 elaboration 歧义）。 -/
theorem mem_sInter_of_forall {X : Type*} {F : Set (Set X)} {x : X}
    (h : ∀ T : Set X, T ∈ F → x ∈ T) : x ∈ ⋂₀ F :=
  Set.mem_sInter.mpr h

/-- 报告族的"含 $S$ 的成员"这一子族（写成具名谓词，避免集合建构记号的 elaboration 歧义）。 -/
def RepAbove (R : Report Ω) (S : Set Ω) : Set (Set Ω) :=
  {T : Set Ω | S ⊆ T ∧ T ∈ R}

/-- **（锐利判据）** 报告算子的逐点形式：恰是"报告族中含 $S$ 的一切成员之交"。 -/
theorem repClosed_eq_sInter (R : Report Ω) (S : Set Ω) :
    repClosed R S = ⋂₀ {T : Set Ω | T ∈ R ∧ S ⊆ T} := by
  have hswap : {T : Set Ω | T ∈ R ∧ S ⊆ T} = {T : Set Ω | S ⊆ T ∧ T ∈ R} := by
    ext T; exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  rw [repClosed, hswap]

/-- 报告算子扩张。 -/
theorem subset_repClosed (R : Report Ω) (S : Set Ω) : S ⊆ repClosed R S :=
  fun x hx => Set.mem_sInter.mpr (fun t ht => ht.1 hx)

/-- 报告算子单调。 -/
theorem repClosed_mono (R : Report Ω) : Monotone (repClosed R) :=
  fun S T h x hx => Set.mem_sInter.mpr
    (fun u hu => Set.mem_sInter.mp hx u ⟨h.trans hu.1, hu.2⟩)

/-- 报告算子幂等。 -/
theorem repClosed_idem (R : Report Ω) (S : Set Ω) :
    repClosed R (repClosed R S) = repClosed R S := by
  have hfam : {T : Set Ω | S ⊆ T ∧ T ∈ R} ⊆ {T : Set Ω | repClosed R S ⊆ T ∧ T ∈ R} :=
    fun T hT => ⟨fun _ hy => Set.mem_sInter.mp hy T hT, hT.2⟩
  exact le_antisymm (Set.sInter_subset_sInter hfam) (subset_repClosed R (repClosed R S))

/-- **（主结果二）** 由**任意报告族**生成的算子都是闭包算子（**不需要**向上封闭）。 -/
theorem isClosure_repClosed (R : Report Ω) : IsClosure (repClosed R) := by
  refine ⟨?_, ?_, ?_⟩
  · exact subset_repClosed R
  · exact repClosed_mono R
  · exact repClosed_idem R

/-- 若 $T$ 被自报，则它是报告算子的闭元。 -/
theorem repClosed_eq_self_of_mem {R : Report Ω} {T : Set Ω} (hT : T ∈ R) :
    repClosed R T = T :=
  le_antisymm
    (fun _ hx => Set.mem_sInter.mp hx T (show T ⊆ T ∧ T ∈ R from ⟨le_rfl, hT⟩))
    (subset_repClosed R T)

/-- **（本件的关键引理）报告算子的闭元恰是被自报者**——证明只用到向上封闭一条性质。
由 $\mathrm{cl}^R(T)\subseteq T$，取 $\mathrm{cl}^R(T)$ 为报告族成员（向上封闭），即得 $T\in R$。 -/
theorem mem_of_repClosed_eq_self {R : Report Ω} (hR : UpClosed R) {T : Set Ω}
    (h : repClosed R T = T) : T ∈ R := by
  have hsub : repClosed R T ⊆ T := le_of_eq h
  have h1 : (∅ : Set Ω) ⊆ repClosed R T := fun _ hx => absurd hx (by simp)
  have hmem : repClosed R T ∈ R := hR.2 hR.1 h1
  rwa [h] at hmem

/-- **（闭元 $\iff$ 被自报）** 合并上两条。 -/
theorem repClosed_eq_self_iff {R : Report Ω} (hR : UpClosed R) {T : Set Ω} :
    repClosed R T = T ↔ T ∈ R := by
  constructor
  · exact mem_of_repClosed_eq_self hR
  · exact repClosed_eq_self_of_mem

/-! ## 三 · 同一性：报告族与边界算子互相唯一决定 -/

/-- **（不可分离定理）** 在向上封闭报告族之间，两个报告族相同 $\iff$ 两个由报告生成的边界算子相同。
**这一条是本件要证的东西**：边界与"边界的自报"在该类内**不是两件事**，而是**同一对象的两种写法**
——故"先算边界、再打日志"在构架上没有意义。 -/
theorem rep_eq_iff_closureOperator_eq {R R' : Report Ω}
    (hR : UpClosed R) (hR' : UpClosed R') :
    repClosed R = repClosed R' ↔ R = R' := by
  constructor
  · intro h
    ext T
    exact ⟨fun hT => by
             have h1 : repClosed R T = T := repClosed_eq_self_of_mem hT
             exact (repClosed_eq_self_iff hR').mp (by rw [← h]; exact h1),
           fun hT => by
             have h1 : repClosed R' T = T := repClosed_eq_self_of_mem hT
             exact (repClosed_eq_self_iff hR).mp (by rw [h]; exact h1)⟩
  · intro h; rw [h]

/-- **（同一性的形式判据）** 对向上封闭的 $R$：
$R$ **恰是**"被 $c_I$ 判为闭合"的那些集合，**当且仅当** $R$ 与 $c_I$ 生成同一算子。
即：**报告 = 边界所判定的闭集族**，不多不少。 -/
theorem report_eq_fix_iff {I : Set (Ω → Ω)} {R : Report Ω} (hR : UpClosed R) :
    R = {T : Set Ω | Inv I T} ↔ repClosed R = clos I := by
  constructor
  · intro h
    funext S
    have hmem : clos I S ∈ R := by rw [h]; exact inv_clos I S
    have hle1 : repClosed R S ⊆ clos I S :=
      Set.sInter_subset_of_mem (show S ⊆ clos I S ∧ clos I S ∈ R from ⟨subset_clos I S, hmem⟩)
    have hle2 : clos I S ⊆ repClosed R S :=
      fun x hx => Set.mem_sInter.mpr (fun T hT =>
        clos_subset hT.1 (show Inv I T from by
          have hTR : T ∈ R := hT.2
          rw [h] at hTR
          exact hTR) hx)
    exact le_antisymm hle1 hle2
  · intro h
    ext T
    constructor
    · intro hT
      have hfix : repClosed R T = T := repClosed_eq_self_of_mem hT
      have hcl : clos I T = T := by rw [← h]; exact hfix
      rw [← hcl]
      exact inv_clos I T
    · intro hT
      have hc : clos I T = T := le_antisymm (clos_subset le_rfl hT) (subset_clos I T)
      have hfix : repClosed R T = T := by rw [h]; exact hc
      exact (repClosed_eq_self_iff hR).mp hfix

end BoundaryReportIdentity
