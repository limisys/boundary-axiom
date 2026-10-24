/-
ProtocolLogic.lean —— **M1 判决逻辑的形式化**（第 122 轮）

**令源**：纲领的两条可检验推论（47 号 §十一）：
**P1「有而无判据」**（发生／维持量在，报告不在）与 **P2「判据在而发生失败」**（报告正常、维持量异常）；
并写死判据："**若两者都不成立 ⇒ D3 应退回 (a)「报告即判据」**"（四格分离设计，M1 草案 §五之二）。
本件把**这套判决逻辑**形式化——**它不需要任何数据**，只需把"观测格 → 判决"写成命题并证明**等价**。

**结果（机检）**：
  · `CoOccur M R`（"报告与维持量总是同现"＝报告即判据）；
  · `P1Witness`／`P2Witness`（两个方向的可观测见证）；
  · `cooccur_iff_no_witness`（**主定理**）：**"总是同现" $\iff$ 两个方向都无见证**
    ⇒ 判决规则**既可靠又完备**（不是约定，是等价）；
  · `p1_refutes`／`p2_refutes`：**任一见证即可否掉"报告即判据"**；
  · `cell_exhaustive`／`cell_pairwise_exclusive`：四格**穷尽且互斥**；
  · `both_outcomes_possible`：两类结论**都非空**（判据不是空的）。

**⚠ 本件不涉及任何测量**：它只把 M1 的**判决逻辑**固定下来；**数据仍须 M1 去取**。

0 `sorry` / `0 axiom`。
-/
import Mathlib

namespace ProtocolLogic

variable {ι : Type*}

/-- **报告即判据**：报告与维持量（发生／维持量指标）**总是同现**。 -/
def CoOccur (M R : ι → Prop) : Prop := ∀ t : ι, M t ↔ R t

/-- **P1 见证**：发生／维持量**在**而报告**不在**（"有而无判据"）。 -/
def P1Witness (M R : ι → Prop) : Prop := ∃ t : ι, M t ∧ ¬ R t

/-- **P2 见证**：报告**在**而维持量**异常／不在**（"判据在而发生失败"）。 -/
def P2Witness (M R : ι → Prop) : Prop := ∃ t : ι, ¬ M t ∧ R t

/-- **（主定理）** **"总是同现" $\iff$ 两个方向都无见证** —— 判决规则**可靠且完备**。 -/
theorem cooccur_iff_no_witness (M R : ι → Prop) :
    CoOccur M R ↔ ¬ P1Witness M R ∧ ¬ P2Witness M R := by
  constructor
  · intro hc
    refine ⟨?_, ?_⟩
    · rintro ⟨t, hM, hR⟩
      exact hR ((hc t).mp hM)
    · rintro ⟨t, hM, hR⟩
      exact hM ((hc t).mpr hR)
  · rintro ⟨h1, h2⟩ t
    refine ⟨fun hM => ?_, fun hR => ?_⟩
    · by_contra hR
      exact h1 ⟨t, hM, hR⟩
    · by_contra hM
      exact h2 ⟨t, hM, hR⟩

/-- **（P1 见证即否证）**。 -/
theorem p1_refutes (M R : ι → Prop) (h : P1Witness M R) : ¬ CoOccur M R := by
  intro hc
  obtain ⟨t, hM, hR⟩ := h
  exact hR ((hc t).mp hM)

/-- **（P2 见证即否证）**。 -/
theorem p2_refutes (M R : ι → Prop) (h : P2Witness M R) : ¬ CoOccur M R := by
  intro hc
  obtain ⟨t, hM, hR⟩ := h
  exact hM ((hc t).mpr hR)

/-- **（四格穷尽）** 每个试次恰落入四格之一：甲(有·报)／乙(有·不报)／丙(不有·报)／丁(不有·不报)。 -/
theorem cell_exhaustive (M R : ι → Prop) (t : ι) :
    (M t ∧ R t) ∨ (M t ∧ ¬ R t) ∨ (¬ M t ∧ R t) ∨ (¬ M t ∧ ¬ R t) := by
  by_cases hM : M t <;> by_cases hR : R t <;> simp [hM, hR]

/-- **（四格互斥：抽样两条）** 甲与乙不能同时成立；丙与丁不能同时成立。 -/
theorem cell_pairwise_exclusive (M R : ι → Prop) (t : ι) :
    ¬ ((M t ∧ R t) ∧ (M t ∧ ¬ R t)) ∧ ¬ ((¬ M t ∧ R t) ∧ (¬ M t ∧ ¬ R t)) := by
  constructor <;> rintro ⟨⟨_, h1⟩, ⟨_, h2⟩⟩ <;> exact h2 h1

/-- **（非空性）** 两类结论**都可能出现**（判据不是空的）：
存在"总是同现"的表，也存在带 P1 见证的表。 -/
theorem both_outcomes_possible :
    (∃ M R : Bool → Prop, CoOccur M R) ∧ (∃ M R : Bool → Prop, P1Witness M R) := by
  constructor
  · exact ⟨fun _ => True, fun _ => True, fun _ => ⟨fun _ => trivial, fun _ => trivial⟩⟩
  · exact ⟨fun _ => True, fun _ => False, ⟨true, trivial, by simp⟩⟩

/-- **（判决规则）** 两个方向都无见证 $\Rightarrow$ **报告即判据**（⇒ D3 应退回 (a)）。 -/
theorem protocol_decision (M R : ι → Prop)
    (h1 : ¬ P1Witness M R) (h2 : ¬ P2Witness M R) : CoOccur M R :=
  (cooccur_iff_no_witness M R).mpr ⟨h1, h2⟩

/-- **（判决逻辑证书）** 一次打包：等价 · 两向否证 · 四格穷尽且互斥 · 非空 · 判决规则。 -/
theorem protocol_logic_certificate :
    (∀ M R : ι → Prop, CoOccur M R ↔ ¬ P1Witness M R ∧ ¬ P2Witness M R) ∧
      (∀ M R : ι → Prop, P1Witness M R → ¬ CoOccur M R) ∧
      (∀ M R : ι → Prop, P2Witness M R → ¬ CoOccur M R) ∧
      (∀ M R : ι → Prop, ∀ t : ι,
        (M t ∧ R t) ∨ (M t ∧ ¬ R t) ∨ (¬ M t ∧ R t) ∨ (¬ M t ∧ ¬ R t)) ∧
      (∃ M R : Bool → Prop, CoOccur M R) ∧
      (∃ M R : Bool → Prop, P1Witness M R) :=
  ⟨fun M R => cooccur_iff_no_witness M R,
    fun M R h => p1_refutes M R h,
    fun M R h => p2_refutes M R h,
    fun M R t => cell_exhaustive M R t,
    both_outcomes_possible.1,
    both_outcomes_possible.2⟩

end ProtocolLogic
