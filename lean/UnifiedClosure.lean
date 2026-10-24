/-
UnifiedClosure.lean —— 本纲领的三个闭包算子是**同一个构造的三个实例**（第 72 轮）

**动机**：到第 70 轮，本纲领一共出现了**三个**闭包算子，各自独立构造、各居一处：

  · `ClosureFromInterventions.clos I` —— 由**干预族**生成（`Set Ω` 上）；
  · `FieldClosure.commit`           —— 芯外动力学"**表态**"（三成分场上）；
  · `SharpnessClosure.c κ μ w`      —— 把**模糊带**压到右端点（ℝ 上）。

第 70 轮自己把它标为"**下一步：把三者统一**"。本轮做这件事。

**统一的那句话**：三者都是"**把点推到其上方最小的『已决』元素**"这一构造的实例。
形式地：设偏序 $\alpha$ 与"已决区" $S\subseteq\alpha$，若**每个点上方都有 $S$ 的最小元**
（`HasLeastAbove`），则 $x\mapsto$「$x$ 上方最小的 $S$-元」是闭包算子，且其不动点集**恰是** $S$。

**关于新意（如实标注）**：这个**一般原理**不是我们的——Mathlib 已有
`ClosureOperator.ofCompletePred`（对任意交封闭的谓词给出闭包算子），二者在"最小元存在"的情形等价。
**本件的贡献是三个实例**：本纲领这三个**各自独立构造**的算子，**都是那一个构造**。
（这正是本纲领的核心动作：找到两个「被错误地分开」的对象，允许它们之间的耦合项。）

0 `sorry` / 0 `axiom`。
-/
import CommitAdjunction
import ClosureFromInterventions
import SharpnessClosure

open scoped Real

namespace UnifiedClosure

open LocusVsBoundary

/-! ## 一 · 一般构造："已决区"决定闭包算子 -/

variable {α : Type*} [PartialOrder α]

/-- **上有最小已决元**：每个 `x` 上方都有 `S` 的最小元。 -/
def HasLeastAbove (S : Set α) : Prop :=
  ∀ x : α, ∃ y ∈ S, x ≤ y ∧ ∀ z ∈ S, x ≤ z → y ≤ z

/-- 取该最小元。 -/
noncomputable def leastAbove (S : Set α) (h : HasLeastAbove S) (x : α) : α :=
  Classical.choose (h x)

theorem leastAbove_mem (S : Set α) (h : HasLeastAbove S) (x : α) : leastAbove S h x ∈ S :=
  (Classical.choose_spec (h x)).1

theorem le_leastAbove (S : Set α) (h : HasLeastAbove S) (x : α) : x ≤ leastAbove S h x :=
  (Classical.choose_spec (h x)).2.1

theorem leastAbove_le (S : Set α) (h : HasLeastAbove S) (x : α) {z : α} (hz : z ∈ S)
    (hxz : x ≤ z) : leastAbove S h x ≤ z :=
  (Classical.choose_spec (h x)).2.2 z hz hxz

/-- **（构造）** "已决区"给出一个闭包算子。 -/
theorem isClosure_leastAbove (S : Set α) (h : HasLeastAbove S) : IsClosure (leastAbove S h) := by
  refine ⟨fun x => le_leastAbove S h x, ?_, ?_⟩
  · intro x y hxy
    exact leastAbove_le S h x (leastAbove_mem S h y) (hxy.trans (le_leastAbove S h y))
  · intro x
    exact le_antisymm (leastAbove_le S h (leastAbove S h x) (leastAbove_mem S h x) le_rfl)
      (le_leastAbove S h (leastAbove S h x))

/-- **（不动点）** 其不动点集**恰是**该已决区。 -/
theorem fix_leastAbove (S : Set α) (h : HasLeastAbove S) :
    LocusVsBoundary.Fix (leastAbove S h) = S := by
  ext x
  constructor
  · intro hx
    simp only [LocusVsBoundary.Fix, Set.mem_ofPred_eq] at hx
    rw [← hx]
    exact leastAbove_mem S h x
  · intro hx
    exact le_antisymm (leastAbove_le S h x hx le_rfl) (le_leastAbove S h x)

/-! ## 二 · 实例一：由干预族生成的闭包 -/

/-- 已决区：`I`-不变集族。 -/
def invSet {Ω : Type*} (I : Set (Ω → Ω)) : Set (Set Ω) := {T | ClosureFromInterventions.Inv I T}

theorem hasLeastAbove_invSet {Ω : Type*} (I : Set (Ω → Ω)) : HasLeastAbove (invSet I) := by
  intro S
  refine ⟨ClosureFromInterventions.clos I S,
    ClosureFromInterventions.inv_clos I S, ClosureFromInterventions.subset_clos I S, ?_⟩
  intro z hz hxz
  exact ClosureFromInterventions.clos_subset hxz hz

/-- `clos I S` 是 `S` 上方**最小**的不变集。 -/
theorem clos_least {Ω : Type*} {I : Set (Ω → Ω)} {S T : Set Ω}
    (hT : T ∈ invSet I) (hST : S ⊆ T) : ClosureFromInterventions.clos I S ⊆ T :=
  ClosureFromInterventions.clos_subset hST hT

/-- **（实例一）** `clos I` 就是它自己的已决区所给出的最小元映射。 -/
theorem intervention_is_instance {Ω : Type*} (I : Set (Ω → Ω)) :
    ∃ h : HasLeastAbove (invSet I),
      ∀ S, leastAbove (invSet I) h S = ClosureFromInterventions.clos I S := by
  refine ⟨hasLeastAbove_invSet I, fun S => le_antisymm ?_ ?_⟩
  · exact leastAbove_le _ _ S (ClosureFromInterventions.inv_clos I S)
      (ClosureFromInterventions.subset_clos I S)
  · exact clos_least (leastAbove_mem _ _ S) (le_leastAbove _ _ S)

/-! ## 三 · 实例二：芯外的"表态" -/

/-- 已决区：**单向归属**（`commit` 的不动点）。 -/
def commitSet : Set ThreeComponent.Field := {x | FieldClosure.commit x = x}

/-- `commit x` 是 `x` 上方**最小**的已决元。 -/
theorem commit_least {x z : ThreeComponent.Field} (hz : z ∈ commitSet) (hxz : x ≤ z) :
    FieldClosure.commit x ≤ z := by
  have h1 : FieldClosure.commit x = FieldClosure.commit z := hxz.2.1
  rw [h1, hz]

theorem hasLeastAbove_commitSet : HasLeastAbove commitSet := by
  intro x
  exact ⟨FieldClosure.commit x, FieldClosure.commit_idem x, CommitAdjunction.le_commit x,
    fun z hz hxz => commit_least hz hxz⟩

/-- **（实例二）** `commit` 就是它自己的已决区所给出的最小元映射。 -/
theorem commit_is_instance :
    ∃ h : HasLeastAbove commitSet, ∀ x, leastAbove commitSet h x = FieldClosure.commit x := by
  refine ⟨hasLeastAbove_commitSet, fun x => le_antisymm ?_ ?_⟩
  · exact leastAbove_le _ _ x (FieldClosure.commit_idem x) (CommitAdjunction.le_commit x)
  · exact commit_least (leastAbove_mem _ _ x) (le_leastAbove _ _ x)

/-! ## 四 · 实例三：按锐度压模糊带 -/

/-- 已决区：**两条尾**（模糊带之外）。 -/
def tailSet (κ μ w : ℝ) : Set ℝ := {z | z ≤ μ - w / κ ∨ μ + w / κ ≤ z}

theorem c_mem_tailSet (κ μ w : ℝ) (x : ℝ) :
    SharpnessClosure.c κ μ w x ∈ tailSet κ μ w := by
  unfold SharpnessClosure.c tailSet
  by_cases h1 : x ≤ μ - w / κ
  · rw [if_pos h1]; exact Or.inl h1
  · rw [if_neg h1]
    by_cases h2 : x < μ + w / κ
    · rw [if_pos h2]; exact Or.inr le_rfl
    · rw [if_neg h2]; exact Or.inr (le_of_not_gt h2)

/-- `c κ μ w x` 是 `x` 上方**最小**的已决元（两条尾之外）。 -/
theorem c_least (κ μ w : ℝ) (x : ℝ) {z : ℝ} (hz : z ∈ tailSet κ μ w) (hxz : x ≤ z) :
    SharpnessClosure.c κ μ w x ≤ z := by
  rcases hz with hz | hz
  · have h1 : x ≤ μ - w / κ := hxz.trans hz
    unfold SharpnessClosure.c
    rw [if_pos h1]
    exact hxz
  · unfold SharpnessClosure.c
    by_cases h1 : x ≤ μ - w / κ
    · rw [if_pos h1]; exact hxz
    · rw [if_neg h1]
      by_cases h2 : x < μ + w / κ
      · rw [if_pos h2]; exact hz
      · rw [if_neg h2]; exact hxz

theorem hasLeastAbove_tailSet (κ μ w : ℝ) (hκ : 0 < κ) (hw : 0 ≤ w) :
    HasLeastAbove (tailSet κ μ w) := by
  intro x
  exact ⟨SharpnessClosure.c κ μ w x, c_mem_tailSet κ μ w x,
    SharpnessClosure.le_c κ μ w x hκ hw, fun z hz hxz => c_least κ μ w x hz hxz⟩

/-- **（实例三）** `c κ μ w` 就是它自己的已决区所给出的最小元映射。 -/
theorem sharpness_is_instance (κ μ w : ℝ) (hκ : 0 < κ) (hw : 0 ≤ w) :
    ∃ h : HasLeastAbove (tailSet κ μ w),
      ∀ x, leastAbove (tailSet κ μ w) h x = SharpnessClosure.c κ μ w x := by
  refine ⟨hasLeastAbove_tailSet κ μ w hκ hw, fun x => le_antisymm ?_ ?_⟩
  · exact leastAbove_le _ _ x (c_mem_tailSet κ μ w x) (SharpnessClosure.le_c κ μ w x hκ hw)
  · exact c_least κ μ w x (leastAbove_mem _ _ x) (le_leastAbove _ _ x)

/-! ## 五 · 收官：一个构造，三个实例 -/

/-- **（统一）** 三个闭包算子各自都是"已决区决定的最小元映射"这一构造的实例。 -/
theorem three_instances :
    (∀ {Ω : Type*} (I : Set (Ω → Ω)), ∃ h : HasLeastAbove (invSet I),
        ∀ S, leastAbove (invSet I) h S = ClosureFromInterventions.clos I S)
    ∧ (∃ h : HasLeastAbove commitSet, ∀ x, leastAbove commitSet h x = FieldClosure.commit x)
    ∧ (∀ (κ μ w : ℝ), 0 < κ → 0 ≤ w → ∃ h : HasLeastAbove (tailSet κ μ w),
        ∀ x, leastAbove (tailSet κ μ w) h x = SharpnessClosure.c κ μ w x) :=
  ⟨fun I => intervention_is_instance I, commit_is_instance, sharpness_is_instance⟩

end UnifiedClosure
