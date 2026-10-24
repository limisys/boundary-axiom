/-
ClosureFromInterventions.lean —— 当 $c$ **由干预族生成**时：**条件性的正桥**（第 68 轮）

**动机**：第 67 轮（附录 J）把 §2.1 的禁令升级为定理，同时**留下一句**：

> 若把 $c$ **定义为由干预族 $i$ 生成**（即 $c$ 依赖 $i$），则问题**重新打开**——本件**未答**，这正是下一步。

本轮回答它。设 $I$ 是一个**干预族**（$I\subseteq(\Omega\to\Omega)$），令

$$c_I(S)\;:=\;\bigcap\{T\supseteq S:\ \forall i\in I,\ i''T\subseteq T\}$$

即**含 $S$ 的最小 $I$-不变集**（$\Omega$ 本身不变，故该交非空）。

**本轮结果**：

  · **`isClosure_clos`**  $c_I$ 是 `Set Ω` 上的**闭包算子**（扩张／单调／幂等）——**由干预族生成**，不是假定的；
  · **`fix_clos`**       $\mathrm{Fix}(c_I)=\{T:\ T\ \text{是}\ I\text{-不变的}\}$；
  · **`equivariant_preserves`（正桥）** 若观测 $a$ **与每个 $i\in I$ 交换**（即 $a\circ i=i\circ a$），
    则 $a$ **把刚性面送到刚性面**：$T\in\mathrm{Fix}(c_I)\Rightarrow a''T\in\mathrm{Fix}(c_I)$；
  · **`preservation_not_equivariant`（限制）** 反之**不成立**：存在 $(I,a)$ 使 $a$ 保持刚性面，但**不**与 $I$ 交换。

**故 §2.1 现在的完整说法是三层**：
（i）**仅由**非交换轨迹**不能**决定边界（第 67 轮，两向独立）；
（ii）若 $c$ **由干预族生成**且观测**与该族交换**，则观测**作用在边界上**（本轮正桥）；
（iii）交换性**不是**"保持边界"的必要条件（本轮反例）——故（ii）是一个**真正的条件**，不是重言式。

0 `sorry` / 0 `axiom`。**复用**第 67 轮的 `IsClosure`／`Fix` 与 `NonComm`（不重复声明）。
-/
import LocusVsBoundary

namespace ClosureFromInterventions

open LocusVsBoundary

variable {Ω : Type*}

/-! ## 一 · 由干预族生成的闭包 -/

/-- `T` 是 **`I`-不变**的：每个干预都把 `T` 映到自身。 -/
def Inv (I : Set (Ω → Ω)) (T : Set Ω) : Prop := ∀ i ∈ I, i '' T ⊆ T

/-- **由干预族 $I$ 生成的闭包**：含 `S` 的最小 `I`-不变集。 -/
noncomputable def clos (I : Set (Ω → Ω)) (S : Set Ω) : Set Ω :=
  ⋂₀ {T : Set Ω | S ⊆ T ∧ Inv I T}

/-- 该族非空（$\Omega$ 自身不变），故交非空。 -/
theorem univ_mem (I : Set (Ω → Ω)) : (Set.univ : Set Ω) ∈ {T : Set Ω | (Set.univ : Set Ω) ⊆ T ∧ Inv I T} :=
  ⟨Set.subset_univ _, fun _ _ => Set.subset_univ _⟩

/-- `clos I S` 含于族中任一成员。 -/
theorem clos_subset {I : Set (Ω → Ω)} {S T : Set Ω} (hS : S ⊆ T) (hT : Inv I T) :
    clos I S ⊆ T :=
  Set.sInter_subset_of_mem ⟨hS, hT⟩

theorem subset_clos (I : Set (Ω → Ω)) (S : Set Ω) : S ⊆ clos I S :=
  fun _ hx => Set.mem_sInter.mpr (fun _ hT => hT.1 hx)

theorem clos_mono (I : Set (Ω → Ω)) : Monotone (clos I) := by
  intro S S' h
  exact Set.sInter_subset_sInter (fun T hT => ⟨h.trans hT.1, hT.2⟩)

theorem inv_clos (I : Set (Ω → Ω)) (S : Set Ω) : Inv I (clos I S) := by
  intro i hi y hy
  rcases hy with ⟨x, hx, rfl⟩
  exact Set.mem_sInter.mpr (fun T hT => hT.2 i hi ⟨x, Set.mem_sInter.mp hx T hT, rfl⟩)

theorem clos_idem (I : Set (Ω → Ω)) (S : Set Ω) : clos I (clos I S) = clos I S :=
  le_antisymm (clos_subset le_rfl (inv_clos I S)) (subset_clos I (clos I S))

/-- **（主结果一）$c_I$ 是闭包算子**——扩张、单调、幂等，全部由构造得到。 -/
theorem isClosure_clos (I : Set (Ω → Ω)) : IsClosure (clos I) :=
  ⟨subset_clos I, clos_mono I, clos_idem I⟩

/-- **（主结果二）刚性面恰是 $I$-不变集**。 -/
theorem fix_clos (I : Set (Ω → Ω)) : Fix (clos I) = {T : Set Ω | Inv I T} := by
  ext T
  constructor
  · intro h
    have := inv_clos I T
    rwa [h] at this
  · intro hT
    exact le_antisymm (clos_subset le_rfl hT) (subset_clos I T)

/-! ## 二 · 正桥：**与干预族交换的观测，作用在刚性面上** -/

/-- **（正桥）** 若 $a$ 与族中每个 $i$ 交换，则 $a$ 把不变集送到不变集——
即 $a$ **保持刚性面**。这是 §2.1 里"条件性的桥"。 -/
theorem equivariant_preserves {I : Set (Ω → Ω)} {a : Ω → Ω}
    (h : ∀ i ∈ I, ∀ x, a (i x) = i (a x)) {T : Set Ω} (hT : Inv I T) : Inv I (a '' T) := by
  intro i hi y hy
  rcases hy with ⟨z, hz, rfl⟩
  rcases hz with ⟨x, hx, rfl⟩
  rw [← h i hi x]
  exact ⟨i x, hT i hi ⟨x, hx, rfl⟩, rfl⟩

/-- 用 `Fix` 重述：交换的观测把 $\mathrm{Fix}(c_I)$ 映入自身。 -/
theorem equivariant_maps_fix {I : Set (Ω → Ω)} {a : Ω → Ω}
    (h : ∀ i ∈ I, ∀ x, a (i x) = i (a x)) {T : Set Ω} (hT : T ∈ Fix (clos I)) :
    a '' T ∈ Fix (clos I) := by
  rw [fix_clos] at hT ⊢
  exact equivariant_preserves h hT

/-! ## 三 · 限制：交换性**不是**必要的

（在 `Fin 2` 上二者其实等价：单干预族 `{对换}` 下的不变集只有 `∅` 与全集，
而"保持刚性面"逼出 `a` 满射，从而必与对换交换。故反例需 **`Fin 3`**。）
-/

/-- 干预 `i₀`：把 `0` 送到 `1`，其余不动。 -/
def i₀ : Fin 3 → Fin 3 := fun x => if x = 0 then 1 else x

/-- 观测 `a₀`：`0 ↦ 1`，其余送到 `2`。 -/
def a₀ : Fin 3 → Fin 3 := fun x => if x = 0 then 1 else 2

theorem a₀_image_subset (T : Set (Fin 3)) : a₀ '' T ⊆ {1, 2} := by
  intro y hy
  rcases hy with ⟨x, -, rfl⟩
  fin_cases x <;> simp [a₀]

/-- **（限制）** 保持刚性面**不蕴含**与干预族交换：`a₀` 把任何不变集的不变集保持住，
但它与 `i₀` **不交换**（`a₀ (i₀ 0) = 2 ≠ 1 = i₀ (a₀ 0)`）。
**故正桥的前提是真正的前提，不是重言式。** -/
theorem preservation_not_equivariant :
    ∃ (I : Set (Fin 3 → Fin 3)) (a : Fin 3 → Fin 3),
      (∀ T, Inv I T → Inv I (a '' T)) ∧ ¬ (∀ i ∈ I, ∀ x, a (i x) = i (a x)) := by
  refine ⟨{i₀}, a₀, ?_, ?_⟩
  · intro T _ i hi y hy
    have hi' : i = i₀ := by simpa using hi
    subst hi'
    rcases hy with ⟨z, hz, rfl⟩
    rcases hz with ⟨x, hx, rfl⟩
    fin_cases x
    · exact ⟨0, hx, by simp [i₀, a₀]⟩
    · exact ⟨1, hx, by simp [i₀, a₀]⟩
    · exact ⟨2, hx, by simp [i₀, a₀]⟩
  · intro h
    have h0 : (2 : Fin 3) = 1 := by
      have h' : a₀ (i₀ 0) = i₀ (a₀ 0) := h i₀ (by simp) 0
      rw [show a₀ (i₀ 0) = (2 : Fin 3) by decide,
        show i₀ (a₀ 0) = (1 : Fin 3) by decide] at h'
      exact h'
    exact absurd h0 (by decide)

/-- **（收官）** §2.1 的三层说法打包：闭包由干预族生成、正桥、以及交换性的非必要性。 -/
theorem three_layer_statement :
    (∀ I : Set (Ω → Ω), IsClosure (clos I))
    ∧ (∀ I : Set (Ω → Ω), Fix (clos I) = {T : Set Ω | Inv I T})
    ∧ (∀ (I : Set (Ω → Ω)) (a : Ω → Ω),
        (∀ i ∈ I, ∀ x, a (i x) = i (a x)) →
        ∀ T ∈ Fix (clos I), a '' T ∈ Fix (clos I)) :=
  ⟨isClosure_clos, fix_clos, fun _ _ h _ hT => equivariant_maps_fix h hT⟩

end ClosureFromInterventions
