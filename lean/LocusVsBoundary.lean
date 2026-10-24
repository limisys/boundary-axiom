/-
LocusVsBoundary.lean —— "非交换轨迹"的定义，及它与边界的**独立性**（第 67 轮）

**动机**：论文 §2.1 写着"**非交换轨迹不是边界**——二者之间的桥不存在"（第 61 轮已把它取窄为"缺的是定义"）。
本轮**给出定义**，并把 §2.1 的那条**禁令升级为定理**。

**定义**（本轮新增）：给定状态空间 $\Omega$（带偏序）、**观测** $a:\Omega\to\Omega$、**干预** $i:\Omega\to\Omega$，

$$\mathrm{NonComm}(a,i)=\{x\in\Omega:\ a(i(x))\neq i(a(x))\}$$

即"观测与干预**不交换**"之点的集合——这是"非交换轨迹"最自然的形式化。

**本轮的主结果（两条不可能性）**：

  · **`no_function_locus_to_fix`**  不存在 $f$ 使 $\mathrm{Fix}(c)=f(\mathrm{NonComm}(a,i))$；
  · **`no_function_fix_to_locus`**  也不存在 $g$ 使 $\mathrm{NonComm}(a,i)=g(\mathrm{Fix}(c))$。

**故两个对象是"独立的"**：非交换轨迹**推不出**边界，边界也**推不出**非交换轨迹。
这不是"我们没找到桥"，而是"**按这种形式，桥不可能存在**"——$\S2.1$ 的禁令由此成为**定理**。
反例在最小的非平凡情形 $\Omega=\mathrm{Fin}\,2$ 上给出；任何声称的**一般**桥都必须在那里也成立，故不可能。

**同时给出正例** `locus_eq_fix_possible`：二者**可以**相等——所以这不是"恒不相等"的平凡否定，
而是"**可以相等但不被强制**"。

**范围声明**：本件否定的是"**仅由** $\mathrm{NonComm}(a,i)$ 决定 $\mathrm{Fix}(c)$"。
若**另外**把 $c$ 定义为**由干预族生成**（即 $c$ 依赖 $i$），则问题重新打开——那是**下一步**，本件未答。

0 `sorry` / 0 `axiom`。
-/
import Mathlib

namespace LocusVsBoundary

/-! ## 一 · 定义 -/

/-- **闭包算子**（扩张、单调、幂等）——论文 §3.1 的 $c$。 -/
def IsClosure {Ω : Type*} [PartialOrder Ω] (c : Ω → Ω) : Prop :=
  (∀ x, x ≤ c x) ∧ Monotone c ∧ ∀ x, c (c x) = c x

/-- **刚性面**：闭包算子的不动点集。 -/
def Fix {Ω : Type*} (c : Ω → Ω) : Set Ω := {x | c x = x}

/-- **非交换轨迹**：观测 `a` 与干预 `i` 不交换之点。 -/
def NonComm {Ω : Type*} (a i : Ω → Ω) : Set Ω := {x | a (i x) ≠ i (a x)}

/-- 非交换轨迹为空 $\iff$ 观测与干预处处交换。 -/
theorem nonComm_eq_empty_iff {Ω : Type*} (a i : Ω → Ω) :
    NonComm a i = (∅ : Set Ω) ↔ ∀ x, a (i x) = i (a x) := by
  constructor
  · intro h x
    by_contra hx
    have : x ∈ NonComm a i := hx
    rw [h] at this
    exact this
  · intro h
    ext x
    simp only [NonComm, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
    exact h x

/-- **离散序退化**：偏序若是离散的（$x\le y\Rightarrow x=y$），则唯一的闭包算子是恒等，
刚性面是**全空间**——边界在该情形下不携带信息。 -/
theorem fix_eq_univ_of_discrete {Ω : Type*} [PartialOrder Ω]
    (hdisc : ∀ x y : Ω, x ≤ y → x = y) {c : Ω → Ω} (hc : IsClosure c) :
    Fix c = Set.univ := by
  have hcid : c = id := by
    funext x
    exact (hdisc x (c x) (hc.1 x)).symm
  ext x
  simp [Fix, hcid]

/-! ## 二 · 最小的非平凡模型：`Ω = Fin 2`，通常序 -/

/-- `Fin 2` 上的**恒等**闭包算子（刚性面＝全空间）。 -/
theorem isClosure_id : IsClosure (id : Fin 2 → Fin 2) :=
  ⟨fun _ => le_rfl, monotone_id, fun _ => rfl⟩

/-- `Fin 2` 上的**常值 1** 闭包算子（刚性面＝`{1}`）。 -/
theorem isClosure_top : IsClosure (fun _ : Fin 2 => (1 : Fin 2)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    fin_cases x <;> decide
  · intro x y _
    rfl
  · intro x
    rfl

/-- `Fin 2` 上的**对换**（`x ↦ x+1`）。 -/
def swap : Fin 2 → Fin 2 := fun x => x + 1

theorem fix_id : Fix (id : Fin 2 → Fin 2) = Set.univ := by
  ext x; simp [Fix]

theorem fix_top : Fix (fun _ : Fin 2 => (1 : Fin 2)) = {1} := by
  ext x
  simp only [Fix, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro h; exact h.symm
  · intro h; exact h.symm

theorem nonComm_id : NonComm (id : Fin 2 → Fin 2) id = (∅ : Set (Fin 2)) := by
  rw [nonComm_eq_empty_iff]
  intro x; rfl

theorem nonComm_swap_const : NonComm swap (fun _ : Fin 2 => (0 : Fin 2)) = Set.univ := by
  ext x
  simp only [NonComm, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  fin_cases x <;> decide

/-! ## 三 · 主结果：**两个方向的独立性** -/

/-- **（主结果一）** 不存在"由非交换轨迹决定边界"的函数。
反例共享**同一个**非交换轨迹（空集）：一个闭包算子给全空间，另一个只给 `{1}`。 -/
theorem no_function_locus_to_fix :
    ¬ ∃ f : Set (Fin 2) → Set (Fin 2),
      ∀ (a i c : Fin 2 → Fin 2), IsClosure c → Fix c = f (NonComm a i) := by
  rintro ⟨f, hf⟩
  have h1 : Fix (id : Fin 2 → Fin 2) = f (NonComm (id : Fin 2 → Fin 2) id) :=
    hf id id id isClosure_id
  have h2 : Fix (fun _ : Fin 2 => (1 : Fin 2)) = f (NonComm (id : Fin 2 → Fin 2) id) :=
    hf id id (fun _ => 1) isClosure_top
  have heq : Fix (id : Fin 2 → Fin 2) = Fix (fun _ : Fin 2 => (1 : Fin 2)) := by rw [h1, h2]
  have h0 : (0 : Fin 2) ∈ Fix (id : Fin 2 → Fin 2) := by simp [Fix]
  rw [heq] at h0
  simp [Fix] at h0

/-- **（主结果二）** 反向也不成立：不存在"由边界决定非交换轨迹"的函数。
反例共享**同一个**刚性面（全空间，取恒等闭包）：一个给空轨迹，另一个给全轨迹。 -/
theorem no_function_fix_to_locus :
    ¬ ∃ g : Set (Fin 2) → Set (Fin 2),
      ∀ (a i c : Fin 2 → Fin 2), IsClosure c → NonComm a i = g (Fix c) := by
  rintro ⟨g, hg⟩
  have h1 : NonComm (id : Fin 2 → Fin 2) id = g (Fix (id : Fin 2 → Fin 2)) :=
    hg id id id isClosure_id
  have h2 : NonComm swap (fun _ : Fin 2 => (0 : Fin 2)) = g (Fix (id : Fin 2 → Fin 2)) :=
    hg swap (fun _ => 0) id isClosure_id
  have heq : NonComm (id : Fin 2 → Fin 2) id = NonComm swap (fun _ : Fin 2 => (0 : Fin 2)) := by
    rw [h1, h2]
  have h0 : (0 : Fin 2) ∈ NonComm swap (fun _ : Fin 2 => (0 : Fin 2)) := by
    rw [nonComm_swap_const]; trivial
  rw [← heq] at h0
  rw [nonComm_id] at h0
  exact h0

/-- **正例**：二者**可以**相等（取恒等闭包与"对换+常值干预"）——故主结果不是"恒不相等"的平凡否定，
而是"**可以相等，但不被强制**"。 -/
theorem locus_eq_fix_possible :
    ∃ (a i c : Fin 2 → Fin 2), IsClosure c ∧ NonComm a i = Fix c :=
  ⟨swap, (fun _ : Fin 2 => 0), id, isClosure_id,
    by rw [nonComm_swap_const, fix_id]⟩

/-- **（收官）** 两面独立性打包：两个方向都不可能，同时存在相等的情形。 -/
theorem independent_but_can_coincide :
    (¬ ∃ f : Set (Fin 2) → Set (Fin 2),
        ∀ (a i c : Fin 2 → Fin 2), IsClosure c → Fix c = f (NonComm a i))
    ∧ (¬ ∃ g : Set (Fin 2) → Set (Fin 2),
        ∀ (a i c : Fin 2 → Fin 2), IsClosure c → NonComm a i = g (Fix c))
    ∧ (∃ (a i c : Fin 2 → Fin 2), IsClosure c ∧ NonComm a i = Fix c) :=
  ⟨no_function_locus_to_fix, no_function_fix_to_locus, locus_eq_fix_possible⟩

end LocusVsBoundary
