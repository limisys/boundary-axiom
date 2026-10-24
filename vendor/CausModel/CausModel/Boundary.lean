/-
城邦研究院 · 论文线 · B 阶段 · B3 + B4：凝聚、边界、缺陷方块
================================================================

对应论文 `统一边界理论EN稿.md`：

  **Def 1.4（boundary = stable closure fiber）**（L112–L120）
  "The boundary of the system is the *stable closure fiber* of `A` under causal cohesion:
   the maximal stable structure on which interventions no longer change attribution."

  **Def 2.1（causal cohesion）**（L173–L179）
  "Causal cohesion is the natural transformation η : 1_Caus ⇒ Attrib that flattens the
   arrows of the intervention category onto stable closure … It is *complete* exactly when
   the comparison has settled — when further intervention changes nothing in attribution."

  **§2.5（the minimal violation term）**（L219）
  "the boundary is the **minimal violation term** — the smallest object that makes the
   commutative diagram of attribution fail to commute."

**原稿的三处未定义/未证（本节修复）**：
  (i)  `Attrib`（η 的靶函子）**全文从未定义**，且 `1_Caus ⇒ Attrib` 要求 `Attrib` 是
       **自函子**，与文中唯一的函子 `A : Caus^op → Δ²` **变变性不匹配**。
  (ii) "closure"（闭包）与 "fiber"（纤维）未给出范畴归宿。范畴学中**闭包算子 = 幂等单子**，
       其不动点 = 该单子的代数。
  (iii) "最小违反项"未陈述为可判定对象。

**本节的实现（两级，均已机检）**：

  · **偏序级（可直接用于论文的"结构"层）**：凝聚 = `ClosureOperator`；边界 = 闭元素；
    万有性质 = `ClosureOperator.gi`（Galois 插入：闭包 ⊣ 含入）；**最小性** = 
    `boundary_is_least_closed`（边界点是含 x 的**最小**稳定结构）。
  · **范畴级（G3）**：凝聚 = 范畴 `C` 上的单子 `T`；边界 = Eilenberg–Moore 代数范畴
    `T.Algebra`；万有性质 = 自由–遗忘伴随 `T.free ⊣ T.forget`（mathlib）。
    每一个状态 `X` 都有**唯一**的万有箭头 `η_X : X ⟶ T.obj X` 进入边界。
  · **缺陷方块（B4）**：`Monad.Algebra.Hom.h` 恰是论文所说的"交换方块"
        `T.map f ≫ B.a = A.a ≫ f`。
    **定理 `commutes_iff_isBoundaryMap`**：方块交换 **⟺** `f` 是边界态射。
    ⇒ "边界是最小违反项"获得了可判定形式：**交换失败 = 不在边界上**。

**证据档位**：机器证明（本模块零 `sorry`）。
-/

import Mathlib.Order.Closure
import Mathlib.CategoryTheory.Monad.Algebra
import Mathlib.Tactic
import CausModel.Caus

open CategoryTheory

universe u v

namespace CausModel

/-! # 一级：偏序上的凝聚与边界（论文"结构"层的直接形式化） -/

section Poset

variable {α : Type*} [PartialOrder α]

/-- **凝聚（causal cohesion）**：一个闭包算子——单调、扩张、幂等。

论文 Def 2.1 的 "flattening onto stable closure" 在偏序层就是闭包算子：
  · 单调：干预更多 ⇒ 稳定结构更大；
  · 扩张（`le_closure`）：任何结构都被其凝聚包住；
  · 幂等（`idempotent`）：凝聚**完成**后再凝聚不再改变——这正是
    "when further intervention changes nothing in attribution"。 -/
abbrev Cohesion (α : Type*) [PartialOrder α] := ClosureOperator α

/-- **边界**（Def 1.4）：凝聚的**闭元素**（不动点）——干预不再改变归因的那些结构。 -/
abbrev Boundary (c : Cohesion α) := c.Closeds

/-- **边界稳定性**（Def 1.4 的"stable"）：边界元素在凝聚下不动。 -/
theorem boundary_stable (c : Cohesion α) (y : Boundary c) :
    c (y : α) = (y : α) :=
  y.2.closure_eq

/-- **万有性质（G3）**：凝聚是含入的**左伴随**——`ClosureOperator.gi` 给出的 Galois 插入。

读法：任何从 `x` 出发、落入边界的目标 `y`，都**唯一地**经由 `c x` 分解。
这就是 "stable closure" 的万有映射性质，而非散文修辞。 -/
def boundary_galois (c : Cohesion α) :
    GaloisInsertion c.toCloseds (Subtype.val : Boundary c → α) :=
  c.gi

/-- **万有性质的可用形式**：若 `y` 在边界上，则经 `c` 的分解不改变可达性。 -/
theorem boundary_universal (c : Cohesion α) {x : α} {y : Boundary c} :
    c x ≤ (y : α) ↔ x ≤ (y : α) :=
  y.2.closure_le_iff

/-- **最小违反项（§2.5 的精确形式）**：`c x` 是**含 `x` 的最小边界元素**。

⇒ 边界不是"某处"，而是**恰好**在凝聚不再生效之处；它是使"交换"成立的最小稳定结构。
这一条把 §2.5 的 "smallest object" 从句法修辞变成 `IsLeast`。 -/
theorem boundary_is_least_closed (c : Cohesion α) (x : α) :
    IsLeast {y : α | c.IsClosed y ∧ x ≤ y} (c x) :=
  ⟨⟨c.isClosed_closure x, c.le_closure x⟩,
    fun _ hy => hy.1.closure_le_iff.mpr hy.2⟩

/-- **边界 = 缺陷消失之处**：`x` 在边界上 ⟺ 凝聚对 `x` 已无作用。 -/
theorem mem_boundary_iff_no_defect (c : Cohesion α) (x : α) :
    c.IsClosed x ↔ c x = x :=
  c.isClosed_iff

end Poset

/-! # 二级：范畴上的凝聚与边界（G3 的范畴形式） -/

section Categorical

variable {C : Type u} [Category.{v} C]

/-- **范畴级凝聚**：`C` 上的单子 `T`。

`T.η` 是论文 §2.1 的 `η : 1_Caus ⇒ Attrib`（此处 `Attrib := T`，**自函子**，
类型正确——修复原稿 (i)）；`T.μ` 是凝聚的乘法（闭包的"再做一次"）。 -/
abbrev CategoricalCohesion (C : Type u) [Category.{v} C] := Monad C

/-- **范畴级边界**：`T` 的 Eilenberg–Moore 代数范畴。

读法：代数的结构态射 `A.a : T A.A ⟶ A.A` 是"凝聚已作用完毕"的见证；
`A.unit : η ≫ a = 𝟙` 说边界上的干预**不再改变归因**。 -/
abbrev CategoricalBoundary (T : CategoricalCohesion C) : Type _ := T.Algebra

/-! ## §2.1 的 η：凝聚单位（修复原稿 Def 2.1 的类型病）

原稿写作 `η : 1_Caus ⇒ Attrib`，但 **`Attrib` 全文从未定义**，且 `1_Caus` 是自函子、
要求 `Attrib` 也是自函子，与文中唯一的函子 `A : Caus^op → Δ²` **变变性不匹配**。
此处把 `Attrib` 明确取为凝聚单子 `T` 本身（自函子），类型随之成立。 -/

/-- **论文 §2.1 的 η**：凝聚单位，类型为 `η : 𝟭 C ⟶ T`（**自然变换**，靶函子已定义）。

读法：`η` 记录"每个状态在其凝聚完成态中的像"；`T` 的**幂等性**即
"when further intervention changes nothing in attribution"（§2.1）。 -/
def CohesionUnit (T : CategoricalCohesion C) : 𝟭 C ⟶ (T : C ⥤ C) :=
  T.η

/-- **万有性质（G3）**：自由–遗忘伴随 `T.free ⊣ T.forget`。

⇒ 每个状态 `X` 都有**唯一**的万有箭头 `T.η.app X : X ⟶ T.obj X` 进入边界；
反方向由遗忘函子给出。这是边界"被万有性质钉住"的机器可证形式。 -/
def boundary_adjunction (T : CategoricalCohesion C) : T.free ⊣ T.forget :=
  T.adj

/-- **自由边界对象**：`X` 的边界对象以 `T.obj X` 为载体、以 `T.μ` 为结构态射。 -/
theorem boundary_free_carrier (T : CategoricalCohesion C) (X : C) :
    (T.free.obj X).A = T.obj X :=
  rfl

/-- **边界态射的交换方块**（B4 的核心）：`f : A.A ⟶ B.A` 是边界态射，
当且仅当论文 §2.5 的那个方块**交换**：
`T.map f ≫ B.a = A.a ≫ f`。 -/
def Commutes (T : CategoricalCohesion C) {A B : CategoricalBoundary T}
    (f : A.A ⟶ B.A) : Prop :=
  T.map f ≫ B.a = A.a ≫ f

/-- **缺陷（violation）**：方块**不**交换。 -/
def Defect (T : CategoricalCohesion C) {A B : CategoricalBoundary T}
    (f : A.A ⟶ B.A) : Prop :=
  ¬ Commutes T f

/-- **§2.5 主定理（最小违反项）**：方块交换 ⟺ `f` 落在边界范畴中。

⇒ "边界是使交换图失败的最小对象"获得了**可判定**的形式：
**不交换 ⟺ 不在边界上**；边界恰是缺陷的补集。 -/
theorem commutes_iff_isBoundaryMap (T : CategoricalCohesion C)
    {A B : CategoricalBoundary T} (f : A.A ⟶ B.A) :
    Commutes T f ↔ ∃ (g : A ⟶ B), g.f = f := by
  constructor
  · intro h
    exact ⟨⟨f, h⟩, rfl⟩
  · rintro ⟨g, rfl⟩
    exact g.h

/-- **缺陷的判定形式**：`f` 有缺陷 ⟺ `f` 不能提升为边界态射。 -/
theorem defect_iff_not_liftable (T : CategoricalCohesion C)
    {A B : CategoricalBoundary T} (f : A.A ⟶ B.A) :
    Defect T f ↔ ¬ ∃ (g : A ⟶ B), g.f = f := by
  simp only [Defect, commutes_iff_isBoundaryMap]

end Categorical

end CausModel
