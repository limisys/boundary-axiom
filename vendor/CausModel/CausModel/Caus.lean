/-
城邦研究院 · 论文线 · B 阶段 · B1：干预范畴 `Caus`
=====================================================

对应论文 `统一边界理论EN稿.md` **Def 1.1（intervention category）**（L90）：

  "The category **Caus** has states as objects and causal interventions as morphisms:
   an arrow `f : X → Y` is an intervention that can carry the system from state `X` to
   state `Y`. Composition is sequential application of interventions; the identity at `X`
   is the null intervention, which does nothing to `X`."

**实现选择（关键）**：`Caus` 取为**干预箭图上的自由范畴** `Paths V`。
  · 对象      := 状态 `V`
  · 态射      := 干预的有限路径 `Quiver.Path X Y`
  · 恒等      := `Quiver.Path.nil`（零干预）
  · 复合      := `Quiver.Path.comp`（顺序施加）
⇒ 结合律与单位律由**自由构造**承担，**无需公设**；且自由构造自带**万有映射性质**。

这解决原稿 §1.1 的两处问题：
  (i) 原稿自认 "we deliberately do not fix what a state is" ⇒ 只给出**范畴的 schema**；
      此处 `V` 是被显式量化的参数，`V ↦ Caus V` 是**函子**（`map_id` / `map_comp`），
      schema 由此升级为函子（G2）。
  (ii) 原稿的"组合律 / 单位律"是散文断言；此处由 `Category (Paths V)` 承担（G3）。

**证据档位**：机器证明（本模块零 `sorry`）。
-/

import Mathlib.CategoryTheory.PathCategory.Basic

open CategoryTheory

universe u v

namespace CausModel

/-- 论文 Def 1.1 的载体：干预箭图 `V` 上的自由范畴。 -/
abbrev Caus (V : Type u) [Quiver.{v} V] : Type u := Paths V

namespace Caus

variable {V : Type u} [Quiver.{v} V]
variable {W : Type u} [Quiver.{v} W]
variable {X : Type u} [Quiver.{v} X]

/-- **Def 1.1 的范畴结构**：对象 = 状态，态射 = 干预路径，恒等 = 零干预，复合 = 顺序施加。 -/
instance instCategory : Category (Caus V) := inferInstance

/-! ## 万有性质（G3） -/

/-- **存在性**：任何从箭图出发的前函子 `φ : V ⥤q C` 唯一地延拓为 `Caus V` 上的函子。

论文读法：一旦固定了"每个干预对目标结构做什么"，整个干预范畴上的作用就被唯一确定。 -/
def lift {C : Type*} [Category C] (φ : V ⥤q C) : Caus V ⥤ C :=
  Paths.lift φ

/-- 延拓在零干预上取值恒等。 -/
@[simp]
theorem lift_nil {C : Type*} [Category C] (φ : V ⥤q C) (Y : V) :
    (lift φ).map (Quiver.Path.nil : Quiver.Path Y Y) = 𝟙 (φ.obj Y) :=
  Paths.lift_nil φ Y

/-- 延拓在路径延拓上取值复合（顺序施加）。 -/
@[simp]
theorem lift_cons {C : Type*} [Category C] (φ : V ⥤q C) {Y Z Z' : V}
    (p : Quiver.Path Y Z) (f : Z ⟶ Z') :
    (lift φ).map (p.cons f) = (lift φ).map p ≫ φ.map f :=
  Paths.lift_cons φ p f

/-- 延拓与单干预箭一致。 -/
@[simp]
theorem lift_toPath {C : Type*} [Category C] (φ : V ⥤q C) {Y Z : V} (f : Y ⟶ Z) :
    (lift φ).map f.toPath = φ.map f :=
  Paths.lift_toPath φ f

/-- 延拓确实是 `φ` 的延拓。 -/
theorem lift_spec {C : Type*} [Category C] (φ : V ⥤q C) :
    Paths.of V ⋙q (lift φ).toPrefunctor = φ :=
  Paths.lift_spec φ

/-- **唯一性**：任何延拓 `Φ` 都等于 `lift φ`。

⇒ `lift` 是 `V ⥤q C` 到 `Caus V ⥤ C` 的**双射**，即自由范畴的万有映射性质。 -/
theorem lift_unique {C : Type*} [Category C] (φ : V ⥤q C) (Φ : Caus V ⥤ C)
    (h : Paths.of V ⋙q Φ.toPrefunctor = φ) : Φ = lift φ :=
  Paths.lift_unique φ Φ h

/-! ## B-b：`Caus` 对状态空间是函子的（schema → 函子，G2） -/

/-- **诱导函子**：状态空间之间的前函子 `φ : V ⥤q W` 诱导干预范畴之间的函子。

这是把 §1.1 的 "schema" 升级为 **函子** 的那一步：框架不是"对某些状态空间成立"，
而是**沿着状态空间的映射协变地搬运**。 -/
def map (φ : V ⥤q W) : Caus V ⥤ Caus W :=
  Paths.lift (φ ⋙q Paths.of W)

/-- **函子律 1（单位）**。 -/
theorem map_id : map (𝟭q V) = 𝟭 (Caus V) := by
  unfold map
  rw [Prefunctor.id_comp]
  exact (Paths.lift_unique (C := Caus V) (Paths.of V) (𝟭 (Caus V)) rfl).symm

/-- **函子律 2（复合）**：`Caus` 保复合。 -/
theorem map_comp (φ : V ⥤q W) (ψ : W ⥤q X) :
    map (φ ⋙q ψ) = map φ ⋙ map ψ := by
  unfold map
  symm
  apply Paths.lift_unique
  rw [← Functor.toPrefunctor_comp]
  rw [← Prefunctor.comp_assoc]
  rw [Paths.lift_spec (φ ⋙q Paths.of W)]
  rw [Prefunctor.comp_assoc]
  rw [Paths.lift_spec (ψ ⋙q Paths.of X)]
  rfl

/-- **2-万有（一般干预范畴的典范刻画）**：任意干预范畴典范地是其路径范畴的商。

论文读法：Def 1.1 不预设"状态是什么"；一般情形由**商**得到，自由情形是基准点。 -/
def quotient_paths_equiv (C : Type u) [Category.{v} C] :
    Quotient (pathsHomRel C) ≌ C :=
  quotientPathsEquiv C

end Caus

end CausModel
