/-
城邦研究院 · 论文线 · B 阶段 · B0 探针
=========================================

目的：在既有 Lean 4.33.0 + mathlib v4.33.0 产物之上，核验
论文 Def 1.1 所需的"干预范畴"是否可由 mathlib 现成构造承担。

论文 Def 1.1（`统一边界理论EN稿.md` L90）：
  "The category **Caus** has states as objects and causal interventions as morphisms:
   an arrow f : X → Y is an intervention that can carry the system from state X to
   state Y. Composition is sequential application of interventions; the identity at X
   is the null intervention, which does nothing to X."

对应 mathlib 构造 `Paths V`（`Mathlib/CategoryTheory/PathCategory/Basic.lean`）：
  · Hom X Y := Quiver.Path X Y      —— 态射 = 干预的有限序列
  · id       := Quiver.Path.nil     —— 单位 = 零干预
  · comp     := Quiver.Path.comp    —— 复合 = 顺序施加
⇒ 结合律与单位律由**自由构造**承担，无需公设。

本探针只做类型级核验（#check + 可编译例证），不产生定理。
-/

import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.CategoryTheory.CommSq
import Mathlib.CategoryTheory.Monad.Algebra
import Mathlib.Order.FixedPoints
import Mathlib.Topology.MetricSpace.Contracting

open CategoryTheory

namespace CausModel.Probe

universe u v

variable {V : Type u} [Quiver.{v} V]

/-! ### 探针 1：`Paths V` 已是范畴（论文 Def 1.1 的载体） -/

example : Category (Paths V) := inferInstance

/-! ### 探针 2：万有性质 `lift` 可用（G3：自由范畴的万有映射性质） -/

example (C : Type*) [Category C] (φ : V ⥤q C) : Paths V ⥤ C := Paths.lift φ

/-! ### 探针 3：泛性质各条已证 -/

#check @Paths.lift
#check @Paths.lift_nil
#check @Paths.lift_cons
#check @Paths.lift_toPath
#check @Paths.lift_unique

/-! ### 探针 4：一般干预范畴的典范刻画（2-万有） -/

#check @CategoryTheory.pathsHomRel
#check @CategoryTheory.toQuotientPaths
#check @CategoryTheory.quotientPathsTo
#check @CategoryTheory.quotientPathsEquiv

/-! ### 探针 4b：Prefunctor 复合（B-b 函子性所需） -/

#check @Prefunctor.comp
#check @Prefunctor.id
#check @Prefunctor.obj
#check @Paths.of

/-! ### 探针 5：mathlib 范畴原语在位（B2–B5 所需） -/

#check @CategoryTheory.Functor
#check @CategoryTheory.NatTrans
#check @CategoryTheory.CommSq
#check @CategoryTheory.Monad
#check @CategoryTheory.Monad.Algebra
#check @OrderHom.lfp
#check @ContractingWith.fixedPoint

end CausModel.Probe
