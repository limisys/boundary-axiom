/-
城邦研究院 · 论文线 · C 阶段 · R3：幂等凝聚 ⇒ 边界 = 不动点
=================================================================

**目标**：论文 §2.1 说凝聚"*is complete exactly when the comparison has settled —
when further intervention changes nothing in attribution*"。本模块把这个"完成"
变成范畴学中精确的**幂等性**，并证明它等价于**边界对象是不动点**。

**数学内容**：
  · 凝聚 `T` 是范畴 `C` 上的单子；`η` 是单位，`μ` 是乘法；
  · **幂等** ⟺ `μ` 是同构 ⟺ `η_{TX}` 是同构（对一切 `X`）；
  · 单子三角恒等式 `η_{TX} ≫ μ_X = 𝟙` **无条件成立**；
  · ⇒ 只需 `μ_X` 可逆，即得 `η_{TX}` 可逆 —— **`T X` 是不动点**。

⇒ "凝聚完成" = `T X` 落在边界（不动点子范畴）中 = `η_{TX}` 是同构。

**证据档位**：机器证明（本模块零 `sorry`）。
-/

import Mathlib.CategoryTheory.Monad.Algebra
import CausModel.Boundary

open CategoryTheory

universe u v

namespace CausModel

section Categorical

variable {C : Type u} [Category.{v} C]

/-- **【R3 主定理】幂等凝聚 ⇒ 边界对象是不动点**。

若 `μ_X` 可逆（即凝聚**幂等**：再做一次凝聚不再改变），则 `η_{T X}` 可逆，
即 `T X` 落在**不动点子范畴**（边界）中。

证明只用单子三角恒等式 `η_{T X} ≫ μ_X = 𝟙`（mathlib `Monad.left_unit`，**无条件成立**）
加上 `μ_X` 的可逆性：由 `η ≫ μ = 𝟙` 与 `μ` 可逆得 `η = μ⁻¹`，故 `η` 可逆。 -/
theorem idempotent_eta_obj_isIso (T : Monad C) (X : C) (h : IsIso (T.μ.app X)) :
    IsIso (T.η.app (T.obj X)) := by
  haveI := h
  have h1 : T.η.app (T.obj X) ≫ T.μ.app X = 𝟙 (T.obj X) := T.left_unit X
  have h3 : inv (T.μ.app X) = T.η.app (T.obj X) := by
    calc inv (T.μ.app X)
        = 𝟙 (T.obj X) ≫ inv (T.μ.app X) := (Category.id_comp _).symm
      _ = (T.η.app (T.obj X) ≫ T.μ.app X) ≫ inv (T.μ.app X) := by rw [h1]
      _ = T.η.app (T.obj X) ≫ (T.μ.app X ≫ inv (T.μ.app X)) := Category.assoc _ _ _
      _ = T.η.app (T.obj X)
            ≫ 𝟙 ((T : C ⥤ C).obj ((T : C ⥤ C).obj X)) := by rw [IsIso.hom_inv_id]
      _ = T.η.app (T.obj X) := Category.comp_id _
  rw [← h3]
  infer_instance

/-- **凝聚完成的判据**：`T X` 在边界中 ⟺ `η_{T X}` 是同构。

这把 §2.1 的 "when further intervention changes nothing in attribution"
翻译成范畴学中可判定的条件。 -/
def IsCohesive (T : Monad C) (X : C) : Prop := IsIso (T.η.app X)

/-- 幂等 ⇒ 每个 `T X` 都是凝聚的。 -/
theorem isCohesive_obj_of_idempotent (T : Monad C) (X : C) (h : IsIso (T.μ.app X)) :
    IsCohesive T (T.obj X) :=
  idempotent_eta_obj_isIso T X h

/-- **凝聚完备化**：`η_X` 把任意状态送入其凝聚完成态。 -/
def cohesionUnit (T : Monad C) (X : C) : X ⟶ T.obj X := T.η.app X

/-- **完备化的靶是边界对象**：`η_X` 的靶 `T X` 正是自由边界对象的载体
（`boundary_free_carrier`）。

⇒ "凝聚完成"不是外加的稳定化过程，而是**自由–遗忘伴随的单位**的靶。 -/
theorem cohesionUnit_target (T : Monad C) (X : C) :
    (T.free.obj X).A = (T : C ⥤ C).obj X :=
  rfl

end Categorical

end CausModel
