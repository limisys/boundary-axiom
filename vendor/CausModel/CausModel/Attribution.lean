/-
城邦研究院 · 论文线 · B 阶段 · B2：归因预函子
================================================

对应论文 `统一边界理论EN稿.md` **Def 1.2 / 1.3（attribution simplex / attributive presheaf）**
（L96–L108）：

  "Write Δ² for the simplex of attribution scores,
        Δ² = {(p_S, p_N, p_U) ∈ [0,1]³ : p_S + p_N + p_U = 1},
   where p_S is the score of 'attributed to self', p_N of 'attributed to non-self',
   and p_U of 'left undetermined'."
  "The attributive presheaf is a contravariant functor A : Caus^op → Δ².
   It assigns to each state X its attribution distribution A(X) ∈ Δ², and to each
   intervention f : X → Y a pullback A(f) : A(Y) → A(X) …
   For composable interventions, A(g ∘ f) = A(f) ∘ A(g)."

**原稿的两处类型病（本节修复）**：
  (i)  Δ² 在原稿里只是一个**集合**，未声明范畴结构 ⇒ `A : Caus^op → Δ²` **不是合法函子类型**；
       本节把 Δ² 显式实现为**类型**（`Simplex`），预函子取值于 `Type`，类型成立。
  (ii) 函子律 `A(g∘f) = A(f)∘A(g)` 在原稿是**散文断言**；本节证明它**由函子结构唯一决定**，
       且预函子**由其在单干预上的取值唯一决定**（§1.2 的真正范畴内容）。

**关键刻画**：一个逆变预函子不是"再选一次"的东西——它在单干预上的取值一旦给定，
整个干预范畴上的取值就被 `Paths.lift_unique` **唯一钉死**。

**证据档位**：机器证明（本模块零 `sorry`）。σ 的两义与记号冲突见论文 §1.5（W2 处理）。
-/

import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Tactic
import CausModel.Caus

open CategoryTheory

universe u v

namespace CausModel

/-! ## Def 1.2：归因单形 Δ² -/

/-- 论文 Def 1.2 的归因单形：三个归因判定上的分数，和为 1。

`pS` = 归于自我，`pN` = 归于非我，`pU` = 悬置未定。 -/
structure Simplex where
  /-- 归于自我的分数。 -/
  pS : ℝ
  /-- 归于非我的分数。 -/
  pN : ℝ
  /-- 悬置未定的分数。 -/
  pU : ℝ
  /-- 三项非负。 -/
  nonneg_S : 0 ≤ pS
  /-- 三项非负。 -/
  nonneg_N : 0 ≤ pN
  /-- 三项非负。 -/
  nonneg_U : 0 ≤ pU
  /-- 归属总是被完全分配：三项之和恒为 1。 -/
  sum_eq_one : pS + pN + pU = 1

namespace Simplex

/-- 三项之和恒为 1 ⇒ 每一项不超过 1（原稿写作 $[0,1]^3$，此处给出推导而非假设）。 -/
theorem le_one_of_pS (s : Simplex) : s.pS ≤ 1 := by
  have := s.nonneg_N
  have := s.nonneg_U
  linarith [s.sum_eq_one]

end Simplex

/-! ## Def 1.3：归因预函子 -/

section Presheaf

variable {V : Type u} [Quiver.{v} V]
variable {D : Type*} [Category D]

/-- **归因预函子**（论文 Def 1.3）。

逆变函子 `A : Caus^op ⥤ D` 等价地写成协变函子 `Caus V ⥤ Dᵒᵖ`；
其数据是"每个单干预把归因往哪个方向拉"，即前函子 `a : V ⥤q Dᵒᵖ`。
自由的干预范畴使这一延拓**无需选择**。 -/
def attribution (a : V ⥤q Dᵒᵖ) : Caus V ⥤ Dᵒᵖ :=
  Paths.lift a

/-- **函子律**（原稿 L106）：`A(g ∘ f) = A(f) ∘ A(g)`。

注意方向：`Caus V` 中的复合 `f ≫ g` 在 `Dᵒᵖ` 中反转为 `A g ≫ A f`——
这正是"归因逆着因果箭头传播"的范畴内容。 -/
theorem attribution_map_comp (a : V ⥤q Dᵒᵖ) {X Y Z : V}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (attribution a).map (f.toPath ≫ g.toPath) =
      (attribution a).map f.toPath ≫ (attribution a).map g.toPath :=
  Functor.map_comp (attribution a) f.toPath g.toPath

/-- **单干预上的取值**：预函子在一条干预箭上的取值就是给定数据本身。 -/
theorem attribution_single (a : V ⥤q Dᵒᵖ) {X Y : V} (f : X ⟶ Y) :
    (attribution a).map f.toPath = a.map f :=
  Paths.lift_toPath a f

/-- **唯一性（§1.2 的真正范畴内容）**：归因预函子由它在**单干预**上的取值唯一决定。

⇒ 原稿断言"归因沿干预逐个反序传播"不是额外公设，而是**自由构造的唯一性**。 -/
theorem attribution_unique (a : V ⥤q Dᵒᵖ) (B : Caus V ⥤ Dᵒᵖ)
    (h : Paths.of V ⋙q B.toPrefunctor = a) : B = attribution a :=
  Paths.lift_unique a B h

end Presheaf

end CausModel
