/-
  Copyright 2026 Xueqiang Gao (高学强) · ORCID 0009-0008-3821-3454
  Licensed under the Apache License, Version 2.0 (see LICENSE).
  Original publication source: caseos.cn/research — https://caseos.cn/research/
  First public release 2026-10-09; formal publication 2026-10-20.
  Part of the B-line canonical subset (group 2): 53 files / 417 theorems+lemmas / 77 definitions.
  Attribution header added at publication; proof bodies unchanged.
-/

/-
CategoricalDictionary.lean —— **偏序情形与范畴情形的字典**（第 73 轮）

**动机**：§3.1 说闭包算子 $c=G\circ F$ 来自"**干预范畴**"上的伴随。
但本纲领此前造出的每一个伴随都是**偏序情形**（Galois 连接）。两者到底是什么关系？
本轮给出**精确的字典**，并**明确划出未做的部分**。

**事实链条**（每一步都可核）：

  1. Galois 连接 $l\dashv u$（偏序）**就是**预序范畴之间的伴随——Mathlib `GaloisConnection.adjunction`（**引用，不主张**）；
  2. 该伴随诱导一个 **monad**——Mathlib `Adjunction.toMonad`，其 `toFunctor = L ⋙ R`；
  3. 于是该 monad 的**对象映射恰是闭包算子**：`(gc.adjunction).toMonad.obj x = gc.closureOperator.toFun x`；
  4. 而"$x$ 承载一个 **Eilenberg–Moore 代数**结构" $\iff$ "$x$ 是闭包算子的不动点"。

**所以**：**刚性面 $\mathrm{Fix}(c)$ 在一般范畴情形里对应 EM 代数范畴**；
偏序情形只是它的退化实例（hom 集是命题，故代数的两条公理自动成立）。

**范围声明（必须连同本件一起读）**：
本件做的是**偏序情形的字典**。**一般范畴**（非预序）的对应**未做**——
"闭包算子"要换成"monad"、"不动点集"要换成"EM 代数范畴"，
而 $b$、$\sigma$、$V$ 这些**值层**对象在一般范畴里**尚无对应物**。
本件不主张一般情形的任何结论。

0 `sorry` / 0 `axiom`。
-/
import Mathlib

open CategoryTheory

namespace CategoricalDictionary

variable {α β : Type*} [PartialOrder α] [PartialOrder β]
variable {l : α → β} {u : β → α}

/-- **由 Galois 连接诱导的 monad**（偏序情形的范畴层对象）。 -/
noncomputable def gcMonad (gc : GaloisConnection l u) : Monad α :=
  (gc.adjunction).toMonad

/-- **（字典 1）** 该 monad 的**对象映射就是闭包算子**——范畴层的 monad 与序论的闭包算子在此重合。 -/
theorem monad_obj_eq_closure (gc : GaloisConnection l u) (x : α) :
    (gcMonad gc).obj x = gc.closureOperator.toFun x := rfl

/-- **（字典 2）** "$x$ 上方有到 $x$ 的态射" $\iff$ "$x$ 是闭包算子的不动点"。
在预序范畴里前者正是 **Eilenberg–Moore 代数的结构映射** $c\,x\longrightarrow x$。 -/
theorem has_algebra_map_iff_fix (gc : GaloisConnection l u) (x : α) :
    Nonempty ((gcMonad gc).obj x ⟶ x) ↔ gc.closureOperator.toFun x = x := by
  rw [monad_obj_eq_closure gc x]
  constructor
  · rintro ⟨f⟩
    exact le_antisymm (CategoryTheory.leOfHom f) (gc.le_u_l x)
  · intro h
    exact ⟨CategoryTheory.homOfLE (le_of_eq h)⟩

/-- **（字典 3）** 承载**一个 EM 代数**（以 `x` 为底对象）$\iff$ `x` 是不动点。
预序范畴里两条代数公理自动成立（hom 集是命题）。 -/
theorem has_algebra_iff_fix (gc : GaloisConnection l u) (x : α) :
    Nonempty {A : (gcMonad gc).Algebra // A.A = x} ↔ gc.closureOperator.toFun x = x := by
  constructor
  · rintro ⟨A, hA⟩
    have h := (has_algebra_map_iff_fix gc x).mp ⟨hA ▸ A.a⟩
    exact h
  · intro h
    exact ⟨{ A := x, a := CategoryTheory.homOfLE (le_of_eq h) }, rfl⟩

/-- **（字典 4 · 不分主次的方向）** 不动点集恰是"其上有代数结构"的对象的集合——
即 §3.1 的刚性面在范畴层的对应物。 -/
theorem fix_eq_objects_with_algebra (gc : GaloisConnection l u) :
    {x : α | gc.closureOperator.toFun x = x}
      = {x : α | Nonempty {A : (gcMonad gc).Algebra // A.A = x}} := by
  ext x
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq]
  exact (has_algebra_iff_fix gc x).symm

/-- **（收官）** 字典三条打包：monad 对象映射＝闭包算子；有代数映射 $\iff$ 不动点；有代数 $\iff$ 不动点。 -/
theorem dictionary (gc : GaloisConnection l u) :
    (∀ x, (gcMonad gc).obj x = gc.closureOperator.toFun x)
    ∧ (∀ x, Nonempty ((gcMonad gc).obj x ⟶ x) ↔ gc.closureOperator.toFun x = x)
    ∧ (∀ x, Nonempty {A : (gcMonad gc).Algebra // A.A = x} ↔ gc.closureOperator.toFun x = x) :=
  ⟨monad_obj_eq_closure gc, has_algebra_map_iff_fix gc, has_algebra_iff_fix gc⟩

end CategoricalDictionary
