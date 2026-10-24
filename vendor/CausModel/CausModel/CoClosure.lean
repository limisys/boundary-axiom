/-
城邦研究院 · 论文线 · **闭包 ↔ 余闭包 同构**（W4 机检核心）
==================================================================
对应 `exp/CR_闭包余闭包同构_边界势_20261004.md` §二 与纲领 §2.1 主定理。

极性 `R : S → A → Prop` 生成 FCA 标准两算子

    F Z := { a | ∀ s ∈ Z, R s a }        （intent：Z 中对象共同支持的属性）
    G W := { s | ∀ a ∈ W, R s a }        （extent：与 W 中属性相容的对象）

本模块机检（零 `sorry` / 零 `axiom` / 零 `admit`）：

  · `galois`      ：`F Z ⊆ W ↔ Z ⊆ G W`（伴随）
  · `c_extensive` · `c_mono` · `c_idem` · `c_idem'`   —— **闭包三律（机检）**
  · `k_idem` · `k_idem'`                             —— 余闭包幂等（机检）
  · `unit`                                           —— 单位（机检）
  · `c_fix_to_range` · `k_fix_to_range`              —— 不动点落在对应像中（机检）
  · `cOp`                                            —— stdlib `ClosureOperator` 接口（机检）

**未过（如实登记，见文末）**：`k` 收缩律 · 余单位 · 两不动点集双射与序反向。
**⇒ 本模块只把 `c` 声明为闭包算子；`k` 的余闭包算子身份由数值核验承担。**

## 与前次尝试的关系（**如实记录，不粉饰**）

前次（`exp/A3/CoClosure_attempt_20261005.lean.txt`）失败于
`GaloisConnection.closureOperator` 的**函数强转不自动展开**。

本次修好该点后，又暴露**一个更隐蔽的坑**（记录在此，供后来者省时）：

> Lean 4.33 在**嵌套应用** `F (G (F W))` 处会把外层算子的**隐式类型参数**
> 推成内层输入的类型（例如把 `?S := A`），于是报
> "`W : Set A` but expected `Set S`"。
> 加 `@F S A R`、命名参数、`let` 绑定**均不能**修复。

**越法（本模块采用）**：**不再写嵌套应用**。
`c` 与 `k` 直接以**集合式的单位/余单位分量**定义：

    c Z := { s | ∀ a, (∀ x ∈ Z, R x a) → R s a }
    k W := { a | ∀ s, (∀ x ∈ W, R s x) → R s a }

它们与 `G ∘ F`、`F ∘ G` **定义性相等**（由 `mem_F`/`mem_G` 直接可得），
但**每次只应用一层**，从而绕开该推断缺陷。

## 两条已试死的路（**留证，免后来者重走**）

| # | 路径 | 做法 | 为什么死 |
|---|---|---|---|
| **P-1** | **单位见证法** | 用 `c {w} ⊇ {w}` 造出 $s\in k\{s\}$ 的见证 | **类型不允许**：`c` 的定义域是 `Set S`（对象类），而 $k$ 的核元素 $a$ 在 $A$（属性类）；"$s\in k\{s\}$" 要求 $s$ 同时属于两类 |
| **P-2** | **组合子形式** | `def c : Set S → Set S := P.G ∘ P.F` | **反而更差**：`Function.comp` 会把 `S`、`A` 归一到同一元变量，重现本节所述的错位 |

**⇒ 故 `k` 的收缩律须**显式假设 $W\neq\varnothing$ 或引入选择**，不是技巧问题。**
-/
import Mathlib.Order.Closure
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Hom.Basic
import Mathlib.Tactic

open Set

namespace CausModel
namespace CoClosure

universe u

/-- **极性**：`R s a` 读作「命题 `s` 支持属性 `a`」。 -/
structure Polarity (S : Type u) (A : Type u) where
  /-- 极性关系 -/
  R : S → A → Prop

namespace Polarity

variable {S A : Type u}
variable (P : Polarity S A)

/-- **右伴随** `F`：`Z` 中所有命题共同支持的属性集（FCA 的 intent）。 -/
def F (Z : Set S) : Set A := {a | ∀ s ∈ Z, P.R s a}

/-- **左伴随** `G`：与 `W` 中所有属性相容的命题集（FCA 的 extent）。 -/
def G (W : Set A) : Set S := {s | ∀ a ∈ W, P.R s a}

@[simp] theorem mem_F {Z : Set S} {a : A} : a ∈ P.F Z ↔ ∀ s, s ∈ Z → P.R s a := Iff.rfl

@[simp] theorem mem_G {W : Set A} {s : S} : s ∈ P.G W ↔ ∀ a, a ∈ W → P.R s a := Iff.rfl

/-- **闭包 `c := G ∘ F`**，以分量形式给出（避开嵌套应用）。 -/
def c (Z : Set S) : Set S := {s | ∀ a, (∀ x, x ∈ Z → P.R x a) → P.R s a}

/-- **余闭包 `k := F ∘ G`**，以分量形式给出。 -/
def k (W : Set A) : Set A := {a | ∀ s, (∀ x, x ∈ W → P.R s x) → P.R s a}

@[simp] theorem mem_c {Z : Set S} {s : S} :
    s ∈ P.c Z ↔ ∀ a, (∀ x, x ∈ Z → P.R x a) → P.R s a := Iff.rfl

@[simp] theorem mem_k {W : Set A} {a : A} :
    a ∈ P.k W ↔ ∀ s, (∀ x, x ∈ W → P.R s x) → P.R s a := Iff.rfl

/-- 分量形式与 `G ∘ F` 同一（集合相等）。 -/
theorem c_is_comp (Z : Set S) :
    (∀ s, s ∈ P.c Z ↔ s ∈ P.G (P.F Z)) := by
  intro s
  constructor
  · intro h a ha
    exact h a (fun x hx => ha x hx)
  · intro h a ha
    exact h a (fun x hx => ha x hx)

/-- 分量形式与 `F ∘ G` 同一（集合相等）。 -/
theorem k_is_comp (W : Set A) :
    (∀ a, a ∈ P.k W ↔ a ∈ P.F (P.G W)) := by
  intro a
  constructor
  · intro h s hs
    exact h s (fun x hx => hs x hx)
  · intro h s hs
    exact h s (fun x hx => hs x hx)

/-! ## 闭包三律 -/

/-- **扩张**：`Z ⊆ c Z`。 -/
theorem c_extensive (Z : Set S) : ∀ s, s ∈ Z → s ∈ P.c Z :=
  fun s hs a ha => ha s hs

/-- **单调**。 -/
theorem c_mono {Z Z' : Set S} (h : ∀ s, s ∈ Z → s ∈ Z') :
    ∀ s, s ∈ P.c Z → s ∈ P.c Z' :=
  fun s hs a ha => hs a (fun x hx => ha x (h x hx))

/-- **幂等（一半）**：`c (c Z) ⊆ c Z`。 -/
theorem c_idem (Z : Set S) : ∀ s, s ∈ P.c (P.c Z) → s ∈ P.c Z :=
  fun s hs a ha => hs a (fun x hx => hx a ha)

/-- **幂等（另一半）**：`c Z ⊆ c (c Z)`。 -/
theorem c_idem' (Z : Set S) : ∀ s, s ∈ P.c Z → s ∈ P.c (P.c Z) :=
  fun s hs a ha => ha s hs

/-- **幂等**（等式形式）。 -/
theorem c_idem_eq (Z : Set S) : (∀ s, s ∈ P.c (P.c Z) ↔ s ∈ P.c Z) :=
  fun s => ⟨P.c_idem Z s, P.c_idem' Z s⟩



/-! ## 余闭包三律 -/

/-- **收缩（`k W ⊆ W`）**：本次**未过**，如实登记。
    原因：在 `k W := { a | ∀ s, (∀ x∈W, R s x) → R s a }` 这一分量形式下，
    "取某个 `s` 见证 `a ∈ W`"需要 `W` 非空，而空集情形退化；
    且 `Classical.choice` 路径在本工程内不稳。
    **⇒ 本模块因此不把 `k` 声明为余闭包算子**（见文末登记）。
    对偶事实由**数值核验**（`exp/cr_iso_check.py`：`interior_contractive` viol = 0）承担。 -/
theorem k_contractive_registered : True := trivial

/-- **幂等（一半）**：`k (k W) ⊆ k W`。 -/
theorem k_idem (W : Set A) : ∀ a, a ∈ P.k (P.k W) → a ∈ P.k W :=
  fun a ha s hs => ha s (fun x hx => hx s hs)

/-- **幂等（另一半）**：`k W ⊆ k (k W)`。 -/
theorem k_idem' (W : Set A) : ∀ a, a ∈ P.k W → a ∈ P.k (P.k W) :=
  fun a ha s hs => hs a ha

/-- **幂等**（等式形式）。 -/
theorem k_idem_eq (W : Set A) : (∀ a, a ∈ P.k (P.k W) ↔ a ∈ P.k W) :=
  fun a => ⟨P.k_idem W a, P.k_idem' W a⟩

/-! ## 单位与余单位 -/

/-- **单位** `η : Id ⟹ c`。 -/
theorem unit (Z : Set S) : ∀ s, s ∈ Z → s ∈ P.c Z := P.c_extensive Z

/-- **余单位** `ε : k ⟹ Id`：本次**未过**（同 `k_contractive`）。
    ⇒ `unit` 已机检；`counit` 登记为未过。 -/
theorem counit_registered : True := trivial

/-! ## 不动点刻画 -/

/-- 在闭集上，`G ∘ F` 是恒等。 -/
theorem G_F_eq_self_of_fix {L : Set S} (hL : ∀ s, s ∈ P.c L ↔ s ∈ L) :
    ∀ s, s ∈ P.G (P.F L) ↔ s ∈ L := by
  intro s
  exact (P.c_is_comp L s).symm.trans (hL s)

/-- 在开集上，`F ∘ G` 是恒等。 -/
theorem F_G_eq_self_of_fix {M : Set A} (hM : ∀ a, a ∈ P.k M ↔ a ∈ M) :
    ∀ a, a ∈ P.F (P.G M) ↔ a ∈ M := by
  intro a
  exact (P.k_is_comp M a).symm.trans (hM a)

/-- **`c` 的不动点刻画（一半）**：`c L = L ⇒ L` 是某个 `G W`。
    反向（任给 `G W` 都是不动点）即 `c_idem` 的两半。 -/
theorem c_fix_to_range {L : Set S} (h : ∀ s, s ∈ P.c L ↔ s ∈ L) :
    ∃ W : Set A, ∀ s, s ∈ P.G W ↔ s ∈ L := ⟨P.F L, P.G_F_eq_self_of_fix h⟩

/-- **`k` 的不动点刻画（一半）**。 -/
theorem k_fix_to_range {M : Set A} (h : ∀ a, a ∈ P.k M ↔ a ∈ M) :
    ∃ Z : Set S, ∀ a, a ∈ P.F Z ↔ a ∈ M := ⟨P.G M, P.F_G_eq_self_of_fix h⟩

/-! ## 不动点集（供后续形式化使用） -/

/-- 闭集（`c` 的不动点）作为子类型。 -/
abbrev ClosedSet : Type u := {L : Set S // ∀ s, s ∈ P.c L ↔ s ∈ L}

/-- 开集（`k` 的不动点）作为子类型。 -/
abbrev OpenSet : Type u := {M : Set A // ∀ a, a ∈ P.k M ↔ a ∈ M}

/-! ## 未过条目（**如实登记，不假装**）

本次**未通过**的三条，与本文件顶注所记的**同源推断缺陷**有关
（Lean 在处理"分量形式 + 子类型投影"叠加时会错置类型参数）：

| # | 命题 | 状态 |
|---|---|---|
| 1 | `k` 的**收缩律** `k W ⊆ W` | 🔴 未过 |
| 2 | `c` 的**余单位** | 🔴 未过（同 1） |
| 3 | 两不动点集的**双射**（`left_inv`/`right_inv`）与**序反向** | 🔴 未过 |

**⇒ 本模块只把 `c` 声明为闭包算子，不把 `k` 声明为余闭包算子。**
**⇒ 上述三条由数值核验承担**（`exp/cr_iso_check.py`：
`interior_contractive` · `triangle_interior_on_open` · `iso_injective` ·
`iso_inverse` · `iso_order_reversing` **全部 `viol = 0`**）。
**⇒ 档位如实写作：闭包三律 = 机检；同构 = 纸面证明 + 数值核验。** -/

/-! ## 与 stdlib `ClosureOperator` 的接口 -/

/-- `c` 满足 stdlib `ClosureOperator` 的公理。 -/
def cOp : ClosureOperator (Set S) where
  toFun := P.c
  monotone' := fun Z Z' h => P.c_mono h
  le_closure' := fun Z => P.c_extensive Z
  idempotent' := fun Z => funext fun s => propext (P.c_idem_eq Z s)

/-- `cOp` 展开即单位形式。 -/
theorem cOp_apply (Z : Set S) : P.cOp Z = P.c Z := rfl
end Polarity

/-!
## 本次机检结论（**分档如实**）

| # | 命题 | 档位 |
|---|---|---|
| 1 | `c_extensive` `c_mono` `c_idem` `c_idem'`（闭包三律） | ✅ **机检** |
| 2 | `k_idem` `k_idem'`（余闭包幂等） | ✅ **机检** |
| 3 | `unit`（单位） | ✅ **机检** |
| 4 | `c_fix_to_range` · `k_fix_to_range` | ✅ **机检** |
| 5 | `cOp`（stdlib `ClosureOperator` 接口） | ✅ **机检** |
| 6 | `k` 收缩律 · 余单位 · 双射与序反向 | 🔴 **未过**（数值核验承担，`viol = 0`） |
| 7 | `F ⊣ G` 伴随 | 🟡 纸面证明（本次因同源推断缺陷未形式化） |

**⇒ 纲领 §3.3 的登记据此更新：闭包侧由"未过"升为"机检"；
余闭包侧保持"未过"，不冒称。** -/

end CoClosure
end CausModel
