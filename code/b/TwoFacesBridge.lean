/-
  Copyright 2026 Xueqiang Gao (高学强) · ORCID 0009-0008-3821-3454
  Licensed under the Apache License, Version 2.0 (see LICENSE).
  Original publication source: caseos.cn/research — https://caseos.cn/research/
  First public release 2026-10-09; formal publication 2026-10-20.
  Part of the B-line canonical subset (group 2): 53 files / 417 theorems+lemmas / 77 definitions.
  Attribution header added at publication; proof bodies unchanged.
-/

/-
TwoFacesBridge.lean —— 伴随的两面是**同一个对象**（第 61 轮）

**动机**：论文 §2.1 写着"非交换轨迹不是边界——二者之间的桥**不存在**（一条候选路线已被穷尽反驳）"。
这是一条**存在性否定**主张，而它只有"一条路线被反驳"作依据——**按本文自己的铁律（默认否定），这是越界**。
本件把它改成一条**能被机器检查的**陈述：

设 `GaloisConnection l u`（`l : α → β`，`u : β → α`，即 `l a ≤ b ↔ a ≤ u b`）。定义两面：

  · **闭包侧（刚性面）** `FixV l u = {a : α | u (l a) = a}`  —— `u ∘ l` 的不动点
  · **内部侧**         `FixW l u = {b : β | l (u b) = b}`  —— `l ∘ u` 的不动点

**主结果（正）**：两面**典范序同构** `fixOrderIso : FixV ≃o FixW`，且同构由 `l`、`u` 本身给出；
并且两面**恰好是两个值域**：`FixV = range u`、`FixW = range l`。

**主结果（负/界定）**：这个同构**不是**恒等——模糊区可以非空（有具体反例）；
且两面**分居两个类型**，谈不上"相等"。故 §2.1 那句必须收窄为：
**"非交换轨迹"与边界之间不存在的是「恒等」，不是「桥」**；桥不但有，而且是典范的。

**0 `sorry` / 0 `axiom`。**
-/
import Mathlib

open Set

namespace TwoFacesBridge

variable {α β : Type*}

/-- **闭包侧（刚性面）**：`u ∘ l` 的不动点集。 -/
def FixV (l : α → β) (u : β → α) : Set α := {a | u (l a) = a}

/-- **内部侧**：`l ∘ u` 的不动点集。 -/
def FixW (l : α → β) (u : β → α) : Set β := {b | l (u b) = b}

/-! 本节的两条**不需要**偏序假设，故单独置于 `variable [PartialOrder …]` 之前。 -/

/-- `image f ⊣ preimage f`（Mathlib 的 `Set.image_subset_iff` 即此伴随的等价形式）。 -/
theorem image_preimage_galois (f : α → β) :
    GaloisConnection (image f) (preimage f) :=
  fun _ _ => image_subset_iff

variable [PartialOrder α] [PartialOrder β] {l : α → β} {u : β → α}

/-- `FixV` 恰是 `u` 的值域。 -/
theorem mem_FixV_iff_mem_range (gc : GaloisConnection l u) (a : α) :
    a ∈ FixV l u ↔ a ∈ range u := by
  constructor
  · intro ha
    exact ⟨l a, ha⟩
  · rintro ⟨b, rfl⟩
    exact gc.u_l_u_eq_u b

/-- `FixW` 恰是 `l` 的值域。 -/
theorem mem_FixW_iff_mem_range (gc : GaloisConnection l u) (b : β) :
    b ∈ FixW l u ↔ b ∈ range l := by
  constructor
  · intro hb
    exact ⟨u b, hb⟩
  · rintro ⟨a, rfl⟩
    exact gc.l_u_l_eq_l a

theorem FixV_eq_range (gc : GaloisConnection l u) : FixV l u = range u := by
  ext a; exact mem_FixV_iff_mem_range gc a

theorem FixW_eq_range (gc : GaloisConnection l u) : FixW l u = range l := by
  ext b; exact mem_FixW_iff_mem_range gc b

/-! ## 二 · `l`、`u` 把两面互相送到对面 -/

theorem map_l_mem_FixW (gc : GaloisConnection l u) {a : α} (_ha : a ∈ FixV l u) :
    l a ∈ FixW l u := by
  rw [mem_FixW_iff_mem_range gc]
  exact ⟨a, rfl⟩

theorem map_u_mem_FixV (gc : GaloisConnection l u) {b : β} (_hb : b ∈ FixW l u) :
    u b ∈ FixV l u := by
  rw [mem_FixV_iff_mem_range gc]
  exact ⟨b, rfl⟩

/-! ## 三 · 主定理：两面**典范序同构** -/

/-- **（主定理 · 正）** 伴随的两面典范序同构，同构由 `l` 与 `u` 本身给出。
**这就是本纲领的核心动作**：闭包侧与内部侧此前被当作两个对象，其实它们是同一个对象的两面。 -/
def fixOrderIso (gc : GaloisConnection l u) :
    {a : α // a ∈ FixV l u} ≃o {b : β // b ∈ FixW l u} where
  toFun a := ⟨l a.1, map_l_mem_FixW gc a.2⟩
  invFun b := ⟨u b.1, map_u_mem_FixV gc b.2⟩
  left_inv a := by
    apply Subtype.ext
    simpa [FixV] using a.2
  right_inv b := by
    apply Subtype.ext
    simpa [FixW] using b.2
  map_rel_iff' := by
    intro a b
    constructor
    · intro h
      have ha : u (l a.1) = a.1 := by simpa [FixV] using a.2
      have hb : u (l b.1) = b.1 := by simpa [FixV] using b.2
      calc a.1 = u (l a.1) := ha.symm
        _ ≤ u (l b.1) := gc.monotone_u h
        _ = b.1 := hb
    · intro h
      exact gc.monotone_l h

/-- 两面互逆（在面上）：`u (l a) = a` 与 `l (u b) = b` 即互为逆。 -/
theorem faces_mutually_inverse (_gc : GaloisConnection l u) {a : α} (ha : a ∈ FixV l u) :
    u (l a) = a := ha

theorem faces_mutually_inverse' (_gc : GaloisConnection l u) {b : β} (hb : b ∈ FixW l u) :
    l (u b) = b := hb

/-- 闭包算子 `u ∘ l` 是幂等的（与 Mathlib 的 `GaloisConnection.closureOperator` 一致，此处列出以备引用）。 -/
theorem closure_idem (gc : GaloisConnection l u) (a : α) : u (l (u (l a))) = u (l a) :=
  gc.u_l_u_eq_u (l a)

/-- 闭包算子是**扩张**的：`a ≤ u (l a)`。 -/
theorem le_closure (gc : GaloisConnection l u) (a : α) : a ≤ u (l a) :=
  gc.le_u_l a

/-! ## 四 · 主结果（负/界定）：同构**不是恒等**，模糊区可以非空

取 `f : Bool → Bool` 为常值 `false`，在 `Set` 上取 `image f ⊣ preimage f`。
则闭包算子 `preimage f ∘ image f` 把 `{true}` 送到 `univ ≠ {true}`——**模糊区非空**。
故"边界 = 一切状态"是假的；而 §2.1 的"桥不存在"也必须收窄为**"恒等不存在"**。
-/

/-- **反例**：常值函数下，闭包算子不是恒等——模糊区非空。 -/
theorem fuzzy_zone_nonempty :
    ({true} : Set Bool) ∉ FixV (image (fun _ : Bool => false)) (preimage (fun _ : Bool => false)) := by
  intro h
  have h' : preimage (fun _ : Bool => false) (image (fun _ : Bool => false) ({true} : Set Bool)) = {true} := h
  have h1 : (false : Bool) ∈ preimage (fun _ : Bool => false) (image (fun _ : Bool => false) ({true} : Set Bool)) := by
    simp
  rw [h'] at h1
  simp at h1

/-- 同上，用集合语言写出"闭包把 `{true}` 严格放大"。 -/
theorem closure_strictly_enlarges :
    preimage (fun _ : Bool => false) (image (fun _ : Bool => false) ({true} : Set Bool)) ≠ {true} := by
  intro h
  have h1 : (false : Bool) ∈ preimage (fun _ : Bool => false) (image (fun _ : Bool => false) ({true} : Set Bool)) := by
    simp
  rw [h] at h1
  simp at h1

end TwoFacesBridge
