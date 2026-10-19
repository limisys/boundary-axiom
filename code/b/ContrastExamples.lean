/-
  Copyright 2026 Xueqiang Gao (高学强) · ORCID 0009-0008-3821-3454
  Licensed under the Apache License, Version 2.0 (see LICENSE).
  Original publication source: caseos.cn/research — https://caseos.cn/research/
  First public release 2026-10-09; formal publication 2026-10-20.
  Part of the B-line canonical subset (group 2): 53 files / 417 theorems+lemmas / 77 definitions.
  Attribution header added at publication; proof bodies unchanged.
-/

/-
ContrastExamples.lean —— §5 判据的**具体实例**与一条**实验设计约束**（第 79 轮）

**动机**：第 76 轮把 §5 的对照强化成一条**精确判据**（存在"身体已决而语言未决"的状态）。
但判据仍是**抽象的**：审稿人会问两件事——
（1）它**非空**吗（两种结果都真的能出现）？（2）它**怎么用**（实验该怎么设计）？本轮回答两者，
在**锐度族** $c_{\kappa,\mu,w}$ 上给出**具体例子**与**设计约束**。

**结果**：

  · **`fix_mono_in_ratio`**     刚性面随比值 $w/\kappa$ **单调增大**；
  · **`witness_concrete`**      **具体例子**：$w=1,\ \mu=0$，身体族 $\kappa=2$（比值 $1/2$）、
    语言族 $\kappa=1$（比值 $1$）⇒ $x=\tfrac34$ **是见证**（身体已决、语言未决）；
  · **`same_ratio_no_witness`** **设计约束（本轮实质）**：若两族的**比值相同**，
    则两个闭包**完全相同**、**见证不存在**、对照**落空**。

**所以**：$\S5$ 的实验**必须变的是比值 $w/\kappa$，而不是"锐度 $\kappa$ 本身"**——
否则可能出现"干预强度确实更大，但对照毫无变化"的局面。这条是**机检的**，不靠直觉。

0 `sorry` / 0 `axiom`。
-/
import LanguageStrict
import ScalingsAndUnits
import SharpnessClosure
import LocusVsBoundary

open scoped Real

namespace ContrastExamples

open LanguageStrict

/-- **（单调性）** 注意方向：已决集是 $\{|z-\mu|\ge w/\kappa\}$，
故**比值越大、已决集越小**（推得越远）。所以下式的包含方向是"比值大的**含于**比值小的"。 -/
theorem fix_mono_in_ratio (κ₁ κ₂ μ w₁ w₂ : ℝ) (h₁ : 0 < κ₁) (h₂ : 0 < κ₂) (hw₁ : 0 ≤ w₁)
    (hw₂ : 0 ≤ w₂) (hr : w₁ / κ₁ ≤ w₂ / κ₂) :
    LocusVsBoundary.Fix (SharpnessClosure.c κ₂ μ w₂)
      ⊆ LocusVsBoundary.Fix (SharpnessClosure.c κ₁ μ w₁) := by
  intro z hz
  rw [SharpnessClosure.fix_c κ₂ μ w₂ h₂ hw₂] at hz
  rw [SharpnessClosure.fix_c κ₁ μ w₁ h₁ hw₁]
  rcases hz with hz | hz
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

/-- **（具体见证）** $w=1,\mu=0$：身体族取 $\kappa=2$（比值 $1/2$）、语言族取 $\kappa=1$（比值 $1$），
则 $x=\tfrac34$ **身体已决而语言未决**——**见证确实存在**，判据非空。 -/
theorem witness_concrete :
    Witness (SharpnessClosure.c 2 0 1) (SharpnessClosure.c 1 0 1) := by
  refine ⟨3 / 4, ?_, ?_⟩
  · -- 身体族（κ=2）：`3/4` 不在带 `(-1/2, 1/2)` 内，故不动
    unfold SharpnessClosure.c
    rw [if_neg (by norm_num), if_neg (by norm_num)]
  · -- 语言族（κ=1）：`3/4` 在带 `(-1, 1)` 内，被推到右端点 `1`
    unfold SharpnessClosure.c
    rw [if_neg (by norm_num), if_pos (by norm_num)]
    norm_num

/-- **（设计约束 · 本轮实质）** 若两族的**比值相同**，则两个闭包**相同**，故**不存在见证**——
即对照**落空**。**故实验必须变的是比值，而不是锐度本身。** -/
theorem same_ratio_no_witness {κ₁ κ₂ μ w₁ w₂ : ℝ} (h : w₁ / κ₁ = w₂ / κ₂) :
    ¬ Witness (SharpnessClosure.c κ₁ μ w₁) (SharpnessClosure.c κ₂ μ w₂) := by
  intro hw
  obtain ⟨x, h1, h2⟩ := hw
  have heq : SharpnessClosure.c κ₁ μ w₁ = SharpnessClosure.c κ₂ μ w₂ :=
    ScalingsAndUnits.c_eq_of_div_eq h
  rw [heq] at h1
  exact h2 h1

/-- **（等比值不算两个"族"）** 具体地：$(\\kappa,w)=(1,1)$ 与 $(2,2)$ 给出**同一个**闭包。 -/
theorem same_ratio_trivial_example :
    SharpnessClosure.c 1 0 1 = SharpnessClosure.c 2 0 2 :=
  ScalingsAndUnits.c_eq_of_div_eq (by norm_num)

/-- **（收官）** §5 判据在锐度族上的使用手册：单调性、非空性、以及设计约束三条打包。 -/
theorem sharpness_family_manual :
    (∀ (κ₁ κ₂ μ w₁ w₂ : ℝ), 0 < κ₁ → 0 < κ₂ → 0 ≤ w₁ → 0 ≤ w₂ → w₁ / κ₁ ≤ w₂ / κ₂ →
        LocusVsBoundary.Fix (SharpnessClosure.c κ₂ μ w₂)
          ⊆ LocusVsBoundary.Fix (SharpnessClosure.c κ₁ μ w₁))
    ∧ Witness (SharpnessClosure.c 2 0 1) (SharpnessClosure.c 1 0 1)
    ∧ (∀ (κ₁ κ₂ μ w₁ w₂ : ℝ), w₁ / κ₁ = w₂ / κ₂ →
        ¬ Witness (SharpnessClosure.c κ₁ μ w₁) (SharpnessClosure.c κ₂ μ w₂)) :=
  ⟨fun κ₁ κ₂ μ w₁ w₂ h₁ h₂ hw₁ hw₂ hr => fix_mono_in_ratio κ₁ κ₂ μ w₁ w₂ h₁ h₂ hw₁ hw₂ hr,
   witness_concrete,
   fun _ _ _ _ _ h => same_ratio_no_witness h⟩

end ContrastExamples
