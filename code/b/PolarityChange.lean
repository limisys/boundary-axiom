/-
  Copyright 2026 Xueqiang Gao (高学强) · ORCID 0009-0008-3821-3454
  Licensed under the Apache License, Version 2.0 (see LICENSE).
  Original publication source: caseos.cn/research — https://caseos.cn/research/
  First public release 2026-10-09; formal publication 2026-10-20.
  Part of the B-line canonical subset (group 2): 53 files / 417 theorems+lemmas / 77 definitions.
  Attribution header added at publication; proof bodies unchanged.
-/

/-
PolarityChange.lean —— 第 40 轮**推论 C**（「组装＝极性变更」）的机检，及一处**身份识别**（第 80 轮）

**动机**：第 40 轮推进件 §四 推论 C 写：

> $\\sigma_{\\text{mech}}>\\sigma^\\ast$ 时，多出来的压差**不能**表示成更高的凝聚（推论 B），
> 只能表示为**换了一个闭包算子**（新的 $c'$、新的极性）。

其 §六 还给出**判别方式**：

> **存在一个干预使旧 $c$ 下 $c(x)\\neq x$、而在新 $c'$ 下成为不动点**。

第 40 轮把它标为 P1（仅"已精确验证"）。**本条把它做成机检**，并顺带发现一件值得记的事：

  **推论 C 的判别方式与 §5 的对照判据是「同一个形式对象」**——
  两者都是 `Witness`（"被一族判定已决、被另一族不判定"），只是方向相反。
  即：**纲领最难的两条面向经验的断言，共享同一个形式内核**。

**结果**：

  · **`sigmaCoh_le_one`**     凝聚度**有上界 1**（任何分布）；
  · **`sigmaMech_unbounded`** 机械压差**无界**（$M$ 再大也有 $\\kappa$ 使 $\\sigma_{\\text{mech}}>M$）；
  · **`assembly_not_more_cohesion`（推论 C 前半）** 二者并置：**凝聚有界而压差无界**，
    故"组装"**不能**被表示成"更高的凝聚"；
  · **`saturated_example`**   具体：模糊带无质量的分布使 $\\sigma_{\\text{coh}}\\equiv1$，
    而 $\\sigma_{\\text{mech}}$ 严格增长 ⇒ **存在两个压差不同、凝聚相同的状态**；
  · **`polarity_change_iff`（推论 C 后半 · 判别方式）** 极性变更的见证
    $\\iff$ 刚性面**严格增大**；
  · **`one_predicate`（身份识别）** 推论 C 的判别方式与 §5 的对照判据**是同一个 `Witness`**。

**范围声明**：本件机检的是推论 C 的**判别方式**与**前半**（"多余压差不能表示成更高凝聚"）。
"**多极性被逼出**"在本件里被形式化为"**同一极性内凝聚力有界、无法表达多余压差**"，
**不是**"极性的个数会增加"——后者**本件不主张**。

0 `sorry` / 0 `axiom`。
-/
import LanguageStrict
import LocusVsBoundary
import BoundaryTheory_sigmaCoh
import ValueLayerExtension

open scoped Real

namespace PolarityChange

open LanguageStrict

/-! ## 一 · 推论 C 前半：凝聚**有界**而压差**无界** -/

/-- **（凝聚有界）** $\\sigma_{\\text{coh}}\\le 1$：任何分布的凝聚度都不超过 1。 -/
theorem sigmaCoh_le_one (F : ℝ → ℝ) (hF : ∀ t, 0 ≤ F t) (L κ : ℝ) :
    BoundaryTheory.sigmaCoh F L κ ≤ 1 := by
  unfold BoundaryTheory.sigmaCoh
  linarith [hF (L / κ)]

/-- **（压差无界）** 对任意 $M$ 都存在 $\\kappa>0$ 使 $\\sigma_{\\text{mech}}>M$。 -/
theorem sigmaMech_unbounded (c₀ C₀ : ℝ) (hc₀ : 0 < c₀) (hC₀ : 0 < C₀) :
    ∀ M : ℝ, ∃ κ : ℝ, 0 < κ ∧ M < ValueLayerExtension.sigma c₀ C₀ κ := by
  intro M
  by_cases hM : M ≤ 0
  · refine ⟨1, one_pos, ?_⟩
    unfold ValueLayerExtension.sigma
    have : 0 < c₀ / C₀ := div_pos hc₀ hC₀
    nlinarith
  · rw [not_le] at hM
    have hpos : 0 < M * C₀ / c₀ := div_pos (mul_pos hM hC₀) hc₀
    refine ⟨Real.sqrt (M * C₀ / c₀) + 1, by positivity, ?_⟩
    unfold ValueLayerExtension.sigma
    have hstrict : M * C₀ / c₀ < (Real.sqrt (M * C₀ / c₀) + 1) ^ 2 := by
      have h := Real.sq_sqrt hpos.le
      nlinarith [h, Real.sqrt_nonneg (M * C₀ / c₀)]
    have h1 : (c₀ / C₀) * (M * C₀ / c₀) = M := by field_simp
    have h2 : (c₀ / C₀) * (M * C₀ / c₀) < (c₀ / C₀) * (Real.sqrt (M * C₀ / c₀) + 1) ^ 2 :=
      mul_lt_mul_of_pos_left hstrict (div_pos hc₀ hC₀)
    linarith [h2, h1]

/-- **（推论 C 前半 · 机检）** 凝聚**有上界 1**而压差**无界**——
故"组装"（$\\sigma_{\\text{mech}}>\\sigma^\\ast$）**不能**被表示成"更高的凝聚"。 -/
theorem assembly_not_more_cohesion (F : ℝ → ℝ) (hF : ∀ t, 0 ≤ F t) (L : ℝ)
    (c₀ C₀ : ℝ) (hc₀ : 0 < c₀) (hC₀ : 0 < C₀) :
    (∀ κ, BoundaryTheory.sigmaCoh F L κ ≤ 1)
      ∧ (∀ M : ℝ, ∃ κ : ℝ, 0 < κ ∧ M < ValueLayerExtension.sigma c₀ C₀ κ) :=
  ⟨fun κ => sigmaCoh_le_one F hF L κ, sigmaMech_unbounded c₀ C₀ hc₀ hC₀⟩

/-- **（具体例）** 取**模糊带无质量**的分布（$F\\equiv0$）：
凝聚**恒为 1**，而压差随 $\\kappa$ **严格增长**——
于是**两个压差不同而凝聚相同**的状态确实存在。 -/
theorem saturated_example :
    ∃ (κ₁ κ₂ : ℝ), 0 < κ₁ ∧ κ₁ < κ₂
      ∧ ValueLayerExtension.sigma 1 1 κ₁ < ValueLayerExtension.sigma 1 1 κ₂
      ∧ BoundaryTheory.sigmaCoh (fun _ => 0) 1 κ₁
          = BoundaryTheory.sigmaCoh (fun _ => 0) 1 κ₂ := by
  refine ⟨1, 2, one_pos, by norm_num, ?_, ?_⟩
  · unfold ValueLayerExtension.sigma; norm_num
  · unfold BoundaryTheory.sigmaCoh; norm_num

/-! ## 二 · 推论 C 后半：极性变更的**判别方式** -/

/-- **（判别方式）** 若新极性 $c'$ 比旧极性 $c$ 判得**更多**（逐点 $c'\\le c$），
则"**存在一个状态在旧 $c$ 下未决、而在新 $c'$ 下已决**" $\\iff$ **刚性面严格增大**。
这正是第 40 轮 §六 给出的判别方式。 -/
theorem polarity_change_iff {α : Type*} [PartialOrder α] {c c' : ClosureOperator α}
    (h : ∀ x, c' x ≤ c x) :
    Witness c' c ↔ LocusVsBoundary.Fix c ⊂ LocusVsBoundary.Fix c' :=
  (rigid_ssubset_iff c' c h).symm

/-- **（身份识别 · 本轮附带发现）** 同一对 $c'\\le c$ 上，
**推论 C 的判别方式**（旧未决 → 新已决）与**§5 的对照判据**（身体已决 → 语言未决）
**是同一个 `Witness`，只是方向相反**。
即：纲领最难的两条面向经验的断言，**共享同一个形式内核**。 -/
theorem one_predicate {α : Type*} [PartialOrder α] {c c' : ClosureOperator α}
    (h : ∀ x, c' x ≤ c x) (h' : ∀ x, c x ≤ c' x) :
    (Witness c' c ↔ LocusVsBoundary.Fix c ⊂ LocusVsBoundary.Fix c')
      ∧ (Witness c c' ↔ LocusVsBoundary.Fix c' ⊂ LocusVsBoundary.Fix c) :=
  ⟨polarity_change_iff h, (rigid_ssubset_iff c c' h').symm⟩

/-- **（收官）** 推论 C 的可机检部分打包：前半（有界 vs 无界）＋ 后半（判别方式）。 -/
theorem corollary_C_machine_checked (F : ℝ → ℝ) (hF : ∀ t, 0 ≤ F t) (L : ℝ)
    (c₀ C₀ : ℝ) (hc₀ : 0 < c₀) (hC₀ : 0 < C₀) :
    ((∀ κ, BoundaryTheory.sigmaCoh F L κ ≤ 1)
        ∧ (∀ M : ℝ, ∃ κ : ℝ, 0 < κ ∧ M < ValueLayerExtension.sigma c₀ C₀ κ))
      ∧ (∀ {α : Type*} [PartialOrder α] (c c' : ClosureOperator α), (∀ x, c' x ≤ c x) →
          (Witness c' c ↔ LocusVsBoundary.Fix c ⊂ LocusVsBoundary.Fix c')) :=
  ⟨assembly_not_more_cohesion F hF L c₀ C₀ hc₀ hC₀,
   fun _ _ h => polarity_change_iff h⟩

end PolarityChange
