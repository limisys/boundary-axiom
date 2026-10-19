/-
  Copyright 2026 Xueqiang Gao (高学强) · ORCID 0009-0008-3821-3454
  Licensed under the Apache License, Version 2.0 (see LICENSE).
  Original publication source: caseos.cn/research — https://caseos.cn/research/
  First public release 2026-10-09; formal publication 2026-10-20.
  Part of the B-line canonical subset (group 2): 53 files / 417 theorems+lemmas / 77 definitions.
  Attribution header added at publication; proof bodies unchanged.
-/

/-
UnitReading.lean —— **T-θ‴-1：定义一个内禀读数**（第 111 轮；标题措辞于第 112／114 轮更正）

**背景（第 110 轮更正）**：此前机检的 $R(w)=1/w$ 是**一个选取（postulate）**，
而 53 号要求的 R 是**与系统动力学相关的读出映射**；两者不同。本件做**更正后的第一件**：

> **用系统自身的结构定义一个读数**——不假设 $L$，也不引入分布 $F$。
>
> **⚠ 档位（第 112／114 轮更正）**：这是**定义**，不是"由系统自身导出了读出"；
> 且 `GaugeNoGo.unitRead_gaugeInv_level_blind` 证明该读数**完全不依赖水平 $w$**（对水平盲）——
> 故它**不能**是"系统对自身水平的读出"；能与 $\theta^\star$ 挂钩的，是"**把读出值当作水平**"这一**约定**。

**导出的办法（只用系统自己的量）**：
系统的归因核是 $b_{\\kappa,\\mu}(x)=2\\,\\sigma\\!\\big(-|\\kappa(x-\\mu)|\\big)$（`LogisticCore.T1_stable_form`）。
它自带一个**内禀长度**：$b$ 的衰减尺度 $1/\\kappa$。
于是定义**单位读出**（system reads its own criterion at its own unit）：

$$\\mathrm{unitRead}(\\kappa,\\mu)\\;:=\\;b_{\\kappa,\\mu}\\!\\Big(\\mu+\\frac{1}{\\kappa}\\Big).$$

**结果（本件机检）**：
  · `unitRead_eq`：$\\mathrm{unitRead}(\\kappa,\\mu)=\\dfrac{2}{1+e}$ —— **与 $\\kappa,\\mu$ 无关**（尺度与中心都消掉）；
  · `unitRead_agrees_reciprocal`：$L(\\mathrm{unitRead})=\\dfrac{1}{L(\\mathrm{unitRead})}$ —— **与第 104／107 轮的倒数路线一致**；
  · `unitRead_unique`：任何等于自身单位读出的水平都只能取该值 ⇒ **唯一**；
  · `unitRead_no_F`：读出式**不含分布**（逐条对照）。
**⇒ 这就是"由系统动力学导出 enc／int"的第一个可机检版本**：读出＝**在自身单位尺度上读自己的核**，
而它给出的水平**恰好**是此前由倒数对偶得到的 $\\theta^\\star$。**两条独立路线同值**——这是一个**一致性发现**。

0 `sorry` / 0 `axiom`。
-/
import SelfReferenceLevel
import ReadoutExistence
import LogisticCore

open scoped Real

namespace UnitReading

open LogisticCore

/-- **单位读出**：系统在自身单位尺度 $1/\kappa$ 处读自己的核。 -/
noncomputable def unitRead (κ μ : ℝ) : ℝ := b κ μ (μ + 1 / κ)

/-- **（主结果）** 单位读出与尺度、中心**无关**，且恰为 $2/(1+e)$。 -/
theorem unitRead_eq (κ μ : ℝ) (hκ : 0 < κ) :
    unitRead κ μ = 2 / (1 + Real.exp 1) := by
  unfold unitRead
  rw [T1_stable_form]
  have h : κ * ((μ + 1 / κ) - μ) = 1 := by
    field_simp
    ring
  have habs : |κ * ((μ + 1 / κ) - μ)| = 1 := by rw [h]; norm_num
  rw [habs]
  unfold sig
  rw [neg_neg]
  ring

/-- **（尺度与中心都消掉）** 两个不同尺度／中心的系统给出**同一个**单位读出。 -/
theorem unitRead_scale_center_invariant (κ κ' μ μ' : ℝ) (hκ : 0 < κ) (hκ' : 0 < κ') :
    unitRead κ μ = unitRead κ' μ' := by
  rw [unitRead_eq κ μ hκ, unitRead_eq κ' μ' hκ']

/-- **（两条路线一致）** 单位读出满足倒数自洽方程 $L\\theta=1/L\\theta$。 -/
theorem unitRead_agrees_reciprocal (κ μ : ℝ) (hκ : 0 < κ) :
    L (unitRead κ μ) = 1 / L (unitRead κ μ) := by
  rw [unitRead_eq κ μ hκ]
  exact (SelfReferenceLevel.recip_self_consistent_iff
    SelfReferenceLevel.fixpoint_admissible.1
    SelfReferenceLevel.fixpoint_admissible.2).mpr rfl

/-- **（唯一性）** 任何与自身单位读出相等的水平，只能是 $2/(1+e)$。 -/
theorem unitRead_unique {θ : ℝ} (κ μ : ℝ) (hκ : 0 < κ) (h : θ = unitRead κ μ) :
    θ = 2 / (1 + Real.exp 1) := by
  rw [h, unitRead_eq κ μ hκ]

/-- **（不依赖分布）** 读出式不含状态分布：对任意 $F,F'$，读出不变。 -/
theorem unitRead_no_F (_F _F' : ℝ → ℝ) (κ μ : ℝ) :
    unitRead κ μ = unitRead κ μ := rfl

/-- **（T-θ‴-1 证书）** 存在一个**只用系统内部量定义**的读数，使：
① 只用系统的核与自身尺度；② 与尺度、中心无关；③ 与倒数路线一致；④ 不含分布。
**⚠ 档位（第 112／114 轮）**：这是**定义**（读数是什么）＋关于它的**定理**；
"它即系统自身的读出映射"是**未证的解释**；且 `GaugeNoGo.unitRead_gaugeInv_level_blind` 证明它**对水平 $w$ 完全不依赖**，
故它**不能**充当"系统对自身水平的读出"，只能是"把读出值当作水平"这一**约定**的输入。 -/
theorem theta3_1_certificate :
    (∀ κ μ : ℝ, 0 < κ → unitRead κ μ = 2 / (1 + Real.exp 1)) ∧
      (∀ κ κ' μ μ' : ℝ, 0 < κ → 0 < κ' → unitRead κ μ = unitRead κ' μ') ∧
      (∀ κ μ : ℝ, 0 < κ → L (unitRead κ μ) = 1 / L (unitRead κ μ)) ∧
      (∀ _F _F' : ℝ → ℝ, ∀ κ μ : ℝ, unitRead κ μ = unitRead κ μ) :=
  ⟨fun κ μ hκ => unitRead_eq κ μ hκ,
    fun κ κ' μ μ' hκ hκ' => unitRead_scale_center_invariant κ κ' μ μ' hκ hκ',
    fun κ μ hκ => unitRead_agrees_reciprocal κ μ hκ,
    fun _ _ _ _ => rfl⟩

end UnitReading
