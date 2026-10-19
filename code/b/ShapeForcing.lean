/-
  Copyright 2026 Xueqiang Gao (高学强) · ORCID 0009-0008-3821-3454
  Licensed under the Apache License, Version 2.0 (see LICENSE).
  Original publication source: caseos.cn/research — https://caseos.cn/research/
  First public release 2026-10-09; formal publication 2026-10-20.
  Part of the B-line canonical subset (group 2): 53 files / 417 theorems+lemmas / 77 definitions.
  Attribution header added at publication; proof bodies unchanged.
-/

/-
ShapeForcing.lean —— **"为何是几何"的一半答案：两条对称性迫使几何**（第 135 轮）

**令源**：诚实清单里"**为何几何收缩**"一直标着"**无独立理由**"。本件给出**一半的答案**：

> 若衰减满足两条**可检验的对称性**——
> **（S1）比例性**：同一对时刻上的**偏差比与初始偏差无关**；
> **（S2）半群性**：等两倍时间 ＝ 把衰减作用两遍（$\\rho(s+t)=\\rho(s)\\rho(t)$）——
> **那么偏差必然写成"初值 × 形状函数"，且形状在整数步上必然是几何的：$d_n=d_0\\cdot\\rho(1)^n$。**
> 特别地，$\\rho(1)=1/2$ 时**每步减半**（第 117／129 轮的定律）**由这两条对称性推出**，而不是被假定。

**结果（机检）**：
  · `proportional_decay`：**（S1）⇒ 偏差＝初值×形状函数**（形状与初值无关）；
  · `rho_zero`／`geometric_on_nat`：**（S2）⇒ 形状在整数步上是几何的**（$\\rho(n)=\\rho(1)^n$）；
  · `halving_law`：$\\rho(1)=1/2$ 时 **$d_n=d_0/2^{n}$** ⇒ 第 117／129 轮的"每步减半"被**推出**；
  · `shape_certificate`：打包。

**⚠ 仍未证（如实标注）**：为什么 **(S1)/(S2)** 成立——它们**是可检验的对称性**（S1 即第 130 轮的无量纲比值检验），
但**本件不证明**自然界满足它们；连续时间上"$\\rho$ 连续且半群 ⇒ 指数"**亦未形式化**（本件只做整数步）。

0 `sorry` / `0 axiom`。
-/
import Mathlib

open scoped Real

namespace ShapeForcing

/-- **（S1 ⇒ 比例性）** 若"同一对时刻上的偏差比与初始偏差无关"，
则偏差＝**初值 × 与初值无关的形状函数**。 -/
theorem proportional_decay (d : ℝ → ℝ → ℝ)
    (hpos : ∀ w t : ℝ, 1 < w → 0 ≤ t → 0 < d w t)
    (hratio : ∀ w w' t₁ t₂ : ℝ, 1 < w → 1 < w' → 0 ≤ t₁ → 0 ≤ t₂ →
      d w t₁ / d w t₂ = d w' t₁ / d w' t₂) :
    ∃ ρ : ℝ → ℝ, ρ 0 = 1 ∧
      ∀ w t : ℝ, 1 < w → 0 ≤ t → d w t = d w 0 * ρ t := by
  refine ⟨fun t => d 2 t / d 2 0, ?_, ?_⟩
  · have h : 0 < d 2 0 := hpos 2 0 (by norm_num) (le_refl 0)
    field_simp
  · intro w t hw ht
    have h0 : 0 < d w 0 := hpos w 0 hw (le_refl 0)
    have h20 : 0 < d 2 0 := hpos 2 0 (by norm_num) (le_refl 0)
    have hr := hratio w 2 t 0 hw (by norm_num) ht (le_refl 0)
    -- hr : d w t / d w 0 = d 2 t / d 2 0
    have h := (div_eq_iff h0.ne').mp hr
    rw [mul_comm] at h
    exact h

/-- **（半群 ⇒ 单位元）** $\\rho(0)=1$（由 $\\rho(0)=\\rho(0)^2$ 与正值性）。 -/
theorem rho_zero {ρ : ℝ → ℝ} (hmul : ∀ s t : ℝ, ρ (s + t) = ρ s * ρ t)
    (hpos0 : ρ 0 ≠ 0) : ρ 0 = 1 := by
  have h : ρ 0 = ρ 0 * ρ 0 := by simpa using hmul 0 0
  have h2 : ρ 0 * (ρ 0 - 1) = 0 := by linarith
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 hpos0
  · linarith

/-- **（（S2）⇒ 整数步上几何）** $\\rho(n)=\\rho(1)^{n}$。 -/
theorem geometric_on_nat {ρ : ℝ → ℝ} (hmul : ∀ s t : ℝ, ρ (s + t) = ρ s * ρ t)
    (h0 : ρ 0 = 1) : ∀ n : ℕ, ρ (n : ℝ) = ρ 1 ^ n := by
  intro n
  induction n with
  | zero => simpa using h0
  | succ k ih =>
      have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      rw [hcast, hmul, ih, pow_succ]

/-- **（每步减半由对称性推出）** $\\rho(1)=1/2\\Rightarrow d_n=d_0/2^{n}$。 -/
theorem halving_law (d : ℝ → ℝ → ℝ)
    (hpos : ∀ w t : ℝ, 1 < w → 0 ≤ t → 0 < d w t)
    (hratio : ∀ w w' t₁ t₂ : ℝ, 1 < w → 1 < w' → 0 ≤ t₁ → 0 ≤ t₂ →
      d w t₁ / d w t₂ = d w' t₁ / d w' t₂)
    (ρ : ℝ → ℝ) (hρ0 : ρ 0 = 1)
    (hprop : ∀ w t : ℝ, 1 < w → 0 ≤ t → d w t = d w 0 * ρ t)
    (hmul : ∀ s t : ℝ, ρ (s + t) = ρ s * ρ t)
    (hhalf : ρ 1 = 1 / 2) :
    ∀ w : ℝ, 1 < w → ∀ n : ℕ, d w (n : ℝ) = d w 0 / 2 ^ n := by
  intro w hw n
  rw [hprop w (n : ℝ) hw (Nat.cast_nonneg n), geometric_on_nat hmul hρ0 n, hhalf]
  have hpow : (1 / 2 : ℝ) ^ n = 1 / 2 ^ n := by
    rw [div_pow]
    norm_num
  rw [hpow]
  ring

/-- **（形状证书）** （S1）⇒ 比例性 · （S2）⇒ 整数步几何 · **每步减半由两条对称性推出**。 -/
theorem shape_certificate :
    (∀ d : ℝ → ℝ → ℝ,
        (∀ w t : ℝ, 1 < w → 0 ≤ t → 0 < d w t) →
        (∀ w w' t₁ t₂ : ℝ, 1 < w → 1 < w' → 0 ≤ t₁ → 0 ≤ t₂ →
          d w t₁ / d w t₂ = d w' t₁ / d w' t₂) →
        ∃ ρ : ℝ → ℝ, ρ 0 = 1 ∧ ∀ w t : ℝ, 1 < w → 0 ≤ t → d w t = d w 0 * ρ t) ∧
      (∀ ρ : ℝ → ℝ, (∀ s t : ℝ, ρ (s + t) = ρ s * ρ t) → ρ 0 = 1 →
        ∀ n : ℕ, ρ (n : ℝ) = ρ 1 ^ n) :=
  ⟨fun d hpos hratio => proportional_decay d hpos hratio,
    fun ρ hmul h0 n => geometric_on_nat hmul h0 n⟩

end ShapeForcing
