/-
  Copyright 2026 Xueqiang Gao (高学强) · ORCID 0009-0008-3821-3454
  Licensed under the Apache License, Version 2.0 (see LICENSE).
  Original publication source: caseos.cn/research — https://caseos.cn/research/
  First public release 2026-10-09; formal publication 2026-10-20.
  Part of the B-line canonical subset (group 2): 53 files / 417 theorems+lemmas / 77 definitions.
  Attribution header added at publication; proof bodies unchanged.
-/

/-
ReadoutDynamics.lean —— **S2 链的闭合：沿维持轨迹，系统自身的读出被夹到 $\\theta^\\star$**（第 118 轮）

**背景**：第 115 轮给了**追踪读出**（$\\mathrm{readout}(\\kappa,\\mu,w)=\\theta(w)$，$\\theta(w)=2/(1+e^{w})$）；
第 117 轮给了**维持动力学**（松弛 $w\\mapsto\\frac{w+1/w}{2}$，误差每步减半，恢复时间有限）。
本件把两者**接起来**，得到 S2 想说的那句话的可证形式：

> **沿系统的维持轨迹，系统自身的读出 $\\theta(w_n)$ 被夹在任意给定的水平之下与 $\\theta^\\star$ 之间，
> 且对任何严格低于 $\\theta^\\star$ 的水平，有限步后即超过它。**

**结果（机检）**：
  · `thetaOf_lt_thetaOf`／`thetaOf_le_thetaOf`：$\\theta$ **严格（弱）单调下降**；
  · `L_lt_L`：$L$ 在 $(0,1)$ 上**严格单调下降**（搬运用的单调性）；
  · `level_squeeze`：$w\\ge1\\Rightarrow\\theta(w_n)\\le\\theta(1)=\\theta^\\star$ —— **上夹**；
  · `level_climbs`：$\\forall\\theta'<\\theta^\\star$，**存在有限 $N$**，$n\\ge N$ 后 $\\theta(w_n)>\\theta'$ —— **下推**；
  · `readout_tracks_along`：轨迹上**读出值＝水平值**（把 115 轮的闭式接到 117 轮的轨迹上）；
  · `s2_readout_certificate`：以上打包。

**⚠ 与 S1（类 $\\mathcal R$）的关系（重要）**：本件实现的读出**破缺 K2**（它是 $w$ 的非常数函数），
这与第 116 轮的定理（**能挑出水平的原则必破缺规范**）**一致**。
⇒ **若采纳 S1 的 K2 门槛（甲案），则"系统自身实现的读出"不可能属于类 $\\mathcal R$**；
即 **P5 的原读法（"R 是系统自身读出且属该内禀类"）在形式上是不可满足的**。

0 `sorry` / `0 axiom`。
-/
import LevelDynamics
import LevelReadout

open scoped Real

namespace ReadoutDynamics

open LevelDynamics LevelReadout LogisticCore
open ReadoutExistence (thetaOf L_thetaOf thetaOf_L thetaOf_mem)

/-- **（水平函数严格下降）** $a<b\\Rightarrow\\theta(b)<\\theta(a)$。 -/
theorem thetaOf_lt_thetaOf {a b : ℝ} (h : a < b) : thetaOf b < thetaOf a := by
  unfold thetaOf
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have := Real.exp_lt_exp.mpr h
  linarith

/-- **（水平函数弱下降）**。 -/
theorem thetaOf_le_thetaOf {a b : ℝ} (h : a ≤ b) : thetaOf b ≤ thetaOf a := by
  rcases lt_or_eq_of_le h with h' | h'
  · exact le_of_lt (thetaOf_lt_thetaOf h')
  · rw [h']

/-- **（$L$ 在 $(0,1)$ 上严格下降）** $0<\\theta_1<\\theta_2<1\\Rightarrow L\\theta_2<L\\theta_1$。 -/
theorem L_lt_L {θ₁ θ₂ : ℝ} (h1 : 0 < θ₁) (h2 : θ₂ < 1) (h : θ₁ < θ₂) :
    L θ₂ < L θ₁ := by
  have h2pos : 0 < θ₂ := lt_trans h1 h
  unfold L
  apply Real.log_lt_log
  · exact div_pos (by linarith) h2pos
  · rw [div_lt_div_iff₀ h2pos h1]
    linarith

/-- **（上夹）** $w\\ge1\\Rightarrow\\theta(w_n)\\le\\theta^\\star=\\theta(1)$。 -/
theorem level_squeeze (w : ℝ) (hw : 1 ≤ w) (n : ℕ) :
    thetaOf ((relax^[n]) w) ≤ thetaOf 1 :=
  thetaOf_le_thetaOf (one_le_iterate w hw n)

/-- **（下推）** 任何严格低于 $\\theta^\\star$ 的水平，**有限步后即被超过**。 -/
theorem level_climbs (w : ℝ) (hw : 1 < w) (θ' : ℝ) (h0 : 0 < θ') (h1 : θ' < 1)
    (hlt : θ' < thetaOf 1) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → θ' < thetaOf ((relax^[n]) w) := by
  have hm : thetaOf 1 ∈ Set.Ioo (0 : ℝ) 1 := thetaOf_mem one_pos
  have hLθ' : 1 < L θ' := by
    have := L_lt_L h0 hm.2 hlt
    rwa [L_thetaOf 1] at this
  obtain ⟨N, hN⟩ := recovery_time w hw (L θ' - 1) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  have hlt' : (relax^[n]) w < L θ' := by
    have := hN n hn
    linarith
  calc θ' = thetaOf (L θ') := (thetaOf_L h0 h1).symm
    _ < thetaOf ((relax^[n]) w) := thetaOf_lt_thetaOf hlt'

/-- **（轨迹上的读出＝水平）** 把 115 轮的闭式接到 117 轮的轨迹上。 -/
theorem readout_tracks_along (κ μ w : ℝ) (hκ : 0 < κ) (hw : 1 ≤ w) (n : ℕ) :
    readout κ μ ((relax^[n]) w) = thetaOf ((relax^[n]) w) := by
  have hpos : 0 ≤ (relax^[n]) w := le_trans (by norm_num) (one_le_iterate w hw n)
  exact readout_eq_thetaOf κ μ _ hκ hpos

/-- **（S2 证书）** 读出＝水平（沿轨迹） · 上夹于 $\\theta^\\star$ · 任意低于 $\\theta^\\star$ 的水平有限步被超过。 -/
theorem s2_readout_certificate (κ μ w : ℝ) (hκ : 0 < κ) (hw : 1 < w) :
    (∀ n : ℕ, readout κ μ ((relax^[n]) w) = thetaOf ((relax^[n]) w)) ∧
      (∀ n : ℕ, thetaOf ((relax^[n]) w) ≤ thetaOf 1) ∧
      (∀ θ' : ℝ, 0 < θ' → θ' < 1 → θ' < thetaOf 1 →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → θ' < readout κ μ ((relax^[n]) w)) := by
  refine ⟨fun n => readout_tracks_along κ μ w hκ (le_of_lt hw) n,
    fun n => level_squeeze w (le_of_lt hw) n, ?_⟩
  intro θ' h0 h1 hlt
  obtain ⟨N, hN⟩ := level_climbs w hw θ' h0 h1 hlt
  exact ⟨N, fun n hn => by
    rw [readout_tracks_along κ μ w hκ (le_of_lt hw) n]
    exact hN n hn⟩

end ReadoutDynamics
