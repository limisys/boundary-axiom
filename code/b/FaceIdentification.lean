/-
  Copyright 2026 Xueqiang Gao (高学强) · ORCID 0009-0008-3821-3454
  Licensed under the Apache License, Version 2.0 (see LICENSE).
  Original publication source: caseos.cn/research — https://caseos.cn/research/
  First public release 2026-10-09; formal publication 2026-10-20.
  Part of the B-line canonical subset (group 2): 53 files / 417 theorems+lemmas / 77 definitions.
  Attribution header added at publication; proof bodies unchanged.
-/

/-
FaceIdentification.lean —— **T-θ‴-4：F 的升级问题有了定理级答案**（第 120 轮）

**背景**：T-θ‴ 的第四件一直是「**据此升级 $F$**」（F＝"边界 ≅ 判据"的同构；此前记为**规范依赖同构**，一直没做）。
第 116 轮证明"**能挑出水平的原则必破缺规范**"，第 118 轮证了"**系统实现的读数破缺 K2**"。
本件把这两条用到 $F$ 本身上，得到：

> **不存在"规范不变"的边界—判据识别；能用的识别是唯一的，且它必然规范依赖。**

**结果（机检）**：
  · `Identifies g`：$g$ 是识别（$\mathrm{Fix}(c_{\kappa,\mu,w})=\{x: b_{\kappa,\mu}(x)\le g\,\kappa\,w\}$）；
  · `b_center_eq_one`：核在中心取 $1$；`threshold_set_unique`：**阈值集合唯一决定阈值**
    （用端点 $\mu+L\theta/\kappa$ 上核值恰为 $\theta$，`LogisticCore.T2_endpoint`）；
  · `identified_on_levels`：**任何识别在水平上必取 $g\,\kappa\,(L\theta)=\theta$**（唯一性）；
  · `canonical_identifies`：**典范识别 $g_0(\kappa,w)=\theta(w)$ 确实成立**（即 $F$ 在形式上**存在**）；
  · `no_gaugeInv_identification`（**主结果**）：**不存在规范不变的识别** ——
    $F$ 的"规范依赖"**不是工夫不够，而是定理级的必然**。

**⇒ T-θ‴ 四件的状态**：①定义内禀读数（已做）②规范作用形式化（已做）③"内禀"判据形式化（已做）④**升级 $F$：本件给出答案——不可能升级为规范不变的同构**。

0 `sorry` / `0 axiom`。
-/
import SharpnessClosure
import ReadoutDynamics

open scoped Real

namespace FaceIdentification

open ClosureGauge SharpnessClosure LocusVsBoundary LogisticCore
open ReadoutExistence (thetaOf L_thetaOf thetaOf_mem)

/-- **识别**：把**边界面**（不动点集）与**判据面**（已决集，阈值为 $g\,\kappa\,w$）对应起来的水平指派。 -/
def Identifies (g : ℝ → ℝ → ℝ) : Prop :=
  ∀ κ μ w : ℝ, 0 < κ → 0 ≤ w → Fix (c κ μ w) = {x : ℝ | b κ μ x ≤ g κ w}

/-- **（核在中心取 1）** $b_{\kappa,\mu}(\mu)=1$。 -/
theorem b_center_eq_one (κ μ : ℝ) : b κ μ μ = 1 := by
  rw [T1_stable_form]
  have h : κ * (μ - μ) = 0 := by ring
  rw [h, abs_zero, neg_zero]
  unfold sig
  norm_num

/-- **（阈值集合唯一决定阈值）** 若两个阈值给出同一个已决集，则阈值相等。 -/
theorem threshold_set_unique (κ μ a c : ℝ) (hκ : 0 < κ) (ha0 : 0 < a) (ha1 : a < 1)
    (h : {x : ℝ | b κ μ x ≤ a} = {x : ℝ | b κ μ x ≤ c}) : c = a := by
  have hxa : b κ μ (μ + L a / κ) = a := T2_endpoint κ μ a hκ ha0 ha1
  have ha_mem : μ + L a / κ ∈ {x : ℝ | b κ μ x ≤ c} := by
    rw [← h]
    exact le_of_eq hxa
  have hac : a ≤ c := by
    have hm := ha_mem
    rw [Set.mem_ofPred_eq, hxa] at hm
    exact hm
  rcases lt_or_ge c 1 with hc1 | hc1
  · have hc0 : 0 < c := by
      by_contra hcon
      simp only [not_lt] at hcon
      have := hac
      linarith
    have hxc : b κ μ (μ + L c / κ) = c := T2_endpoint κ μ c hκ hc0 hc1
    have hc_mem : μ + L c / κ ∈ {x : ℝ | b κ μ x ≤ a} := by
      rw [h]
      exact le_of_eq hxc
    have hca : c ≤ a := by
      have hm := hc_mem
      rw [Set.mem_ofPred_eq, hxc] at hm
      exact hm
    linarith
  · have hcenter : b κ μ μ = 1 := b_center_eq_one κ μ
    have hmem : μ ∈ {x : ℝ | b κ μ x ≤ c} := by
      rw [Set.mem_ofPred_eq, hcenter]
      linarith
    have hmem' : μ ∈ {x : ℝ | b κ μ x ≤ a} := by
      rw [h]
      exact hmem
    rw [Set.mem_ofPred_eq] at hmem'
    linarith

/-- **（唯一性）** 任何识别在**水平**上必取 $g\,\kappa\,(L\theta)=\theta$。 -/
theorem identified_on_levels (g : ℝ → ℝ → ℝ) (hg : Identifies g)
    (κ : ℝ) (hκ : 0 < κ) (θ : ℝ) (h0 : 0 < θ) (h1 : θ < 1) :
    g κ (L θ) = θ := by
  have hL : 0 ≤ L θ := (L_pos h0 h1).le
  have h1' := hg κ 0 (L θ) hκ hL
  have h2 := fix_c_eq_decided κ 0 θ hκ h0 h1
  have hset : {x : ℝ | b κ 0 x ≤ g κ (L θ)} = {x : ℝ | b κ 0 x ≤ θ} := by
    rw [← h1', h2]
  exact threshold_set_unique κ 0 θ (g κ (L θ)) hκ h0 h1 hset.symm

/-- **（存在性）** 典范识别 $g_0(\kappa,w)=\theta(w)$ **确实成立**（$w>0$）。 -/
theorem canonical_identifies (κ μ w : ℝ) (hκ : 0 < κ) (hw : 0 < w) :
    Fix (c κ μ w) = {x : ℝ | b κ μ x ≤ thetaOf w} := by
  have hw0 : 0 ≤ w := le_of_lt hw
  have hθ : thetaOf w ∈ Set.Ioo (0 : ℝ) 1 := thetaOf_mem hw
  rw [fix_c κ μ w hκ hw0]
  ext x
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, tail_iff κ μ w x hκ hw0,
    T6_complement κ μ x (thetaOf w) hκ hθ.1 hθ.2, L_thetaOf w]

/-- **（主结果 · T-θ‴-4）** **不存在规范不变的识别**：
$F$ 的"规范依赖"是**定理级必然**，不是工夫不够。 -/
theorem no_gaugeInv_identification (g : ℝ → ℝ → ℝ) (hg : Identifies g) :
    ¬ (∀ t κ w : ℝ, 0 < t → 0 < κ → 0 < w → g (t * κ) (t * w) = g κ w) := by
  intro hinv
  have hL1 : 0 < L (1 / 4 : ℝ) := L_pos (by norm_num) (by norm_num)
  -- 取 θ=1/4、κ=1、t=2
  have h1 : g 1 (L (1 / 4 : ℝ)) = 1 / 4 :=
    identified_on_levels g hg 1 one_pos (1 / 4) (by norm_num) (by norm_num)
  have h2 : g 2 (2 * L (1 / 4 : ℝ)) = g 1 (L (1 / 4 : ℝ)) := by
    have := hinv 2 1 (L (1 / 4 : ℝ)) (by norm_num) one_pos hL1
    simpa using this
  -- 另一个水平 θ' = θ(2 L(1/4))
  set θ' := thetaOf (2 * L (1 / 4 : ℝ)) with hθ'def
  have hθ'0 : 0 < θ' := by
    rw [hθ'def]
    unfold thetaOf
    positivity
  have hθ'1 : θ' < 1 := (thetaOf_mem (by linarith)).2
  have hLθ' : L θ' = 2 * L (1 / 4 : ℝ) := by
    rw [hθ'def, L_thetaOf]
  have h3 : g 2 (2 * L (1 / 4 : ℝ)) = θ' := by
    have := identified_on_levels g hg 2 (by norm_num) θ' hθ'0 hθ'1
    rwa [hLθ'] at this
  have h4 : θ' = 1 / 4 := by
    rw [← h3, h2, h1]
  -- 但 θ' ≠ 1/4：因为 θ 严格下降且 2L(1/4) ≠ L(1/4)
  have hne : (2 : ℝ) * L (1 / 4 : ℝ) ≠ L (1 / 4 : ℝ) := by
    intro hcon
    have := hL1
    linarith
  have : θ' ≠ 1 / 4 := by
    intro hcon
    have hLc : L θ' = L (1 / 4 : ℝ) := by rw [hcon]
    rw [hLθ'] at hLc
    exact hne hLc
  exact this h4

/-- **（T-θ‴-4 证书）** 识别存在且典范 · 识别在水平上唯一 · **不存在规范不变的识别**。 -/
theorem t_theta_4_certificate :
    (∀ κ μ w : ℝ, 0 < κ → 0 < w → Fix (c κ μ w) = {x : ℝ | b κ μ x ≤ thetaOf w}) ∧
      (∀ g : ℝ → ℝ → ℝ, Identifies g → ∀ κ : ℝ, 0 < κ → ∀ θ : ℝ, 0 < θ → θ < 1 →
        g κ (L θ) = θ) ∧
      (∀ g : ℝ → ℝ → ℝ, Identifies g →
        ¬ (∀ t κ w : ℝ, 0 < t → 0 < κ → 0 < w → g (t * κ) (t * w) = g κ w)) :=
  ⟨fun κ μ w hκ hw => canonical_identifies κ μ w hκ hw,
    fun g hg κ hκ θ h0 h1 => identified_on_levels g hg κ hκ θ h0 h1,
    fun g hg => no_gaugeInv_identification g hg⟩

end FaceIdentification
