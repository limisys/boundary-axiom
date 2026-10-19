/-
  Copyright 2026 Xueqiang Gao (高学强) · ORCID 0009-0008-3821-3454
  Licensed under the Apache License, Version 2.0 (see LICENSE).
  Original publication source: caseos.cn/research — https://caseos.cn/research/
  First public release 2026-10-09; formal publication 2026-10-20.
  Part of the B-line canonical subset (group 2): 53 files / 417 theorems+lemmas / 77 definitions.
  Attribution header added at publication; proof bodies unchanged.
-/

/-
LevelSelection.lean —— **T-θ‴-3：把"内禀判据"形式化为"选取原则"，并证明正确的 T-no-go**（第 116 轮）

**背景与动机（承接第 114／115 轮的更正）**：
  · 第 114 轮否掉了"定出水平必须破缺规范"这条**泛函**版说法（规范不变泛函**可以**对水平敏感，只要把内禀 $\\kappa^\\star$ 当常数）；
  · 第 115 轮证明**水平可由已决集唯一识别**（给定尺度），且存在**追踪水平**的读出（但它破缺 K2）。
  ⇒ 于是"第二层"的正确问法不是"哪个泛函定出 $\\theta$"，而是：
    **要在自由参数 $w$ 上"挑出"一个值，所加的那条原则必须是什么样？**

**本件结果（把 T-no-go 写成真命题）**：

  · `GaugeInvPrinciple`：**规范不变的选取原则**（对 $w$ 的谓词，在 $w\\mapsto tw$ 下不变）；
  · `gaugeInvPrinciple_constant`（**主定理**）：规范不变的原则**只能"全体成立"或"全体不成立"**
    ⇒ `gaugeInvPrinciple_notSelects`：**它永远挑不出一个水平**；
  · 反之：**能挑出水平的原则必破缺规范** —— `selfConsistency_not_gaugeInv`（$w=1/w$ 不不变）
    ＋ `selfConsistency_selects`（它**唯一**挑出 $w=1$，与 `R_fixed_unique` 一致）；
  · **⚠ 诚实边界（`alternative_selector_selects`）**：**"破缺规范"是必要条件，不是充分条件**——
    例如 $P(w):=(w=2)$ 同样破缺规范、同样唯一挑出 $w=2$，**给出的水平与 $\\theta^\\star$ 不同**。
    ⇒ **"第二层只能由自指／描述定出"仍未成立**；已成立的只是"**第二层必须由破缺规范的原则给出**"；
  · `selection_induces_level`：任何选取原则都**诱导出唯一的水平**（S3 的选取版）。

**⇒ 本件把纲领主线的一句话从"论证"抬到"定理"，同时把它的另一半如实标为未证。**

0 `sorry` / `0 axiom`。
-/
import ReadoutExistence

open scoped Real

namespace LevelSelection

open ReadoutExistence (thetaOf)

/-- **规范不变的选取原则**：对 $w\\mapsto tw$（$t>0$）不变的谓词。 -/
def GaugeInvPrinciple (P : ℝ → Prop) : Prop :=
  ∀ t w : ℝ, 0 < t → 0 < w → (P (t * w) ↔ P w)

/-- **选取原则"挑出一个水平"**：在正数中**有且仅有一个**解。 -/
def Selects (P : ℝ → Prop) : Prop :=
  ∃ w : ℝ, 0 < w ∧ P w ∧ ∀ w' : ℝ, 0 < w' → P w' → w' = w

/-- **（主定理 · T-no-go）** 规范不变的原则**恒真或恒假**（在 $w>0$ 上）。 -/
theorem gaugeInvPrinciple_constant (P : ℝ → Prop) (h : GaugeInvPrinciple P) :
    (∀ w : ℝ, 0 < w → P w) ∨ (∀ w : ℝ, 0 < w → ¬ P w) := by
  have key : ∀ w : ℝ, 0 < w → (P w ↔ P 1) := by
    intro w hw
    have h1 := h (1 / w) w (by positivity) hw
    have h2 : (1 / w) * w = 1 := by rw [one_div, inv_mul_cancel₀ hw.ne']
    rw [h2] at h1
    exact h1.symm
  by_cases h1 : P 1
  · left
    intro w hw
    exact (key w hw).mpr h1
  · right
    intro w hw hP
    exact h1 ((key w hw).mp hP)

/-- **（T-no-go）** **规范不变的原则挑不出任何水平**。 -/
theorem gaugeInvPrinciple_notSelects (P : ℝ → Prop) (h : GaugeInvPrinciple P) :
    ¬ Selects P := by
  rintro ⟨w₀, hw₀, hPw, huniq⟩
  rcases gaugeInvPrinciple_constant P h with hall | hnone
  · have h2 : 0 < 2 * w₀ := by linarith
    have := huniq (2 * w₀) h2 (hall (2 * w₀) h2)
    linarith
  · exact hnone w₀ hw₀ hPw

/-- **（必要条件的一面）** 倒数自洽原则 $w=1/w$ **破缺规范不变**。 -/
theorem selfConsistency_not_gaugeInv :
    ¬ GaugeInvPrinciple (fun w : ℝ => 1 / w = w) := by
  intro h
  have h2 : (1 : ℝ) / (2 * 1) = 2 * 1 :=
    (h 2 1 (by norm_num) (by norm_num)).mpr (by norm_num : (1 : ℝ) / 1 = 1)
  norm_num at h2

/-- **（它确实挑得出）** $w=1/w$ **唯一**挑出 $w=1$（与 `ReadoutExistence.R_fixed_unique` 一致）。 -/
theorem selfConsistency_selects : Selects (fun w : ℝ => 1 / w = w) := by
  refine ⟨1, by norm_num, by norm_num, ?_⟩
  intro w' hw' hP
  exact ReadoutExistence.R_fixed_unique hw' hP

/-- **（⚠ 诚实边界）** **"破缺规范"不是充分条件**：$P(w):=(w=2)$ 同样破缺规范、同样唯一挑出，
但给出的水平是 $\\theta(2)\\neq\\theta^\\star$。⇒ "第二层只能自指出"**仍未证**。 -/
theorem alternative_selector_selects :
    Selects (fun w : ℝ => w = 2) ∧ ¬ GaugeInvPrinciple (fun w : ℝ => w = 2) := by
  constructor
  · refine ⟨2, by norm_num, rfl, ?_⟩
    intro w' _ hP
    exact hP
  · intro h
    have hbad : (1 : ℝ) = 2 := (h 2 1 (by norm_num) (by norm_num)).mp (by norm_num)
    norm_num at hbad

/-- **（选取 ⇒ 唯一水平）** 任何选取原则都**诱导出唯一的水平**。 -/
theorem selection_induces_level (P : ℝ → Prop) (hP : Selects P) :
    ∃! θ : ℝ, ∃ w : ℝ, 0 < w ∧ P w ∧ θ = thetaOf w := by
  obtain ⟨w₀, hw₀, hPw, huniq⟩ := hP
  refine ⟨thetaOf w₀, ⟨w₀, hw₀, hPw, rfl⟩, ?_⟩
  rintro θ ⟨w, hw, hPw', rfl⟩
  have h : w = w₀ := huniq w hw hPw'
  rw [h]

/-- **（T-θ‴-3 证书）** 一次打包：不变原则恒真或恒假 · 不变原则挑不出水平 · 自洽原则破缺不变且
唯一挑出 $w=1$ · **破缺规范不是充分条件** · **选取诱导唯一水平**。 -/
theorem t_theta_3_certificate :
    (∀ P : ℝ → Prop, GaugeInvPrinciple P →
        ((∀ w : ℝ, 0 < w → P w) ∨ (∀ w : ℝ, 0 < w → ¬ P w))) ∧
      (∀ P : ℝ → Prop, GaugeInvPrinciple P → ¬ Selects P) ∧
      ¬ GaugeInvPrinciple (fun w : ℝ => 1 / w = w) ∧
      Selects (fun w : ℝ => 1 / w = w) ∧
      (∀ P : ℝ → Prop, Selects P → ∃! θ : ℝ, ∃ w : ℝ, 0 < w ∧ P w ∧ θ = thetaOf w) ∧
      (∃ Q : ℝ → Prop, Selects Q ∧ ¬ GaugeInvPrinciple Q) :=
  ⟨fun P h => gaugeInvPrinciple_constant P h,
    fun P h => gaugeInvPrinciple_notSelects P h,
    selfConsistency_not_gaugeInv,
    selfConsistency_selects,
    fun P h => selection_induces_level P h,
    ⟨fun w : ℝ => w = 2, alternative_selector_selects.1, alternative_selector_selects.2⟩⟩

end LevelSelection
