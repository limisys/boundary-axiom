/-
  Copyright 2026 Xueqiang Gao (高学强) · ORCID 0009-0008-3821-3454
  Licensed under the Apache License, Version 2.0 (see LICENSE).
  Original publication source: caseos.cn/research — https://caseos.cn/research/
  First public release 2026-10-09; formal publication 2026-10-20.
  Part of the B-line canonical subset (group 2): 53 files / 417 theorems+lemmas / 77 definitions.
  Attribution header added at publication; proof bodies unchanged.
-/

/-
ObservableProxy.lean —— **给出一个具体可观测代理：测试状态"已决／未决"**（第 141 轮）

**令源**：第 132／133 轮把桥写成可判定条件（且只需**保序代理**），但"**怎么取到读数**"只答了一半。
本件给出**一个具体的、由模型自身给出的代理**：

> 取一个固定测试状态 $x_0$，观察它是否落在**刚性面** $\mathrm{Fix}(c_{\kappa,\mu,L\theta})$ 里
> （即"**这个状态被决了吗**"）。
> 则：**这个 0/1 观测恰好是一个阈式桥，其阈值就是 $x_0$ 处的读数** $b_{\kappa,\mu}(x_0)$。

**结果（机检）**：
  · `mem_fix_iff`：已决 $\\iff$ **宽度 ≤ 核单位下的距离**（$w\\le\\kappa|x_0-\\mu|$）；
  · `fix_anti_w`：宽度越大，刚性面**越小**（单调收缩）；
  · `membership_is_threshold_bridge`（**主结果**）：$x_0\\in\\mathrm{Fix}(c_{\\kappa,\\mu,L\\theta})\\iff b_{\\kappa,\\mu}(x_0)\\le\\theta$；
  · `threshold_is_reading`：该阈值 $=x_0$ 处的读数 $\\theta(\\kappa|x_0-\\mu|)$；
  · `membership_monotone_in_level`：指示量对 $\\theta$ **单调不减**（故 132 轮"向下封闭"判据**自动成立**）；
  · `observable_proxy_certificate`：打包。

**⇒ 对 M1 的意义**：第七条条款（桥的可判定性）**有了一个具体可执行的代理**——
"**测一个状态是否被决**"，其阈值**就是该状态处的读数**；再结合 133 轮，**只需保序**，不需标度。

**⚠ 不声称的**：不声称"已决／未决"在实验上容易测（那是**实验设计**问题）；本件只把代理**构造出来**并证其桥性质。

0 `sorry` / `0 axiom`。
-/
import Mathlib
import ClosureGauge
import KernelCalibration

open scoped Real

namespace ObservableProxy

open SharpnessClosure LocusVsBoundary LogisticCore
open ReadoutExistence (thetaOf L_thetaOf thetaOf_mem)

/-- **（已决 ⟺ 宽度不超过核单位下的距离）** $x\in\mathrm{Fix}(c_{\kappa,\mu,w})\iff w\le\kappa|x-\mu|$。 -/
theorem mem_fix_iff (κ μ w x : ℝ) (hκ : 0 < κ) (hw : 0 ≤ w) :
    x ∈ Fix (c κ μ w) ↔ w ≤ κ * |x - μ| := by
  rw [ClosureGauge.fix_ratio_form κ μ w hκ hw, Set.mem_ofPred_eq, tail_iff κ μ w x hκ hw]
  rw [abs_mul, abs_of_pos hκ]

/-- **（宽度越大，刚性面越小）** $w_1\le w_2\Rightarrow\mathrm{Fix}(c_{\kappa,\mu,w_2})\subseteq\mathrm{Fix}(c_{\kappa,\mu,w_1})$。 -/
theorem fix_anti_w (κ μ w₁ w₂ : ℝ) (hκ : 0 < κ) (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂)
    (h : w₁ ≤ w₂) : Fix (c κ μ w₂) ⊆ Fix (c κ μ w₁) := by
  intro x hx
  rw [mem_fix_iff κ μ w₁ x hκ hw₁]
  rw [mem_fix_iff κ μ w₂ x hκ hw₂] at hx
  linarith

/-- **（主结果）** **测试状态是否已决，恰是一个阈式桥，阈值为该状态处的读数**。 -/
theorem membership_is_threshold_bridge (κ μ θ x₀ : ℝ) (hκ : 0 < κ) (h0 : 0 < θ) (h1 : θ < 1) :
    (x₀ ∈ Fix (c κ μ (L θ))) ↔ b κ μ x₀ ≤ θ := by
  rw [fix_c_eq_decided κ μ θ hκ h0 h1, Set.mem_ofPred_eq]

/-- **（阈值就是该处的读数）** $b_{\kappa,\mu}(x_0)=\theta(\\kappa|x_0-\\mu|)$。 -/
theorem threshold_is_reading (κ μ x₀ : ℝ) (hκ : 0 < κ) :
    b κ μ x₀ = thetaOf (κ * |x₀ - μ|) := by
  rw [KernelCalibration.b_eq_thetaOf_abs, abs_mul, abs_of_pos hκ]

/-- **（指示量对水平单调不减）** 这正是 132 轮"向下封闭"判据的形式，故**自动成立**。 -/
theorem membership_monotone_in_level (κ μ θ₁ θ₂ x₀ : ℝ) (hκ : 0 < κ)
    (h1a : 0 < θ₁) (h1b : θ₁ < 1) (h2a : 0 < θ₂) (h2b : θ₂ < 1) (h : θ₁ ≤ θ₂) :
    x₀ ∈ Fix (c κ μ (L θ₁)) → x₀ ∈ Fix (c κ μ (L θ₂)) := by
  intro hx
  rw [membership_is_threshold_bridge κ μ θ₂ x₀ hκ h2a h2b]
  rw [membership_is_threshold_bridge κ μ θ₁ x₀ hκ h1a h1b] at hx
  linarith

/-- **（可观测代理证书）** 已决的宽度判据 · 刚性面随宽度收缩 · **指示量＝阈式桥（阈值即读数）** · 单调不减。 -/
theorem observable_proxy_certificate :
    (∀ κ μ w x : ℝ, 0 < κ → 0 ≤ w → (x ∈ Fix (c κ μ w) ↔ w ≤ κ * |x - μ|)) ∧
      (∀ κ μ w₁ w₂ : ℝ, 0 < κ → 0 ≤ w₁ → 0 ≤ w₂ → w₁ ≤ w₂ →
        Fix (c κ μ w₂) ⊆ Fix (c κ μ w₁)) ∧
      (∀ κ μ θ x₀ : ℝ, 0 < κ → 0 < θ → θ < 1 →
        (x₀ ∈ Fix (c κ μ (L θ)) ↔ b κ μ x₀ ≤ θ)) ∧
      (∀ κ μ x₀ : ℝ, 0 < κ → b κ μ x₀ = thetaOf (κ * |x₀ - μ|)) ∧
      (∀ κ μ θ₁ θ₂ x₀ : ℝ, 0 < κ → 0 < θ₁ → θ₁ < 1 → 0 < θ₂ → θ₂ < 1 → θ₁ ≤ θ₂ →
        x₀ ∈ Fix (c κ μ (L θ₁)) → x₀ ∈ Fix (c κ μ (L θ₂))) :=
  ⟨fun κ μ w x hκ hw => mem_fix_iff κ μ w x hκ hw,
    fun κ μ w₁ w₂ hκ h1 h2 h => fix_anti_w κ μ w₁ w₂ hκ h1 h2 h,
    fun κ μ θ x₀ hκ h0 h1 => membership_is_threshold_bridge κ μ θ x₀ hκ h0 h1,
    fun κ μ x₀ hκ => threshold_is_reading κ μ x₀ hκ,
    fun κ μ θ₁ θ₂ x₀ hκ h1a h1b h2a h2b h => membership_monotone_in_level κ μ θ₁ θ₂ x₀ hκ h1a h1b h2a h2b h⟩

end ObservableProxy
