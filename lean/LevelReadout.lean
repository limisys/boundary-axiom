/-
LevelReadout.lean —— **S2（部分）＋ S3（部分）：一个"追踪水平"的读出，与水平的可识别性**（第 115 轮）

**背景**：第 114 轮的更正指出两件事：
  ①`unitRead` **对水平盲**（`GaugeNoGo.unitRead_gaugeInv_level_blind`）⇒ 它**不能**充当"系统对自身水平的读出"；
  ②"规范方向"**证不出**水平定不出（`gaugeInv_and_level_sensitive`）。
  ⇒ **S2 的新目标被写定为**：给出一个**随水平变化**（追踪）的读出。

**本件把这一目标做掉，并给出 S3 的可证部分**：

  · `readout`：**在宽度边缘读自己的核** —— $\\mathrm{readout}(\\kappa,\\mu,w):=b_{\\kappa,\\mu}\\!\\big(\\mu+\\frac{w}{\\kappa}\\big)$；
  · `readout_eq_thetaOf`（**闭式**）：$\\mathrm{readout}(\\kappa,\\mu,w)=\\theta(w)=\\dfrac{2}{1+e^{w}}$ —— 读出**就是**水平函数；
  · `readout_tracks_level`：$\\mathrm{readout}(\\kappa,\\mu,L\\,\\theta)=\\theta$ ⇒ **追踪性成立**（S2 的要求被满足）；
  · `readout_not_gauge_invariant`：该读出**破缺 K2**（$\\mathrm{readout}(t\\kappa,\\mu,tw)\\neq\\mathrm{readout}(\\kappa,\\mu,w)$，$t\\neq1$）
    ⇒ 与 `unitRead`（K2 ✓／追踪 ✗）**恰好相反**：**在这条线上，K2 与追踪性互斥**；
  · `unitRead_eq_readout_one`：`unitRead` **＝宽度取自洽值 $w=1$ 时的读数** ⇒ 第 111 轮的"单位读出"是它的特例；
  · `level_identified_by_closure`（**S3 部分**）：**给定尺度，已决集唯一决定水平**（$\\mathrm{Fix}(c_{\\kappa,\\mu,L\\theta_1})=\\mathrm{Fix}(c_{\\kappa,\\mu,L\\theta_2})\\Rightarrow\\theta_1=\\theta_2$）
    ⇒ **水平是可识别的（因而原则上可观测）**，M1 把 $\\theta^\\star$ 放在因变量位置上**有形式依据**。

**⚠ 本件不声称的**：不声称"系统**自己**导出了 $\\theta$"。本件给的是
**一个由系统的核与宽度定义的、可追踪水平的读出**（**定义**＋**定理**），
以及**水平的可识别性**（定理）。"系统动力学**实现**该读出"（S2 的存在性正题）**仍未做**。

0 `sorry` / 0 `axiom`。
-/
import SharpnessClosure
import UnitReading
import GaugeNoGo

open scoped Real

namespace LevelReadout

open SharpnessClosure LocusVsBoundary LogisticCore UnitReading
open ReadoutExistence (thetaOf L_thetaOf thetaOf_L)

/-- **追踪读出**：在**宽度边缘** $\\mu+w/\\kappa$ 处读自己的核。 -/
noncomputable def readout (κ μ w : ℝ) : ℝ := b κ μ (μ + w / κ)

/-- **（闭式）** 读出恰为**水平函数**：$\\mathrm{readout}(\\kappa,\\mu,w)=\\theta(w)$。 -/
theorem readout_eq_thetaOf (κ μ w : ℝ) (hκ : 0 < κ) (hw : 0 ≤ w) :
    readout κ μ w = thetaOf w := by
  unfold readout
  rw [T1_stable_form]
  have h : κ * ((μ + w / κ) - μ) = w := by field_simp; ring
  rw [h, abs_of_nonneg hw]
  unfold sig thetaOf
  rw [neg_neg]
  ring

/-- **（S2 的追踪性）** 在宽度取 $L\\,\\theta$ 时，读出**取到水平本身**。 -/
theorem readout_tracks_level (κ μ θ : ℝ) (hκ : 0 < κ) (h0 : 0 < θ) (h1 : θ < 1) :
    readout κ μ (L θ) = θ := by
  rw [readout_eq_thetaOf κ μ (L θ) hκ (le_of_lt (L_pos h0 h1)), thetaOf_L h0 h1]

/-- **（水平函数的单射性）** $\\theta(\\cdot)$ 在 $(0,\\infty)$ 上单射。 -/
theorem thetaOf_injOn : Set.InjOn thetaOf (Set.Ioi (0 : ℝ)) := by
  intro a ha b hb h
  have h1 : Real.exp a = Real.exp b := by
    have h2 : 2 / (1 + Real.exp a) = 2 / (1 + Real.exp b) := h
    field_simp at h2
    linarith
  exact Real.exp_injective h1

/-- **（K2 与追踪性互斥）** 追踪读出**破缺规范不变**：
$t\\neq1\\Rightarrow\\mathrm{readout}(t\\kappa,\\mu,tw)\\neq\\mathrm{readout}(\\kappa,\\mu,w)$（$w>0$）。 -/
theorem readout_not_gauge_invariant (κ μ w t : ℝ) (hκ : 0 < κ) (hw : 0 < w)
    (ht : 0 < t) (ht1 : t ≠ 1) :
    readout (t * κ) μ (t * w) ≠ readout κ μ w := by
  intro h
  rw [readout_eq_thetaOf (t * κ) μ (t * w) (by positivity) (le_of_lt (by positivity)),
    readout_eq_thetaOf κ μ w hκ (le_of_lt hw)] at h
  have h2 : t * w = w := thetaOf_injOn (Set.mem_Ioi.mpr (by positivity)) hw h
  have h3 : (t - 1) * w = 0 := by linarith
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact ht1 (by linarith)
  · exact hw.ne' h4

/-- **（单位读出＝自洽宽度处的读数）** $w=1$ 时追踪读出即第 111 轮的 `unitRead`；
而 $w=1$ 恰是倒数自洽方程 $w=1/w$ 的**唯一正解**（`ReadoutExistence.R_fixed_unique`）。 -/
theorem unitRead_eq_readout_one (κ μ : ℝ) : readout κ μ 1 = unitRead κ μ := by
  unfold readout unitRead
  norm_num

/-- **（S3 部分：水平可由闭包识别）** 给定尺度，**已决集唯一决定水平**。 -/
theorem level_identified_by_closure (κ μ : ℝ) (hκ : 0 < κ) {θ₁ θ₂ : ℝ}
    (h1a : 0 < θ₁) (h1b : θ₁ < 1) (h2a : 0 < θ₂) (h2b : θ₂ < 1)
    (h : Fix (c κ μ (L θ₁)) = Fix (c κ μ (L θ₂))) : θ₁ = θ₂ := by
  have hw1 : 0 < L θ₁ := L_pos h1a h1b
  have hw2 : 0 < L θ₂ := L_pos h2a h2b
  have hp1 : 0 < L θ₁ / κ := div_pos hw1 hκ
  have hp2 : 0 < L θ₂ / κ := div_pos hw2 hκ
  -- 端点 $\mu+a/\kappa$（其核值即 $\theta(a)$）落在阈值 $b$ 的已决集里 $\iff b\le a$
  have key : ∀ a b : ℝ, 0 < a → 0 < b → 0 < b / κ →
      μ + a / κ ∈ Fix (c κ μ b) → b ≤ a := by
    intro a b ha hb hbk hmem
    have hak : 0 < a / κ := div_pos ha hκ
    rw [ClosureGauge.fix_ratio_form κ μ b hκ (le_of_lt hb), Set.mem_ofPred_eq] at hmem
    rcases hmem with hmm | hmm
    · linarith
    · have : b / κ ≤ a / κ := by linarith
      exact (div_le_div_iff_of_pos_right hκ).mp this
  have hle : L θ₁ ≤ L θ₂ := by
    refine key (L θ₂) (L θ₁) hw2 hw1 hp1 ?_
    rw [h]
    rw [ClosureGauge.fix_ratio_form κ μ (L θ₂) hκ (le_of_lt hw2), Set.mem_ofPred_eq]
    right
    linarith
  have hge : L θ₂ ≤ L θ₁ := by
    refine key (L θ₁) (L θ₂) hw1 hw2 hp2 ?_
    rw [← h]
    rw [ClosureGauge.fix_ratio_form κ μ (L θ₁) hκ (le_of_lt hw1), Set.mem_ofPred_eq]
    right
    linarith
  exact ReadoutExistence.L_injOn (Set.mem_Ioo.mpr ⟨h1a, h1b⟩) (Set.mem_Ioo.mpr ⟨h2a, h2b⟩)
    (le_antisymm hle hge)

/-- **（S2-部分 ＋ S3-部分 证书）** 一次打包：
读出有闭式 · 读出追踪水平 · 读出破缺 K2 · `unitRead` 是 $w=1$ 特例 · **水平可由闭包唯一识别**。 -/
theorem s2_s3_certificate (κ μ : ℝ) (hκ : 0 < κ) :
    (∀ w : ℝ, 0 ≤ w → readout κ μ w = thetaOf w) ∧
      (∀ θ : ℝ, 0 < θ → θ < 1 → readout κ μ (L θ) = θ) ∧
      (∀ w t : ℝ, 0 < w → 0 < t → t ≠ 1 → readout (t * κ) μ (t * w) ≠ readout κ μ w) ∧
      readout κ μ 1 = unitRead κ μ ∧
      (∀ θ₁ θ₂ : ℝ, 0 < θ₁ → θ₁ < 1 → 0 < θ₂ → θ₂ < 1 →
        Fix (c κ μ (L θ₁)) = Fix (c κ μ (L θ₂)) → θ₁ = θ₂) :=
  ⟨fun w hw => readout_eq_thetaOf κ μ w hκ hw,
    fun _ h0 h1 => readout_tracks_level κ μ _ hκ h0 h1,
    fun w t hw ht ht1 => readout_not_gauge_invariant κ μ w t hκ hw ht ht1,
    unitRead_eq_readout_one κ μ,
    fun _ _ h1a h1b h2a h2b hfix => level_identified_by_closure κ μ hκ h1a h1b h2a h2b hfix⟩

end LevelReadout
