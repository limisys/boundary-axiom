/-
ContinuousRelaxation.lean —— **把"每步减半"写成连续时间的形状**（第 129 轮）

**令源**：第 117 轮给的是**步**（迭代 $w_{n+1}=\\mathrm{relax}\\,w_n$，误差每步减半），
而实验测的是**时间**（衰减曲线）。本件把两者之间的**形状**固定下来：

> **在声明的连续时间包络下，宽度误差按 $e^{-(\\ln 2)t}$ 衰减——即半衰期恰为一个时间单位；
> 水平误差承同样的指数界。**

**结果（机检）**：
  · `wOf w₀ t = 1 + (w₀-1)\\,e^{-(\\ln 2)t}`（**声明的**连续包络）；
  · `wOf_zero`：$t=0$ 处回到初值；
  · `wOf_half_life`（**主结果**）：**误差每单位时间恰好减半**（$t\\mapsto t+1$）；
  · `wOf_ge_one`／`wOf_antitone`：始终不越过 $1$，且**随时间单调下降**；
  · `wOf_nat_eq`：在整数时刻**与步长公式一致**（$(w₀-1)/2^n$）；
  · `cont_level_bound`／`cont_level_nondecreasing`：**水平误差的指数界**与**单调趋近**。

**⚠ 声明的部分**：`wOf` 是**连续包络**（建模选择），**不是**由 117 轮的离散迭代导出的；
实际"步 ↔ 秒"的换算**仍未做**——本件只把**曲线形状**固定为指数、半衰期已知。

0 `sorry` / `0 axiom`。
-/
import LevelDynamics
import ReadoutDynamics
import Falsifiers

open scoped Real

namespace ContinuousRelaxation

open LevelDynamics
open LogisticCore (L)
open ReadoutExistence (thetaOf)

/-- **连续包络（声明）**：$w(t)=1+(w_0-1)e^{-(\\ln 2)t}$。 -/
noncomputable def wOf (w₀ t : ℝ) : ℝ := 1 + (w₀ - 1) * Real.exp (-(Real.log 2) * t)

/-- **（初值）** $w(0)=w_0$。 -/
theorem wOf_zero (w₀ : ℝ) : wOf w₀ 0 = w₀ := by
  unfold wOf
  simp

/-- **（主结果 · 半衰期＝一个时间单位）** $w(t+1)-1=\\dfrac{w(t)-1}{2}$。 -/
theorem wOf_half_life (w₀ t : ℝ) : wOf w₀ (t + 1) - 1 = (wOf w₀ t - 1) / 2 := by
  have hlog : Real.exp (-(Real.log 2)) = 1 / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hsplit : -(Real.log 2) * (t + 1) = -(Real.log 2) * t + (-(Real.log 2)) := by ring
  unfold wOf
  rw [hsplit, Real.exp_add, hlog]
  ring

/-- **（整数时刻与步长公式一致）** $w(n)-1=\\dfrac{w_0-1}{2^{n}}$。 -/
theorem wOf_nat_eq (w₀ : ℝ) (n : ℕ) : wOf w₀ (n : ℝ) - 1 = (w₀ - 1) / 2 ^ n := by
  have hlog : Real.exp (-(Real.log 2)) = 1 / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hmul : -(Real.log 2) * (n : ℝ) = (n : ℝ) * (-(Real.log 2)) := by ring
  have hexp : Real.exp (-(Real.log 2) * (n : ℝ)) = (1 / 2 : ℝ) ^ n := by
    rw [hmul, Real.exp_nat_mul, hlog]
  unfold wOf
  rw [hexp]
  have hpow : (1 / 2 : ℝ) ^ n = 1 / 2 ^ n := by
    rw [div_pow]
    norm_num
  rw [hpow]
  ring

/-- **（不越过）** $w_0\\ge1,\\ t\\ge0\\Rightarrow w(t)\\ge1$。 -/
theorem wOf_ge_one {w₀ : ℝ} (hw : 1 ≤ w₀) {t : ℝ} (ht : 0 ≤ t) : 1 ≤ wOf w₀ t := by
  have hexp : Real.exp (-(Real.log 2) * t) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith
  have : 0 ≤ (w₀ - 1) * Real.exp (-(Real.log 2) * t) :=
    mul_nonneg (by linarith) (le_of_lt (Real.exp_pos _))
  unfold wOf
  linarith

/-- **（单调下降）** $0\\le t\\le t'\\Rightarrow w(t')\\le w(t)$（$w_0\\ge1$）。 -/
theorem wOf_antitone {w₀ : ℝ} (hw : 1 ≤ w₀) {t t' : ℝ} (ht : 0 ≤ t) (h : t ≤ t') :
    wOf w₀ t' ≤ wOf w₀ t := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hexp : Real.exp (-(Real.log 2) * t') ≤ Real.exp (-(Real.log 2) * t) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hcoef : 0 ≤ w₀ - 1 := by linarith
  unfold wOf
  nlinarith [mul_le_mul_of_nonneg_left hexp hcoef]

/-- **（水平误差的指数界）** $\\theta^\\star-\\theta\\big(w(t)\\big)\\le\\theta^\\star(w_0-1)e^{-(\\ln 2)t}$。 -/
theorem cont_level_bound {w₀ : ℝ} (hw : 1 ≤ w₀) {t : ℝ} (ht : 0 ≤ t) :
    thetaOf 1 - thetaOf (wOf w₀ t)
      ≤ thetaOf 1 * ((w₀ - 1) * Real.exp (-(Real.log 2) * t)) := by
  have h1 : 1 ≤ wOf w₀ t := wOf_ge_one hw ht
  have h2 := Falsifiers.thetaStar_sub_le (wOf w₀ t) h1
  have h3 : wOf w₀ t - 1 = (w₀ - 1) * Real.exp (-(Real.log 2) * t) := by
    unfold wOf
    ring
  rw [h3] at h2
  exact h2

/-- **（水平单调趋近）** $\\theta(w(t))$ 随时间**单调非降**（$w_0\\ge1$）。 -/
theorem cont_level_nondecreasing {w₀ : ℝ} (hw : 1 ≤ w₀) {t t' : ℝ} (ht : 0 ≤ t) (h : t ≤ t') :
    thetaOf (wOf w₀ t) ≤ thetaOf (wOf w₀ t') :=
  ReadoutDynamics.thetaOf_le_thetaOf (wOf_antitone hw ht h)

/-- **（连续时间证书）** 初值 · **半衰期＝1** · 整数时刻与步长公式一致 · 不越过 · 单调下降 · **水平误差指数界** · 水平单调趋近。 -/
theorem continuous_certificate :
    (∀ w₀ : ℝ, wOf w₀ 0 = w₀) ∧
      (∀ w₀ t : ℝ, wOf w₀ (t + 1) - 1 = (wOf w₀ t - 1) / 2) ∧
      (∀ w₀ : ℝ, ∀ n : ℕ, wOf w₀ (n : ℝ) - 1 = (w₀ - 1) / 2 ^ n) ∧
      (∀ w₀ : ℝ, 1 ≤ w₀ → ∀ t : ℝ, 0 ≤ t → 1 ≤ wOf w₀ t) ∧
      (∀ w₀ : ℝ, 1 ≤ w₀ → ∀ t t' : ℝ, 0 ≤ t → t ≤ t' → wOf w₀ t' ≤ wOf w₀ t) ∧
      (∀ w₀ : ℝ, 1 ≤ w₀ → ∀ t : ℝ, 0 ≤ t →
        thetaOf 1 - thetaOf (wOf w₀ t)
          ≤ thetaOf 1 * ((w₀ - 1) * Real.exp (-(Real.log 2) * t))) ∧
      (∀ w₀ : ℝ, 1 ≤ w₀ → ∀ t t' : ℝ, 0 ≤ t → t ≤ t' →
        thetaOf (wOf w₀ t) ≤ thetaOf (wOf w₀ t')) :=
  ⟨fun w₀ => wOf_zero w₀,
    fun w₀ t => wOf_half_life w₀ t,
    fun w₀ n => wOf_nat_eq w₀ n,
    fun w₀ hw t ht => wOf_ge_one hw ht,
    fun w₀ hw t t' ht h => wOf_antitone hw ht h,
    fun w₀ hw t ht => cont_level_bound hw ht,
    fun w₀ hw t t' ht h => cont_level_nondecreasing hw ht h⟩

end ContinuousRelaxation
