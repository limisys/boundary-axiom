/-
  Copyright 2026 Xueqiang Gao (高学强) · ORCID 0009-0008-3821-3454
  Licensed under the Apache License, Version 2.0 (see LICENSE).
  Original publication source: caseos.cn/research — https://caseos.cn/research/
  First public release 2026-10-09; formal publication 2026-10-20.
  Part of the B-line canonical subset (group 2): 53 files / 417 theorems+lemmas / 77 definitions.
  Attribution header added at publication; proof bodies unchanged.
-/

/-
RelaxRobust.lean —— **缺口缩小（可证形式）：结论不依赖"松弛"的具体形状**（第 121 轮）

**背景**：第 117 轮用**声明的**松弛 $\\mathrm{relax}(w)=\\frac{w+1/w}{2}$ 形式化了 $\\tau$；
第 116 轮留下**唯一缺口**，第 117／118 轮把它缩小为
「**为什么用与倒数对称的松弛**」。本件把这一缩小**做成定理**：

> **只要松弛属于某个"可采纳类"（不动点在最省力宽度、一步后不越过、误差减半），
> 那么第 117–119 轮的全部结论（有限恢复时间、单侧夹逼、每步减半、指数逼近）都照旧成立。**

**⇒ 具体形状（$\\frac{w+1/w}{2}$）**只影响**常数**，不影响**定性结论与曲线形状**；
缺口因此**不再是"为什么是它"，而只是"为什么要求误差减半"**。

**结果（机检）**：
  · `Admissible f`（定义）：三步条件；
  · `relax_admissible`：第 117 轮的松弛**属于**该类（故它是特例，不是唯一选择）；
  · `admissible_iterate_ge_one`／`admissible_iterate_antitone`／`admissible_error`／`admissible_recovery_time`：
    一般 $f$ 下的**不越界／单调／每步减半／有限恢复时间**；
  · `admissible_level_squeeze`／`admissible_level_climbs`：一般 $f$ 下的**水平被夹到 $\\theta^\\star$**；
  · `robustness_certificate`：以上打包。

0 `sorry` / `0 axiom`。
-/
import LevelDynamics
import ReadoutDynamics

open scoped Real

namespace RelaxRobust

open LevelDynamics LogisticCore
open ReadoutExistence (thetaOf thetaOf_mem L_thetaOf thetaOf_L)
open ReadoutDynamics (thetaOf_le_thetaOf thetaOf_lt_thetaOf)

/-- **可采纳的松弛**：①一步后不越过 $1$；②在 $\\ge1$ 侧单调非增；③误差减半。 -/
def Admissible (f : ℝ → ℝ) : Prop :=
  (∀ w : ℝ, 0 < w → 1 ≤ f w) ∧
    (∀ w : ℝ, 1 ≤ w → f w ≤ w) ∧
    (∀ w : ℝ, 1 ≤ w → f w - 1 ≤ (w - 1) / 2)

/-- **（第 117 轮的松弛是可采纳的）** —— 它是**特例**，不是唯一选择。 -/
theorem relax_admissible : Admissible relax :=
  ⟨fun w hw => one_le_relax w hw,
    fun w hw => by
      rcases lt_or_eq_of_le hw with h | h
      · exact le_of_lt (relax_lt_self h)
      · rw [← h]
        norm_num [relax],
    fun w hw => relax_error_halves hw⟩

/-- **（不越界）** 迭代始终在 $\\ge1$ 一侧。 -/
theorem admissible_iterate_ge_one {f : ℝ → ℝ} (hf : Admissible f) {w : ℝ} (hw : 1 ≤ w) :
    ∀ n : ℕ, 1 ≤ (f^[n]) w := by
  intro n
  induction n with
  | zero => simpa using hw
  | succ k ih =>
      have hstep : 1 ≤ f ((f^[k]) w) := hf.1 _ (by linarith)
      have hidx : (f^[k + 1]) w = f ((f^[k]) w) := by rw [Function.iterate_succ_apply']
      rwa [hidx]

/-- **（单调非增）**。 -/
theorem admissible_iterate_antitone {f : ℝ → ℝ} (hf : Admissible f) {w : ℝ} (hw : 1 ≤ w) :
    ∀ n : ℕ, (f^[n + 1]) w ≤ (f^[n]) w := by
  intro n
  have hge := admissible_iterate_ge_one hf hw n
  have hidx : (f^[n + 1]) w = f ((f^[n]) w) := by rw [Function.iterate_succ_apply']
  rw [hidx]
  exact hf.2.1 _ hge

/-- **（每步减半 · 显式几何界）**。 -/
theorem admissible_error {f : ℝ → ℝ} (hf : Admissible f) {w : ℝ} (hw : 1 ≤ w) :
    ∀ n : ℕ, (f^[n]) w - 1 ≤ (w - 1) / 2 ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
      have hge := admissible_iterate_ge_one hf hw k
      have hstep : f ((f^[k]) w) - 1 ≤ ((f^[k]) w - 1) / 2 := hf.2.2 _ hge
      have hdiv : ((f^[k]) w - 1) / 2 ≤ ((w - 1) / 2 ^ k) / 2 :=
        div_le_div_of_nonneg_right ih (by norm_num)
      have hpow : ((w - 1) / 2 ^ k) / 2 = (w - 1) / 2 ^ (k + 1) := by
        rw [pow_succ, div_div]
      have hidx : (f^[k + 1]) w = f ((f^[k]) w) := by rw [Function.iterate_succ_apply']
      rw [hidx]
      linarith

/-- **（有限恢复时间）** 任意精度 $\\varepsilon>0$，存在有限 $N$。 -/
theorem admissible_recovery_time {f : ℝ → ℝ} (hf : Admissible f) {w : ℝ} (hw : 1 < w)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (f^[n]) w - 1 < ε := by
  have hw1 : 1 ≤ w := le_of_lt hw
  obtain ⟨N, hN⟩ := exists_nat_gt ((w - 1) / ε)
  have hNpow : (w - 1) / ε < (2 : ℝ) ^ N := by
    have h1 : (N : ℝ) < (2 : ℝ) ^ N := by
      exact_mod_cast Nat.lt_pow_self (by norm_num : 1 < 2)
    linarith
  refine ⟨N, fun n hn => ?_⟩
  have hb := admissible_error hf hw1 n
  have hmono : (w - 1) / 2 ^ n ≤ (w - 1) / 2 ^ N :=
    div_le_div_of_nonneg_left (by linarith) (by positivity)
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn)
  have hlt : (w - 1) / 2 ^ N < ε := by
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 ^ N)]
    have := (div_lt_iff₀ hε).mp hNpow
    linarith
  linarith

/-- **（水平上夹）** 一般 $f$：读数永不越过 $\\theta^\\star$。 -/
theorem admissible_level_squeeze {f : ℝ → ℝ} (hf : Admissible f) {w : ℝ} (hw : 1 ≤ w) (n : ℕ) :
    thetaOf ((f^[n]) w) ≤ thetaOf 1 :=
  thetaOf_le_thetaOf (admissible_iterate_ge_one hf hw n)

/-- **（水平下推）** 一般 $f$：任何低于 $\\theta^\\star$ 的水平有限步被超过。 -/
theorem admissible_level_climbs {f : ℝ → ℝ} (hf : Admissible f) {w : ℝ} (hw : 1 < w)
    (θ' : ℝ) (h0 : 0 < θ') (h1 : θ' < 1) (hlt : θ' < thetaOf 1) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → θ' < thetaOf ((f^[n]) w) := by
  have hm : thetaOf 1 ∈ Set.Ioo (0 : ℝ) 1 := thetaOf_mem one_pos
  have hLθ' : 1 < L θ' := by
    have := ReadoutDynamics.L_lt_L h0 hm.2 hlt
    rwa [L_thetaOf 1] at this
  obtain ⟨N, hN⟩ := admissible_recovery_time hf hw (L θ' - 1) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  have hlt' : (f^[n]) w < L θ' := by
    have := hN n hn
    linarith
  calc θ' = thetaOf (L θ') := (thetaOf_L h0 h1).symm
    _ < thetaOf ((f^[n]) w) := thetaOf_lt_thetaOf hlt'

/-- **（稳健性证书）** 第 117–119 轮的结论**不依赖松弛的具体形状**：
只要 $f$ 可采纳，就有 不越界 · 单调 · 每步减半 · 有限恢复时间 · 水平夹逼。 -/
theorem robustness_certificate (f : ℝ → ℝ) (hf : Admissible f) (w : ℝ) (hw : 1 < w) :
    (∀ n : ℕ, 1 ≤ (f^[n]) w) ∧
      (∀ n : ℕ, (f^[n + 1]) w ≤ (f^[n]) w) ∧
      (∀ n : ℕ, (f^[n]) w - 1 ≤ (w - 1) / 2 ^ n) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (f^[n]) w - 1 < ε) ∧
      (∀ n : ℕ, thetaOf ((f^[n]) w) ≤ thetaOf 1) ∧
      (∀ θ' : ℝ, 0 < θ' → θ' < 1 → θ' < thetaOf 1 →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → θ' < thetaOf ((f^[n]) w)) :=
  ⟨fun n => admissible_iterate_ge_one hf (le_of_lt hw) n,
    fun n => admissible_iterate_antitone hf (le_of_lt hw) n,
    fun n => admissible_error hf (le_of_lt hw) n,
    fun ε hε => admissible_recovery_time hf hw ε hε,
    fun n => admissible_level_squeeze hf (le_of_lt hw) n,
    fun θ' h0 h1 hlt => admissible_level_climbs hf hw θ' h0 h1 hlt⟩

/-- **（特例回接）** 第 117 轮的 $\\mathrm{relax}$ 满足全部结论。 -/
theorem relax_special_case (w : ℝ) (hw : 1 < w) :
    (∀ n : ℕ, (relax^[n]) w - 1 ≤ (w - 1) / 2 ^ n) ∧
      (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (relax^[n]) w - 1 < ε) :=
  ⟨fun n => admissible_error relax_admissible (le_of_lt hw) n,
    fun ε hε => admissible_recovery_time relax_admissible hw ε hε⟩

end RelaxRobust
