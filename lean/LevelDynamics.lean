/-
LevelDynamics.lean —— **P6 的动力学一半：水平的维持与恢复时间 $\\tau$**（第 117 轮）

**背景（承接第 113／116 轮）**：
  · P6 此前只有**静态一半**（`MaintenanceMargin.margin`：距离翻转还有多少余量）；
  · 第 116 轮把"第二层"归结为**在自由参数 $w$ 上选取一个值的原则**，并留下**唯一缺口**：
    **"为什么选自洽原理（$w=1$），而不是别的破缺原则（如 $w=2$）？"**
本件用一个**显式声明的**最小动力学回答它的一半。

**模型（⚠ 建模选择，不是导出）**：**与自身倒数做对称平均**的松弛
$$

\\mathrm{relax}(w)\\;:=\\;\\frac{w+\\dfrac{1}{w}}{2}.

$$

**结果（机检）**：
  · `relax_fixed_iff`：**不动点恰为自洽宽度**（$\\mathrm{relax}\\,w=w\\iff w=1$，$w>0$）；
  · `one_le_relax`：一步之后必 $\\ge1$（AM–GM 形式）；`relax_lt_self`：$w>1$ 时严格下降；
    `one_lt_relax_of_lt_one`：$w<1$ 时一步**越过**到 $>1$；
  · `relax_error_halves`：$w\\ge1$ 时 $\\mathrm{relax}\\,w-1\\le\\frac{w-1}{2}$ —— **误差每步减半**；
  · `relax_iterate_error`：$n$ 步后 $\\big(\\mathrm{relax}^{[n]}w\\big)-1\\le\\dfrac{w-1}{2^{n}}$ —— **显式几何界**；
  · `recovery_time`（**$\\tau$ 的形式化**）：$\\forall\\varepsilon>0$，**存在 $N$**，使 $n\\ge N$ 后宽度误差 $<\\varepsilon$
    ⇒ 恢复时间 $\\tau=\\Theta(\\log_2\\frac{w-1}{\\varepsilon})$（**有界、可算**）。

**⇒ 对"唯一缺口"的作用（如实标注）**：在**这个**动力学下，自洽宽度 $w=1$ 是**全局吸引**的不动点
（$w=2$ **不是**不动点，会衰减到 $1$）——这**给出一条独立于"断言"的理由**。
**但**：松弛式本身是**被声明的**，故这只是把缺口**缩小**为：
"**为什么用与倒数做对称平均**（而不是别的松弛）"——**不是消除缺口**。

0 `sorry` / `0 axiom`。
-/
import LevelSelection
import ReadoutExistence

open scoped Real

namespace LevelDynamics

open ReadoutExistence (thetaOf)

/-- **松弛动力学（建模选择）**：与自身倒数做**对称平均**。 -/
noncomputable def relax (w : ℝ) : ℝ := (w + 1 / w) / 2

/-- **（不动点＝自洽宽度）** $w>0$：$\\mathrm{relax}\\,w=w\\iff w=1$。 -/
theorem relax_fixed_iff {w : ℝ} (hw : 0 < w) : relax w = w ↔ w = 1 := by
  constructor
  · intro h
    have h' : 1 / w = w := by
      unfold relax at h
      linarith
    exact ReadoutExistence.R_fixed_unique hw h'
  · intro h
    rw [h]
    unfold relax
    norm_num

/-- **（一步之后必 $\\ge1$）** AM–GM 形式：$1\\le\\mathrm{relax}\\,w$。 -/
theorem one_le_relax (w : ℝ) (hw : 0 < w) : 1 ≤ relax w := by
  have h2 : w + 1 / w - 2 = (w - 1) ^ 2 / w := by
    field_simp
    ring
  have h3 : 0 ≤ (w - 1) ^ 2 / w := div_nonneg (sq_nonneg _) hw.le
  unfold relax
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- **（$w>1$ 时严格下降）**。 -/
theorem relax_lt_self {w : ℝ} (hw : 1 < w) : relax w < w := by
  have hw0 : 0 < w := by linarith
  have h : 1 / w < w := by
    rw [div_lt_iff₀ hw0]
    nlinarith
  unfold relax
  rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- **（$0<w<1$ 时一步越过到 $>1$）**。 -/
theorem one_lt_relax_of_lt_one {w : ℝ} (hw : 0 < w) (h1 : w < 1) : 1 < relax w := by
  rcases lt_or_eq_of_le (one_le_relax w hw) with h | h
  · exact h
  · exfalso
    have hsum : w + 1 / w = 2 := by
      unfold relax at h
      linarith
    have hsq : (w - 1) ^ 2 = 0 := by
      have h3 : w + 1 / w - 2 = (w - 1) ^ 2 / w := by
        field_simp
        ring
      have h4 : (w - 1) ^ 2 / w = 0 := by linarith
      exact (div_eq_zero_iff).mp h4 |>.resolve_right hw.ne'
    have : w - 1 = 0 := sq_eq_zero_iff.mp hsq
    linarith

/-- **（误差每步减半）** $w\\ge1\\Rightarrow\\mathrm{relax}\\,w-1\\le\\dfrac{w-1}{2}$。 -/
theorem relax_error_halves {w : ℝ} (hw : 1 ≤ w) : relax w - 1 ≤ (w - 1) / 2 := by
  have hw0 : 0 < w := by linarith
  have h2 : relax w - 1 = (w - 1) ^ 2 / (2 * w) := by
    unfold relax
    field_simp
    ring
  rw [h2, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * w)]
  have h3 : (w - 1) / 2 * (2 * w) = (w - 1) * w := by
    field_simp
  rw [h3]
  nlinarith

/-- **（不变性）** $w\\ge1$ 时，迭代仍在 $\\ge1$ 一侧。 -/
theorem one_le_iterate (w : ℝ) (hw : 1 ≤ w) : ∀ n : ℕ, 1 ≤ (relax^[n]) w := by
  intro n
  induction n with
  | zero => simpa using hw
  | succ k ih =>
      have hpos : 0 < (relax^[k]) w := by linarith
      have hnext : 1 ≤ relax ((relax^[k]) w) := one_le_relax ((relax^[k]) w) hpos
      have hidx : (relax^[k + 1]) w = relax ((relax^[k]) w) := by
        rw [Function.iterate_succ_apply']
      rwa [hidx]

/-- **（$\\tau$ 的显式界）** $n$ 步后误差 $\\le\\dfrac{w-1}{2^{n}}$（$w\\ge1$）。 -/
theorem relax_iterate_error (w : ℝ) (hw : 1 ≤ w) :
    ∀ n : ℕ, (relax^[n]) w - 1 ≤ (w - 1) / 2 ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
      have hge : 1 ≤ (relax^[k]) w := one_le_iterate w hw k
      have hstep : relax ((relax^[k]) w) - 1 ≤ ((relax^[k]) w - 1) / 2 :=
        relax_error_halves hge
      have hdiv : ((relax^[k]) w - 1) / 2 ≤ ((w - 1) / 2 ^ k) / 2 :=
        div_le_div_of_nonneg_right ih (by norm_num)
      have hpow : ((w - 1) / 2 ^ k) / 2 = (w - 1) / 2 ^ (k + 1) := by
        rw [pow_succ, div_div]
      have hidx : (relax^[k + 1]) w = relax ((relax^[k]) w) := by
        rw [Function.iterate_succ_apply']
      rw [hidx]
      linarith

/-- **（$\\tau$ 的形式化 · 恢复时间）** 任意精度 $\\varepsilon>0$，**存在有限 $N$**，
使 $n\\ge N$ 后宽度误差 $<\\varepsilon$。 -/
theorem recovery_time (w : ℝ) (hw : 1 < w) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (relax^[n]) w - 1 < ε := by
  have hw1 : 1 ≤ w := le_of_lt hw
  have hx : 0 < (w - 1) / ε := div_pos (by linarith) hε
  obtain ⟨N, hN⟩ := exists_nat_gt ((w - 1) / ε)
  have hNpow : (w - 1) / ε < (2 : ℝ) ^ N := by
    have h1 : (N : ℝ) < (2 : ℝ) ^ N := by
      exact_mod_cast Nat.lt_pow_self (by norm_num : 1 < 2)
    linarith
  refine ⟨N, ?_⟩
  intro n hn
  have hb := relax_iterate_error w hw1 n
  have hmono : (w - 1) / 2 ^ n ≤ (w - 1) / 2 ^ N :=
    div_le_div_of_nonneg_left (by linarith) (by positivity)
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn)
  have hlt : (w - 1) / 2 ^ N < ε := by
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 ^ N)]
    have := (div_lt_iff₀ hε).mp hNpow
    linarith
  linarith

/-- **（P6-动力学证书）** 一次打包：不动点＝自洽宽度 · 一步后 $\\ge1$ · $>1$ 时严格下降 ·
误差每步减半 · $n$ 步显式界 · **恢复时间有限**。 -/
theorem p6_dynamics_certificate :
    (∀ w : ℝ, 0 < w → (relax w = w ↔ w = 1)) ∧
      (∀ w : ℝ, 0 < w → 1 ≤ relax w) ∧
      (∀ w : ℝ, 1 < w → relax w < w) ∧
      (∀ w : ℝ, 1 ≤ w → relax w - 1 ≤ (w - 1) / 2) ∧
      (∀ w : ℝ, 1 ≤ w → ∀ n : ℕ, (relax^[n]) w - 1 ≤ (w - 1) / 2 ^ n) ∧
      (∀ w : ℝ, 1 < w → ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (relax^[n]) w - 1 < ε) :=
  ⟨fun w hw => relax_fixed_iff hw,
    fun w hw => one_le_relax w hw,
    fun w hw => relax_lt_self hw,
    fun w hw => relax_error_halves hw,
    fun w hw n => relax_iterate_error w hw n,
    fun w hw ε hε => recovery_time w hw ε hε⟩

end LevelDynamics
