import Mathlib

/-!
# 边界认知假说 · 三命题的 Lean 形式化
对应 `docs/边界认知假说·边界概念的数学形式.md` §3。

命题一（κ*）：边界势 `V(κ)=c₀κ + απ²/(3κ)` 的最小作用量锐度
  `κ* = π·√(α/(3c₀))` 是 V 的临界点（`V'(κ*)=0`）。

命题二（σ*=1）：张力 `σ* = π²α/(3C₀)`；在自洽条件 `α = 3C₀/π²` 下 `σ*=1`。

命题三（dE/dt≡0）：EOM 广义力 `F(κ)=απ²/(3κ²)−c₀` 是势梯度的负值，
  故能量 `E=½Iκ̇²+V(κ)` 沿 EOM 的时间导数为零（Noether 守恒的代数芯）。

全部命题只用实数域的域运算与 `deriv`，除 `π ≠ 0`、参数为正外无其他假设。
-/

noncomputable section

open scoped Real
open MeasureTheory

namespace BoundaryTheory

/-- 边界势 V(κ) = c₀·κ + α·π²/(3·κ)（κ ≠ 0）。写成 κ⁻¹ 形式便于求导。 -/
def V (c₀ α : ℝ) (κ : ℝ) : ℝ := c₀ * κ + (α * (Real.pi ^ 2) / 3) / κ

/-- 最小作用量边界锐度 κ* = π·√(α/(3c₀))。 -/
def kappaStar (c₀ α : ℝ) : ℝ := Real.pi * Real.sqrt (α / (3 * c₀))

/-- 张力 σ* = π²·α/(3·C₀)。 -/
def sigmaStar (α C₀ : ℝ) : ℝ := (Real.pi ^ 2) * α / (3 * C₀)

/-- EOM 广义力 F(κ) = α·π²/(3·κ²) − c₀（即 −V′）。 -/
def force (c₀ α : ℝ) (κ : ℝ) : ℝ := α * (Real.pi ^ 2) / (3 * κ ^ 2) - c₀

/-! ## 命题一 · 代数芯：κ* 满足平方恒等式与平衡方程 -/

theorem kappaStar_sq (hc₀ : 0 < c₀) (hα : 0 ≤ α) :
    (kappaStar c₀ α) ^ 2 = (Real.pi ^ 2) * α / (3 * c₀) := by
  rw [kappaStar]
  have hnonneg : 0 ≤ α / (3 * c₀) := by positivity
  rw [mul_pow, Real.sq_sqrt hnonneg]
  field_simp [hc₀.ne']

/-- κ* 处「维持成本梯度 = 不确定代价梯度」：c₀ = απ²/(3κ*²)，即 V'(κ*)=0 的代数形式。 -/
theorem kappaStar_balance (hc₀ : 0 < c₀) (hα : 0 < α) :
    c₀ = α * (Real.pi ^ 2) / (3 * (kappaStar c₀ α) ^ 2) := by
  rw [kappaStar_sq hc₀ (le_of_lt hα)]
  field_simp [hc₀.ne', hα.ne', Real.pi_ne_zero]

/-! ## 命题一 · 全导数：V'(κ*) = 0 -/

theorem deriv_V_kappaStar (hc₀ : 0 < c₀) (hα : 0 < α) :
    deriv (fun κ : ℝ => V c₀ α κ) (kappaStar c₀ α) = 0 := by
  have hκ : kappaStar c₀ α ≠ 0 := by
    rw [kappaStar]
    exact mul_ne_zero Real.pi_ne_zero (ne_of_gt (Real.sqrt_pos.2 (by positivity)))
  unfold V
  change deriv ((fun κ : ℝ => c₀ * κ) + (fun κ : ℝ => (α * (Real.pi ^ 2) / 3) / κ))
      (kappaStar c₀ α) = 0
  rw [deriv_add]
  · rw [deriv_const_mul_id, deriv_const_div_id]
    rw [kappaStar_sq hc₀ (le_of_lt hα)]
    field_simp [hc₀.ne', hα.ne', Real.pi_ne_zero, pow_ne_zero 2 Real.pi_ne_zero]
    ring
  · fun_prop
  · fun_prop

/-! ## 命题二 · σ* = 1（自洽条件 α = 3C₀/π²） -/

/-- 一般参数下张力公式（无任何规范化）：σ* = π²α/(3C₀)，对任意 α、C₀ 成立。 -/
theorem sigmaStar_general (α C₀ : ℝ) :
    sigmaStar α C₀ = (Real.pi ^ 2) * α / (3 * C₀) := by
  rfl

/-- 临界条件 σ*=1 等价于无量纲平衡 π²α = 3C₀（不特设数值，量纲内禀）。 -/
theorem sigmaStar_eq_one_iff (α C₀ : ℝ) (hC₀ : C₀ ≠ 0) :
    sigmaStar α C₀ = 1 ↔ (Real.pi ^ 2) * α = 3 * C₀ := by
  rw [sigmaStar_general]
  constructor
  · intro h
    field_simp [hC₀] at h
    exact h
  · intro h
    rw [h]
    field_simp [hC₀]

/-- 规范参数（α=3C₀/π²）下 σ* 数值等于 1 —— 「规范值」层级，非一般律。
    注：c₀=C₀=1 是单位选择；量纲只通过无量纲比 π²α/(3C₀) 出现。 -/
theorem sigmaStar_eq_one (hC₀ : C₀ ≠ 0) :
    sigmaStar (3 * C₀ / (Real.pi ^ 2)) C₀ = 1 := by
  rw [sigmaStar_general]
  field_simp [hC₀, Real.pi_ne_zero, pow_ne_zero 2 Real.pi_ne_zero]

/-! ## 命题三 · Noether 守恒的代数芯：广义力 = −∇V，能量括号为零 -/

theorem force_is_neg_gradient (c₀ α κ : ℝ) :
    force c₀ α κ = -(c₀ - α * (Real.pi ^ 2) / (3 * κ ^ 2)) := by
  rw [force]
  ring_nf

/-- 能量括号（dE/dt 的代数因子）恒为零：F + V′ = 0。 -/
theorem energy_bracket_zero (c₀ α κ : ℝ) :
    force c₀ α κ + (c₀ - α * (Real.pi ^ 2) / (3 * κ ^ 2)) = 0 := by
  rw [force]
  ring_nf

/-! ## 解析严密性 · §3.2′ 积分常数 C_H 的收敛性（P4 补丁）

`C_H = ∫_{-∞}^{+∞} h(σ(z)) dz = π²/3` 在推导时隐含 `z ∈ ℝ`。此处把「无穷积分收敛」
（即 `entropyDensity` 在 ℝ 上可积）作为引理严格引入，再谈常数取值。 -/

/-- 二值归属逐点 Shannon 熵 h(p) = -p log p - (1-p) log(1-p)，p ∈ (0,1)。 -/
def hbin (p : ℝ) : ℝ := -p * Real.log p - (1 - p) * Real.log (1 - p)

/-- logistic 归属场 σ(z) = 1/(1+e^{-z})。 -/
def sig (z : ℝ) : ℝ := 1 / (1 + Real.exp (-z))

/-- 边界熵密度 z ↦ h(σ(z))。 -/
def entropyDensity (z : ℝ) : ℝ := hbin (sig z)

/-- h 的对称性：h(p) = h(1-p)。 -/
theorem hbin_symm (p : ℝ) : hbin (1 - p) = hbin p := by
  unfold hbin
  ring_nf

/-- logistic 反对称：σ(-z) = 1 - σ(z)。 -/
theorem sig_neg (z : ℝ) : sig (-z) = 1 - sig z := by
  unfold sig
  rw [Real.exp_neg]
  field_simp [Real.exp_ne_zero]
  ring

/-- 边界熵密度的偶性：h(σ(-z)) = h(σ(z))（积分域关于 0 对称的依据）。 -/
theorem entropyDensity_even (z : ℝ) : entropyDensity (-z) = entropyDensity z := by
  unfold entropyDensity
  rw [sig_neg, hbin_symm]

/-! ## §3.2′ 收敛性：逐条编译（P4 完全闭合） -/

/-- logistic 归属场取值于 (0,1)。 -/
theorem sig_pos (z : ℝ) : 0 < sig z := by
  unfold sig
  positivity

theorem sig_lt_one (z : ℝ) : sig z < 1 := by
  unfold sig
  exact (div_lt_one (by positivity : 0 < 1 + Real.exp (-z))).mpr
    (by linarith [Real.exp_pos (-z)])

/-- h 在 (0,1) 上非负。 -/
theorem hbin_nonneg (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) : 0 ≤ hbin p := by
  unfold hbin
  have hlogp : Real.log p ≤ 0 := Real.log_nonpos (le_of_lt hp0) (le_of_lt hp1)
  have hlog1p : Real.log (1 - p) ≤ 0 := Real.log_nonpos (by positivity) (by linarith)
  have h1 : 0 ≤ -p * Real.log p := by
    exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (le_of_lt hp0)) hlogp
  have h2 : 0 ≤ -(1 - p) * Real.log (1 - p) := by
    exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (by positivity)) hlog1p
  linarith

theorem entropyDensity_nonneg (z : ℝ) : 0 ≤ entropyDensity z := by
  unfold entropyDensity
  exact hbin_nonneg (sig z) (sig_pos z) (sig_lt_one z)

/-- 对数界一：-log(1-q) ≤ q/(1-q)，q ∈ [0,1)。 -/
theorem neg_log_one_sub_le_div (q : ℝ) (_hq0 : 0 ≤ q) (hq1 : q < 1) :
    -Real.log (1 - q) ≤ q / (1 - q) := by
  have h1q : 0 < 1 - q := by linarith
  have hx : 0 < (1 - q)⁻¹ := inv_pos.2 h1q
  have h := Real.log_le_sub_one_of_pos hx
  rw [Real.log_inv] at h
  have h' : (1 - q)⁻¹ - 1 = q / (1 - q) := by
    field_simp [h1q.ne']
    ring
  rwa [h'] at h

/-- 对数界二：-q·log q ≤ 2√q，q ∈ (0,1]。 -/
theorem neg_q_mul_log_q_le (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    -q * Real.log q ≤ 2 * Real.sqrt q := by
  have hsq0 : 0 < Real.sqrt q := Real.sqrt_pos.2 hq0
  have hsq1 : Real.sqrt q ≤ 1 := by
    simpa [Real.sqrt_one] using (Real.sqrt_le_sqrt hq1)
  have hlt : |Real.sqrt q * Real.log (Real.sqrt q)| < 1 := by
    simpa [mul_comm] using (Real.abs_log_mul_self_lt (Real.sqrt q) hsq0 hsq1)
  have hneg : Real.log (Real.sqrt q) ≤ 0 := Real.log_nonpos (le_of_lt hsq0) hsq1
  have hnonpos : Real.sqrt q * Real.log (Real.sqrt q) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt hsq0) hneg
  have habs : -(Real.sqrt q) * Real.log (Real.sqrt q) < 1 := by
    rw [abs_of_nonpos hnonpos] at hlt
    simpa using hlt
  have hlogq : Real.log q = 2 * Real.log (Real.sqrt q) := by
    calc
      Real.log q = Real.log ((Real.sqrt q) ^ 2) :=
        congrArg Real.log (Real.sq_sqrt (le_of_lt hq0)).symm
      _ = 2 * Real.log (Real.sqrt q) := by
        simpa using (Real.log_pow (Real.sqrt q) 2)
  calc
    -q * Real.log q = -q * (2 * Real.log (Real.sqrt q)) := by rw [hlogq]
    _ = 2 * Real.sqrt q * (-(Real.sqrt q) * Real.log (Real.sqrt q)) := by
        nlinarith [Real.sq_sqrt (le_of_lt hq0)]
    _ ≤ 2 * Real.sqrt q * 1 := by
        gcongr
    _ = 2 * Real.sqrt q := by ring

/-- 指数衰减（z ≥ 0 半轴）：h(σ(z)) ≤ 3·e^{-z/2}。 -/
theorem entropyDensity_decay_of_nonneg (hz : 0 ≤ z) :
    entropyDensity z ≤ 3 * Real.exp (-(1 / 2) * z) := by
  unfold entropyDensity hbin
  have hsig_ge : 1 / 2 ≤ sig z := by
    unfold sig
    have h : Real.exp (-z) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    exact one_div_le_one_div_of_le (by positivity : 0 < 1 + Real.exp (-z)) (by linarith)
  have hq0 : 0 ≤ 1 - sig z := by linarith [sig_lt_one z]
  have hqlt1 : 1 - sig z < 1 := by linarith [sig_pos z]
  have hq_le_exp : 1 - sig z ≤ Real.exp (-z) := by
    unfold sig
    have hpos : 0 < Real.exp (-z) := Real.exp_pos _
    have : 1 - 1 / (1 + Real.exp (-z)) ≤ Real.exp (-z) := by
      field_simp [ne_of_gt hpos]
      nlinarith [sq_nonneg (Real.exp (-z))]
    exact this
  have h1 : -(sig z) * Real.log (sig z) ≤ 1 - sig z := by
    have hlog : -Real.log (sig z) ≤ (1 - sig z) / (sig z) := by
      simpa using (neg_log_one_sub_le_div (1 - sig z) hq0 hqlt1)
    have hsig_pos : 0 < sig z := sig_pos z
    have hmul := mul_le_mul_of_nonneg_right hlog (le_of_lt hsig_pos)
    have h1' : -Real.log (sig z) * sig z = -(sig z) * Real.log (sig z) := by ring
    have h2' : ((1 - sig z) / (sig z)) * sig z = 1 - sig z := by
      field_simp [ne_of_gt hsig_pos]
    rw [h1', h2'] at hmul
    exact hmul
  have h2 : -(1 - sig z) * Real.log (1 - sig z) ≤ 2 * Real.sqrt (1 - sig z) := by
    by_cases hqz : 1 - sig z = 0
    · simp [hqz]
    · exact neg_q_mul_log_q_le (1 - sig z) (by positivity) (le_of_lt hqlt1)
  have hq_le_sqrt : 1 - sig z ≤ Real.sqrt (1 - sig z) := by
    have hsqrt_le_one : Real.sqrt (1 - sig z) ≤ 1 := by
      simpa [Real.sqrt_one] using (Real.sqrt_le_sqrt (le_of_lt hqlt1))
    have hsqrt_nonneg : 0 ≤ Real.sqrt (1 - sig z) := Real.sqrt_nonneg _
    have hsq_le : Real.sqrt (1 - sig z) ^ 2 ≤ Real.sqrt (1 - sig z) := by
      simpa [sq] using (mul_le_mul_of_nonneg_right hsqrt_le_one hsqrt_nonneg)
    simpa [Real.sq_sqrt hq0] using hsq_le
  have hsum : -(sig z) * Real.log (sig z) - (1 - sig z) * Real.log (1 - sig z)
      ≤ 3 * Real.sqrt (1 - sig z) := by
    nlinarith [h1, h2, hq_le_sqrt]
  have hsqrt_le_exp : Real.sqrt (1 - sig z) ≤ Real.exp (-(1 / 2) * z) := by
    have hsqrt_le : Real.sqrt (1 - sig z) ≤ Real.sqrt (Real.exp (-z)) :=
      Real.sqrt_le_sqrt hq_le_exp
    have hhalf : Real.sqrt (Real.exp (-z)) = Real.exp (-z / 2) := (Real.exp_half (-z)).symm
    have hconv : Real.exp (-z / 2) = Real.exp (-(1 / 2) * z) := by
      exact congrArg Real.exp (by ring : -z / 2 = -(1 / 2) * z)
    rw [hhalf, hconv] at hsqrt_le
    exact hsqrt_le
  nlinarith

/-- 指数衰减（全局）：h(σ(z)) ≤ 3·e^{-|z|/2}。 -/
theorem entropyDensity_decay (z : ℝ) :
    entropyDensity z ≤ 3 * Real.exp (-|z| / 2) := by
  by_cases hz : 0 ≤ z
  · have hzabs : |z| = z := abs_of_nonneg hz
    rw [hzabs]
    have h := entropyDensity_decay_of_nonneg hz
    convert h using 1
    ring_nf
  · have hzneg : 0 ≤ -z := by linarith
    have hzabs : |z| = -z := abs_of_neg (by linarith)
    rw [← entropyDensity_even, hzabs]
    have h := entropyDensity_decay_of_nonneg hzneg
    convert h using 1
    ring_nf

/-- 边界熵密度连续（h 与 σ 均连续，σ 值域 ⊆ (0,1)）。 -/
theorem entropyDensity_continuous : Continuous entropyDensity := by
  unfold entropyDensity
  have hbin_contOn : ContinuousOn hbin (Set.Ioo 0 1) := by
    unfold hbin
    have hlog : ContinuousOn Real.log (Set.Ioi 0) :=
      Real.continuousOn_log.mono (by intro x hx; exact ne_of_gt hx)
    have hlog_id : ContinuousOn (fun p : ℝ => Real.log p) (Set.Ioo 0 1) :=
      hlog.mono (by intro x hx; exact hx.1)
    have hlog_sub : ContinuousOn (fun p : ℝ => Real.log (1 - p)) (Set.Ioo 0 1) :=
      hlog.comp (continuousOn_const.sub continuousOn_id) (by intro x hx; exact sub_pos.mpr hx.2)
    have h1 : ContinuousOn (fun p : ℝ => -p * Real.log p) (Set.Ioo 0 1) :=
      continuousOn_id.neg.mul hlog_id
    have h2 : ContinuousOn (fun p : ℝ => (1 - p) * Real.log (1 - p)) (Set.Ioo 0 1) :=
      (continuousOn_const.sub continuousOn_id).mul hlog_sub
    exact h1.sub h2
  have sig_cont : Continuous sig := by
    unfold sig
    have hfun : (fun z : ℝ => 1 / (1 + Real.exp (-z))) = (fun z : ℝ => (1 + Real.exp (-z))⁻¹) := by
      funext z
      rw [one_div]
    rw [hfun]
    exact Continuous.inv₀ (continuous_const.add (Real.continuous_exp.comp continuous_neg))
      (fun z => by positivity)
  have hst : Set.MapsTo sig Set.univ (Set.Ioo 0 1) := by
    intro z _
    exact ⟨sig_pos z, sig_lt_one z⟩
  have hcomp : ContinuousOn (fun z => hbin (sig z)) Set.univ :=
    ContinuousOn.comp hbin_contOn sig_cont.continuousOn hst
  exact continuousOn_univ.mp hcomp

/-- §3.2′ 收敛性引理：边界熵密度在 ℝ 上可积（C_H 良定义）。 -/
theorem boundary_entropy_integrable :
    MeasureTheory.Integrable entropyDensity := by
  have hLI : MeasureTheory.LocallyIntegrable (entropyDensity : ℝ → ℝ) :=
    entropyDensity_continuous.locallyIntegrable
  refine MeasureTheory.LocallyIntegrable.integrable_of_isBigO_atTop_of_norm_isNegInvariant
    (g := fun x : ℝ => Real.exp (-(1 / 2) * x)) hLI ?_ ?_ ?_
  · -- 偶性：‖h(σ(-z))‖ = ‖h(σ(z))‖
    exact Filter.Eventually.of_forall (fun z => by simp [entropyDensity_even z])
  · -- f =O[atTop] exp(-(1/2) z)
    refine Asymptotics.isBigO_iff.2 ⟨3, ?_⟩
    filter_upwards [Filter.eventually_ge_atTop 0] with z hz
    rw [Real.norm_of_nonneg (entropyDensity_nonneg z),
        Real.norm_of_nonneg (Real.exp_pos _).le]
    exact entropyDensity_decay_of_nonneg hz
  · -- exp(-(1/2) z) 在 atTop 可积
    exact ⟨Set.Ioi 0, Filter.Ioi_mem_atTop 0,
      exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1 / 2)⟩

/-! ## §3.2′ 值机验（P4 补丁 · 2026-08-20 新增，D15 授权追加）

论文定理 4.6：C_H = π²/3。本段落地其「级数侧」机器证明：
- 引理 A：∫₀¹ xⁿ dx = 1/(n+1)（幂积分，微积分基本定理）
- 引理 B：Σ' n, 1/(n+1)² = π²/6（由 mathlib `hasSum_zeta_two`（Basel）重索引）

积分-级数连接（∫₀¹(-ln x)/(1-x) dx = Σ 1/n²）与 logit 换元
（C_H = 2∫₀¹(-ln p)/(1-p)dp）为后续增量工作。
-/

/-- 引理 A：∫₀¹ xⁿ dx = 1/(n+1)。 -/
theorem integral_pow_zero_one (n : ℕ) :
    ∫ x in (0 : ℝ)..1, (x : ℝ) ^ n = 1 / ((n : ℝ) + 1) := by
  let F : ℝ → ℝ := fun x => (x : ℝ) ^ (n + 1) / ((n : ℝ) + 1)
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt F ((x : ℝ) ^ n) x := by
    intro x hx
    dsimp [F]
    have h1 : HasDerivAt (fun x : ℝ => (x : ℝ) ^ (n + 1)) (((n : ℝ) + 1) * (x : ℝ) ^ n) x := by
      simpa [pow_succ] using (hasDerivAt_pow (n + 1) x)
    have h2 : HasDerivAt (fun x : ℝ => (x : ℝ) ^ (n + 1) / ((n : ℝ) + 1))
        (((n : ℝ) + 1) * (x : ℝ) ^ n / ((n : ℝ) + 1)) x := h1.div_const ((n : ℝ) + 1)
    convert h2 using 1
    field_simp
  have hint : IntervalIntegrable (fun x : ℝ => (x : ℝ) ^ n) volume (0 : ℝ) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  calc
    ∫ x in (0 : ℝ)..1, (x : ℝ) ^ n
        = F 1 - F 0 := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    _ = 1 / ((n : ℝ) + 1) := by
      dsimp [F]
      simp [pow_succ]

/-- 引理 B：Σ' n, 1/(n+1)² = π²/6（ζ(2) 的平移重索引，Basel 由 mathlib 提供）。 -/
theorem tsum_inv_succ_sq_eq_pi_sq_div_six :
    (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2) = π ^ 2 / 6 := by
  have hz : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) (π ^ 2 / 6) := hasSum_zeta_two
  let f : ℕ → ℝ := fun m => (1 : ℝ) / (m : ℝ) ^ 2
  have hf : HasSum f (π ^ 2 / 6) := by
    simpa [f] using hz
  have hshift : HasSum (fun n : ℕ => f (n + 1)) ((π ^ 2 / 6) - f 0) := by
    rw [hasSum_nat_add_iff (k := 1) (f := f)]
    simp only [Finset.range_one, Finset.sum_singleton]
    simpa using hf
  have htarget : (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2) = (∑' n : ℕ, f (n + 1)) := by
    apply tsum_congr
    intro n
    simp [f, Nat.cast_add, Nat.cast_one]
  calc
    (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2) = (∑' n : ℕ, f (n + 1)) := htarget
    _ = (π ^ 2 / 6) - f 0 := hshift.tsum_eq
    _ = π ^ 2 / 6 := by simp [f]

/-! ## §3.2′ 值机验（P4 补丁 · 2026-08-20 新增 · 阶段 1）

`C_H = π²/3` 积分侧证明 · 阶段 1（幂·对数母积分）：

    ∫₀¹ xⁿ·log x dx = −1/(n+1)²

策略（mathlib `integral_log` 同款模板）：取原函数

    F(x) = (n+1)⁻¹·(xⁿ⁺¹·log x) − (n+1)⁻²·xⁿ⁺¹

其导数在开区间 (0,1) 上恰为 xⁿ·log x（乘积法则 + log' = x⁻¹，即分部积分的
机器版本）；log 在 0 处的奇点用「端点趋近 FTC」`integral_eq_sub_of_hasDerivAt_of_tendsto`
处理——F 在 0⁺ 的极限为 0（`tendsto_log_mul_rpow_nhdsGT_zero`：xⁿ⁺¹·log x → 0），
在 1⁻ 处 F 连续（值为 −1/(n+1)²）。该引理是阶段 2（级数-积分交换）的母项。
-/

/-- 阶段 1：∫₀¹ xⁿ·log x dx = −1/(n+1)²（幂·对数母积分，log 奇点经端点趋近处理）。 -/
theorem integral_pow_mul_log_zero_one (n : ℕ) :
    ∫ x in (0 : ℝ)..1, (x : ℝ) ^ n * Real.log x = -1 / ((n : ℝ) + 1) ^ 2 := by
  let F : ℝ → ℝ := fun x => ((n : ℝ) + 1)⁻¹ * (x ^ (n + 1) * Real.log x)
    - ((n : ℝ) + 1)⁻¹ ^ 2 * x ^ (n + 1)
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt F ((x : ℝ) ^ n * Real.log x) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx.1
    have hxpowmul : x ^ (n + 1) * x⁻¹ = x ^ n := by
      rw [pow_succ]
      simp [mul_assoc, mul_inv_cancel₀ hx0]
    have hpow : HasDerivAt (fun y : ℝ => y ^ (n + 1)) (((n : ℝ) + 1) * x ^ n) x := by
      simpa using (hasDerivAt_pow (n + 1) x)
    have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx0
    have hprod : HasDerivAt (fun y : ℝ => y ^ (n + 1) * Real.log y)
        (((n : ℝ) + 1) * x ^ n * Real.log x + x ^ (n + 1) * x⁻¹) x := by
      exact hpow.mul hlog
    have hF1 : HasDerivAt (fun y : ℝ => ((n : ℝ) + 1)⁻¹ * (y ^ (n + 1) * Real.log y))
        (((n : ℝ) + 1)⁻¹ * (((n : ℝ) + 1) * x ^ n * Real.log x + x ^ (n + 1) * x⁻¹)) x :=
      hprod.const_mul ((n : ℝ) + 1)⁻¹
    have hF2 : HasDerivAt (fun y : ℝ => ((n : ℝ) + 1)⁻¹ ^ 2 * y ^ (n + 1))
        (((n : ℝ) + 1)⁻¹ ^ 2 * (((n : ℝ) + 1) * x ^ n)) x :=
      hpow.const_mul (((n : ℝ) + 1)⁻¹ ^ 2)
    have hF : HasDerivAt F
        (((n : ℝ) + 1)⁻¹ * (((n : ℝ) + 1) * x ^ n * Real.log x + x ^ (n + 1) * x⁻¹)
          - ((n : ℝ) + 1)⁻¹ ^ 2 * (((n : ℝ) + 1) * x ^ n)) x := hF1.sub hF2
    convert hF using 1
    rw [hxpowmul]
    field_simp [show ((n : ℝ) + 1) ≠ 0 by positivity]
    ring
  have hint : IntervalIntegrable (fun x : ℝ => x ^ n * Real.log x) volume (0 : ℝ) 1 := by
    have hlogI : IntervalIntegrable Real.log volume (0 : ℝ) 1 :=
      intervalIntegral.intervalIntegrable_log'
    have hxI : ContinuousOn (fun x : ℝ => x ^ n) (Set.uIcc (0 : ℝ) 1) := by fun_prop
    exact hlogI.continuousOn_mul hxI
  have ha : Filter.Tendsto F (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hlogmul : Filter.Tendsto (fun x : ℝ => x ^ (n + 1) * Real.log x)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have hbase : Filter.Tendsto (fun x : ℝ => Real.log x * x ^ ((n : ℝ) + 1))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
        tendsto_log_mul_rpow_nhdsGT_zero (by positivity : 0 < (n : ℝ) + 1)
      simpa [mul_comm, ← Real.rpow_natCast] using hbase
    have hxpow : Filter.Tendsto (fun x : ℝ => x ^ (n + 1))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have hc : ContinuousAt (fun x : ℝ => x ^ (n + 1)) (0 : ℝ) := by fun_prop
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    have h1 : Filter.Tendsto (fun x : ℝ => ((n : ℝ) + 1)⁻¹ * (x ^ (n + 1) * Real.log x))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (((n : ℝ) + 1)⁻¹ * 0)) :=
      hlogmul.const_mul ((n : ℝ) + 1)⁻¹
    have h2 : Filter.Tendsto (fun x : ℝ => ((n : ℝ) + 1)⁻¹ ^ 2 * x ^ (n + 1))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (((n : ℝ) + 1)⁻¹ ^ 2 * 0)) :=
      hxpow.const_mul (((n : ℝ) + 1)⁻¹ ^ 2)
    dsimp [F]
    convert h1.sub h2 using 1
    simp
  have hb : Filter.Tendsto F (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds (F 1)) := by
    have hlogc : ContinuousAt Real.log (1 : ℝ) :=
      Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)
    have hpowc : ContinuousAt (fun x : ℝ => x ^ (n + 1)) (1 : ℝ) := by fun_prop
    have hc : ContinuousAt (fun x : ℝ => ((n : ℝ) + 1)⁻¹ * (x ^ (n + 1) * Real.log x)
        - ((n : ℝ) + 1)⁻¹ ^ 2 * x ^ (n + 1)) (1 : ℝ) := by
      exact (continuousAt_const.mul (hpowc.mul hlogc)).sub (continuousAt_const.mul hpowc)
    simpa [F] using hc.tendsto.mono_left nhdsWithin_le_nhds
  calc
    ∫ x in (0 : ℝ)..1, (x : ℝ) ^ n * Real.log x = F 1 - 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (f := F) (a := (0 : ℝ))
        (b := 1) (fa := 0) (fb := F 1) (hab := by norm_num) hderiv hint ha hb
    _ = -1 / ((n : ℝ) + 1) ^ 2 := by
      dsimp [F]
      simp only [one_pow, Real.log_one, mul_zero, mul_one, zero_sub, sub_zero]
      rw [neg_div, one_div, inv_pow]

/-! ## §3.2′ 值机验（P4 补丁 · 2026-08-20 新增 · 阶段 2）

`C_H = π²/3` 积分侧证明 · 阶段 2（级数-积分交换）：

    ∫₀¹ (−ln x)/(1−x) dx = Σₙ 1/(n+1)² = π²/6

策略：在 (0,1) 内 1/(1−x) = Σₙ xⁿ（几何级数，`hasSum_geometric_of_norm_lt_one`），
故逐点 (−ln x)/(1−x) = Σₙ xⁿ·(−ln x)（`neg_log_div_one_sub_eq_tsum`）；
级数与积分交换用 `MeasureTheory.integral_tsum_of_summable_integral_norm`（控制收敛版）：
每项可积（阶段 1 的可积性，负号）且 Σₙ ∫₀¹‖xⁿ·(−ln x)‖ = Σₙ 1/(n+1)² = π²/6 < ∞
（`tsum_inv_succ_sq_eq_pi_sq_div_six`，Basel）。交换后逐项用阶段 1 闭式。
-/

/-- 逐点恒等式（几何级数）：x ∈ [0,1] 时 (−ln x)/(1−x) = Σ' n, xⁿ·(−ln x)。
端点处两侧均为 0（Lean 语义：ln 0 = 0、0/0 = 0、∑0 = 0），(0,1) 内为真几何级数。 -/
lemma neg_log_div_one_sub_eq_tsum {x : ℝ} (hx : x ∈ Set.uIcc (0 : ℝ) 1) :
    -Real.log x / (1 - x) = ∑' n : ℕ, x ^ n * (-Real.log x) := by
  have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hx
  rcases lt_or_eq_of_le hx'.1 with hx0 | hxeq0
  · rcases lt_or_eq_of_le hx'.2 with hx1 | hxeq1
    · have hxnorm : ‖x‖ < 1 := by rwa [Real.norm_of_nonneg (le_of_lt hx0)]
      have hsum : ∑' n : ℕ, x ^ n = (1 - x)⁻¹ := (hasSum_geometric_of_norm_lt_one hxnorm).tsum_eq
      calc
        -Real.log x / (1 - x) = (1 - x)⁻¹ * (-Real.log x) := by rw [div_eq_mul_inv, mul_comm]
        _ = (∑' n : ℕ, x ^ n) * (-Real.log x) := by rw [hsum]
        _ = ∑' n : ℕ, x ^ n * (-Real.log x) :=
          (tsum_mul_right (f := fun n : ℕ => x ^ n) (a := -Real.log x)).symm
    · subst x
      simp
  · subst x
    simp

/-- 阶段 2：∫₀¹ (−ln x)/(1−x) dx = π²/6（几何级数 + 级数-积分交换 + 阶段 1 闭式 + Basel）。 -/
theorem integral_neg_log_div_one_sub_zero_one :
    ∫ x in (0 : ℝ)..1, -Real.log x / (1 - x) = π ^ 2 / 6 := by
  have hnonneg : ∀ x ∈ Set.uIcc (0 : ℝ) 1, ∀ n : ℕ, 0 ≤ -(x ^ n * Real.log x) := by
    intro x hx n
    have hx0 : 0 ≤ x := by simpa using hx.1
    have hpow : 0 ≤ x ^ n := pow_nonneg hx0 n
    have hlog : Real.log x ≤ 0 := Real.log_nonpos hx0 (by simpa using hx.2)
    have hlog_nonneg : 0 ≤ -Real.log x := neg_nonneg.mpr hlog
    have hprod : 0 ≤ x ^ n * (-Real.log x) := mul_nonneg hpow hlog_nonneg
    simpa [mul_neg] using hprod
  have hf_int : ∀ n : ℕ, MeasureTheory.Integrable (fun x : ℝ => -(x ^ n * Real.log x))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    intro n
    have hlogI : IntervalIntegrable Real.log volume (0 : ℝ) 1 :=
      intervalIntegral.intervalIntegrable_log'
    have hxI : ContinuousOn (fun x : ℝ => x ^ n) (Set.uIcc (0 : ℝ) 1) := by fun_prop
    have hII : IntervalIntegrable (fun x : ℝ => x ^ n * Real.log x) volume (0 : ℝ) 1 :=
      hlogI.continuousOn_mul hxI
    have hII' : IntervalIntegrable (fun x : ℝ => -(x ^ n * Real.log x)) volume (0 : ℝ) 1 :=
      hII.neg
    change MeasureTheory.Integrable (fun x : ℝ => -(x ^ n * Real.log x))
      (volume.restrict (Set.Ioc (0 : ℝ) 1))
    exact hII'.1
  have hterm : ∀ n : ℕ, ∫ x in (0 : ℝ)..1, -(x ^ n * Real.log x) = (1 : ℝ) / ((n : ℝ) + 1) ^ 2 := by
    intro n
    calc
      ∫ x in (0 : ℝ)..1, -(x ^ n * Real.log x) = -∫ x in (0 : ℝ)..1, x ^ n * Real.log x := by
        rw [intervalIntegral.integral_neg]
      _ = -(-1 / ((n : ℝ) + 1) ^ 2) := by rw [integral_pow_mul_log_zero_one n]
      _ = (1 : ℝ) / ((n : ℝ) + 1) ^ 2 := by ring
  have hterm_norm : ∀ n : ℕ, ∫ x in (0 : ℝ)..1, ‖-(x ^ n * Real.log x)‖ = (1 : ℝ) / ((n : ℝ) + 1) ^ 2 := by
    intro n
    calc
      ∫ x in (0 : ℝ)..1, ‖-(x ^ n * Real.log x)‖ = ∫ x in (0 : ℝ)..1, -(x ^ n * Real.log x) := by
        apply intervalIntegral.integral_congr
        intro x hx
        change ‖-(x ^ n * Real.log x)‖ = -(x ^ n * Real.log x)
        rw [Real.norm_of_nonneg (hnonneg x hx n)]
      _ = (1 : ℝ) / ((n : ℝ) + 1) ^ 2 := hterm n
  have hsummable : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 2) := by
    let f : ℕ → ℝ := fun m => (1 : ℝ) / (m : ℝ) ^ 2
    have hf : HasSum f (π ^ 2 / 6) := by simpa [f] using hasSum_zeta_two
    have hshift : HasSum (fun n : ℕ => f (n + 1)) ((π ^ 2 / 6) - f 0) := by
      rw [hasSum_nat_add_iff (k := 1) (f := f)]
      simp only [Finset.range_one, Finset.sum_singleton]
      simpa using hf
    simpa [f, Nat.cast_add, Nat.cast_one] using hshift.summable
  have hF_sum : Summable
      (fun n : ℕ => ∫ x : ℝ, ‖-(x ^ n * Real.log x)‖ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
    have hint : ∀ n : ℕ,
        (∫ x : ℝ, ‖-(x ^ n * Real.log x)‖ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)))
          = (1 : ℝ) / ((n : ℝ) + 1) ^ 2 := by
      intro n
      rw [← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
      exact hterm_norm n
    exact hsummable.congr (fun n => (hint n).symm)
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm
    (μ := volume.restrict (Set.Ioc (0 : ℝ) 1)) (F := fun n x => -(x ^ n * Real.log x))
    hf_int hF_sum
  have hint_sum : ∫ x in (0 : ℝ)..1, ∑' n : ℕ, -(x ^ n * Real.log x) = π ^ 2 / 6 := by
    calc
      ∫ x in (0 : ℝ)..1, ∑' n : ℕ, -(x ^ n * Real.log x)
          = ∫ x : ℝ, ∑' n : ℕ, -(x ^ n * Real.log x) ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
            rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
      _ = ∑' n : ℕ, ∫ x : ℝ, -(x ^ n * Real.log x) ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
            hswap.symm
      _ = ∑' n : ℕ, ∫ x in (0 : ℝ)..1, -(x ^ n * Real.log x) := by
            apply tsum_congr
            intro n
            rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
      _ = ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2 := by
            apply tsum_congr
            intro n
            exact hterm n
      _ = π ^ 2 / 6 := tsum_inv_succ_sq_eq_pi_sq_div_six
  calc
    ∫ x in (0 : ℝ)..1, -Real.log x / (1 - x)
        = ∫ x in (0 : ℝ)..1, ∑' n : ℕ, x ^ n * (-Real.log x) := by
          apply intervalIntegral.integral_congr
          intro x hx
          exact neg_log_div_one_sub_eq_tsum hx
    _ = ∫ x in (0 : ℝ)..1, ∑' n : ℕ, -(x ^ n * Real.log x) := by
          apply intervalIntegral.integral_congr
          intro x hx
          apply tsum_congr
          intro n
          ring
    _ = π ^ 2 / 6 := hint_sum

/-! ## §3.2′ 值机验（P4 补丁 · 2026-08-20 新增 · 阶段 3）

`C_H = π²/3` 积分侧证明 · 阶段 3（logit 换元 + hbin 对称性）：

    ∫ℝ h(σ(z)) dz = 2·∫₀¹ (−ln p)/(1−p) dp

策略：有限区间 [−R,R] 上做严格换元（`integral_comp_mul_deriv'`，f=σ、f'=σ(1−σ)、
g(p)=hbin(p)/(p(1−p))——σ 的导数由 `sig_hasDerivAt` 给出），再令 R→∞ 取极限：
ℝ 侧由 `intervalIntegral_tendsto_integral`（entropyDensity 已证可积）收敛到全空间积分，
p 侧由 AECover 反常积分机器（`aecover_Ioc_of_Ioc`，σ(−R)→0、σ R→1）配非负函数的
有限极限判据（`AECover.integral_eq_of_tendsto_of_nonneg_ae`，g ≥ 0 且极限有限 ⇒ 可积且
等于极限值）收敛到 ∫₀¹ g。hbin 对称性 hbin(p)=hbin(1−p) 给出
g(p) = f1(p) + f1(1−p)，其中 f1(p) = −ln p/(1−p)；∫₀¹ f1(1−p) dp = ∫₀¹ f1（
`integral_comp_sub_right` + `integral_comp_neg`，无需端点可积性前提的恒等式），
故 ∫₀¹ g = 2∫₀¹ f1。至此 C_H = 2∫₀¹(−ln p)/(1−p) dp，阶段 4 拼接 π²/6 即得 π²/3。
-/

/-- σ 的导数：σ'(z) = σ(z)·(1−σ(z))（logistic 导数，logit 换元的 Jacobi 因子）。 -/
lemma sig_hasDerivAt (z : ℝ) : HasDerivAt sig (sig z * (1 - sig z)) z := by
  unfold sig
  have hpos : 0 < 1 + Real.exp (-z) := by positivity
  have hden : HasDerivAt (fun y : ℝ => 1 + Real.exp (-y)) (-Real.exp (-z)) z := by
    have h1 : HasDerivAt (fun y : ℝ => -y) (-(1 : ℝ)) z := (hasDerivAt_id z).neg
    have h2 : HasDerivAt (fun y : ℝ => Real.exp (-y)) (Real.exp (-z) * (-1)) z :=
      (Real.hasDerivAt_exp (-z)).comp z h1
    have h3 : HasDerivAt (fun y : ℝ => 1 + Real.exp (-y)) (0 + Real.exp (-z) * (-1)) z :=
      (show HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 z from hasDerivAt_const z (1 : ℝ)).add h2
    simpa using h3
  have hinv : HasDerivAt (fun y : ℝ => (1 + Real.exp (-y))⁻¹)
      (-(-Real.exp (-z)) / (1 + Real.exp (-z)) ^ 2) z := by
    exact hden.inv hpos.ne'
  rw [show (fun y : ℝ => 1 / (1 + Real.exp (-y))) = (fun y : ℝ => (1 + Real.exp (-y))⁻¹) from by
    funext y
    rw [one_div]]
  have hval : Real.exp (-z) / (1 + Real.exp (-z)) ^ 2
      = 1 / (1 + Real.exp (-z)) * (1 - 1 / (1 + Real.exp (-z))) := by
    field_simp [hpos.ne']
    ring
  simpa [hval] using hinv

/-- σ 连续（换元定理的连续性前提）。 -/
lemma sig_continuous : Continuous sig := by
  unfold sig
  have hfun : (fun z : ℝ => 1 / (1 + Real.exp (-z))) = (fun z : ℝ => (1 + Real.exp (-z))⁻¹) := by
    funext z
    rw [one_div]
  rw [hfun]
  exact Continuous.inv₀ (continuous_const.add (Real.continuous_exp.comp continuous_neg))
    (fun z => by positivity)

/-- σ 在 −∞ 处趋于 0（logit 换元左端点的收敛）。 -/
lemma tendsto_sig_atBot_nhds_zero : Filter.Tendsto sig Filter.atBot (nhds 0) := by
  unfold sig
  have hexp : Filter.Tendsto (fun z : ℝ => Real.exp (-z)) Filter.atBot Filter.atTop :=
    Real.tendsto_exp_atTop.comp (Filter.tendsto_neg_atBot_atTop (G := ℝ))
  have hsum : Filter.Tendsto (fun z : ℝ => 1 + Real.exp (-z)) Filter.atBot Filter.atTop :=
    Filter.tendsto_atTop_mono (fun z => by linarith) hexp
  convert (tendsto_inv_atTop_zero.comp hsum) using 1
  funext z
  simp [one_div]

/-- σ 在 +∞ 处趋于 1（logit 换元右端点的收敛）。 -/
lemma tendsto_sig_atTop_nhds_one : Filter.Tendsto sig Filter.atTop (nhds 1) := by
  unfold sig
  have hexp : Filter.Tendsto (fun z : ℝ => Real.exp (-z)) Filter.atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp (Filter.tendsto_neg_atTop_atBot (G := ℝ))
  have hsum : Filter.Tendsto (fun z : ℝ => 1 + Real.exp (-z)) Filter.atTop (nhds (1 + 0)) :=
    hexp.const_add 1
  have hinv : Filter.Tendsto (fun z : ℝ => (1 + Real.exp (-z))⁻¹) Filter.atTop (nhds ((1 + 0)⁻¹)) :=
    hsum.inv₀ (by norm_num)
  simpa [one_div] using hinv

/-- g(p) = hbin(p)/(p(1−p)) 在 (0,1) 上连续（换元定理在有限子区间上的前提）。 -/
lemma hbin_div_contOn : ContinuousOn (fun p : ℝ => hbin p / (p * (1 - p))) (Set.Ioo 0 1) := by
  unfold hbin
  have hlog : ContinuousOn Real.log (Set.Ioo 0 1) :=
    Real.continuousOn_log.mono (by intro p hp; exact ne_of_gt hp.1)
  have hlog_sub : ContinuousOn (fun p : ℝ => Real.log (1 - p)) (Set.Ioo 0 1) :=
    hlog.comp (continuousOn_const.sub continuousOn_id)
      (by intro p hp; exact ⟨sub_pos.mpr hp.2, sub_lt_self (1 : ℝ) hp.1⟩)
  have h1 : ContinuousOn (fun p : ℝ => -p * Real.log p) (Set.Ioo 0 1) :=
    continuousOn_id.neg.mul hlog
  have h2 : ContinuousOn (fun p : ℝ => (1 - p) * Real.log (1 - p)) (Set.Ioo 0 1) :=
    (continuousOn_const.sub continuousOn_id).mul hlog_sub
  have hhbin : ContinuousOn (fun p : ℝ => -p * Real.log p - (1 - p) * Real.log (1 - p)) (Set.Ioo 0 1) :=
    h1.sub h2
  have hden : ContinuousOn (fun p : ℝ => p * (1 - p)) (Set.Ioo 0 1) :=
    continuousOn_id.mul (continuousOn_const.sub continuousOn_id)
  have hne : ∀ p ∈ Set.Ioo (0 : ℝ) 1, p * (1 - p) ≠ 0 := by
    intro p hp
    exact mul_ne_zero (ne_of_gt hp.1) (sub_ne_zero.mpr (ne_of_gt hp.2))
  refine ContinuousOn.div hhbin hden ?_
  intro x hx
  exact hne x hx

/-- 阶段 3：C_H = ∫ℝ h(σ(z)) dz = 2·∫₀¹ (−ln p)/(1−p) dp（logit 换元 + hbin 对称性）。 -/
theorem entropyDensity_integral_eq_two_mul_integral_neg_log_div :
    (∫ z : ℝ, entropyDensity z) = 2 * (∫ p in (0 : ℝ)..1, -Real.log p / (1 - p)) := by
  let f1 : ℝ → ℝ := fun p => -Real.log p / (1 - p)
  let f2 : ℝ → ℝ := fun p => -Real.log (1 - p) / p
  let g : ℝ → ℝ := fun p => hbin p / (p * (1 - p))
  have hzlim : Filter.Tendsto (fun R : ℝ => ∫ z in (-R)..R, entropyDensity z) Filter.atTop
      (nhds (∫ z : ℝ, entropyDensity z)) :=
    MeasureTheory.intervalIntegral_tendsto_integral (μ := volume) (f := entropyDensity)
      boundary_entropy_integrable (a := fun R : ℝ => -R) (b := fun R : ℝ => R)
      (ha := by simpa using (Filter.tendsto_neg_atTop_atBot (G := ℝ)))
      (hb := Filter.tendsto_id)
  have hsub_fin (R : ℝ) :
      ∫ z in (-R)..R, entropyDensity z = ∫ p in (sig (-R))..(sig R), g p := by
    have hcomp := intervalIntegral.integral_comp_mul_deriv' (f := sig)
      (f' := fun z => sig z * (1 - sig z)) (g := g) (a := -R) (b := R)
      (h := fun z hz => sig_hasDerivAt z)
      (h' := (sig_continuous.mul (continuous_const.sub sig_continuous)).continuousOn)
      (hg := hbin_div_contOn.mono (by
        intro p hp
        rcases hp with ⟨z, hz, rfl⟩
        exact ⟨sig_pos z, sig_lt_one z⟩))
    rw [← hcomp]
    apply intervalIntegral.integral_congr
    intro z hz
    dsimp [entropyDensity, g]
    have hz1 : sig z ≠ 0 := ne_of_gt (sig_pos z)
    have hz2 : 1 - sig z ≠ 0 := sub_ne_zero.mpr (ne_of_gt (sig_lt_one z))
    field_simp [hz1, hz2]
  have hplim : Filter.Tendsto (fun R : ℝ => ∫ p in (sig (-R))..(sig R), g p) Filter.atTop
      (nhds (∫ z : ℝ, entropyDensity z)) := by
    refine hzlim.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with R hR
    exact hsub_fin R
  have ha0 : Filter.Tendsto (fun R : ℝ => sig (-R)) Filter.atTop (nhds 0) :=
    tendsto_sig_atBot_nhds_zero.comp Filter.tendsto_neg_atTop_atBot
  have hb1 : Filter.Tendsto (fun R : ℝ => sig R) Filter.atTop (nhds 1) :=
    tendsto_sig_atTop_nhds_one.comp Filter.tendsto_id
  have hφ : MeasureTheory.AECover (volume.restrict (Set.Ioc (0 : ℝ) 1)) Filter.atTop
      (fun R : ℝ => Set.Ioc (sig (-R)) (sig R)) :=
    MeasureTheory.aecover_Ioc_of_Ioc (μ := volume) (A := (0 : ℝ)) (B := 1) ha0 hb1
  have hsub' (R : ℝ) : Set.Ioc (sig (-R)) (sig R) ⊆ Set.Ioc (0 : ℝ) 1 := by
    intro p hp
    exact ⟨lt_trans (sig_pos (-R)) hp.1, le_of_lt (lt_of_le_of_lt hp.2 (sig_lt_one R))⟩
  have hcover_int : ∀ R : ℝ, IntegrableOn g (Set.Ioc (sig (-R)) (sig R))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    intro R
    have hcont : ContinuousOn g (Set.Icc (sig (-R)) (sig R)) :=
      hbin_div_contOn.mono (by
        intro p hp
        exact ⟨lt_of_lt_of_le (sig_pos (-R)) hp.1, lt_of_le_of_lt hp.2 (sig_lt_one R)⟩)
    have hInt : IntegrableOn g (Set.Icc (sig (-R)) (sig R)) volume := hcont.integrableOn_Icc
    have hInt' : IntegrableOn g (Set.Ioc (sig (-R)) (sig R)) volume :=
      hInt.mono_set Set.Ioc_subset_Icc_self
    change MeasureTheory.Integrable g
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).restrict (Set.Ioc (sig (-R)) (sig R)))
    rw [Measure.restrict_restrict_of_subset (hsub' R)]
    exact hInt'
  have hbridge (R : ℝ) (hR : 0 ≤ R) :
      (∫ x in Set.Ioc (sig (-R)) (sig R), g x ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)))
        = ∫ p in (sig (-R))..(sig R), g p := by
    have hle : sig (-R) ≤ sig R := by
      have hsig_ge : 1 / 2 ≤ sig R := by
        unfold sig
        have h : Real.exp (-R) ≤ 1 := by
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr (by linarith)
        exact one_div_le_one_div_of_le (by positivity : 0 < 1 + Real.exp (-R)) (by linarith)
      rw [sig_neg]
      linarith
    rw [Measure.restrict_restrict_of_subset (hsub' R)]
    rw [intervalIntegral.integral_of_le hle]
  have hcovlim : Filter.Tendsto
      (fun R : ℝ => ∫ x in Set.Ioc (sig (-R)) (sig R), g x ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)))
      Filter.atTop (nhds (∫ z : ℝ, entropyDensity z)) := by
    refine hplim.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with R hR
    exact (hbridge R hR).symm
  have hg_meas : Measurable g := by
    dsimp [g, hbin]
    exact ((measurable_id.neg.mul Real.measurable_log).sub
      ((measurable_const.sub measurable_id).mul
        (Real.measurable_log.comp (measurable_const.sub measurable_id)))).div
      (measurable_id.mul (measurable_const.sub measurable_id))
  have hg_nonneg_pointwise (p : ℝ) (hp : p ∈ Set.Ioc (0 : ℝ) 1) : 0 ≤ g p := by
    rcases lt_or_eq_of_le hp.2 with hp1 | hpeq1
    · dsimp [g]
      exact div_nonneg (hbin_nonneg p hp.1 hp1) (le_of_lt (mul_pos hp.1 (sub_pos.mpr hp1)))
    · subst p
      simp [g, hbin]
  have hg_nonneg_ae : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] g := by
    refine (MeasureTheory.ae_restrict_iff (s := Set.Ioc (0 : ℝ) 1)
      (hp := measurableSet_le (show Measurable (fun _ : ℝ => (0 : ℝ)) from measurable_const) hg_meas)).2 ?_
    exact Filter.Eventually.of_forall (fun p hp => hg_nonneg_pointwise p hp)
  have hInt_g : MeasureTheory.Integrable g (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    MeasureTheory.AECover.integrable_of_integral_tendsto_of_nonneg_ae
      (μ := volume.restrict (Set.Ioc (0 : ℝ) 1)) (l := Filter.atTop)
      (φ := fun R : ℝ => Set.Ioc (sig (-R)) (sig R)) hφ (I := ∫ z : ℝ, entropyDensity z)
      hcover_int hg_nonneg_ae hcovlim
  have hg_eq : (∫ x : ℝ, g x ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))) = ∫ z : ℝ, entropyDensity z :=
    MeasureTheory.AECover.integral_eq_of_tendsto_of_nonneg_ae
      (μ := volume.restrict (Set.Ioc (0 : ℝ) 1)) (l := Filter.atTop)
      (φ := fun R : ℝ => Set.Ioc (sig (-R)) (sig R)) hφ (I := ∫ z : ℝ, entropyDensity z)
      hg_nonneg_ae hcover_int hcovlim
  have hsub_main : (∫ z : ℝ, entropyDensity z) = ∫ p in (0 : ℝ)..1, g p := by
    rw [hg_eq.symm]
    rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  have hmem_uIcc {p : ℝ} (hp : p ∈ Set.Ioc (0 : ℝ) 1) : p ∈ Set.uIcc (0 : ℝ) 1 := by
    simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using (Set.Ioc_subset_Icc_self hp)
  have hg_sum : Set.EqOn g (fun p => f1 p + f2 p) (Set.uIcc (0 : ℝ) 1) := by
    intro p hp
    dsimp [g, f1, f2, hbin]
    have hp' : p ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hp
    rcases lt_or_eq_of_le hp'.1 with hp0 | hpeq0
    · rcases lt_or_eq_of_le hp'.2 with hp1 | hpeq1
      · have hp0' : p ≠ 0 := ne_of_gt hp0
        have h1p : 1 - p ≠ 0 := sub_ne_zero.mpr (ne_of_gt hp1)
        field_simp [hp0', h1p, mul_ne_zero hp0' h1p]
        ring
      · subst p
        norm_num
    · subst p
      norm_num
  have hf1_nonneg (p : ℝ) (hp : p ∈ Set.Ioc (0 : ℝ) 1) : 0 ≤ f1 p := by
    rcases lt_or_eq_of_le hp.2 with hp1 | hpeq1
    · dsimp [f1]
      exact div_nonneg (neg_nonneg.mpr (Real.log_nonpos (le_of_lt hp.1) (le_of_lt hp1)))
        (le_of_lt (sub_pos.mpr hp1))
    · subst p
      simp [f1]
  have hf2_nonneg (p : ℝ) (hp : p ∈ Set.Ioc (0 : ℝ) 1) : 0 ≤ f2 p := by
    rcases lt_or_eq_of_le hp.2 with hp1 | hpeq1
    · dsimp [f2]
      have h1p0 : 0 ≤ 1 - p := sub_nonneg.mpr (le_of_lt hp1)
      have h1p1 : 1 - p ≤ 1 := sub_le_self 1 (le_of_lt hp.1)
      exact div_nonneg (neg_nonneg.mpr (Real.log_nonpos h1p0 h1p1)) (le_of_lt hp.1)
    · subst p
      simp [f2]
  have hf1_meas : Measurable f1 := by
    dsimp [f1]
    exact (Real.measurable_log.neg).div (measurable_const.sub measurable_id)
  have hf2_meas : Measurable f2 := by
    dsimp [f2]
    exact ((Real.measurable_log.comp (measurable_const.sub measurable_id)).neg).div measurable_id
  have hdom1 : (fun p : ℝ => ‖f1 p‖) ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] fun p : ℝ => ‖g p‖ := by
    refine (MeasureTheory.ae_restrict_iff (s := Set.Ioc (0 : ℝ) 1)
      (hp := measurableSet_le hf1_meas.norm hg_meas.norm)).2 ?_
    exact Filter.Eventually.of_forall (fun p hp => by
      rw [Real.norm_of_nonneg (hf1_nonneg p hp), Real.norm_of_nonneg (hg_nonneg_pointwise p hp)]
      rw [hg_sum (hmem_uIcc hp)]
      exact le_add_of_nonneg_right (hf2_nonneg p hp))
  have hdom2 : (fun p : ℝ => ‖f2 p‖) ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] fun p : ℝ => ‖g p‖ := by
    refine (MeasureTheory.ae_restrict_iff (s := Set.Ioc (0 : ℝ) 1)
      (hp := measurableSet_le hf2_meas.norm hg_meas.norm)).2 ?_
    exact Filter.Eventually.of_forall (fun p hp => by
      rw [Real.norm_of_nonneg (hf2_nonneg p hp), Real.norm_of_nonneg (hg_nonneg_pointwise p hp)]
      rw [hg_sum (hmem_uIcc hp)]
      exact le_add_of_nonneg_left (hf1_nonneg p hp))
  have hInt_f1 : MeasureTheory.Integrable f1 (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    hInt_g.mono hf1_meas.aestronglyMeasurable hdom1
  have hInt_f2 : MeasureTheory.Integrable f2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    hInt_g.mono hf2_meas.aestronglyMeasurable hdom2
  have hII_f1 : IntervalIntegrable f1 volume (0 : ℝ) 1 := by
    refine ⟨?_, ?_⟩
    · change MeasureTheory.IntegrableOn f1 (Set.Ioc (0 : ℝ) 1) volume
      exact hInt_f1
    · change MeasureTheory.IntegrableOn f1 (Set.Ioc (1 : ℝ) 0) volume
      change MeasureTheory.Integrable f1 (volume.restrict (Set.Ioc (1 : ℝ) 0))
      have hempty : Set.Ioc (1 : ℝ) 0 = ∅ := by
        ext x
        constructor <;> intro hx
        · exact (not_le_of_gt hx.1) (le_trans hx.2 (by norm_num : (0 : ℝ) ≤ 1))
        · exact False.elim hx
      rw [hempty]
      simp
  have hII_f2 : IntervalIntegrable f2 volume (0 : ℝ) 1 := by
    refine ⟨?_, ?_⟩
    · change MeasureTheory.IntegrableOn f2 (Set.Ioc (0 : ℝ) 1) volume
      exact hInt_f2
    · change MeasureTheory.IntegrableOn f2 (Set.Ioc (1 : ℝ) 0) volume
      change MeasureTheory.Integrable f2 (volume.restrict (Set.Ioc (1 : ℝ) 0))
      have hempty : Set.Ioc (1 : ℝ) 0 = ∅ := by
        ext x
        constructor <;> intro hx
        · exact (not_le_of_gt hx.1) (le_trans hx.2 (by norm_num : (0 : ℝ) ≤ 1))
        · exact False.elim hx
      rw [hempty]
      simp
  have hcomp_f2 : ∫ p in (0 : ℝ)..1, f2 p = ∫ p in (0 : ℝ)..1, f1 p := by
    calc
      ∫ p in (0 : ℝ)..1, f2 p = ∫ p in (0 : ℝ)..1, (f1 ∘ Neg.neg) (p - 1) := by
        apply intervalIntegral.integral_congr
        intro p hp
        dsimp [f2, f1]
        rw [neg_sub]
        congr 2
        ring
      _ = ∫ q in (0 - 1)..(1 - 1), (f1 ∘ Neg.neg) q := by
        rw [intervalIntegral.integral_comp_sub_right (f1 ∘ Neg.neg) 1]
      _ = ∫ q in (0 : ℝ)..1, f1 q := by
        change ∫ q in (0 - 1)..(1 - 1), f1 (-q) = ∫ q in (0 : ℝ)..1, f1 q
        rw [intervalIntegral.integral_comp_neg]
        norm_num
  have hsymm : ∫ p in (0 : ℝ)..1, g p = 2 * (∫ p in (0 : ℝ)..1, f1 p) := by
    calc
      ∫ p in (0 : ℝ)..1, g p = ∫ p in (0 : ℝ)..1, f1 p + f2 p := by
        apply intervalIntegral.integral_congr
        exact hg_sum
      _ = (∫ p in (0 : ℝ)..1, f1 p) + ∫ p in (0 : ℝ)..1, f2 p :=
        intervalIntegral.integral_add hII_f1 hII_f2
      _ = (∫ p in (0 : ℝ)..1, f1 p) + ∫ p in (0 : ℝ)..1, f1 p := by rw [hcomp_f2]
      _ = 2 * (∫ p in (0 : ℝ)..1, f1 p) := by ring
  rw [hsub_main, hsymm]

/-! ## §3.2′ 值机验（P4 补丁 · 2026-08-20 新增 · 阶段 4）

`C_H = π²/3` 积分侧证明 · 阶段 4（拼接）：

    C_H = ∫ℝ h(σ(z)) dz = 2·∫₀¹(−ln p)/(1−p) dp = 2·(π²/6) = π²/3

阶段 3（logit 换元 + 对称性）给出前一个等号，阶段 2（级数-积分交换 + Basel）给出
后一个等号；本阶段只做代数拼接。四阶段全部落地后，论文定理 4.6
「C_H = π²/3」在 Lean + Mathlib 中获得零 sorry 机器证明。
-/

/-- 定理 4.6 精确值：C_H = ∫ℝ h(σ(z)) dz = π²/3（边界熵-面积常数）。 -/
theorem C_H_eq_pi_sq_div_three : (∫ z : ℝ, entropyDensity z) = π ^ 2 / 3 := by
  rw [entropyDensity_integral_eq_two_mul_integral_neg_log_div,
    integral_neg_log_div_one_sub_zero_one]
  ring

end BoundaryTheory
