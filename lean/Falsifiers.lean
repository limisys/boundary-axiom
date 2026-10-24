/-
Falsifiers.lean —— **S4：把"落空条件"形式化（预言＋反驳）**（第 119 轮）

**背景**：S4 此前标为"未形式化"。本件把它落成两半：

  1. **预言（机检的定理）**：沿声明的维持轨迹（$w\\ge1$ 侧），读数
     · **永不越过** $\\theta^\\star$（`level_le_thetaStar`）；
     · **单调非降**（`level_monotone`）；
     · **有限时间超过任何更低水平**（第 118 轮 `level_climbs`）；
     · **每步误差减半，且水平误差也有显式几何界**：$\\theta^\\star-\\theta(w_n)\\le\\theta^\\star\\cdot\\dfrac{w_0-1}{2^{n}}$（`level_geometric`）。
  2. **落空条件（形式化的反驳）**：给出三条可观测的否证形态，并**逐条证明它们与模型不相容**：
     · `falsifier_overshoot`：观测到读数**越过** $\\theta^\\star$ ⇒ 模型不成立；
     · `falsifier_nonmonotone`：观测到读数**回落** ⇒ 模型不成立；
     · `falsifier_stalls`：观测到读数**长期停在某个 $\\theta'<\\theta^\\star$ 之下** ⇒ 模型不成立。

**⚠ 本条不是"经验已证"**：本件只把"可证伪性"写成**机检的命题对**
（预言是定理；反驳是那些定理的否命题），**尚未做任何测量**（M1 未开工）。

0 `sorry` / `0 axiom`。
-/
import ReadoutDynamics

open scoped Real

namespace Falsifiers

open LevelDynamics ReadoutDynamics
open ReadoutExistence (thetaOf)

/-! ## 一 · 预言（机检） -/

/-- **（预言 1）** 读数**永不越过** $\\theta^\\star$。 -/
theorem level_le_thetaStar (w : ℝ) (hw : 1 ≤ w) (n : ℕ) :
    thetaOf ((relax^[n]) w) ≤ thetaOf 1 :=
  level_squeeze w hw n

/-- **（迭代非增）** $w\\ge1\\Rightarrow w_{n+1}\\le w_n$。 -/
theorem relax_iterate_antitone (w : ℝ) (hw : 1 ≤ w) :
    ∀ n : ℕ, (relax^[n + 1]) w ≤ (relax^[n]) w := by
  intro n
  have hge : 1 ≤ (relax^[n]) w := one_le_iterate w hw n
  have hidx : (relax^[n + 1]) w = relax ((relax^[n]) w) := by
    rw [Function.iterate_succ_apply']
  rw [hidx]
  rcases lt_or_eq_of_le hge with h | h
  · exact le_of_lt (relax_lt_self h)
  · rw [← h]
    norm_num [relax]

/-- **（预言 2）** 读数沿轨迹**单调非降**。 -/
theorem level_monotone (w : ℝ) (hw : 1 ≤ w) (n : ℕ) :
    thetaOf ((relax^[n]) w) ≤ thetaOf ((relax^[n + 1]) w) :=
  thetaOf_le_thetaOf (relax_iterate_antitone w hw n)

/-- **（定量引理）** $\\theta^\\star-\\theta(w)\\le\\theta^\\star\\cdot(w-1)$（$w\\ge1$）。 -/
theorem thetaStar_sub_le (w : ℝ) (hw : 1 ≤ w) :
    thetaOf 1 - thetaOf w ≤ thetaOf 1 * (w - 1) := by
  set t := Real.exp (w - 1) with ht
  have ht1 : 1 ≤ t := by rw [ht]; exact Real.one_le_exp (by linarith)
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have htpos' : 0 < 1 + Real.exp 1 * t := by positivity
  have htw : Real.exp w = Real.exp 1 * t := by
    rw [ht, ← Real.exp_add]
    congr 1
    ring
  have hlog : Real.log t = w - 1 := by rw [ht, Real.log_exp]
  have hcore : Real.exp 1 ≤ (1 + Real.exp 1 * t) / t := by
    rw [le_div_iff₀ htpos]
    nlinarith
  have key : thetaOf 1 - thetaOf w
      = 2 * Real.exp 1 * (t - 1) / ((1 + Real.exp 1) * (1 + Real.exp 1 * t)) := by
    unfold thetaOf
    rw [htw]
    field_simp
    ring
  have step1 : 2 * Real.exp 1 * (t - 1) / ((1 + Real.exp 1) * (1 + Real.exp 1 * t))
      ≤ 2 / (1 + Real.exp 1) * ((t - 1) / t) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 + Real.exp 1) * (1 + Real.exp 1 * t))]
    have h1 : 2 / (1 + Real.exp 1) * ((t - 1) / t) * ((1 + Real.exp 1) * (1 + Real.exp 1 * t))
        = 2 * (t - 1) * ((1 + Real.exp 1 * t) / t) := by
      field_simp
    rw [h1]
    have ht1' : (0 : ℝ) ≤ t - 1 := by linarith
    nlinarith
  have step2 : 2 / (1 + Real.exp 1) * ((t - 1) / t) ≤ 2 / (1 + Real.exp 1) * (w - 1) := by
    have hid : (t - 1) / t = 1 - 1 / t := by
      field_simp
    rw [hid]
    have h := Real.one_sub_inv_le_log_of_pos htpos
    rw [hlog] at h
    have h' : 1 - 1 / t ≤ w - 1 := by
      simpa [one_div] using h
    exact mul_le_mul_of_nonneg_left h' (by positivity)
  have hfin : thetaOf 1 = 2 / (1 + Real.exp 1) := rfl
  rw [key, hfin]
  linarith

/-- **（预言 3 · 水平误差的几何界）** 水平误差也**每步减半**：
$\\theta^\\star-\\theta(w_n)\\le\\theta^\\star\\cdot\\dfrac{w-1}{2^{n}}$。 -/
theorem level_geometric (w : ℝ) (hw : 1 ≤ w) (n : ℕ) :
    thetaOf 1 - thetaOf ((relax^[n]) w) ≤ thetaOf 1 * ((w - 1) / 2 ^ n) := by
  have hge : 1 ≤ (relax^[n]) w := one_le_iterate w hw n
  have h := thetaStar_sub_le ((relax^[n]) w) hge
  have hb := relax_iterate_error w hw n
  have hnn : (0 : ℝ) ≤ thetaOf 1 := by
    unfold thetaOf
    positivity
  calc thetaOf 1 - thetaOf ((relax^[n]) w) ≤ thetaOf 1 * ((relax^[n]) w - 1) := h
    _ ≤ thetaOf 1 * ((w - 1) / 2 ^ n) := mul_le_mul_of_nonneg_left hb hnn

/-! ## 二 · 落空条件（形式化的反驳） -/

/-- **（落空 1）** 观测到读数**越过** $\\theta^\\star$ ⇒ 与模型（读数＝轨迹水平）**不相容**。 -/
theorem falsifier_overshoot (r : ℕ → ℝ) (w : ℝ) (hw : 1 ≤ w) (n : ℕ)
    (hgt : thetaOf 1 < r n) (hmodel : ∀ m : ℕ, r m = thetaOf ((relax^[m]) w)) : False := by
  have := level_le_thetaStar w hw n
  rw [hmodel n] at hgt
  linarith

/-- **（落空 2）** 观测到读数**回落**（$r_{n+1}<r_n$）⇒ 与模型**不相容**。 -/
theorem falsifier_nonmonotone (r : ℕ → ℝ) (w : ℝ) (hw : 1 ≤ w) (n : ℕ)
    (hdown : r (n + 1) < r n) (hmodel : ∀ m : ℕ, r m = thetaOf ((relax^[m]) w)) : False := by
  have hmono := level_monotone w hw n
  rw [hmodel n, hmodel (n + 1)] at hdown
  linarith

/-- **（落空 3）** 观测到读数**长期停在某个 $\\theta'<\\theta^\\star$ 之下** ⇒ 与模型**不相容**。 -/
theorem falsifier_stalls (r : ℕ → ℝ) (w : ℝ) (hw : 1 < w) (θ' : ℝ)
    (h0 : 0 < θ') (h1 : θ' < 1) (hlt : θ' < thetaOf 1)
    (hbelow : ∀ m : ℕ, r m ≤ θ') (hmodel : ∀ m : ℕ, r m = thetaOf ((relax^[m]) w)) : False := by
  obtain ⟨N, hN⟩ := level_climbs w hw θ' h0 h1 hlt
  have hup : θ' < thetaOf ((relax^[N]) w) := hN N le_rfl
  have hdn : r N ≤ θ' := hbelow N
  rw [hmodel N] at hdn
  linarith

/-- **（S4 证书）** 预言（永不越过 · 单调非降 · 几何界）＋ 三条落空条件。 -/
theorem s4_falsifier_certificate (w : ℝ) (hw : 1 < w) :
    (∀ n : ℕ, thetaOf ((relax^[n]) w) ≤ thetaOf 1) ∧
      (∀ n : ℕ, thetaOf ((relax^[n]) w) ≤ thetaOf ((relax^[n + 1]) w)) ∧
      (∀ n : ℕ, thetaOf 1 - thetaOf ((relax^[n]) w) ≤ thetaOf 1 * ((w - 1) / 2 ^ n)) ∧
      (∀ r : ℕ → ℝ, ∀ n : ℕ, thetaOf 1 < r n →
        (∀ m : ℕ, r m = thetaOf ((relax^[m]) w)) → False) ∧
      (∀ r : ℕ → ℝ, ∀ n : ℕ, r (n + 1) < r n →
        (∀ m : ℕ, r m = thetaOf ((relax^[m]) w)) → False) ∧
      (∀ r : ℕ → ℝ, ∀ θ' : ℝ, 0 < θ' → θ' < 1 → θ' < thetaOf 1 →
        (∀ m : ℕ, r m ≤ θ') → (∀ m : ℕ, r m = thetaOf ((relax^[m]) w)) → False) :=
  ⟨fun n => level_le_thetaStar w (le_of_lt hw) n,
    fun n => level_monotone w (le_of_lt hw) n,
    fun n => level_geometric w (le_of_lt hw) n,
    fun r n hgt hm => falsifier_overshoot r w (le_of_lt hw) n hgt hm,
    fun r n hdown hm => falsifier_nonmonotone r w (le_of_lt hw) n hdown hm,
    fun r θ' h0 h1 hlt hb hm => falsifier_stalls r w hw θ' h0 h1 hlt hb hm⟩

end Falsifiers
