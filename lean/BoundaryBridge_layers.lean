/-
BoundaryBridge_layers.lean —— **靶心 3：范畴层 ↔ 值层的机检接缝**（第 50 轮）

背景（本轮清点发现，见件 `靶心3_两层接缝`）：
  · 值层 `BoundaryTheory.lean`（repos/godcore/lean-boundary）定义了 V、kappaStar、sigmaStar、
    force、hbin、sig、entropyDensity，并证明 `C_H_eq_pi_sq_div_three : ∫ entropyDensity = π²/3`。
  · 范畴层 `CausModel`（论文/02_形式化与机验/Lean源码_CausModel）定义了 hbin、sig、
    entropyDensity F、rescale、coreConstant F = ∫ h(F z)，并证明主定理 `coreConstant_rescale`。
  · **两层互不 import**：链接靠"重复定义对齐"（KernelModuli 注释自称"同 BoundaryTheory.hbin"）。
    ⇒ 这是**镜像，不是机检接缝**：任一侧改了定义，没有任何东西会报错。

本文件把镜像升为**机检接缝**：
  (1) 两层同名定义逐点相同（`rfl` 级）；
  (2) **主桥**：范畴层的核心常数在 logistic 核上恰等于值层机检过的 C_H = π²/3。
-/

import BoundaryTheory
import CausModel

open MeasureTheory
open scoped Real

namespace BoundaryBridge

/-- (1a) 二元熵函数逐点相同。 -/
theorem hbin_agree : CausModel.hbin = BoundaryTheory.hbin := rfl

/-- (1b) logistic 核逐点相同。 -/
theorem sig_agree : CausModel.sig = BoundaryTheory.sig := rfl

/-- (1c) **熵密度的元数不同（本轮发现）**：范畴层是**核一般**的
`entropyDensity F z = hbin (F z)`；值层是**已在 logistic 核上实例化**的
`entropyDensity z = hbin (sig z)`。故正确对齐式是在 `F = sig` 处——
（KernelModuli 的注释"同 BoundaryTheory.entropyDensity"是**宽松说法**，本文件予以精确化。） -/
theorem entropyDensity_sig_agree :
    CausModel.entropyDensity CausModel.sig = BoundaryTheory.entropyDensity := rfl

/-- **(2) 主桥**：范畴层的 `coreConstant` 在 logistic 核上等于值层已机检的 `C_H = π²/3`。
这条把"论文 §5.2 表里 logistic 一行"从**引用**变成**定理**。 -/
theorem coreConstant_sig_eq_pi_sq_div_three :
    CausModel.coreConstant CausModel.sig = π ^ 2 / 3 := by
  have h : CausModel.coreConstant CausModel.sig = ∫ z : ℝ, BoundaryTheory.entropyDensity z := by
    unfold CausModel.coreConstant
    rw [entropyDensity_sig_agree]
  rw [h, BoundaryTheory.C_H_eq_pi_sq_div_three]

/-- (3) 推论：由 `coreConstant_rescale`，tanh 核（= σ(2z)，同轨 λ=2）的核心常数恰为 C_H/2 = π²/6。 -/
theorem coreConstant_tanh_eq_pi_sq_div_six :
    CausModel.coreConstant (CausModel.rescale 2 CausModel.sig) = π ^ 2 / 6 := by
  rw [CausModel.coreConstant_rescale CausModel.sig (by norm_num : (0:ℝ) < 2),
      coreConstant_sig_eq_pi_sq_div_three]
  ring

/-! ## (4) V 链的接缝（第 51 轮）：值层的势是范畴层"两项权衡律"的**实例**

范畴层 `CausModel.Tradeoff` 已证明一般律：
  `two_term_bound : 2√(AB) ≤ A·κ + B/κ`（`A>0, B≥0, κ>0`）
  `crit_ratio_sq  : A·κ = B/κ ⇒ κ² = B/A`
值层 `BoundaryTheory` **只有**临界点（`deriv_V_kappaStar`、`kappaStar_sq`），**没有** √ 律。
故下面三条是**由范畴层导入值层的新定理**：
把 $A=c_0,\ B=\alpha\pi^2/3$ 代入，值层的 $V$ 恰是范畴层的"两笔账之和"。 -/

/-- (4a) **√ 律**：值层的势 $V(\kappa)$ 有下界 $2\sqrt{c_0\cdot\alpha\pi^2/3}$。 -/
theorem V_lower_bound (c₀ α : ℝ) (hc₀ : 0 < c₀) (hα : 0 ≤ α) {κ : ℝ} (hκ : 0 < κ) :
    2 * Real.sqrt (c₀ * (α * Real.pi ^ 2 / 3)) ≤ BoundaryTheory.V c₀ α κ := by
  have hB : 0 ≤ α * Real.pi ^ 2 / 3 := by positivity
  have h := CausModel.Tradeoff.two_term_bound (A := c₀) (B := α * Real.pi ^ 2 / 3) (κ := κ)
      hc₀ hB hκ
  unfold BoundaryTheory.V
  linarith [h]

/-- (4b) **值层的 κ★ 就是范畴层一般律的实例**：$A\kappa^{\star2}=B$（即 $c_0\kappa^{\star2}=\alpha\pi^2/3$）。 -/
theorem kappaStar_balance_bridge (c₀ α : ℝ) (hc₀ : 0 < c₀) (hα : 0 < α) :
    c₀ * (BoundaryTheory.kappaStar c₀ α) ^ 2 = α * Real.pi ^ 2 / 3 := by
  rw [BoundaryTheory.kappaStar_sq hc₀ (le_of_lt hα)]
  field_simp

/-- (4c) **极小值闭式（值层原本没有）**：$V(\kappa^\star)=2\sqrt{c_0\cdot\alpha\pi^2/3}$。 -/
theorem V_at_kappaStar (c₀ α : ℝ) (hc₀ : 0 < c₀) (hα : 0 < α) :
    BoundaryTheory.V c₀ α (BoundaryTheory.kappaStar c₀ α)
      = 2 * Real.sqrt (c₀ * (α * Real.pi ^ 2 / 3)) := by
  have hk : BoundaryTheory.kappaStar c₀ α ≠ 0 := by
    unfold BoundaryTheory.kappaStar
    exact mul_ne_zero Real.pi_ne_zero
      (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))
  -- κ★² = B/c₀
  have hk2 : (BoundaryTheory.kappaStar c₀ α) ^ 2 = Real.pi ^ 2 * α / (3 * c₀) :=
    BoundaryTheory.kappaStar_sq hc₀ (le_of_lt hα)
  -- 去分母形式：c₀·κ★² = B
  have hk2' : c₀ * (BoundaryTheory.kappaStar c₀ α) ^ 2 = α * Real.pi ^ 2 / 3 := by
    rw [hk2]; field_simp
  -- 两项在 κ★ 处相等
  have hbal : c₀ * BoundaryTheory.kappaStar c₀ α
      = (α * Real.pi ^ 2 / 3) / BoundaryTheory.kappaStar c₀ α := by
    rw [eq_div_iff hk]
    rw [show c₀ * BoundaryTheory.kappaStar c₀ α * BoundaryTheory.kappaStar c₀ α
          = c₀ * (BoundaryTheory.kappaStar c₀ α) ^ 2 by ring, hk2']
  -- (c₀κ★)² = c₀·B
  have hsq : (c₀ * BoundaryTheory.kappaStar c₀ α) ^ 2 = c₀ * (α * Real.pi ^ 2 / 3) := by
    nlinarith [hk2', hc₀]
  have hkpos : 0 < BoundaryTheory.kappaStar c₀ α := by
    unfold BoundaryTheory.kappaStar
    positivity
  have hnonneg : 0 ≤ c₀ * BoundaryTheory.kappaStar c₀ α := le_of_lt (mul_pos hc₀ hkpos)
  unfold BoundaryTheory.V
  rw [← hbal, ← hsq, Real.sqrt_sq hnonneg]
  ring

/-! ## (5) §5.2 表的其余行（第 52 轮）：把两行从"确定性计算"升为**机检**

范畴层 `Orbit.lean` 自注：轨道不变量 $I(F)=C_F\cdot F'(0)$ 的**数值表**是
"确定性计算，**非机检**"（logistic $\pi^2/12$、tanh 同、probit $\approx0.720647$）。
本轮把其中两行变成定理：logistic 与 tanh 的 $I$ 值，以及 Heaviside 行的 $C_F=0$。 -/

/-- (5a) **Heaviside 行**（表格第五行"0"）：$C_{\text{Heaviside}}=0$。
积分被积函数恒为 0（$h(0)=h(1)=0$），故积分为 0。 -/
noncomputable def heaviside (z : ℝ) : ℝ := if z < 0 then 0 else 1

theorem coreConstant_heaviside : CausModel.coreConstant heaviside = 0 := by
  have hzero : (fun z : ℝ => CausModel.entropyDensity heaviside z) = fun _ => 0 := by
    funext z
    unfold CausModel.entropyDensity CausModel.hbin heaviside
    split_ifs with h
    · simp [Real.log_zero, Real.log_one]
    · simp [Real.log_zero, Real.log_one]
  unfold CausModel.coreConstant
  rw [hzero]
  simp

/-- (5b) **logistic 行的轨道不变量**（范畴层记为"确定性计算"）：
$I(\sigma)=C_\sigma\cdot\sigma'(0)=(\pi^2/3)\cdot(1/4)=\pi^2/12$。 -/
theorem orbitInvariant_sig : CausModel.orbitInvariant CausModel.sig = Real.pi ^ 2 / 12 := by
  unfold CausModel.orbitInvariant
  rw [coreConstant_sig_eq_pi_sq_div_three, CausModel.deriv_sig_zero]
  ring

/-- (5c) **tanh 行与 logistic 同轨**：$I(\sigma(2\cdot))=I(\sigma)=\pi^2/12$。
（范畴层 `orbitInvariant_rescale` 已证不变性；此处代入桥定理给出**数值**。） -/
theorem orbitInvariant_tanh :
    CausModel.orbitInvariant (CausModel.rescale 2 CausModel.sig) = Real.pi ^ 2 / 12 := by
  rw [CausModel.orbitInvariant_rescale CausModel.sig (by norm_num : (0:ℝ) < 2),
      orbitInvariant_sig]

/-! ## (6) V 链的**参数级**接缝（第 53 轮）：值层的势是范畴层模型类的**一个实例**

范畴层 `Maintenance.lean` 的模型类：
    `structure BoundaryModel := (maint : MaintenanceCost) (α) (alpha_pos) (C_F) (core_pos)`
    `def V (M : BoundaryModel) (κ) := M.maint κ + M.α * M.C_F / κ`
    **`V_form_forced`**：`M.V κ = M.maint.unitCost * κ + M.α * M.C_F / κ`
    —— 论文 §2.3 那句 "*Why this form is forced* is a structural claim, not a theorem"
       在补上 A7（维护成本可加且连续）之后，**成为定理**（T3）。
本轮把**值层**的 `V` 认成该模型类在 `C_F = π²/3`、线性维护（slope `c₀`）处的实例。 -/

/-- 由值层参数构造的范畴层模型：线性维护 `κ ↦ c₀·κ`、同一 `α`、`C_F = π²/3`。 -/
noncomputable def modelOf (c₀ α : ℝ) (hc₀ : 0 < c₀) (hα : 0 < α) : CausModel.BoundaryModel :=
  ⟨⟨AddMonoidHom.mulLeft c₀, continuous_const.mul continuous_id⟩, α, hα,
   Real.pi ^ 2 / 3, by positivity⟩

/-- 该模型的单位维护成本恰为 `c₀`（T4 里那个唯一残余的自由参数）。 -/
theorem modelOf_unitCost (c₀ α : ℝ) (hc₀ : 0 < c₀) (hα : 0 < α) :
    (modelOf c₀ α hc₀ hα).maint.unitCost = c₀ := by
  simp [modelOf, CausModel.MaintenanceCost.unitCost]

/-- **(6a) 主桥（参数级）**：**值层的势 = 范畴层模型类之对应实例的势**。
即值层的 `V` 不是另一个对象，而是范畴层 `BoundaryModel.V` 在
`(线性维护 slope c₀, α, C_F = π²/3)` 处的一次代入。 -/
theorem BoundaryTheory_V_eq_model_V (c₀ α : ℝ) (hc₀ : 0 < c₀) (hα : 0 < α) (κ : ℝ) :
    BoundaryTheory.V c₀ α κ = (modelOf c₀ α hc₀ hα).V κ := by
  rw [CausModel.BoundaryModel.V_form_forced, modelOf_unitCost]
  unfold BoundaryTheory.V
  simp only [modelOf]
  ring

/-- **(6b) 于是范畴层的"形式被迫"定理适用于值层**：值层的 `V` 形如 `c₀κ + αC_F/κ`，
且该形式**由 A7 决定**（而非"结构主张"）。 -/
theorem value_layer_form_forced (c₀ α : ℝ) (hc₀ : 0 < c₀) (hα : 0 < α) (κ : ℝ) :
    BoundaryTheory.V c₀ α κ = c₀ * κ + α * (Real.pi ^ 2 / 3) / κ := by
  rw [BoundaryTheory_V_eq_model_V c₀ α hc₀ hα κ, CausModel.BoundaryModel.V_form_forced,
      modelOf_unitCost]
  simp only [modelOf]

/-! ## (7) 把范畴层的**非范畴性负定理**搬到值层（第 54 轮）

范畴层 `Maintenance.lean` 已证（对它的模型类）：
    `unitCost_not_determined`：∃ 两个合法模型，`c₀` 不同
    `non_categoricity`、`M1_V_ne_M2_V`：故公理**不决定**维护项，也不决定 `V`
**值层此前没有对应陈述。** 本轮把它搬过来：值层的中心对象 $V$ 的参数 $c_0$
**不被公理决定**——这同时是值层自己的第一条**机检负定理**（"默认否定"的落实）。 -/

/-- (7a) **值层的 $c_0$ 不被决定**：存在两个模型，$lpha$ 与 $C_F$ 完全相同、仅 $c_0$ 不同。 -/
theorem value_layer_c0_not_determined :
    ∃ M1 M2 : CausModel.BoundaryModel,
      M1.maint.unitCost ≠ M2.maint.unitCost ∧ M1.α = M2.α ∧ M1.C_F = M2.C_F := by
  refine ⟨modelOf 1 1 (by norm_num) (by norm_num),
          modelOf 2 1 (by norm_num) (by norm_num), ?_, rfl, rfl⟩
  rw [modelOf_unitCost, modelOf_unitCost]
  norm_num

/-- (7b) **故值层的势不被公理决定**：同一 $lpha,\ C_F$ 下，两个合法 $c_0$ 给出不同的 $V(1)$。
这与范畴层的 `M1_V_ne_M2_V` 同型，但**落在值层自己的对象上**。 -/
theorem value_layer_V_not_determined :
    BoundaryTheory.V 1 1 1 ≠ BoundaryTheory.V 2 1 1 := by
  intro h
  unfold BoundaryTheory.V at h
  norm_num at h

/-- (7c) 搬运版：把 (7b) 用范畴层的模型说出来（供两层同时引用）。 -/
theorem model_V_not_determined :
    (modelOf 1 1 (by norm_num) (by norm_num)).V 1
      ≠ (modelOf 2 1 (by norm_num) (by norm_num)).V 1 := by
  rw [← BoundaryTheory_V_eq_model_V 1 1 (by norm_num) (by norm_num) 1,
      ← BoundaryTheory_V_eq_model_V 2 1 (by norm_num) (by norm_num) 1]
  exact value_layer_V_not_determined

end BoundaryBridge
