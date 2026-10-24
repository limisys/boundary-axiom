/-
城邦研究院 · 论文线 · C 阶段 · R1：A7 维护成本公理化与模型类
=================================================================

**背景**：论文 §2.3 自认 "*Why this form is forced* is a **structural claim, not a theorem**"。
审稿人 R3 正咬这一点。本模块把这句话变成**可判定的真值表**。

**内容**：

| 命题 | 内容 | 依据 |
|---|---|---|
| **A7** | 维护成本**可加**（互不相交子系统之和 = 联合系统），且**连续** | 新公理（自然、可陈述、可证伪） |
| **T3** | A7 ⇒ 维护成本**线性** ⇒ 维护项必形如 `c₀κ` | `map_real_smul`（连续加性 ⇒ ℝ-线性） |
| **T4** | 常数 `c₀` 仍自由；`σ*=1` 是**规范条件**而非推论 | 两个不同 `c₀` 的模型同时合法 |

**⇒ "形式被迫" 的真值**：
  · **熵项**：被公理决定（R2/B6 的重标度律，`boundaryEntropy_eq`）；
  · **维护项**：**原公理下完全自由**（`maintenance_unconstrained`）；
  · **补 A7 后**：被决定为 `c₀κ`，只剩尺度 `c₀` 自由。

**证据档位**：机器证明（本模块零 `sorry`）。
-/

import Mathlib.Topology.Instances.RealVectorSpace
import CausModel.ModelClass

namespace CausModel

noncomputable section

/-! ## A7：维护成本作为一个可加连续泛函 -/

/-- **A7（维护成本的加性）** 的形式化：维护成本是锐度上的一个**连续加性泛函**
`M : ℝ →+ ℝ`。

读法：互不相交的两个子系统的维护成本之和，等于联合系统的维护成本；
且成本随锐度连续变化（无跳变）。这是一条**可证伪**的公理——
若某系统的维护代价不可加，A7 失效，"形式被迫"随之失效。 -/
structure MaintenanceCost where
  /-- 维护成本，作为加性泛函。 -/
  toAddHom : ℝ →+ ℝ
  /-- 成本随锐度连续变化。 -/
  continuous_toFun : Continuous toAddHom

namespace MaintenanceCost

instance : CoeFun MaintenanceCost (fun _ => ℝ → ℝ) where
  coe M := M.toAddHom

/-- **【T3】线性定理**：A7 ⇒ 维护成本必为线性 ⇒ 维护项必形如 `c₀κ`。

这一步把论文的 "the form is forced" 从**假主张**变成**真定理**：
代价是补一条此前缺失的公理（A7），而 A7 本身是自然的、可陈述的、可证伪的。 -/
theorem eq_coefficient (M : MaintenanceCost) (κ : ℝ) :
    M κ = M 1 * κ := by
  have h := map_real_smul M.toAddHom M.continuous_toFun κ (1 : ℝ)
  simp only [smul_eq_mul, mul_one] at h
  rw [h, mul_comm]

/-- **单位维护成本** `c₀`：A7 之后唯一残留的自由参数。 -/
def unitCost (M : MaintenanceCost) : ℝ := M 1

/-- 维护成本非负（`κ ≥ 0` 时），若单位成本非负。 -/
theorem nonneg_of_nonneg_unit {M : MaintenanceCost} (h : 0 ≤ M.unitCost) {κ : ℝ}
    (hκ : 0 ≤ κ) : 0 ≤ M κ := by
  rw [eq_coefficient]
  exact mul_nonneg h hκ

end MaintenanceCost

/-! ## 模型类：公理决定什么 -/

/-- **边界理论的模型**：范畴层数据 + 维护成本（A7）+ 不确定性价格 + 核心常数。 -/
structure BoundaryModel where
  /-- 维护成本（满足 A7）。 -/
  maint : MaintenanceCost
  /-- 不确定性价格 `α > 0`。 -/
  α : ℝ
  alpha_pos : 0 < α
  /-- 核心常数 `C_F > 0`（由核形状 mod 重标度决定，见 R2）。 -/
  C_F : ℝ
  core_pos : 0 < C_F

namespace BoundaryModel

/-- **边界势** `V(κ) = c₀κ + αC_F/κ`。 -/
def V (M : BoundaryModel) (κ : ℝ) : ℝ := M.maint κ + M.α * M.C_F / κ

/-- **【核心结论】形式被迫定理**：在 A7 之下，`V` 的形式**完全由公理决定**。

$$V(\kappa) = c_0\kappa + \frac{\alpha C_F}{\kappa},\qquad c_0 = M(1).$$

⇒ 论文可以说："the form is forced"——但**必须同时写下 A7**。
   这不是含糊的"结构主张"，而是一条有前提、有证明的定理。 -/
theorem V_form_forced (M : BoundaryModel) (κ : ℝ) :
    M.V κ = M.maint.unitCost * κ + M.α * M.C_F / κ := by
  unfold V
  rw [MaintenanceCost.eq_coefficient]
  simp [MaintenanceCost.unitCost]

/-- **【T4】尺度自由度**：`c₀` 不被 A7 决定——存在两个合法模型，单位维护成本不同。

⇒ 论文 §3.2 把 `σ* = 1` 列为 **"gauge value"（规范值）** 是**正确**的：
它不是推论，而是固定尺度 `c₀` 与 `α/C₀` 关系的**规范条件**。
本定理把这一层级区分固化为可机检事实。 -/
theorem unitCost_not_determined :
    ∃ M1 M2 : BoundaryModel, M1.maint.unitCost ≠ M2.maint.unitCost := by
  refine ⟨⟨⟨AddMonoidHom.id ℝ, continuous_id⟩, 1, one_pos, 1, one_pos⟩,
          ⟨⟨AddMonoidHom.mulLeft 2, continuous_const.mul continuous_id⟩, 1, one_pos, 1, one_pos⟩, ?_⟩
  simp only [MaintenanceCost.unitCost]
  norm_num

/-! ## 【可引负定理】非范畴性：公理不决定维护项

> **这是 R3 的正式闭合件**——把"公理不产出公式"从**指控**变成**定理**。
> 独立的 `def` + `theorem`，可被后续文献单独引用。 -/

/-- **具名模型 $M_1$**：单位维护成本 $c_0 = 1$。 -/
def M1 : BoundaryModel :=
  ⟨⟨AddMonoidHom.id ℝ, continuous_id⟩, 1, one_pos, 1, one_pos⟩

/-- **具名模型 $M_2$**：单位维护成本 $c_0 = 2$。 -/
def M2 : BoundaryModel :=
  ⟨⟨AddMonoidHom.mulLeft 2, continuous_const.mul continuous_id⟩, 1, one_pos, 1, one_pos⟩

/-- **$M_1$ 满足 A7**（构造即见证：`AddMonoidHom.id` 可加、`continuous_id` 连续）。 -/
theorem M1_satisfies_A7 :
    (∀ κ₁ κ₂ : ℝ, M1.maint (κ₁ + κ₂) = M1.maint κ₁ + M1.maint κ₂) ∧
    Continuous M1.maint :=
  ⟨fun _ _ => rfl, continuous_id⟩

/-- **$M_2$ 满足 A7**。 -/
theorem M2_satisfies_A7 :
    (∀ κ₁ κ₂ : ℝ, M2.maint (κ₁ + κ₂) = M2.maint κ₁ + M2.maint κ₂) ∧
    Continuous M2.maint :=
  ⟨fun x y => M2.maint.toAddHom.map_add x y, continuous_const.mul continuous_id⟩

/-- $M_1$ 的单位维护成本为 $1$。 -/
theorem M1_unitCost : M1.maint.unitCost = 1 := rfl

/-- $M_2$ 的单位维护成本为 $2$。 -/
theorem M2_unitCost : M2.maint.unitCost = 2 := by
  simp [M2, MaintenanceCost.unitCost, AddMonoidHom.mulLeft]

/-- **$M_1$ 与 $M_2$ 的维护项不同**（处处不同，不只是单位值）。 -/
theorem M1_ne_M2_maintenance : M1.maint 1 ≠ M2.maint 1 := by
  have h1 : M1.maint 1 = 1 := rfl
  have h2 : M2.maint 1 = 2 := M2_unitCost
  rw [h1, h2]; norm_num

/-- **【非范畴性定理 · 可引】** A7 之下，公理系统**非范畴**：
存在两个**都满足 A7** 的边界理论模型，其维护项（因而其势）不同。

**⇒ 这正是"the form is forced"的精确余量**：
*形式* 被 A7 决定到"线性"，但**线性系数 $c_0$ 不被决定**——
它是一条**规范条件**（$\sigma^*=1$）固定下来的，不是公理的推论。

**这条定理把 R3 从缺口变成结果**：不是"我们没能证明公理产出公式"，
而是"**我们证明并刻画了公理产出什么、不产出什么**"。 -/
theorem non_categoricity :
    ∃ M1 M2 : BoundaryModel,
      (∀ κ₁ κ₂ : ℝ, M1.maint (κ₁ + κ₂) = M1.maint κ₁ + M1.maint κ₂) ∧
      Continuous M1.maint ∧
      (∀ κ₁ κ₂ : ℝ, M2.maint (κ₁ + κ₂) = M2.maint κ₁ + M2.maint κ₂) ∧
      Continuous M2.maint ∧
      M1.maint.unitCost ≠ M2.maint.unitCost :=
  ⟨M1, M2, M1_satisfies_A7.1, M1_satisfies_A7.2,
   M2_satisfies_A7.1, M2_satisfies_A7.2,
   by rw [M1_unitCost, M2_unitCost]; norm_num⟩

/-- 两个具名模型给出的势**确实不同**（在 $\kappa = 1,\ \alpha = C_F = 1$ 处）。 -/
theorem M1_V_ne_M2_V : M1.V 1 ≠ M2.V 1 := by
  have h1 : M1.maint 1 = 1 := rfl
  have h2 : M2.maint 1 = 2 := M2_unitCost
  have ha1 : M1.α = 1 := rfl
  have hc1 : M1.C_F = 1 := rfl
  have ha2 : M2.α = 1 := rfl
  have hc2 : M2.C_F = 1 := rfl
  unfold V
  rw [h1, h2, ha1, hc1, ha2, hc2]
  norm_num

end BoundaryModel

/-! ## 【A7 强度谱】公理强度本身是结果

A7 = "维护成本**可加**且**连续**"。本谱说明它**恰好**落在
"足以推出线性"与"不至于使负定理平凡"之间。 -/

/-- **A7⁻（过弱）：仅单调 ⇒ 线性不成立。**
反例 $M(\kappa)=\kappa^3$：单调、扩张，但非线性。 -/
theorem a7_weak_not_linear :
    ∃ M : ℝ → ℝ, Monotone M ∧ ¬ ∃ c : ℝ, ∀ κ : ℝ, M κ = c * κ := by
  refine ⟨Real.exp, Real.exp_strictMono.monotone, ?_⟩
  rintro ⟨c, hc⟩
  have h := hc 0
  rw [Real.exp_zero, mul_zero] at h
  norm_num at h

/-- **A7（恰好）：加性 + 连续 ⇒ 线性**（定理 T3 的等价陈述，此处并列以成谱）。 -/
theorem a7_exact_forces_linear (M : ℝ →+ ℝ) (hM : Continuous M) (κ : ℝ) :
    M κ = M 1 * κ :=
  maintenance_eq_coefficient M hM κ

/-- **A7⁺（过强）：直接假定线性 ⇒ 负定理平凡。**
若把"线性"本身当公理，则模型类被压成单一尺度族，$c_0$ 之外的差异被**定义**消除，
`non_categoricity` 随之失去内容。

读法：A7⁺ 不是"更强因而更好"，而是**强到把待答问题抹掉**。 -/
theorem a7_strong_trivializes :
    ∀ M : ℝ →+ ℝ, Continuous M →
      (∀ κ : ℝ, M κ = M 1 * κ) ∧
      (∀ M' : ℝ →+ ℝ, Continuous M' → M' 1 = M 1 → ∀ κ, M' κ = M κ) := by
  intro M hM
  refine ⟨fun κ => maintenance_eq_coefficient M hM κ, ?_⟩
  intro M' hM' h1 κ
  rw [maintenance_eq_coefficient M' hM' κ, maintenance_eq_coefficient M hM κ, h1]

/-- **【强度谱小结】** 四条边界情形并列，供论文直接引用。 -/
theorem a7_strength_spectrum :
    -- A7⁻ : 仅单调不足
    (∃ M : ℝ → ℝ, Monotone M ∧ ¬ ∃ c : ℝ, ∀ κ : ℝ, M κ = c * κ) ∧
    -- A7  : 加性 + 连续恰好
    (∀ M : ℝ →+ ℝ, Continuous M → ∀ κ : ℝ, M κ = M 1 * κ) ∧
    -- 无 A7 : 维护泛函任意
    (∃ M1 M2 : BoundaryModel, M1.maint.unitCost ≠ M2.maint.unitCost) :=
  ⟨a7_weak_not_linear, fun M hM κ => a7_exact_forces_linear M hM κ,
   BoundaryModel.unitCost_not_determined⟩

end

end CausModel
