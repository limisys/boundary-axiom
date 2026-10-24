/-
ScalingsAndUnits.lean —— 待裁定的"锚定"到底**有多少自由度**（第 77 轮）

**动机**：论文 §7 把"状态轴单位的**物理锚定**"列为待裁定事项，措辞是"未锚定前不主张任何预测"。
这句话**太粗**：它没有说清锚定**究竟固定了什么**。第 76 轮把 §5 的对照强化成一条**可跑实验的预言**之后，
这个问题分量更重——**预言要落到数字上就需要锚定**。

本轮把**缩放结构**机检，从而说明：**锚定只固定一个自由度**，其余全是无量纲的。

**结果**（值层，记 $V,c_0,\\alpha,C_F,\\kappa^\\star,\\sigma^\\ast,\\sigma$）：

  · **`V_smul`**        $V(t c_0,t\\alpha,\\kappa)=t\\,V(c_0,\\alpha,\\kappa)$ —— $V$ 对 $(c_0,\\alpha)$ **一次齐次**；
  · **`kappaStar_smul`** $\\kappa^\\star(tc_0,t\\alpha)=\\kappa^\\star(c_0,\\alpha)$ —— **临界锐度不变**；
  · **`sigmaStar_smul`** $\\sigma^\\ast(t\\alpha,tC_0)=\\sigma^\\ast(\\alpha,C_0)$ —— **张力不变**；
  · **`sigma_smul`**     $\\sigma(tc_0,tC_0,\\kappa)=\\sigma(c_0,C_0,\\kappa)$ —— **局部比不变**；
  · **`c_eq_of_div_eq`** 闭包只依赖 $w/\\kappa$：比值相同则算子相同。

**结论（本轮的实质）**：值层**只依赖无量纲比**与**一个整体尺度**；
而**锚定恰好固定那一个尺度**。**故待裁定事项的自由度是 1，不是"一大片"。**

**范围声明（必须连同本件一起读）**：
本件机检的是**值层**的缩放结构。**闭包侧**（状态轴与 $\\kappa$ 同时缩放时已决集的**等变性**）
**未**在本件机检——那是**下一步**，本件**不主张**它。
换句话说：**"自由度为一"在值层已证，在闭包侧尚待证。**

0 `sorry` / 0 `axiom`。
-/
import BoundaryTheory
import ValueLayerExtension
import SharpnessClosure

open scoped Real

namespace ScalingsAndUnits

/-- **（齐次性）** $V(tc_0,t\\alpha,\\kappa)=t\\,V(c_0,\\alpha,\\kappa)$。 -/
theorem V_smul (t c₀ α κ : ℝ) (hκ : κ ≠ 0) :
    BoundaryTheory.V (t * c₀) (t * α) κ = t * BoundaryTheory.V c₀ α κ := by
  unfold BoundaryTheory.V
  field_simp

/-- **（临界锐度不变）** $\\kappa^\\star$ 在 $(c_0,\\alpha)$ 整体缩放下不变。 -/
theorem kappaStar_smul (t c₀ α : ℝ) (ht : 0 < t) (hc₀ : c₀ ≠ 0) :
    BoundaryTheory.kappaStar (t * c₀) (t * α) = BoundaryTheory.kappaStar c₀ α := by
  unfold BoundaryTheory.kappaStar
  have h : t * α / (3 * (t * c₀)) = α / (3 * c₀) := by field_simp
  rw [h]

/-- **（张力不变）** $\\sigma^\\ast$ 在 $(\\alpha,C_0)$ 整体缩放下不变。 -/
theorem sigmaStar_smul (t α C₀ : ℝ) (ht : t ≠ 0) :
    BoundaryTheory.sigmaStar (t * α) (t * C₀) = BoundaryTheory.sigmaStar α C₀ := by
  unfold BoundaryTheory.sigmaStar
  field_simp

/-- **（局部比不变）** $\\sigma$ 在 $(c_0,C_0)$ 整体缩放下不变。 -/
theorem sigma_smul (t c₀ C₀ κ : ℝ) (ht : t ≠ 0) :
    ValueLayerExtension.sigma (t * c₀) (t * C₀) κ = ValueLayerExtension.sigma c₀ C₀ κ := by
  unfold ValueLayerExtension.sigma
  field_simp

/-- **（只依赖比值）** 锐度闭包只依赖 $w/\\kappa$。 -/
theorem c_eq_of_div_eq {κ κ' μ w w' : ℝ} (h : w / κ = w' / κ') :
    SharpnessClosure.c κ μ w = SharpnessClosure.c κ' μ w' := by
  funext z
  unfold SharpnessClosure.c
  rw [h]

/-- **（收官）** 锚定的自由度**恰为一**：整体缩放使 $V$ 乘以 $t$，
而 $\\kappa^\\star$、$\\sigma^\\ast$、$\\sigma$ **全部不变**。 -/
theorem anchoring_fixes_one_degree :
    (∀ (t c₀ α κ : ℝ), κ ≠ 0 →
        BoundaryTheory.V (t * c₀) (t * α) κ = t * BoundaryTheory.V c₀ α κ)
    ∧ (∀ (t c₀ α : ℝ), 0 < t → c₀ ≠ 0 →
        BoundaryTheory.kappaStar (t * c₀) (t * α) = BoundaryTheory.kappaStar c₀ α)
    ∧ (∀ (t α C₀ : ℝ), t ≠ 0 →
        BoundaryTheory.sigmaStar (t * α) (t * C₀) = BoundaryTheory.sigmaStar α C₀)
    ∧ (∀ (t c₀ C₀ κ : ℝ), t ≠ 0 →
        ValueLayerExtension.sigma (t * c₀) (t * C₀) κ = ValueLayerExtension.sigma c₀ C₀ κ) :=
  ⟨fun t c₀ α κ hκ => V_smul t c₀ α κ hκ,
   fun t c₀ α ht hc₀ => kappaStar_smul t c₀ α ht hc₀,
   fun t α C₀ ht => sigmaStar_smul t α C₀ ht,
   fun t c₀ C₀ κ ht => sigma_smul t c₀ C₀ κ ht⟩

end ScalingsAndUnits
