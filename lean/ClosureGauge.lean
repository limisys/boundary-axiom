/-
ClosureGauge.lean —— 锐度族的**规范对称性**：闭包只依赖比值 `w/κ`（第 103 轮）

**动机**：纲领的候选 F（边界 ≅ 判据）被判为**规范依赖同构**（第 101／102 轮）：
`fix_c_eq_decided` 里 θ 是**自由参数**，而 V 的极小只定出 κ★。本轮把这件事**做成定理**：

  · 闭包 `c κ μ w` 只通过**比值** `w/κ` 依赖参数——
    故 **(κ, w) → (λκ, λw)** 是闭包的一条**一维规范方向**（Gauge direction）；
  · 于是「已决集」（＝边界）**在同一条规范轨道上不变**；
  · 而 V 并**不**在这条变换下不变（`V` 只对 (c₀,α) 齐次，κ 不被缩放）——
    ⇒ **极小化定出"尺度"（κ★），但定不出"水平"（w，等价地 θ）**。

**这一步的意义**：F 的"规范依赖"从一句判断变成**定理**（存在一条闭包看不见的自由方向）。
它同时说明：要让 F 成为**内禀**同构，必须**新增一个把"水平"与"尺度"绑定的原语**——
这不是构造技巧问题，而是**量库缺一个水平原语**。

0 `sorry` / 0 `axiom`。
-/
import SharpnessClosure

open scoped Real

namespace ClosureGauge

open SharpnessClosure LocusVsBoundary

/-- **（规范不变性 · 主结果）** 闭包在 **(κ,w) 联合缩放**下不变：
$c_{\lambda\kappa,\mu,\lambda w}=c_{\kappa,\mu,w}$（$\lambda>0$）。 -/
theorem c_scale (κ μ w z : ℝ) {lam : ℝ} (hlam : 0 < lam) :
    c (lam * κ) μ (lam * w) z = c κ μ w z := by
  have hlam0 : lam ≠ 0 := hlam.ne'
  unfold c
  have h : (lam * w) / (lam * κ) = w / κ := by
    field_simp
  rw [h]

/-- **（等价形式）** 闭包只依赖**比值** $w/\kappa$：把 $w$ 换成 $(\kappa/\kappa')\,w$ 而同时把 $\kappa$ 换成 $\kappa'$，
闭包不变。 -/
theorem c_ratio (κ κ' μ w z : ℝ) (hκ : 0 < κ) (hκ' : 0 < κ') :
    c κ' μ ((κ' / κ) * w) z = c κ μ w z := by
  have h1 : κ' / κ * w = (κ' / κ) * w := rfl
  have h2 : (κ' / κ) * w / κ' = w / κ := by
    field_simp
  unfold c
  rw [h1, h2]

/-- **（边界的规范不变性）** 已决集＝刚性面在联合缩放下**不变**：
$\mathrm{Fix}(c_{\lambda\kappa,\mu,\lambda w})=\mathrm{Fix}(c_{\kappa,\mu,w})$。 -/
theorem fix_scale (κ μ w : ℝ) {lam : ℝ} (hlam : 0 < lam) :
    Fix (c (lam * κ) μ (lam * w)) = Fix (c κ μ w) := by
  have hfun : c (lam * κ) μ (lam * w) = c κ μ w := by
    funext z
    exact c_scale κ μ w z hlam
  rw [hfun]

/-- **（"看不见"的形式）** 刚性面的**下水平表述**同样只含比值：
$\mathrm{Fix}(c_{\kappa,\mu,w})=\{z: z\le\mu-w/\kappa\ \vee\ \mu+w/\kappa\le z\}$。 -/
theorem fix_ratio_form (κ μ w : ℝ) (hκ : 0 < κ) (hw : 0 ≤ w) :
    Fix (c κ μ w) = {z : ℝ | z ≤ μ - w / κ ∨ μ + w / κ ≤ z} :=
  fix_c κ μ w hκ hw

end ClosureGauge
