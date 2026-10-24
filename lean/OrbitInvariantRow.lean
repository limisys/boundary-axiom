/-
OrbitInvariantRow.lean —— 轨道不变量 `I(F) = C_F · F'(0)` 的**机检行**（第 69 轮）

**动机**：§7 的"未证"清单里有"**核心常数表的 probit／Cauchy 行**"，而范畴层 `Orbit.lean` 自己注明
它的轨道不变量数值表是"**确定性计算，非机检**"，并为此专门加了"零浮点负定理"。
本轮把该表**能机检的行**机检掉，并**明确写下不能机检的行**——不把清单含糊化。

**结果**：

  · **`I_sig`**      轨道不变量 `I(F) = C_F·F'(0)` 在 logistic 核上 **$=π^2/12$**（机检）；
  · **`I_rescale`**  同一轨道的核给出**同一个** $I$（由 `coreConstant_rescale` 与链式法则）；
  · **`I_rescale_two_sig`**  故 `rescale 2 σ`（即 tanh 行）与 logistic **同值** $π^2/12$——两行**一致**；
  · **仍非机检（如实记下）**：**probit 行**。`Orbit.lean` 的 $C_\Phi\approx1.8064$ 是数值积分
    （$I(\Phi)=C_\Phi\Phi'(0)\approx0.720647$），本轮**不**声称它，也**不**把它写成定理。

**顺带核清一处疑似前后矛盾**：`KernelModuli.lean` 表里的 `1.8064` 与 `Orbit.lean` 里的 `0.720647`
**不是**同一个量——前者是 $C_\Phi$，后者是 $I(\Phi)=C_\Phi\cdot\Phi'(0)$（$\Phi'(0)=1/\sqrt{2\pi}$）。
二者**相容**（$1.806395\times0.398942\approx0.720647$），**不是**矛盾。

0 `sorry` / 0 `axiom`。
-/
import BoundaryBridge_layers

open scoped Real

namespace OrbitInvariantRow

/-- **轨道不变量** $I(F)=C_F\cdot F'(0)$。 -/
noncomputable def I (F : ℝ → ℝ) : ℝ := CausModel.coreConstant F * deriv F 0

/-- **（logistic 行，机检）** $I(\sigma)=\frac{\pi^2}{3}\cdot\frac14=\frac{\pi^2}{12}$。 -/
theorem I_sig : I CausModel.sig = Real.pi ^ 2 / 12 := by
  unfold I
  rw [BoundaryBridge.coreConstant_sig_eq_pi_sq_div_three, CausModel.deriv_sig_zero]
  ring

/-- 重标定核在原点的导数按 $\lambda$ 缩放：$(\lambda F)'(0)=\lambda F'(0)$。 -/
theorem deriv_rescale_zero (F : ℝ → ℝ) (lam : ℝ) :
    deriv (CausModel.rescale lam F) 0 = lam * deriv F 0 := by
  have h : CausModel.rescale lam F = fun z : ℝ => F (lam * z) := rfl
  rw [h, deriv_comp_mul_left, mul_zero, smul_eq_mul]

/-- **（同轨一致）** 同一轨道的核给出**同一个** $I$：
由 $C_{\lambda F}=C_F/\lambda$ 与 $(\lambda F)'(0)=\lambda F'(0)$，两者相乘抵消。 -/
theorem I_rescale (F : ℝ → ℝ) {lam : ℝ} (hlam : 0 < lam) :
    I (CausModel.rescale lam F) = I F := by
  unfold I
  rw [CausModel.coreConstant_rescale F hlam, deriv_rescale_zero F lam]
  field_simp

/-- **（tanh 行，机检）** $\mathrm{rescale}\,2\,\sigma$ 与 logistic **同轨**，故 $I$ 相同：$\pi^2/12$。 -/
theorem I_rescale_two_sig : I (CausModel.rescale 2 CausModel.sig) = Real.pi ^ 2 / 12 := by
  rw [I_rescale CausModel.sig (by norm_num : (0:ℝ) < 2), I_sig]

end OrbitInvariantRow
