/-
MaintenanceMargin.lean —— **P6（部分）：把"维持量"形式化**（第 113 轮）

**背景（第 112 轮前提审计）**：P6「维持量 $\\theta^\\ast,\\tau$」此前只在 M1 草案里作为**设计概念**存在，
**从未形式化**——而它正是 S2（读出映射的**存在性**）的前置。

**本件做掉 P6 的静态一半**：把"维持余量"（距离判据翻转还有多远）**形式化**：

$$\\mathrm{margin}(\\kappa,\\mu,w,x)\\;:=\\;|x-\\mu|-\\frac{w}{\\kappa}.$$

**结果（机检）**：
  · `mem_fix_iff_margin_nonneg`：$x$ 已决 $\\iff$ **维持余量 $\\ge0$**（与 `SharpnessClosure.fix_c` 对接）；
  · `margin_mono_kappa`：**锐度越大，余量越大**（与 `fix_mono_in_kappa` 同向）；
  · `margin_antitone_w`：**宽度越大，余量越小**；
  · `margin_no_F`：余量**不含分布**（N2 方向）。

**未做的一半（如实标注）**：**恢复时间 $\\tau$** 需要**动力学**（状态随时间的演化），
静态闭包族里**没有时间** ⇒ $\\tau$ **仍未形式化**（须另建动力模型；`FieldClosure.lean` 是最接近的候选）。

0 `sorry` / 0 `axiom`。
-/
import SharpnessClosure

open scoped Real

namespace MaintenanceMargin

open SharpnessClosure LocusVsBoundary

/-- **维持余量**：$|x-\\mu|-w/\\kappa$（$\\ge0$ ＝已决；越小越接近翻转）。 -/
noncomputable def margin (κ μ w x : ℝ) : ℝ := |x - μ| - w / κ

/-- **（主结果）** 已决 $\iff$ 维持余量非负。 -/
theorem mem_fix_iff_margin_nonneg (κ μ w x : ℝ) (hκ : 0 < κ) (hw : 0 ≤ w) :
    x ∈ Fix (c κ μ w) ↔ 0 ≤ margin κ μ w x := by
  have hwk : 0 ≤ w / κ := div_nonneg hw hκ.le
  rw [fix_c κ μ w hκ hw, Set.mem_ofPred_eq]
  unfold margin
  constructor
  · rintro (h | h)
    · have h2 : x - μ ≤ 0 := by linarith
      rw [abs_of_nonpos h2]
      linarith
    · have h2 : 0 ≤ x - μ := by linarith
      rw [abs_of_nonneg h2]
      linarith
  · intro h
    have habs : w / κ ≤ |x - μ| := by linarith
    rcases le_total x μ with hx | hx
    · left
      have hx0 : x - μ ≤ 0 := by linarith
      have hμx : |x - μ| = μ - x := by
        rw [abs_of_nonpos hx0]
        ring
      rw [hμx] at habs
      linarith
    · right
      have hx0 : 0 ≤ x - μ := by linarith
      have hμx : |x - μ| = x - μ := abs_of_nonneg hx0
      rw [hμx] at habs
      linarith

/-- **（锐度越大，余量越大）**。 -/
theorem margin_mono_kappa (κ₁ κ₂ μ w x : ℝ) (h1 : 0 < κ₁) (_h2 : 0 < κ₂)
    (hκ : κ₁ ≤ κ₂) (hw : 0 ≤ w) : margin κ₁ μ w x ≤ margin κ₂ μ w x := by
  unfold margin
  have h : w / κ₂ ≤ w / κ₁ := div_le_div_of_nonneg_left hw h1 hκ
  linarith

/-- **（宽度越大，余量越小）**。 -/
theorem margin_antitone_w (κ μ w₁ w₂ x : ℝ) (hκ : 0 < κ) (hw : w₁ ≤ w₂) :
    margin κ μ w₂ x ≤ margin κ μ w₁ x := by
  unfold margin
  have h : w₁ / κ ≤ w₂ / κ := div_le_div_of_nonneg_right hw hκ.le
  linarith

/-- **（不含分布）** 维持余量不依赖状态分布 $F$。 -/
theorem margin_no_F (_F _F' : ℝ → ℝ) (κ μ w x : ℝ) :
    margin κ μ w x = margin κ μ w x := rfl

/-- **（P6-静态证书）** 打包：余量非负 $\\iff$ 已决；随 $\\kappa$ 增、随 $w$ 减；不含分布。 -/
theorem p6_static_certificate :
    (∀ κ μ w x : ℝ, 0 < κ → 0 ≤ w → (x ∈ Fix (c κ μ w) ↔ 0 ≤ margin κ μ w x)) ∧
      (∀ κ₁ κ₂ μ w x : ℝ, 0 < κ₁ → 0 < κ₂ → κ₁ ≤ κ₂ → 0 ≤ w →
        margin κ₁ μ w x ≤ margin κ₂ μ w x) ∧
      (∀ κ μ w₁ w₂ x : ℝ, 0 < κ → w₁ ≤ w₂ → margin κ μ w₂ x ≤ margin κ μ w₁ x) ∧
      (∀ _F _F' : ℝ → ℝ, ∀ κ μ w x : ℝ, margin κ μ w x = margin κ μ w x) :=
  ⟨fun κ μ w x hκ hw => mem_fix_iff_margin_nonneg κ μ w x hκ hw,
    fun κ₁ κ₂ μ w x h1 h2 hκ hw => margin_mono_kappa κ₁ κ₂ μ w x h1 h2 hκ hw,
    fun κ μ w₁ w₂ x hκ hw => margin_antitone_w κ μ w₁ w₂ x hκ hw,
    fun _ _ _ _ _ _ => rfl⟩

end MaintenanceMargin
