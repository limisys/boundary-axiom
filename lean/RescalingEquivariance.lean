/-
RescalingEquivariance.lean —— 缩放**等变性**（闭包侧），补上第 77 轮明确留空的那一半（第 78 轮）

**动机**：第 77 轮把"锚定有多少自由度"机检到**值层**（$V$ 一次齐次；$\\kappa^\\star,\\sigma^\\ast,\\sigma$ 不变），
并**明确留下**一句范围声明：

> **闭包侧**（状态轴与 $\\kappa$ 同时缩放时已决集的**等变性**）**未**机检——本件不主张它。

本轮补上它。**关键是把半宽 $d:=w/\\kappa$ 显式提出**：这样不等式里不再出现嵌套除法，
代数退化为**一次除法引理的应用**（第 77 轮之所以卡住，正是因为把嵌套除法交给 `linarith`）。

**结果**：

  · **`mem_tailD_rescale`**   $\\mu+\\frac{x-\\mu}{t}$ 落在半宽 $d/t$ 的两条尾上 $\\iff$ $x$ 落在半宽 $d$ 的两条尾上；
  · **`mem_tailSet_rescale`** 锐度写法：$\\mu+\\frac{x-\\mu}{t}\\in\\mathrm{tailSet}(t\\kappa,\\mu,w)\\iff x\\in\\mathrm{tailSet}(\\kappa,\\mu,w)$；
  · **`tailSet_rescale_image`** 状态轴缩放把**已决集**映成**新锐度下的已决集**；
  · **`fix_rescale_image`** 用 $\\mathrm{Fix}$ 重述：$\\mu+\\frac{\\cdot-\\mu}{t}''\\,\\mathrm{Fix}(c_{\\kappa,\\mu,w})=\\mathrm{Fix}(c_{t\\kappa,\\mu,w})$。

**于是第 77 轮那句范围声明可以划掉**：**"自由度为一"在值层与闭包侧都已机检**。

0 `sorry` / 0 `axiom`。
-/
import ScalingsAndUnits
import UnifiedClosure
import SharpnessClosure
import LocusVsBoundary

open scoped Real

namespace RescalingEquivariance

/-- **半宽写法**的两条尾：不再含除法，便于缩放。 -/
def tailD (μ d : ℝ) : Set ℝ := {z : ℝ | z ≤ μ - d ∨ μ + d ≤ z}

/-- 锐度写法与半宽写法一致。 -/
theorem tailSet_eq_tailD (κ μ w : ℝ) : UnifiedClosure.tailSet κ μ w = tailD μ (w / κ) := rfl

/-- **状态轴缩放**：$x\\mapsto\\mu+\\frac{x-\\mu}{t}$。 -/
noncomputable def rescaleState (t μ x : ℝ) : ℝ := μ + (x - μ) / t

/-- 其逆：$y\\mapsto\\mu+(y-\\mu)t$。 -/
noncomputable def rescaleStateInv (t μ y : ℝ) : ℝ := μ + (y - μ) * t

theorem rescale_inv (t μ x : ℝ) (ht : t ≠ 0) :
    rescaleStateInv t μ (rescaleState t μ x) = x := by
  unfold rescaleStateInv rescaleState
  field_simp
  ring

theorem rescale_inv' (t μ y : ℝ) (ht : t ≠ 0) :
    rescaleState t μ (rescaleStateInv t μ y) = y := by
  unfold rescaleState rescaleStateInv
  field_simp
  ring

/-- 除以正数保持 $\\le$。 -/
theorem div_le_div_iff_of_pos (t : ℝ) (ht : 0 < t) (a b : ℝ) :
    a / t ≤ b / t ↔ a ≤ b := by
  constructor
  · intro h
    have := mul_le_mul_of_nonneg_right h ht.le
    rwa [div_mul_cancel₀ a ht.ne', div_mul_cancel₀ b ht.ne'] at this
  · intro h
    exact div_le_div_of_nonneg_right h ht.le

/-- **（核心）** 状态轴缩放把半宽 $d$ 的两条尾**送到**半宽 $d/t$ 的两条尾。 -/
theorem mem_tailD_rescale (t μ d x : ℝ) (ht : 0 < t) :
    rescaleState t μ x ∈ tailD μ (d / t) ↔ x ∈ tailD μ d := by
  have h1 : rescaleState t μ x ≤ μ - d / t ↔ x ≤ μ - d := by
    unfold rescaleState
    rw [show μ + (x - μ) / t ≤ μ - d / t ↔ (x - μ) / t ≤ -(d / t) by
      constructor <;> intro h <;> linarith]
    rw [← neg_div, div_le_div_iff_of_pos t ht (x - μ) (-d)]
    constructor <;> intro h <;> linarith
  have h2 : μ + d / t ≤ rescaleState t μ x ↔ μ + d ≤ x := by
    unfold rescaleState
    rw [show μ + d / t ≤ μ + (x - μ) / t ↔ d / t ≤ (x - μ) / t by
      constructor <;> intro h <;> linarith]
    rw [div_le_div_iff_of_pos t ht d (x - μ)]
    constructor <;> intro h <;> linarith
  unfold tailD
  simp only [Set.mem_ofPred_eq]
  exact ⟨fun h => h.elim (fun hh => Or.inl (h1.mp hh)) (fun hh => Or.inr (h2.mp hh)),
         fun h => h.elim (fun hh => Or.inl (h1.mpr hh)) (fun hh => Or.inr (h2.mpr hh))⟩

/-- **（锐度写法）** $\\mu+\\frac{x-\\mu}{t}\\in\\mathrm{tailSet}(t\\kappa,\\mu,w)\\iff x\\in\\mathrm{tailSet}(\\kappa,\\mu,w)$。 -/
theorem mem_tailSet_rescale (t κ μ w x : ℝ) (ht : 0 < t) :
    rescaleState t μ x ∈ UnifiedClosure.tailSet (t * κ) μ w
      ↔ x ∈ UnifiedClosure.tailSet κ μ w := by
  have hw : w / (t * κ) = (w / κ) / t := by field_simp
  rw [show UnifiedClosure.tailSet (t * κ) μ w = tailD μ ((w / κ) / t) by
        rw [tailSet_eq_tailD (t * κ) μ w, hw],
      show UnifiedClosure.tailSet κ μ w = tailD μ (w / κ) from tailSet_eq_tailD κ μ w]
  exact mem_tailD_rescale t μ (w / κ) x ht

/-- **（集合形式 · 主结果）** 状态轴缩放把 $c_{\\kappa,\\mu,w}$ 的已决集**映成** $c_{t\\kappa,\\mu,w}$ 的已决集。 -/
theorem tailSet_rescale_image (t κ μ w : ℝ) (ht : 0 < t) :
    rescaleState t μ '' UnifiedClosure.tailSet κ μ w
      = UnifiedClosure.tailSet (t * κ) μ w := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_tailSet_rescale t κ μ w x ht).mpr hx
  · intro hy
    refine ⟨rescaleStateInv t μ y, ?_, rescale_inv' t μ y ht.ne'⟩
    rw [← rescale_inv' t μ y ht.ne'] at hy
    exact (mem_tailSet_rescale t κ μ w (rescaleStateInv t μ y) ht).mp hy

/-- **（`Fix` 写法）** 补上第 77 轮留空的那一半：
$\\mu+\\frac{\\cdot-\\mu}{t}''\\,\\mathrm{Fix}(c_{\\kappa,\\mu,w})=\\mathrm{Fix}(c_{t\\kappa,\\mu,w})$。 -/
theorem fix_rescale_image (t κ μ w : ℝ) (ht : 0 < t) (hκ : 0 < κ) (hw : 0 ≤ w) :
    rescaleState t μ '' LocusVsBoundary.Fix (SharpnessClosure.c κ μ w)
      = LocusVsBoundary.Fix (SharpnessClosure.c (t * κ) μ w) := by
  rw [SharpnessClosure.fix_c κ μ w hκ hw, SharpnessClosure.fix_c (t * κ) μ w (mul_pos ht hκ) hw]
  exact tailSet_rescale_image t κ μ w ht

/-- **（收官）** 第 77 轮的"自由度为一"现在**两侧都已机检**：
值层的缩放结构（见 `ScalingsAndUnits`）＋ 闭包侧的状态轴等变性（本件）。 -/
theorem anchoring_freedom_done_both_sides :
    (∀ (t κ μ w : ℝ), 0 < t → rescaleState t μ '' UnifiedClosure.tailSet κ μ w
        = UnifiedClosure.tailSet (t * κ) μ w)
    ∧ (∀ (t κ μ w : ℝ), 0 < t → 0 < κ → 0 ≤ w →
        rescaleState t μ '' LocusVsBoundary.Fix (SharpnessClosure.c κ μ w)
          = LocusVsBoundary.Fix (SharpnessClosure.c (t * κ) μ w)) :=
  ⟨fun t κ μ w ht => tailSet_rescale_image t κ μ w ht,
   fun t κ μ w ht hκ hw => fix_rescale_image t κ μ w ht hκ hw⟩

end RescalingEquivariance
