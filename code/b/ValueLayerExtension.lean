/-
  Copyright 2026 Xueqiang Gao (高学强) · ORCID 0009-0008-3821-3454
  Licensed under the Apache License, Version 2.0 (see LICENSE).
  Original publication source: caseos.cn/research — https://caseos.cn/research/
  First public release 2026-10-09; formal publication 2026-10-20.
  Part of the B-line canonical subset (group 2): 53 files / 417 theorems+lemmas / 77 definitions.
  Attribution header added at publication; proof bodies unchanged.
-/

/-
ValueLayerExtension.lean —— 值层扩展件（**去重复版**，第 59 轮）

**改动**：本件**导入冻结的值层** `BoundaryTheory`，**不再重复声明** `V`/`kappaStar`/`sigmaStar`/`force`/`kappaStar_sq`
（旧稿为求自足复制了它们，导致五个 Lean 文件不能互相 import——见论文附录 A）。
**第 62 轮命名自纠**：第 59 轮的去重正则把限定名误加到**声明名**上，产生了
`theorem BoundaryTheory.deriv_V_eq` 这种名字；现改回 `deriv_V_eq` 等（引用处已同步）。
本件只新增**库中原本没有的**东西：`def sigma` 与下列定理。
状态：Lean 4.33.0 + Mathlib 编译通过（exit 0，无 sorry / axiom）。
-/
import BoundaryTheory
open scoped Real Topology
namespace ValueLayerExtension

/-- **新增 def**：功能压差 σ(κ) = (c₀/C₀)·κ²。
原值层只有常数 `BoundaryTheory.sigmaStar`；把 σ 提升为函数，是"两义"能被陈述的前提。 -/
noncomputable def sigma (c₀ C₀ : ℝ) (κ : ℝ) : ℝ := (c₀ / C₀) * κ ^ 2

/-! ## 一 · 一般 κ 的导数（`BoundaryTheory.deriv_V_kappaStar` 的推广）

原文件只证 κ = κ* 处 BoundaryTheory.V′=0。下面这条对一切 κ ≠ 0 给出 BoundaryTheory.V′ 的闭式。
证明手法照原文件 `BoundaryTheory.deriv_V_kappaStar` 的结构（`deriv_add` → 逐项 → `field_simp` → `ring`）。 -/

theorem deriv_V_eq (c₀ α : ℝ) (κ : ℝ) (hκ : κ ≠ 0) :
    deriv (fun κ : ℝ => BoundaryTheory.V c₀ α κ) κ = c₀ - α * (Real.pi ^ 2) / (3 * κ ^ 2) := by
  unfold BoundaryTheory.V
  change deriv ((fun κ : ℝ => c₀ * κ) + (fun κ : ℝ => (α * (Real.pi ^ 2) / 3) / κ)) κ
      = c₀ - α * (Real.pi ^ 2) / (3 * κ ^ 2)
  rw [deriv_add]
  · rw [deriv_const_mul_id, deriv_const_div_id]
    field_simp [hκ]
    ring
  · fun_prop
  · fun_prop

/-- 与既有 `BoundaryTheory.force` 定义对接：BoundaryTheory.V′(κ) = −BoundaryTheory.force(κ)。 -/
theorem deriv_V_eq_neg_force (c₀ α : ℝ) (κ : ℝ) (hκ : κ ≠ 0) :
    deriv (fun κ : ℝ => BoundaryTheory.V c₀ α κ) κ = - BoundaryTheory.force c₀ α κ := by
  rw [deriv_V_eq c₀ α κ hκ, BoundaryTheory.force]
  ring

/-! ## 二 · 式 (2)：BoundaryTheory.V′(κ) = c₀·(1 − σ*/σ(κ))

这是本轮推进的核心式：它把"三态"（σ<σ* / = / >）与势的单调性绑成同一件事。
**注意**：原文件已证的 `sigmaStar_eq_one_iff`（σ*=1 ⟺ π²α = 3C₀）**不是我这两条的新内容**，
本文件不重复声称它。 -/

theorem deriv_V_eq_sigma_form (c₀ C₀ α : ℝ) (κ : ℝ)
    (hκ : κ ≠ 0) (hc₀ : c₀ ≠ 0) (hC₀ : C₀ ≠ 0) :
    deriv (fun κ : ℝ => BoundaryTheory.V c₀ α κ) κ = c₀ * (1 - BoundaryTheory.sigmaStar α C₀ / sigma c₀ C₀ κ) := by
  rw [deriv_V_eq c₀ α κ hκ]
  unfold sigma BoundaryTheory.sigmaStar
  field_simp [hκ, hc₀, hC₀, Real.pi_ne_zero]

/-! ## 三 · 式 (1)：σ(κ) = σ*·(κ²/κ*²)

右端的 `π²α/(3c₀)` 即 `BoundaryTheory.kappaStar_sq` 给出的 κ*²，故本式即"σ 是相对锐度的平方"。
原文件**没有** σ(κ)，故本式在库中无对应物。 -/

theorem sigma_eq_sigmaStar_mul_ratio (c₀ C₀ α : ℝ) (κ : ℝ)
    (hc₀ : c₀ ≠ 0) (hC₀ : C₀ ≠ 0) (hα : α ≠ 0) :
    sigma c₀ C₀ κ = BoundaryTheory.sigmaStar α C₀ * (κ ^ 2 / ((Real.pi ^ 2) * α / (3 * c₀))) := by
  unfold sigma BoundaryTheory.sigmaStar
  field_simp [hc₀, hC₀, hα, Real.pi_ne_zero]

/-! 本地补入：原文件 `BoundaryTheory.lean` 的 `BoundaryTheory.kappaStar_sq`（证明照抄，仅为本文件自足；
   与原件同名同内容，合并入值层时应去重）。 -/
/-- 与 `BoundaryTheory.kappaStar_sq` 的显式对接：上式的分母正是 κ*²。 -/
theorem sigma_eq_sigmaStar_mul_ratio_kappaStar (c₀ C₀ α : ℝ) (κ : ℝ)
    (hc₀ : 0 < c₀) (hα : 0 ≤ α) (hC₀ : C₀ ≠ 0) :
    BoundaryTheory.kappaStar c₀ α ^ 2 = (Real.pi ^ 2) * α / (3 * c₀) :=
  BoundaryTheory.kappaStar_sq (c₀ := c₀) (α := α) hc₀ hα

/-! ## 四 · 待证（**未写成 Lean 证明**，故不写成 `sorry` 定理，以遵守 0-sorry 纪律）

**三态符号判据**：在 c₀>0, C₀>0, α>0, κ>0 下，
  BoundaryTheory.V′(κ) < 0 ↔ σ(κ) < σ* ； BoundaryTheory.V′(κ) = 0 ↔ σ(κ) = σ* ； BoundaryTheory.V′(κ) > 0 ↔ σ(κ) > σ* 。
由 `deriv_V_eq_sigma_form` 知 BoundaryTheory.V′ = c₀(1 − σ*/σ)，σ>0，c₀>0，
故符号等价于 (1 − σ*/σ) 的符号，即 σ 与 σ* 的大小关系。证明需 `positivity` 与除法符号引理。
**这是下一步的 Lean 目标**，不是本文件的既有结论。

**饱和桥** σ_coh = min(σ_mech/σ*, 1) 属**建模选择**（其论证来自不动点语义，见 40 轮推进件 §四推论 B），
**不进入值层**。 -/


/-! ## 五 · 三态符号判据（第 47 轮：由"待证"改为**已证**） -/

theorem sign_trichotomy (c₀ C₀ α κ : ℝ)
    (hc₀ : 0 < c₀) (hC₀ : 0 < C₀) (hα : 0 < α) (hκ : 0 < κ) :
    (deriv (fun κ : ℝ => BoundaryTheory.V c₀ α κ) κ < 0 ↔ sigma c₀ C₀ κ < BoundaryTheory.sigmaStar α C₀) ∧
    (deriv (fun κ : ℝ => BoundaryTheory.V c₀ α κ) κ = 0 ↔ sigma c₀ C₀ κ = BoundaryTheory.sigmaStar α C₀) ∧
    (0 < deriv (fun κ : ℝ => BoundaryTheory.V c₀ α κ) κ ↔ BoundaryTheory.sigmaStar α C₀ < sigma c₀ C₀ κ) := by
  have hκ0 : κ ≠ 0 := ne_of_gt hκ
  have hc0 : c₀ ≠ 0 := ne_of_gt hc₀
  have hC0 : C₀ ≠ 0 := ne_of_gt hC₀
  have hd := deriv_V_eq_sigma_form c₀ C₀ α κ hκ0 hc0 hC0
  have hs : 0 < sigma c₀ C₀ κ := by unfold sigma; positivity
  have hss : 0 < BoundaryTheory.sigmaStar α C₀ := by unfold BoundaryTheory.sigmaStar; positivity
  -- 关键改写：BoundaryTheory.V′ = (c₀/σ)·(σ − σ*)，其中 c₀/σ > 0
  have hkey : deriv (fun κ : ℝ => BoundaryTheory.V c₀ α κ) κ
      = (c₀ / sigma c₀ C₀ κ) * (sigma c₀ C₀ κ - BoundaryTheory.sigmaStar α C₀) := by
    rw [hd]; field_simp
  have hpos : 0 < c₀ / sigma c₀ C₀ κ := div_pos hc₀ hs
  rw [hkey]
  refine ⟨?_, ?_, ?_⟩
  · -- 负号：用 x<0 ↔ 0<−x 归约到已确认存在的 mul_pos_iff_of_pos_left
    have hneg : (c₀ / sigma c₀ C₀ κ) * (sigma c₀ C₀ κ - BoundaryTheory.sigmaStar α C₀) < 0
        ↔ 0 < (c₀ / sigma c₀ C₀ κ) * (BoundaryTheory.sigmaStar α C₀ - sigma c₀ C₀ κ) := by
      rw [← neg_pos]; ring_nf
    rw [hneg, mul_pos_iff_of_pos_left hpos, sub_pos]
  · rw [mul_eq_zero]
    constructor
    · intro h; exact sub_eq_zero.mp (h.resolve_left (ne_of_gt hpos))
    · intro h; exact Or.inr (sub_eq_zero.mpr h)
  · rw [mul_pos_iff_of_pos_left hpos, sub_pos]

/-! ## 六 · σ* 与 c₀ 的关系（第 55 轮）：**gauge 条件管不住 c₀，c₀ 的自由度落在 κ★ 上** -/

/-- (A) 临界锐度处的压差恰为 σ*，**与 c₀ 无关**（c₀ 相消）。 -/
theorem sigma_at_kappaStar (c₀ C₀ α : ℝ) (hc₀ : 0 < c₀) (hC₀ : 0 < C₀) (hα : 0 ≤ α) :
    sigma c₀ C₀ (BoundaryTheory.kappaStar c₀ α) = BoundaryTheory.sigmaStar α C₀ := by
  have hk : (BoundaryTheory.kappaStar c₀ α) ^ 2 = Real.pi ^ 2 * (α / (3 * c₀)) := by
    unfold BoundaryTheory.kappaStar
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  unfold sigma BoundaryTheory.sigmaStar
  rw [hk]
  field_simp

/-- (A′) 换任一 c₀，σ(κ★) 不变。 -/
theorem sigma_at_kappaStar_c0_invariant (c₀ c₀' C₀ α : ℝ)
    (hc₀ : 0 < c₀) (hc₀' : 0 < c₀') (hC₀ : 0 < C₀) (hα : 0 ≤ α) :
    sigma c₀ C₀ (BoundaryTheory.kappaStar c₀ α) = sigma c₀' C₀ (BoundaryTheory.kappaStar c₀' α) := by
  rw [sigma_at_kappaStar c₀ C₀ α hc₀ hC₀ hα,
      sigma_at_kappaStar c₀' C₀ α hc₀' hC₀ hα]

/-- (B) κ★ **确实依赖 c₀**：κ★(1,1) ≠ κ★(2,1)。 -/
theorem kappaStar_depends_on_c0 :
    BoundaryTheory.kappaStar 1 1 ≠ BoundaryTheory.kappaStar 2 1 := by
  intro h
  unfold BoundaryTheory.kappaStar at h
  have h2 := mul_left_cancel₀ (ne_of_gt Real.pi_pos) h
  rw [Real.sqrt_inj (by norm_num) (by norm_num)] at h2
  norm_num at h2
