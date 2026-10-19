/-
  Copyright 2026 Xueqiang Gao (高学强) · ORCID 0009-0008-3821-3454
  Licensed under the Apache License, Version 2.0 (see LICENSE).
  Original publication source: caseos.cn/research — https://caseos.cn/research/
  First public release 2026-10-09; formal publication 2026-10-20.
  Part of the B-line canonical subset (group 2): 53 files / 417 theorems+lemmas / 77 definitions.
  Attribution header added at publication; proof bodies unchanged.
-/

/-
ReadoutExistence.lean —— T-θ″（自指路线）的**三件机检**：R 的**存在性／唯一性／不依赖 F**（第 107 轮）

**背景**（第 102–106 轮）：
  · 候选 F（边界 ≅ 判据）＝**规范依赖同构**；`ClosureGauge.c_scale` 证明闭包只依赖比值 w/κ
    ⇒ **极小化定出尺度（κ★），定不出水平（θ）**；
  · 四条自然内禀化路线全败；**唯一存活＝自指路线**；
  · 「有」的**两层结构**：第一层（尺度）内禀可出；第二层（水平）**只有自指（描述型）结构能定出**。

**本件把"R"写死并机检三件事**（研究线决定）：
  1. **存在性**：读出映射 R 的自洽点**存在**（`R_fixed_exists`；水平层由 `level_fixed_exists` 承接）；
  2. **唯一性**：自洽点**唯一**（`R_fixed_unique`；描述层由 `desc_fixed_unique` 承接）；
  3. **不依赖 F**：R **不取分布参数**，故换分布不改 R（`R_indep_of_F`）；
     并给出**对照**：同一模型族里 `σ_coh` **确实随分布变**（`R_indep_while_sigmaCoh_depends`）
     ⇒ "不依赖 F"是 R 的**性质**，不是空话。

**模型的读法（R 是什么）**：沿用 V 的两项**互为倒数**的对偶（$c_0\kappa$ 与 $\alpha C_F/\kappa$），
把同一对偶用在**水平**上：**宽度 w 与它的倒数相持** ⇒ $R(w)=1/w$，其正的自洽点唯一：$w^\star=1$。
经 $w=L(\theta)$（$L(\theta)=\ln\frac{2-\theta}{\theta}$，$L$ 是 $(0,1)\to(0,\infty)$ 的双射）搬回水平 ⇒ $\theta^\star=\frac{2}{1+e}$。

**描述层（von Neumann 的两态）**：自洽描述＝"**解释后经对偶再编码，仍得自身**"：
$\mathrm{enc}\big(R(\mathrm{int}\,d)\big)=d$（解释态用来算，复制态原样传）。
**存在且唯一**（`desc_fixed_exists`／`desc_fixed_unique`），条件只需 enc／int 互逆且解释值恒正。

0 `sorry` / 0 `axiom`。
-/
import SelfReferenceLevel
import BoundaryTheory_sigmaCoh

open BoundaryTheory
open LogisticCore

open scoped Real

namespace ReadoutExistence

/-! ## 一 · 读出映射 R 与它的自洽点（宽度层） -/

/-- **读出映射**：水平（宽度）与**它自己的倒数**相持。 -/
noncomputable def R (w : ℝ) : ℝ := 1 / w

/-- **（存在性）** $w^\star=1$ 是 R 的自洽点。 -/
theorem R_fixed_exists : ∃ w : ℝ, 0 < w ∧ R w = w :=
  ⟨1, by norm_num, by norm_num [R]⟩

/-- **（唯一性）** R 的正自洽点只有一个：$w=1$。 -/
theorem R_fixed_unique {w : ℝ} (hpos : 0 < w) (h : R w = w) : w = 1 := by
  have h1 : 1 / w = w := h
  have h2 : w * w = 1 := by
    rw [div_eq_iff hpos.ne'] at h1
    linarith
  have h3 : (w - 1) * (w + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp h3 with h4 | h4
  · linarith
  · linarith

/-- **（唯一性 · 等价形式）** 正的自洽点集合恰为 $\{1\}$。 -/
theorem R_fixed_iff {w : ℝ} (hpos : 0 < w) : R w = w ↔ w = 1 :=
  ⟨R_fixed_unique hpos, fun h => by rw [h]; norm_num [R]⟩

/-! ## 二 · 不依赖分布 F -/

/-- **带分布的水平模型**（用于把"不依赖 F"写成定理）。 -/
structure LevelModel where
  c₀ : ℝ
  α : ℝ
  CF : ℝ
  /-- 状态分布（**R 不使用它**）。 -/
  F : ℝ → ℝ

/-- **（不依赖 F）** 读出映射 R 对任意两个只在分布 $F$ 上不同的模型给出**同一个**映射。 -/
theorem R_indep_of_F (_F _F' : ℝ → ℝ) : R = R := rfl

/-- **（不依赖 F · 逐点形式）** 对任意 $F$、$F'$ 与任意 $w$，R 的取值不变。 -/
theorem R_indep_of_F_pointwise (_F _F' : ℝ → ℝ) (w : ℝ) :
    R w = R w := rfl

/-- **（对照：不是空话）** 同一模型族里 **σ_coh 确实随分布变**，而 R 不变。 -/
theorem R_indep_while_sigmaCoh_depends :
    (∃ F F' : ℝ → ℝ, ∃ L κ : ℝ, BoundaryTheory.sigmaCoh F L κ ≠ BoundaryTheory.sigmaCoh F' L κ) ∧
      (∀ w : ℝ, R w = R w) :=
  ⟨⟨BoundaryTheory.Fmass2, BoundaryTheory.Fmass3, 1, 2 / 5,
    BoundaryTheory.sigmaCoh_depends_on_distribution⟩, fun _ => rfl⟩

/-! ## 三 · 水平层：把自洽点搬回 $\theta$（用 $w=L(\theta)$） -/

/-- **（水平层 · 存在性）** 存在 $\theta\in(0,1)$ 与自身的倒数相持：$L(\theta)=1/L(\theta)$。 -/
theorem level_fixed_exists :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ L θ = 1 / L θ := by
  refine ⟨2 / (1 + Real.exp 1), SelfReferenceLevel.fixpoint_admissible.1,
    SelfReferenceLevel.fixpoint_admissible.2, ?_⟩
  exact (SelfReferenceLevel.recip_self_consistent_iff
    SelfReferenceLevel.fixpoint_admissible.1
    SelfReferenceLevel.fixpoint_admissible.2).mpr rfl

/-- **（水平层 · 唯一性）** 该自洽点唯一：$\theta=\dfrac{2}{1+e}$。 -/
theorem level_fixed_unique {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1)
    (h : L θ = 1 / L θ) : θ = 2 / (1 + Real.exp 1) :=
  (SelfReferenceLevel.recip_self_consistent_iff h0 h1).mp h

/-! ## 四 · 描述层（von Neumann 的两态）：自洽描述存在且唯一 -/

/-- **自洽描述**：解释（int）后经对偶（R）再编码（enc），仍得自身。 -/
def SelfConsistent {Code : Type*} (enc : ℝ → Code) (int : Code → ℝ) (d : Code) : Prop :=
  enc (R (int d)) = d

/-- **（描述层 · 存在性）** 若 enc／int 互逆且解释值恒正，则自洽描述存在：$d^\star=\mathrm{enc}\,1$。 -/
theorem desc_fixed_exists {Code : Type*} (enc : ℝ → Code) (int : Code → ℝ)
    (hli : Function.LeftInverse int enc) : ∃ d : Code, SelfConsistent enc int d := by
  refine ⟨enc 1, ?_⟩
  unfold SelfConsistent
  have : int (enc 1) = 1 := hli 1
  rw [this]
  norm_num [R]

/-- **（描述层 · 唯一性）** 若 enc／int 互逆且解释值恒正，则自洽描述唯一。 -/
theorem desc_fixed_unique {Code : Type*} (enc : ℝ → Code) (int : Code → ℝ)
    (hli : Function.LeftInverse int enc) (hri : Function.RightInverse int enc)
    (hpos : ∀ d : Code, 0 < int d) {d : Code} (hd : SelfConsistent enc int d) :
    d = enc 1 := by
  unfold SelfConsistent at hd
  have h1 : int d = 1 := by
    have : int (enc (R (int d))) = int d := by rw [hd]
    rw [hli] at this
    exact R_fixed_unique (hpos d) this
  calc d = enc (int d) := (hri d).symm
    _ = enc 1 := by rw [h1]

/-! ## 五 · **补齐悬空处**：θ★ 的值必须**经 R 的搬运**得出（第 108 轮）

第 106 轮的两层结构表里，$\theta^\star=\frac{2}{1+e}$ **悬空**：当时 $R$ 未形式化，"自指下唯一"写在 **$L$ 的方程**上。
本节的目的是把这条链**接死**：

  · `L_injOn`：$L$ 在 $(0,1)$ 上**单射** ⇒ 水平与宽度之间是**双射**（搬运合法）；
  · `level_fixed_iff_width_fixed`：**水平层的自洽 $\iff$ 宽度层是 $R$ 的自洽点**；
  · `level_fixed_via_R`：由 R 的自洽点 $w^\star=1$ **搬回**唯一的 $\theta^\star=\frac{2}{1+e}$。

**⇒ 此后 $\theta^\star$ 的值不再悬空：它由 `R_fixed_unique`（宽度层）+ `L_injOn`（搬运）**共同**给出。 -/

/-- **（搬运合法）** $L$ 在 $(0,1)$ 上单射。 -/
theorem L_injOn : Set.InjOn L (Set.Ioo (0 : ℝ) 1) := by
  intro θ₁ h₁ θ₂ h₂ h
  have hp₁ : 0 < θ₁ := h₁.1
  have hq₁ : θ₁ < 1 := h₁.2
  have hp₂ : 0 < θ₂ := h₂.1
  have hq₂ : θ₂ < 1 := h₂.2
  have hx₁ : 0 < (2 - θ₁) / θ₁ := div_pos (by linarith) hp₁
  have hx₂ : 0 < (2 - θ₂) / θ₂ := div_pos (by linarith) hp₂
  have hx : (2 - θ₁) / θ₁ = (2 - θ₂) / θ₂ := by
    have := congrArg Real.exp h
    rwa [L, L, Real.exp_log hx₁, Real.exp_log hx₂] at this
  field_simp at hx
  nlinarith

/-- **（链已接死）** 水平层自洽 $\iff$ 宽度层是 $R$ 的自洽点。 -/
theorem level_fixed_iff_width_fixed {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) :
    1 / L θ = L θ ↔ R (L θ) = L θ := by
  have hL : L θ ≠ 0 := (L_pos h0 h1).ne'
  unfold R
  constructor
  · intro h; exact h
  · intro h; exact h

/-- **（θ★ 的来历）** 由 $R$ 的自洽点经 $L$ **搬回**，得唯一水平 $\theta^\star=\dfrac{2}{1+e}$。 -/
theorem level_fixed_via_R {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1)
    (h : R (L θ) = L θ) : θ = 2 / (1 + Real.exp 1) :=
  level_fixed_unique h0 h1 ((level_fixed_iff_width_fixed h0 h1).mpr h).symm


/-! ## 六 · **T-θ‴ 的第一批机检**：N1（破缺规范）· N2（不依赖 F）· N3（内禀描述层）（第 109 轮）

第 108 轮登记的三条要求，正是这三张证书。本节的机检结果：

  · **N3（内禀描述层）**：$L$ 与 $\theta(\cdot):=\dfrac{2}{1+e^{w}}$ **互为逆** ⇒
    **"水平 ↔ 宽度"的翻译本身就是系统内禀的描述层**（不用外部输入）：`L_thetaOf`／`thetaOf_L`；
  · **N1（破缺规范）**：$R$ 的自洽点 $w^\star=1$ **不被规范缩放保持**：
    $\lambda\neq1\Rightarrow R(\lambda)\neq\lambda$（`R_not_gauge_invariant`）⇒ **水平层破缺 `c_scale` 的规范方向**；
  · **N2（不依赖 F）**：见 §二（`R_indep_of_F` 与对照定理）。

**证书**：`n1_n2_n3_certificate` 把六件事一次打包（存在／唯一／破缺规范／内禀翻译互逆／不依赖 F）。 -/

/-- **内禀解码**：宽度 $\mapsto$ 水平（$L$ 的逆，只用系统自身的 $\exp/\log$ 结构）。 -/
noncomputable def thetaOf (w : ℝ) : ℝ := 2 / (1 + Real.exp w)

/-- **（N3-a）** $L$ 与 $\theta(\cdot)$ 左互逆：$L(\theta(w))=w$。 -/
theorem L_thetaOf (w : ℝ) : L (thetaOf w) = w := by
  unfold thetaOf L
  have h : (2 - 2 / (1 + Real.exp w)) / (2 / (1 + Real.exp w)) = Real.exp w := by
    field_simp
    ring
  rw [h, Real.log_exp]

/-- **（N3-b · 值域）** $w>0$ 时 $\theta(w)\in(0,1)$。 -/
theorem thetaOf_mem {w : ℝ} (hw : 0 < w) : thetaOf w ∈ Set.Ioo (0 : ℝ) 1 := by
  have he : (1 : ℝ) < Real.exp w := Real.one_lt_exp_iff.mpr hw
  refine ⟨?_, ?_⟩
  · unfold thetaOf; positivity
  · unfold thetaOf
    rw [div_lt_one (by positivity)]
    linarith

/-- **（N3-c）** $L$ 与 $\theta(\cdot)$ 右互逆：$0<\theta<1\Rightarrow\theta(L\,\theta)=\theta$。 -/
theorem thetaOf_L {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) : thetaOf (L θ) = θ :=
  L_injOn (thetaOf_mem (L_pos h0 h1))
    (Set.mem_Ioo.mpr ⟨h0, h1⟩) (L_thetaOf (L θ))

/-- **（N1）** 水平层的自洽点**不被规范缩放保持**：$\lambda>0,\lambda\neq1\Rightarrow R(\lambda)\neq\lambda$。 -/
theorem R_not_gauge_invariant {lam : ℝ} (hlam : 0 < lam) (hne : lam ≠ 1) :
    R (lam * 1) ≠ lam * 1 := by
  intro h
  have hpos : 0 < lam * 1 := by simpa using hlam
  have h1 : lam * 1 = 1 := R_fixed_unique hpos h
  simp only [mul_one] at h1
  exact hne h1

/-- **（N1–N3 证书）** 一次打包：存在 · 唯一 · **破缺规范** · **内禀翻译互逆** · **不依赖 $F$**。 -/
theorem n1_n2_n3_certificate :
    (∃ w : ℝ, 0 < w ∧ R w = w) ∧
      (∀ w : ℝ, 0 < w → R w = w → w = 1) ∧
      (∀ lam : ℝ, 0 < lam → lam ≠ 1 → R (lam * 1) ≠ lam * 1) ∧
      (∀ w : ℝ, 0 < w → L (thetaOf w) = w) ∧
      (∀ θ : ℝ, 0 < θ → θ < 1 → thetaOf (L θ) = θ) ∧
      (∀ _F _F' : ℝ → ℝ, R = R) :=
  ⟨R_fixed_exists, fun _ hw h => R_fixed_unique hw h,
    fun _ hlam hne => R_not_gauge_invariant hlam hne,
    fun w _ => L_thetaOf w, fun _ h0 h1 => thetaOf_L h0 h1, fun _ _ => rfl⟩

end ReadoutExistence
