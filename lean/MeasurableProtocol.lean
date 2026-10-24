/-
MeasurableProtocol.lean —— **可测协议的核心推断**：见证 $\\iff$ $b$ 越过阈值（第 86 轮）

**动机**：纲领的靶心 2 是"$V(\\kappa)$ 的量纲锚定**与可测协议**"。
锚定的自由度已在第 77／78 轮算清（恰一个尺度）；但**可测协议**——即
"**要测什么、怎么从数据判出 §5 那条判据**"——此前**从未写出**。

本轮把协议的**核心推断**做成定理，从而把"可测"这件事**接到已机检的链上**。

**推断链（每一环都可核）**：

  1. 边界隶属度由归因场定义：$b(x)=1-|p_S(x)-p_N(x)|$（论文定义 2.2）；
  2. **已决集恰是 $b$ 的下水平集**：$\\mathrm{Fix}(c_{\\kappa,\\mu,L(\\theta)})=\\{x: b(x)\\le\\theta\\}$
     （第 70 轮 `fix_c_eq_decided`，§4 第 14 项）；
  3. §5 的见证是"一族已决、另一族未决"（第 76 轮 `Witness`，§4 第 18 项）；
  4. **（本轮）** 于是见证 $\\iff$ **存在一个状态，其 $b$ 在一族下 $\\le\\theta$、在另一族下 $>\\theta$**
     ——`witness_iff_b_crosses`。

**这一步的意义**：$b$ 是**从数据算得**的量（定义 2.2 只要归因场可测），
$\\theta$ 是**约定**（建模选择，不是测量）；故第 4 条把 §5 的判据
**从"关于闭包算子的陈述"翻译成"关于一个可测标量的陈述"**——
这正是"可测协议"所缺的那一环。

0 `sorry` / 0 `axiom`。
-/
import ContrastExamples
import LogisticCore
import SharpnessClosure

open scoped Real

namespace MeasurableProtocol

open LanguageStrict LogisticCore

/-- **（协议核心 · 主结果）** 在锐度族上，§5 的见证**等价于**"$b$ 越过阈值 $\\theta$"：
存在一个状态，其 $b$ 在一族下 $\\le\\theta$、在另一族下 $>\\theta$。
**这把判据从"关于闭包算子的陈述"翻译成"关于一个可测标量的陈述"。** -/
theorem witness_iff_b_crosses (κ₁ κ₂ μ θ : ℝ)
    (hκ₁ : 0 < κ₁) (hκ₂ : 0 < κ₂) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    Witness (SharpnessClosure.c κ₁ μ (L θ)) (SharpnessClosure.c κ₂ μ (L θ))
      ↔ ∃ x : ℝ, b κ₁ μ x ≤ θ ∧ θ < b κ₂ μ x := by
  have key₁ := SharpnessClosure.fix_c_eq_decided κ₁ μ θ hκ₁ hθ0 hθ1
  have key₂ := SharpnessClosure.fix_c_eq_decided κ₂ μ θ hκ₂ hθ0 hθ1
  constructor
  · rintro ⟨x, h1, h2⟩
    have hm1 : x ∈ LocusVsBoundary.Fix (SharpnessClosure.c κ₁ μ (L θ)) := h1
    rw [key₁] at hm1
    have hm2 : x ∉ LocusVsBoundary.Fix (SharpnessClosure.c κ₂ μ (L θ)) := h2
    rw [key₂] at hm2
    exact ⟨x, hm1, not_le.mp hm2⟩
  · rintro ⟨x, h1, h2⟩
    refine ⟨x, ?_, ?_⟩
    · have : x ∈ LocusVsBoundary.Fix (SharpnessClosure.c κ₁ μ (L θ)) := by
        rw [key₁]; exact h1
      exact this
    · intro hc
      have : x ∈ LocusVsBoundary.Fix (SharpnessClosure.c κ₂ μ (L θ)) := hc
      rw [key₂] at this
      exact absurd this (not_le.mpr h2)

/-- **（协议核心 · 集合形式）** 两族的**已决集之差**恰是"$b$ 的跨阈状态"：
$\\mathrm{Fix}(c_{\\kappa_1})\\setminus\\mathrm{Fix}(c_{\\kappa_2})
 =\\{x: b_{\\kappa_1}(x)\\le\\theta < b_{\\kappa_2}(x)\\}$。 -/
theorem decided_diff_eq_crossing (κ₁ κ₂ μ θ : ℝ)
    (hκ₁ : 0 < κ₁) (hκ₂ : 0 < κ₂) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    LocusVsBoundary.Fix (SharpnessClosure.c κ₁ μ (L θ)) \ 
        LocusVsBoundary.Fix (SharpnessClosure.c κ₂ μ (L θ))
      = {x : ℝ | b κ₁ μ x ≤ θ ∧ θ < b κ₂ μ x} := by
  have key₁ := SharpnessClosure.fix_c_eq_decided κ₁ μ θ hκ₁ hθ0 hθ1
  have key₂ := SharpnessClosure.fix_c_eq_decided κ₂ μ θ hκ₂ hθ0 hθ1
  ext x
  simp only [Set.mem_sdiff, Set.mem_ofPred_eq]
  rw [key₁, key₂]
  simp only [Set.mem_ofPred_eq]
  exact ⟨fun h => ⟨h.1, not_le.mp h.2⟩, fun h => ⟨h.1, not_le.mpr h.2⟩⟩

/-- **（收官）** 协议的三条打包：跨阈判据、集合形式、以及"$\\theta$ 是约定"这一事实的**形式痕迹**
（$\\theta$ 是显式参数，不是一个常数——换 $\\theta$ 就换判据）。 -/
theorem protocol_core (κ₁ κ₂ μ θ : ℝ)
    (hκ₁ : 0 < κ₁) (hκ₂ : 0 < κ₂) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (Witness (SharpnessClosure.c κ₁ μ (L θ)) (SharpnessClosure.c κ₂ μ (L θ))
        ↔ ∃ x : ℝ, b κ₁ μ x ≤ θ ∧ θ < b κ₂ μ x)
      ∧ (LocusVsBoundary.Fix (SharpnessClosure.c κ₁ μ (L θ)) \ 
            LocusVsBoundary.Fix (SharpnessClosure.c κ₂ μ (L θ))
          = {x : ℝ | b κ₁ μ x ≤ θ ∧ θ < b κ₂ μ x}) :=
  ⟨witness_iff_b_crosses κ₁ κ₂ μ θ hκ₁ hκ₂ hθ0 hθ1,
   decided_diff_eq_crossing κ₁ κ₂ μ θ hκ₁ hκ₂ hθ0 hθ1⟩

end MeasurableProtocol
