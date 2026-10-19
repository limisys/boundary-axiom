/-
  Copyright 2026 Xueqiang Gao (高学强) · ORCID 0009-0008-3821-3454
  Licensed under the Apache License, Version 2.0 (see LICENSE).
  Original publication source: caseos.cn/research — https://caseos.cn/research/
  First public release 2026-10-09; formal publication 2026-10-20.
  Part of the B-line canonical subset (group 2): 53 files / 417 theorems+lemmas / 77 definitions.
  Attribution header added at publication; proof bodies unchanged.
-/

/-
ReportBridge.lean —— **"报告＝读数"这一步：写成可检验的桥，并给出它的落空条件**（第 132 轮）

**令源**：纲领的诚实清单里一直有一条未证项：**"报告＝读数"**（把形式读数接到经验报告上）。
本件不把它当作已证，而是：
  1. 把"桥"**定义**清楚（阈式桥）；
  2. 证出它的**必要条件**（读数—报告必须**单调一致**）；
  3. 把**违反该条件**写成**落空条件**（一次观测即可否掉桥）；
  4. 证明在**有限**试次上该条件**也是充分的**（故桥的存在性在数据上是**可判定的**）；
  5. 给出**传递定理**：桥成立时，模型对读数的预言**传递给报告**。

**结果（机检）**：
  · `Bridge`（定义）：$\\mathrm{rep}\\,t\\iff \\mathrm{read}\\,t\\le\\theta$；
  · `bridge_monotone`：桥 ⇒ 报告在读数上**向下封闭**（必要条件）；
  · `bridge_falsifier`：一旦观测到"读数更小却不报、读数更大却报"⇒ **桥不存在**；
  · `bridge_iff_monotone_finite`：**有限试次上，向下封闭 $\\iff$ 桥存在**（可判定）；
  · `bridge_transfer`：桥成立 ⇒ 读数的界**传递**为报告的界；
  · `bridge_certificate`：打包。

**⚠ 本件不声称**桥成立——它只把桥**精确化**，并给出**判定的条件与落空条件**。

0 `sorry` / `0 axiom`。
-/
import Mathlib

open scoped Real

namespace ReportBridge

variable {ι : Type*}

/-- **阈式桥**：报告成立 $\\iff$ 读数不超过阈值 $\\theta$。 -/
def Bridge (read : ι → ℝ) (rep : ι → Prop) (θ : ℝ) : Prop :=
  ∀ t : ι, rep t ↔ read t ≤ θ

/-- **（必要条件）** 桥 ⇒ 报告在读数上**向下封闭**：
读数更小者若被报出，则更小者也被报出。 -/
theorem bridge_monotone {read : ι → ℝ} {rep : ι → Prop} {θ : ℝ}
    (h : Bridge read rep θ) :
    ∀ t t' : ι, read t ≤ read t' → rep t' → rep t := by
  intro t t' hle hrep
  have h1 : read t' ≤ θ := (h t').mp hrep
  exact (h t).mpr (le_trans hle h1)

/-- **（落空条件）** 观测到"读数更小却不报、读数更大却报" ⇒ **任何阈式桥都不存在**。 -/
theorem bridge_falsifier {read : ι → ℝ} {rep : ι → Prop} (t t' : ι)
    (hle : read t ≤ read t') (hrep : rep t') (hnrep : ¬ rep t) :
    ¬ ∃ θ : ℝ, Bridge read rep θ := by
  rintro ⟨θ, hθ⟩
  exact hnrep (bridge_monotone hθ t t' hle hrep)

/-- **（传递）** 桥成立且读数有上界 $\\theta$ ⇒ 相应试次**都被报出**。 -/
theorem bridge_transfer {read : ι → ℝ} {rep : ι → Prop} {θ : ℝ}
    (h : Bridge read rep θ) :
    ∀ t : ι, read t ≤ θ → rep t :=
  fun t ht => (h t).mpr ht

/-- **（有限版 · 充分性）** 有限试次上，"向下封闭"**就是**桥存在的充要条件（故桥的存在性**可判定**）。 -/
theorem bridge_iff_monotone_finite [Fintype ι] [Nonempty ι] (read : ι → ℝ) (rep : ι → Prop)
    [DecidablePred rep] :
    (∃ θ : ℝ, Bridge read rep θ) ↔
      (∀ t t' : ι, read t ≤ read t' → rep t' → rep t) := by
  constructor
  · rintro ⟨θ, hθ⟩
    exact bridge_monotone hθ
  · intro hmono
    classical
    by_cases hemp : ∃ t : ι, rep t
    · -- 有报告者：取"报告集合"上读数的最大值
      let S : Finset ι := Finset.univ.filter rep
      have hSne : S.Nonempty := by
        obtain ⟨t, ht⟩ := hemp
        exact ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ t, ht⟩⟩
      obtain ⟨t₁, ht₁S, ht₁max⟩ := Finset.exists_mem_eq_sup' hSne read
      have hrep₁ : rep t₁ := (Finset.mem_filter.mp ht₁S).2
      refine ⟨read t₁, fun t => ⟨fun ht => ?_, fun ht => ?_⟩⟩
      · have h1 : read t ≤ S.sup' hSne read :=
          Finset.le_sup' read (Finset.mem_filter.mpr ⟨Finset.mem_univ t, ht⟩)
        rwa [ht₁max] at h1
      · exact hmono t t₁ ht hrep₁
    · -- 无人报告：取下界减一
      push_neg at hemp
      have hne : (Finset.univ : Finset ι).Nonempty := Finset.univ_nonempty
      refine ⟨(Finset.univ : Finset ι).inf' hne read - 1, fun t => ⟨fun ht => ?_, fun ht => ?_⟩⟩
      · exact absurd ht (hemp t)
      · have hle : (Finset.univ : Finset ι).inf' hne read ≤ read t :=
          Finset.inf'_le _ (Finset.mem_univ t)
        linarith

end ReportBridge
