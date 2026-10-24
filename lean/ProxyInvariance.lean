/-
ProxyInvariance.lean —— **桥的检验是"序数"的：读出的代理可以任意换标度**（第 133 轮）

**令源**：第 132 轮把「报告＝读数」写成可判定的阈式桥，并留下一个前提问题：
**"读数在实验上如何取到"**（可观测代理）。本件给出**答案的一半**：

> **桥的存在性与落空条件只依赖读出的"序"**：把读出换成**任意严格递增**的函数，桥的存在性不变，
> 逆序观测**仍然**是逆序观测。⇒ 实验上只需要一个**序数代理**（保序的可观测量），**不需要**读出本身、也不需要它的标度。

**结果（机检）**：
  · `bridge_mono_transform`：严格递增变换把桥**推过去**（存在性保持）；
  · `bridge_mono_transform_iff`：（变换还是满射时）**存在性等价**；
  · `inverted_pair_preserved`：**逆序对在保序变换下仍是逆序对**（落空条件的代理不变性）；
  · `proxy_certificate`：打包。

**⚠ 不声称的**：本件**不**给出"读数＝哪一个可测量"的**具体识别**——那仍是实验的事；
本件只说明：**要执行第 132 轮第七条条款，只需一个保序代理**。

0 `sorry` / `0 axiom`。
-/
import ReportBridge

open scoped Real

namespace ProxyInvariance

variable {ι : Type*}

open ReportBridge (Bridge)

/-- **（桥经保序变换推过去）** 严格递增 $\\varphi$：读出换成 $\\varphi\\circ\\mathrm{read}$ 仍有桥。 -/
theorem bridge_mono_transform {read : ι → ℝ} {rep : ι → Prop} {φ : ℝ → ℝ}
    (hφ : StrictMono φ) (h : ∃ θ : ℝ, Bridge read rep θ) :
    ∃ θ' : ℝ, Bridge (fun t => φ (read t)) rep θ' := by
  obtain ⟨θ, hθ⟩ := h
  refine ⟨φ θ, fun t => ?_⟩
  show rep t ↔ φ (read t) ≤ φ θ
  exact (hθ t).trans hφ.le_iff_le.symm

/-- **（满射时存在性等价）** $\\varphi$ 严格递增且满射 $\\Rightarrow$ 两侧桥的存在性**等价**。 -/
theorem bridge_mono_transform_iff {read : ι → ℝ} {rep : ι → Prop} {φ : ℝ → ℝ}
    (hφ : StrictMono φ) (hsurj : Function.Surjective φ) :
    (∃ θ : ℝ, Bridge read rep θ) ↔ (∃ θ' : ℝ, Bridge (fun t => φ (read t)) rep θ') := by
  constructor
  · exact bridge_mono_transform hφ
  · rintro ⟨θ', hθ'⟩
    obtain ⟨a, ha⟩ := hsurj θ'
    have hiff : ∀ x : ℝ, x ≤ θ' ↔ x ≤ φ a := by
      intro x
      rw [← ha]
    refine ⟨a, fun t => ?_⟩
    exact (hθ' t).trans ((hiff (φ (read t))).trans hφ.le_iff_le)

/-- **（落空条件是序数的）** 逆序对在保序变换下**仍是逆序对**：
原来"读数更小却不报、更大却报"的观测，换标度后照样如此。 -/
theorem inverted_pair_preserved {read : ι → ℝ} {rep : ι → Prop} {φ : ℝ → ℝ}
    (hφ : StrictMono φ) (t t' : ι) (hle : read t ≤ read t') (hrep : rep t')
    (hnrep : ¬ rep t) :
    φ (read t) ≤ φ (read t') ∧ rep t' ∧ ¬ rep t :=
  ⟨hφ.le_iff_le.mpr hle, hrep, hnrep⟩

/-- **（桥的可判定性也保持不变）** 有限试次上：原读出满足"向下封闭" $\iff$ 保序变换后的读出满足。 -/
theorem monotone_iff_after_transform {read : ι → ℝ} {rep : ι → Prop} {φ : ℝ → ℝ}
    (hφ : StrictMono φ) :
    (∀ t t' : ι, read t ≤ read t' → rep t' → rep t) ↔
      (∀ t t' : ι, φ (read t) ≤ φ (read t') → rep t' → rep t) := by
  constructor
  · intro h t t' hle hrep
    exact h t t' (hφ.le_iff_le.mp hle) hrep
  · intro h t t' hle hrep
    exact h t t' (hφ.le_iff_le.mpr hle) hrep

/-- **（代理证书）** 桥随保序变换保持 · 满射时等价 · **逆序对保持** · **可判定性不变**。 -/
theorem proxy_certificate :
    (∀ {read : ι → ℝ} {rep : ι → Prop} {φ : ℝ → ℝ}, StrictMono φ →
      (∃ θ : ℝ, Bridge read rep θ) → ∃ θ' : ℝ, Bridge (fun t => φ (read t)) rep θ') ∧
      (∀ {read : ι → ℝ} {rep : ι → Prop} {φ : ℝ → ℝ}, StrictMono φ → Function.Surjective φ →
        ((∃ θ : ℝ, Bridge read rep θ) ↔
          (∃ θ' : ℝ, Bridge (fun t => φ (read t)) rep θ'))) ∧
      (∀ {read : ι → ℝ} {rep : ι → Prop} {φ : ℝ → ℝ}, StrictMono φ →
        ∀ t t' : ι, read t ≤ read t' → rep t' → ¬ rep t →
          φ (read t) ≤ φ (read t') ∧ rep t' ∧ ¬ rep t) ∧
      (∀ {read : ι → ℝ} {rep : ι → Prop} {φ : ℝ → ℝ}, StrictMono φ →
        ((∀ t t' : ι, read t ≤ read t' → rep t' → rep t) ↔
          (∀ t t' : ι, φ (read t) ≤ φ (read t') → rep t' → rep t))) :=
  ⟨fun hφ h => bridge_mono_transform hφ h,
    fun hφ hs => bridge_mono_transform_iff hφ hs,
    fun hφ t t' hle hrep hn => inverted_pair_preserved hφ t t' hle hrep hn,
    fun hφ => monotone_iff_after_transform hφ⟩

end ProxyInvariance
