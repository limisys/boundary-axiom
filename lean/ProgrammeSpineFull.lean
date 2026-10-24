/-
ProgrammeSpineFull.lean —— **全部机检结果的单一证书（扩展主干）**（第 136 轮）

**为什么要这一件**：`ProgrammeSpine.spine` 覆盖**主干九条**（逻辑层）；
此后又加了**假设（校准）／协议（两点、桥、代理）／形状（连续、被迫）**等件。
本件把它们**一并纳入同一条定理**，使"**任何一处被改坏，构建立刻失败**"覆盖**当前全部**结果。

**本件不新增主张**：proof 逐条引用已证定理；statement 逐条写出命题。

条目（共 17）：
  ①–⑨ 主干九条（同 `spine`）
  ⑩ 校准恒等式⇒核唯一　　⑪ 两点否证（校准核对）
  ⑫ 连续形状半衰期＝1　　⑬ 时间尺度（比值与初值无关）
  ⑭ 桥的存在性⇔向下封闭　　⑮ 代理不变性（满射时等价）
  ⑯ 比例性⇒形状函数　　⑰ 半群性⇒整数步几何（含每步减半）

0 `sorry` / `0 axiom`。
-/
import GaugeNoGo
import LevelSelection
import LevelReadout
import ReadoutDynamics
import Falsifiers
import FaceIdentification
import RelaxRobust
import ProtocolLogic
import DescriptionLayer
import KernelCalibration
import CalibrationProtocol
import ContinuousRelaxation
import TimeScaleInvariance
import ReportBridge
import ProxyInvariance
import ShapeForcing
import ContinuousSemigroupExp
import ObservableProxy

open scoped Real

namespace ProgrammeSpineFull

open LogisticCore (L b)
open ReportBridge (Bridge)

/-- **（全部机检 · 单一证书）** 十七条一次核对。 -/
theorem spine_full {ι : Type*} :
    -- ① K2 的精确形式
    (∀ f : ℝ → ℝ → ℝ, GaugeNoGo.GaugeInv f ↔
        ∃ g : ℝ → ℝ, ∀ κ w : ℝ, 0 < κ → f κ w = g (w / κ)) ∧
      -- ② 不变原则挑不出水平
      (∀ P : ℝ → Prop, LevelSelection.GaugeInvPrinciple P → ¬ LevelSelection.Selects P) ∧
      -- ③ 追踪读出＝水平函数
      (∀ κ μ w : ℝ, 0 < κ → 0 ≤ w → LevelReadout.readout κ μ w = ReadoutExistence.thetaOf w) ∧
      -- ④ 读数永不越过 θ*
      (∀ w : ℝ, 1 ≤ w → ∀ n : ℕ,
        ReadoutExistence.thetaOf ((LevelDynamics.relax^[n]) w) ≤ ReadoutExistence.thetaOf 1) ∧
      -- ⑤ 任意更低水平有限步被超过
      (∀ w : ℝ, 1 < w → ∀ θ' : ℝ, 0 < θ' → θ' < 1 → θ' < ReadoutExistence.thetaOf 1 →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          θ' < ReadoutExistence.thetaOf ((LevelDynamics.relax^[n]) w)) ∧
      -- ⑥ 不存在规范不变的识别
      (∀ g : ℝ → ℝ → ℝ, FaceIdentification.Identifies g →
        ¬ (∀ t κ w : ℝ, 0 < t → 0 < κ → 0 < w → g (t * κ) (t * w) = g κ w)) ∧
      -- ⑦ 描述层由核唯一决定
      (∀ g : ℝ → ℝ,
        (∀ κ μ x θ : ℝ, 0 < κ → 0 < θ → θ < 1 →
          (b κ μ x ≤ θ ↔ g θ ≤ |κ * (x - μ)|)) →
        ∀ θ : ℝ, 0 < θ → θ < 1 → g θ = L θ) ∧
      -- ⑧ M1 判决逻辑
      (∀ M R : ι → Prop,
        ProtocolLogic.CoOccur M R ↔ ¬ ProtocolLogic.P1Witness M R ∧ ¬ ProtocolLogic.P2Witness M R) ∧
      -- ⑨ 稳健性
      (∀ f : ℝ → ℝ, RelaxRobust.Admissible f → ∀ w : ℝ, 1 ≤ w → ∀ n : ℕ,
        (f^[n]) w - 1 ≤ (w - 1) / 2 ^ n) ∧
      -- ⑩ 校准恒等式 ⇒ 核唯一
      (∀ φ : ℝ → ℝ, (∀ d : ℝ, 0 < d → 0 < φ d ∧ φ d < 1) →
        (∀ d : ℝ, 0 < d → L (φ d) = d) →
        ∀ d : ℝ, 0 < d → φ d = ReadoutExistence.thetaOf d) ∧
      -- ⑪ 两点否证（校准核对）
      (∀ φ : ℝ → ℝ, (∀ d : ℝ, 0 < d → 0 < φ d ∧ φ d < 1) →
        ∀ d₁ d₂ : ℝ, 0 < d₁ → 0 < d₂ → d₁ ≠ d₂ → φ d₁ = φ d₂ →
          ¬ (∀ d : ℝ, 0 < d → L (φ d) = d)) ∧
      -- ⑫ 连续形状：半衰期＝1
      (∀ w₀ t : ℝ,
        ContinuousRelaxation.wOf w₀ (t + 1) - 1 = (ContinuousRelaxation.wOf w₀ t - 1) / 2) ∧
      -- ⑬ 时间尺度：比值与初值无关
      (∀ c w₀ w₀' t₁ t₂ : ℝ, 0 < c → 1 < w₀ → 1 < w₀' →
        (TimeScaleInvariance.wOfRate c w₀ t₁ - 1) / (TimeScaleInvariance.wOfRate c w₀ t₂ - 1)
          = (TimeScaleInvariance.wOfRate c w₀' t₁ - 1)
              / (TimeScaleInvariance.wOfRate c w₀' t₂ - 1)) ∧
      -- ⑭ 桥的存在性 ⇔ 向下封闭（有限试次）
      (∀ {ι' : Type*} [Fintype ι'] [Nonempty ι'] (read : ι' → ℝ) (rep : ι' → Prop)
          [DecidablePred rep],
        (∃ θ : ℝ, Bridge read rep θ) ↔
          (∀ t t' : ι', read t ≤ read t' → rep t' → rep t)) ∧
      -- ⑮ 代理不变性（满射时等价）
      (∀ {ι' : Type*} (read : ι' → ℝ) (rep : ι' → Prop) (φ : ℝ → ℝ),
        StrictMono φ → Function.Surjective φ →
        ((∃ θ : ℝ, Bridge read rep θ) ↔
          (∃ θ' : ℝ, Bridge (fun t => φ (read t)) rep θ'))) ∧
      -- ⑯ 比例性 ⇒ 形状函数
      (∀ d : ℝ → ℝ → ℝ,
        (∀ w t : ℝ, 1 < w → 0 ≤ t → 0 < d w t) →
        (∀ w w' t₁ t₂ : ℝ, 1 < w → 1 < w' → 0 ≤ t₁ → 0 ≤ t₂ →
          d w t₁ / d w t₂ = d w' t₁ / d w' t₂) →
        ∃ ρ : ℝ → ℝ, ρ 0 = 1 ∧ ∀ w t : ℝ, 1 < w → 0 ≤ t → d w t = d w 0 * ρ t) ∧
      -- ⑰ 半群性 ⇒ 整数步几何
      (∀ ρ : ℝ → ℝ, (∀ s t : ℝ, ρ (s + t) = ρ s * ρ t) → ρ 0 = 1 →
        ∀ n : ℕ, ρ (n : ℝ) = ρ 1 ^ n) ∧
      -- ⑱ **连续**半群 ⇒ 指数（连续时间版）
      (∀ ρ : ℝ → ℝ, (∀ s t : ℝ, ρ (s + t) = ρ s * ρ t) → (∀ t : ℝ, 0 < ρ t) →
        Continuous ρ → ∀ t : ℝ, ρ t = Real.exp (t * Real.log (ρ 1))) ∧
      -- ⑲ 可观测代理：测试状态"已决／未决"是阈式桥，阈值即该处读数
      (∀ κ μ θ x₀ : ℝ, 0 < κ → 0 < θ → θ < 1 →
        (x₀ ∈ LocusVsBoundary.Fix (SharpnessClosure.c κ μ (L θ)) ↔ b κ μ x₀ ≤ θ)) :=
  ⟨GaugeNoGo.gaugeInv_iff_ratioForm,
    LevelSelection.gaugeInvPrinciple_notSelects,
    fun κ μ w hκ hw => LevelReadout.readout_eq_thetaOf κ μ w hκ hw,
    fun w hw n => ReadoutDynamics.level_squeeze w hw n,
    fun w hw θ' h0 h1 hlt => ReadoutDynamics.level_climbs w hw θ' h0 h1 hlt,
    FaceIdentification.no_gaugeInv_identification,
    DescriptionLayer.description_layer_forced,
    fun M R => ProtocolLogic.cooccur_iff_no_witness M R,
    fun f hf w hw n => RelaxRobust.admissible_error hf hw n,
    fun φ hb hcal d hd => KernelCalibration.calibrated_unique φ hb hcal d hd,
    fun φ hb d₁ d₂ h1 h2 hne heq =>
      CalibrationProtocol.two_point_falsifier φ hb d₁ d₂ h1 h2 hne heq,
    fun w₀ t => ContinuousRelaxation.wOf_half_life w₀ t,
    fun c w₀ w₀' t₁ t₂ hc hw hw' =>
      TimeScaleInvariance.ratio_indep_of_deviation hc hw hw',
    fun read rep _ => ReportBridge.bridge_iff_monotone_finite read rep,
    fun read rep φ hφ hsurj => ProxyInvariance.bridge_mono_transform_iff hφ hsurj,
    fun d hpos hratio => ShapeForcing.proportional_decay d hpos hratio,
    fun ρ hmul h0 n => ShapeForcing.geometric_on_nat hmul h0 n,
    fun ρ hmul hpos hcont => ContinuousSemigroupExp.continuous_semigroup_exp ρ hmul hpos hcont,
    fun κ μ θ x₀ hκ h0 h1 => ObservableProxy.membership_is_threshold_bridge κ μ θ x₀ hκ h0 h1⟩

end ProgrammeSpineFull
