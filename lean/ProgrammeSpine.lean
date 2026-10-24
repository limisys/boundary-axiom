/-
ProgrammeSpine.lean —— **纲领逻辑主干的单一证书**（第 124 轮）

**为什么要这一件**：第 104–123 轮的结果分散在十二个文件里。
本件把**主干的八条**写成**一个定理的类型**（每条命题**逐字写出**），证明时**逐条引用**对应轮次的定理
⇒ **此后任何一处被改动而破坏主干，`build_lean_all.sh` 立刻报错**（单一核对点）。

**主干八条**（本件**不新增主张**，只把已证结果合成一句话）：

  S1 **K2 的精确形式**：规范不变 $\\iff$ 只依赖比值 $w/\\kappa$
  S2 **不变原则挑不出水平**（选取必破缺）
  S3 **追踪读出＝水平函数**（$\\mathrm{readout}=\\theta(w)$）
  S4 **轨迹夹逼**：读数永不越过 $\\theta^\\star$，且任意更低水平有限步被超过
  S5 **$F$：不存在规范不变的识别**（识别存在且水平上唯一）
  S6 **描述层由核唯一决定**
  S7 **M1 判决逻辑**：同现 $\\iff$ 两向皆无见证
  S8 **稳健性**：误差每步减半对**可采纳类**中任意松弛成立

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

open scoped Real

namespace ProgrammeSpine

open LogisticCore (L b)

/-- **（纲领主干 · 单一证书）** 八条一次核对。 -/
theorem spine {ι : Type*} :
    (∀ f : ℝ → ℝ → ℝ, GaugeNoGo.GaugeInv f ↔
        ∃ g : ℝ → ℝ, ∀ κ w : ℝ, 0 < κ → f κ w = g (w / κ)) ∧
      (∀ P : ℝ → Prop, LevelSelection.GaugeInvPrinciple P → ¬ LevelSelection.Selects P) ∧
      (∀ κ μ w : ℝ, 0 < κ → 0 ≤ w → LevelReadout.readout κ μ w = ReadoutExistence.thetaOf w) ∧
      (∀ w : ℝ, 1 ≤ w → ∀ n : ℕ,
        ReadoutExistence.thetaOf ((LevelDynamics.relax^[n]) w) ≤ ReadoutExistence.thetaOf 1) ∧
      (∀ w : ℝ, 1 < w → ∀ θ' : ℝ, 0 < θ' → θ' < 1 → θ' < ReadoutExistence.thetaOf 1 →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          θ' < ReadoutExistence.thetaOf ((LevelDynamics.relax^[n]) w)) ∧
      (∀ g : ℝ → ℝ → ℝ, FaceIdentification.Identifies g →
        ¬ (∀ t κ w : ℝ, 0 < t → 0 < κ → 0 < w → g (t * κ) (t * w) = g κ w)) ∧
      (∀ g : ℝ → ℝ,
        (∀ κ μ x θ : ℝ, 0 < κ → 0 < θ → θ < 1 →
          (b κ μ x ≤ θ ↔ g θ ≤ |κ * (x - μ)|)) →
        ∀ θ : ℝ, 0 < θ → θ < 1 → g θ = L θ) ∧
      (∀ M R : ι → Prop,
        ProtocolLogic.CoOccur M R ↔ ¬ ProtocolLogic.P1Witness M R ∧ ¬ ProtocolLogic.P2Witness M R) ∧
      (∀ f : ℝ → ℝ, RelaxRobust.Admissible f → ∀ w : ℝ, 1 ≤ w → ∀ n : ℕ,
        (f^[n]) w - 1 ≤ (w - 1) / 2 ^ n) :=
  ⟨GaugeNoGo.gaugeInv_iff_ratioForm,
    LevelSelection.gaugeInvPrinciple_notSelects,
    fun κ μ w hκ hw => LevelReadout.readout_eq_thetaOf κ μ w hκ hw,
    fun w hw n => ReadoutDynamics.level_squeeze w hw n,
    fun w hw θ' h0 h1 hlt => ReadoutDynamics.level_climbs w hw θ' h0 h1 hlt,
    FaceIdentification.no_gaugeInv_identification,
    DescriptionLayer.description_layer_forced,
    fun M R => ProtocolLogic.cooccur_iff_no_witness M R,
    fun f hf w hw n => RelaxRobust.admissible_error hf hw n⟩

end ProgrammeSpine
