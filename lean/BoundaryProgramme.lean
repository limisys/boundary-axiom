/-
BoundaryProgramme.lean —— **单一入口件**（第 59 轮）

目的：把此前五个**互相不能 import** 的检查文件收成**一个可编译的入口**
（论文附录 A 曾把"不能互相 import"列为可复现性弱点）。

去重记录（第 59 轮）：
  · `ValueLayerExtension.lean` 取代 `BoundaryTheory_sigma_bridge.lean` 的**自足副本**
    （旧件为求自足复制了 `V`/`kappaStar`/`sigmaStar`/`force`/`kappaStar_sq`，
     现改为 `import BoundaryTheory`，只保留库中没有的 `def sigma` 与各定理）；
  · `DimensionAlgebra.lean` 删除本地 `def sigmaStar`，改用冻结层 `BoundaryTheory.sigmaStar`
    （逐字相同的重复声明）。

本件本身**不声明任何定理**，只做 import；编译通过即证明各层**互不冲突**。

第 60 轮加入 `LogisticCore.lean`（可解芯 T1–T4/T6/T7 的 Lean 化）；
第 61 轮加入 `TwoFacesBridge.lean`（伴随两面典范序同构）；
第 62 轮加入 `ValueLayerMin.lean`（κ★ 的全局最小性与两端极限）；
第 63 轮加入 `ThreeComponent.lean`（三成分场：模糊 ≠ 不确定）；
第 64 轮加入 `BridgeCaliberMenu.lean`（桥的口径：这个选择值多少）；
第 65 轮加入 `FieldClosure.lean`（芯外动力学：两个干预族作用在正交坐标上）；
第 66 轮加入 `CommitAdjunction.lean`（commit 来自伴随；b 是新序上的反单调势）；
第 67 轮加入 `LocusVsBoundary.lean`（非交换轨迹的定义与两向独立性）；
第 68 轮加入 `ClosureFromInterventions.lean`（由干预族生成的闭包与条件性正桥）；
第 69 轮加入 `OrbitInvariantRow.lean`（轨道不变量的机检行）；
第 70 轮加入 `SharpnessClosure.lean`（值层的 κ 进入范畴层的闭包算子）；
第 72 轮加入 `UnifiedClosure.lean`（三个闭包算子是同一个构造的三个实例）；
第 73 轮加入 `CategoricalDictionary.lean`（偏序情形与范畴情形的字典）；
第 76 轮加入 `LanguageStrict.lean`（§5 对照的严格性判据）；
第 77 轮加入 `ScalingsAndUnits.lean`（锚定的自由度恰为一）；
第 78 轮加入 `RescalingEquivariance.lean`（闭包侧的缩放等变性，补上第 77 轮留空的一半）；
第 79 轮加入 `ContrastExamples.lean`（§5 判据的具体实例与实验设计约束）；
第 80 轮加入 `PolarityChange.lean`（推论 C 的机检与"同一谓词"的识别）；
第 81 轮加入 `ComparabilityMatters.lean`（那两条判据共享的隐含假设，及去掉它的反例）；
第 86 轮加入 `MeasurableProtocol.lean`（可测协议的核心推断：见证 ⟺ b 越过阈值）；
第 87 轮加入 `CoreConstantSpectrum.lean`（核心常数 C_F 的频谱三分，与"ℝ 值把发散读成 0"的值域陷阱）；
第 103 轮加入 `ClosureGauge.lean`（锐度族的**规范对称性**：闭包只依赖比值 w/κ ⇒ 极小化定出尺度、定不出水平）；
第 104 轮加入 `SelfReferenceLevel.lean`（**T-θ′ 自指路线**：水平方程 L(θ)=1/L(θ) 有唯一解 θ=2/(1+e)）；
第 107 轮加入 `ReadoutExistence.lean`（**T-θ″**：读出映射 R 的**存在／唯一／不依赖 F** 三件机检，含 von Neumann 式描述层）；
第 111 轮加入 `UnitReading.lean`（**T-θ‴-1**：由**系统自身**导出读出——在自身单位尺度 $1/\kappa$ 处读自己的核，尺度与中心都消掉）。
 **第 69 轮（补录，2026-10-08）加入 `BoundaryReportIdentity.lean`**（**桥的同一性定理**：报告族与边界算子互相唯一决定——边界与"边界的自报"在向上封闭类内是**同一对象**；承第 67／68 轮的三层说法）。
 **统一仓（2026-10-19）补入 `ReportCountermodels.lean`**（同一性定理的反例侧：非向上封闭报告族不是自己的规范代表；无条件版因此不成立）。
 **自此本件覆盖统一仓全部 56 个开发件**：B 线 55 件（53 正典 + BoundaryReportIdentity + ReportCountermodels）、A 线 1 件（BoundaryTheory）。
 编译本件 = 全部开发件互不冲突、单一入口可达。
-/
import BoundaryTheory
import CausModel
import ValueLayerExtension
import BoundaryTheory_sigmaCoh
import BoundaryBridge_layers
import DimensionAlgebra
import LanguageInterventions
import LogisticCore
import TwoFacesBridge
import ValueLayerMin
import ThreeComponent
import BridgeCaliberMenu
import FieldClosure
import CommitAdjunction
import LocusVsBoundary
import ClosureFromInterventions
import BoundaryReportIdentity
import ReportCountermodels
import OrbitInvariantRow
import SharpnessClosure
import UnifiedClosure
import CategoricalDictionary
import LanguageStrict
import ScalingsAndUnits
import RescalingEquivariance
import ContrastExamples
import PolarityChange
import ComparabilityMatters
import MeasurableProtocol
import CoreConstantSpectrum
import ClosureGauge
import SelfReferenceLevel
import ReadoutExistence
import UnitReading
import MaintenanceMargin
import GaugeNoGo
import LevelReadout
import LevelSelection
import LevelDynamics
import ReadoutDynamics
import Falsifiers
import FaceIdentification
import RelaxRobust
import ProtocolLogic
import DescriptionLayer
import ProgrammeSpine
import KernelCalibration
import CalibrationProtocol
import ContinuousRelaxation
import TimeScaleInvariance
import ReportBridge
import ProxyInvariance
import ShapeForcing
import ProgrammeSpineFull
import ContinuousSemigroupExp
import ObservableProxy
