import BoundaryTheory
import ValueLayerExtension
import ValueLayerMin
import BoundaryReportIdentity
import ReportCountermodels

/-!
# 独立审计入口：A 线硬证据 + 边界↔自报同一性

从统一仓 `lean/` 的**工作区源码**编译产物检查，不读任何 godcore 项目产物。期望：

    'BoundaryTheory.C_H_eq_pi_sq_div_three' depends on axioms:
      [propext, Classical.choice, Quot.sound]
    'ValueLayerMin.V_global_min' depends on axioms:
      [propext, Classical.choice, Quot.sound]
    'BoundaryReportIdentity.rep_eq_iff_closureOperator_eq' depends on axioms:
      [propext, Classical.choice, Quot.sound]
    'ReportCountermodels.nonUpClosed_not_canonical' depends on axioms:
      [propext, Classical.choice, Quot.sound]

出现 `sorryAx` 或自定义 `axiom` 即不可作为硬证据。
-/

#print axioms BoundaryTheory.C_H_eq_pi_sq_div_three
#print axioms ValueLayerMin.V_global_min
#print axioms ValueLayerMin.V_eq_min_iff
#print axioms BoundaryReportIdentity.rep_eq_iff_closureOperator_eq
#print axioms ReportCountermodels.nonUpClosed_not_canonical
#check @BoundaryTheory.C_H_eq_pi_sq_div_three
#check @ValueLayerMin.V_global_min
#check @ValueLayerExtension.sigma
#check @BoundaryReportIdentity.rep_eq_iff_closureOperator_eq
#check @ReportCountermodels.nonUpClosed_not_canonical
