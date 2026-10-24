/-
ReportIdentity.lean —— 发布包单一入口（v1.1 修正版）。

v1.0 的 `UpClosed` 条件（`∅ ∈ R` 且对超集封闭）在 Lean 中是退化的：
它强制 `R = Set.univ`，使“相互决定”退化为重言式。v1.1 改用 **Moore 族**
（对任意交封闭），它恰好是闭包算子不动点族的特征条件，非退化且可检查。

本文件只导入：
  1. `ReportIdentityCore`：Moore 族、互决定、联合不动点、表示定理；
  2. `ReportCountermodelsCore`：非 Moore 族的反例。
不新增任何声明。
-/
import ReportIdentityCore
import ReportCountermodelsCore
