# CausModel · 论文线 B 阶段范畴层模型

把《A Boundary for Mind》第三稿 §1–§3 的**范畴层**从散文升级为可编译、带万有性质的 Lean 模型。

## 构建

```bash
export ELAN_HOME=$HOME/I7服务化/验证/.lean-home
export PATH="$ELAN_HOME/bin:$PATH"
cd "论文/02_形式化与机验/Lean源码_CausModel"
lake build CausModel
```

预期：`Build completed successfully (3245 jobs)`，零 `sorry` / 零 `admit` / 零 `axiom`。

## 环境方案（不复制 6.5 G、不重跑 mathlib）

| 项 | 做法 |
|---|---|
| 工具链 | `leanprover/lean4:v4.33.0`（`lean-toolchain`） |
| mathlib | 以 **path 依赖**指向既有已构建 checkout |
| 依赖解析 | `.lake/packages` **符号链接**指向既有 packages 目录 |
| 冻结纪律 | Godcore `BoundaryTheory.lean` **只读**，不改动其冻结语料 |

## 模块与论文对应

| 模块 | 论文位置 | 内容 |
|---|---|---|
| `CausModel/Probe.lean` | — | B0 探针：核验 mathlib 原语在位 |
| `CausModel/Caus.lean` | §1.1（L90） | `Caus := Paths V`；范畴结构；**万有性质**；`V ↦ Caus V` **函子性** |
| `CausModel/Attribution.lean` | §1.2（L96–L108） | `Simplex`（Δ²）；归因预函子；函子律；**唯一性** |
| `CausModel/Boundary.lean` | §1.3/§2.1/§2.5（L112–L219） | 凝聚 = 闭包算子/单子；**边界 = 不动点**；`η`；**缺陷方块** |
| `CausModel/Attractor.lean` | §3.5（L289–L299） | 装配吸引子：**存在 + 唯一 + 几何速率 + 收敛** |
| `CausModel/KernelModuli.lean` | §5.1–§5.2（L405–L425） | 核模空间；$C_F$ **权 −1 等变律**；tanh 同轨 |

## 判据（B-a … B-g）

- **B-a** ✅ `Caus` 是范畴，万有性质被证 —— `Caus.lift` · `Caus.lift_unique`
- **B-b** ✅ `V ↦ Caus V` 是函子 —— `Caus.map_id` · `Caus.map_comp`
- **B-c** ✅ `A` 是真函子，靶先声明为范畴 —— `attribution` · `attribution_unique`
- **B-d** ✅ `Attrib` 被定义，`η` 是真自然变换 —— `CategoricalCohesion` · `CohesionUnit`
- **B-e** ✅ 边界 = 不动点，带万有性质 —— `boundary_galois` · `boundary_adjunction`
- **B-f** ✅ 缺陷方块与障碍类 —— `Commutes` · `Defect` · `commutes_iff_isBoundaryMap`
- **B-g** ✅ §3.5 不动点（闭合 T5）· 核层 $C_F$ 函子性 —— `cascade_tendsto` · `coreConstant_rescale`

详见 `../B阶段验收报告_20260930.md`（含**证明↔主张映射表**与**形式化对论文的反向修正 X1–X6**）。

## 关键结论（可引用）

1. **§1.1 的"范畴"是 free category**：论文 Def 1.1 逐字对应 mathlib 的 `Paths V`，结合律/单位律与
   **万有映射性质**由自由构造承担，无需公设。
2. **§1.2 的函子律不是公设**：`attribution_unique` 表明预函子由其在**单干预**上的取值唯一决定。
3. **§1.3 的"闭包"有精确范畴归宿**：闭包算子 = 幂等单子，边界 = 其不动点/代数，万有性 = Galois 插入。
4. **§2.5 的"最小违反项"可判定**：方块交换 ⟺ 落在边界上。
5. **§3.5 的 ε 必须为正**（`ε = −1` 是反例）——这是形式化对论文的精确化增益。
6. **§5.2 的 $C_F$ 是权 −1 的等变函数**，不是轨道不变量；logistic 与 tanh **同轨**。

## 边界（不做的事）

- **不声称范畴层"为真"**：建模同一化（"某系统的归因结构就是这样的函子"）仍是**建模假设 A6**。
- **不把机检冒充 agent 结论**。
- **不动 §4 的 33 条**（Godcore 冻结语料）。
- **不替代 W9**（判据操作化）。
