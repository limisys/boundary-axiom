# 统一仓计数口径（唯一真源）

**执行脚本**：`scripts/counts.py`。本文件与 `docs/counts.json` 是该脚本的期望值；`--check` 不一致即失败。
**统一仓审计体**：**56 文件 / 467 定理或引理 / 90 定义或结构**。

## 一 · 一套源件，四个作用域（不是四套互相矛盾的数）

| 作用域 | 文件 | thm/lem | def | 组成 |
|---|---:|---:|---:|---|
| **统一仓审计体 `all`** | **56** | **467** | **90** | B 线 55 ＋ A 线 `BoundaryTheory` 1 |
| **B 线全量 `b_line`** | **55** | **434** | **83** | 正典 53 ＋ `BoundaryReportIdentity` ＋ `ReportCountermodels` |
| **A 模块 `a_module`** | 1 | 33 | 7 | `BoundaryTheory`（论文 A 的硬证据） |
| **论文 B 正典 `paper_b_canonical`** | 53 | 417 | 77 | 论文 B 正文所引的正典树 |

## 二 · 算术闭合（逐项可核算）

```
正典树（论文 B）                     417 / 77 / 53
  ＋ BoundaryReportIdentity           13 /  5 /  1
  ＋ ReportCountermodels               4 /  1 /  1
  = B 线全量                          434 / 83 / 55
  ＋ BoundaryTheory（A 模块）          33 /  7 /  1
  = 统一仓审计体                      467 / 90 / 56
```

**三个历史数字各自是什么**：

| 历史数字 | 对应 | 与统一仓的关系 |
|---|---|---|
| **417 / 77 / 53** | 论文 B 正典树 | 统一仓的 `paper_b_canonical` 子集，逐件不变 |
| **434 / 84 / 55** | 权威树（含两件同一性文件） | 定理/文件数相同；**定义数差 1**：权威树的 `DimensionAlgebra` 保留本地 `def sigmaStar`，统一仓采用第 59 轮去重版（`import BoundaryTheory`），故为 83 而非 84 |
| **450 / 84 / 54** | 公开仓（正典 ＋ `BoundaryTheory`，缺两件同一性文件） | 统一仓 = 450 + 17 定理 + 6 定义 + 2 文件 = 467 / 90 / 56 |

> **口径提醒**：公开仓 `450/84/54` 与权威树 `434/84/55` 的文件集合不同，不能直接相减。统一仓把两者并集与去重一次做完。
> 论文 B 正文仍可写 **417/77/53**（它是 `paper_b_canonical` 的精确口径）；若写"全审计体"，必须写 **467/90/56**，或写"417 ＋ 同一性 17/6/2 ＋ A 模块 33/7/1"。

## 三 · 计数规则

`scripts/counts.py` 与 `scripts/check_no_sorry.py` 使用同一条规则：

1. 剥离可嵌套块注释 `/- … -/` 与 `--` 行注释；
2. `thm_lem`：匹配 `^\s*(noncomputable|private|protected)* (theorem|lemma)\s` 的行数；
3. `def`：匹配同前缀的 `(def|abbrev|structure|instance)\s` 的行数；
4. `archive/` 不在 `lean/` 下，**不计入任何作用域**。

**历史口径**：公开仓 `docs/counts.md`（本仓保留为 `docs/counts_public_legacy.md`）里 450/84/54 与"独立剥离 458/83"的差，是**计数规则差**，不是漏件或多件；统一仓不沿用那一口径，也不把 458/83 当作定理事实。

## 四 · 这些数字不主张什么

- **不是独立数学结果的条数**。`sigmaStar_general` 是定义展开；`force_is_neg_gradient`、`energy_bracket_zero` 是代数恒等式；`p6_static_certificate` 含一个空洞合取（`x = x`）。哪些声明承重见 `docs/claims.yaml` 与 `data/claim_index.json`。
- **不是编译通过的证明**。编译由 `scripts/build.py` 单独负责；0 `sorry`/0 `axiom` 由 `scripts/check_no_sorry.py` 负责；公理依赖由 `scripts/audit_C_H/run_check.sh` 负责。
- **不是"三套数字谁对"的裁决**。它们是同一批源件在不同作用域的切片；统一仓把这四个作用域写进同一个 `counts.json`，从此只有一个计数真源。

## 五 · 复现

```bash
cd 形式化全局完整唯一仓库
bash scripts/build.py                 # 干净构建 + 入口覆盖检查
python3 scripts/counts.py --root lean --out data/counts.json --check docs/counts.json
```

期望最后一行：`PASS`。逐文件计数见 `data/counts.json` 的 `files` 数组。
