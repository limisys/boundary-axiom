# 状态（2026-10-19）

## 一句话

**统一仓已建立并通过完整验证**：56 件开发体 / 467 thm-lem / 90 def / 0 `sorry` / 0 `axiom`；
71 个模块（56 主 ＋ 15 CausModel）全部编译通过；单一入口 `BoundaryProgramme` 覆盖全部开发件。

## 一 · 数字

| 作用域 | 文件 | thm/lem | def |
|---|---:|---:|---:|
| **统一仓审计体** | **56** | **467** | **90** |
| B 线全量 | 55 | 434 | 83 |
| 论文 B 正典 | 53 | 417 | 77 |
| A 模块 `BoundaryTheory` | 1 | 33 | 7 |

三套历史数字的关系：**417/77/53** 是论文 B 正典子集；**434/84/55** 是权威树（统一仓去重后 434/83/55）；**450/84/54** 是公开仓（缺两件同一性）。统一仓并全后 **467/90/56**。详见 `docs/counts.md`。

## 二 · 验证证据

**最后一次全量验证**：`logs/verify/verify_20261019_152918.log`（2026-10-19T15:29:18+08:00，9/9 PASS）；摘要见 `VERIFICATION.md`。

| 检查 | 结果 |
|---|---|
| 干净构建（71 模块，入口可达） | ✅ 71/71 OK；入口覆盖 71（56 主开发件 ＋ 15 CausModel） |
| 0 `sorry` / 0 `axiom`（56 件） | ✅ |
| 0 `sorry` / 0 `axiom`（CausModel 15 件） | ✅ |
| 四作用域计数对账 | ✅ 56/467/90；55/434/83；1/33/7；53/417/77 |
| 主张索引（C01–C21，44 条定理引用） | ✅ 全部解析 |
| 静态审计 | ✅ |
| 公理依赖（5 条承重声明） | ✅ 仅 `[propext, Classical.choice, Quot.sound]` |
| 独立数值复现（B 线 / A 线） | ✅ |
| 跨工程对接件（2 条） | ✅ 仅标准三公理 |

## 三 · 单一源

- **源件**：`lean/`（56 件）＋ `vendor/CausModel/`（15 件）＋ `vendor/Godcore_BoundaryTheory/`（出处/备份）。
- **计数**：`scripts/counts.py` → `data/counts.json`；期望值 `docs/counts.json`。
- **入口**：`lean/BoundaryProgramme.lean`，import 全部 56 件。
- **溯源**：`PROVENANCE.md`、`data/source_manifest.tsv`、`MANIFEST.sha256`。

## 四 · 仍未做（等高总/后续）

1. **旧树处置**：`lean_check/`、`exp/…/lean/`、`public/boundary-programme/lean/` 仍在，未删除/改名；现为只读历史快照。
2. **公开仓发布**：`boundary-axiom` 由本仓的 curated 公开树导出（GitHub canonical / Gitee mirror）；公开树不含 `archive/`、`logs/`、`docs/rounds/`、`docs/audits/`。旧 `public/boundary-programme` 的 450/84/54 是历史口径，不再作为代码源。
3. **Lake 联网路径**：`lakefile.toml` 已就绪，但本次只验证了离线 `scripts/build.py`，未实跑 `lake update && lake build`。
4. **Z3 脚本**：未进默认验证（需 `z3-solver`，见 `scripts/z3/README.md`）。
5. **论文数字回填**：论文 B 仍可写 417/77/53；若改“全审计体”，必须改 467/90/56（或分层写法）。本仓不改论文稿。

## 五 · 限制（如实）

- Mathlib 是第三方依赖，不在仓内；离线构建依赖本机预构建 packages。
- 统一仓只新增 1 行 import（`ReportCountermodels`）与说明头注，不改任何定理/定义/证明。
- 历史轮次笔记中的路径与计数是当时口径，不作为当前真源。
