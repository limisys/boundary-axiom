# 溯源与合并裁定

**日期** 2026-10-19 · **对象** `形式化全局完整唯一仓库/` 的每一件从何而来、为何这样合。
**纪律**：只并全、不删源；旧树在合并期间**未被修改**；所有改动集中在新的单一入口文件（见 §4）。

---

## 一 · 三棵源树（合并前的实测状态）

| | 正典树 | 权威树 | 公开仓 |
|---|---|---|---|
| 路径 | `论文/04_研究支撑/潜龙_理论主场/03-数学形式化/lean_check/` | `exp/边界势推进_20261006/lean/` | `public/boundary-programme/` |
| 可见 `.lean` | 55（53 B ＋ `BoundaryTheory` ＋ 已取代 `sigma_bridge`） | 56（53 B ＋ 两件同一性 ＋ 已取代 `sigma_bridge`） | 54（53 B ＋ `BoundaryTheory`） |
| 统计口径 | B 线 417/77/53；含 A 模块 450/84/54 | 434/84/55（`sigma_bridge` 排除） | 450/84/54 |
| 另有 | 隐藏失败件 `.DimensionAlgebra_v1_failed.lean` | `build_prev_20261008/`、旧日志 | `data/`、`docs/claims.yaml`、`scripts/`、`vendor/CausModel/` |
| 角色 | 论文 B 的开发体 | “边界↔自报同一性”定理的唯一载体 | 发布/复现包 |
| 合并时的 git 状态 | 主仓工作区（部分未提交） | 主仓工作区 | `main` 分支**尚无提交**，全部文件 staged |

**三棵树的真实差异**（逐字节哈希比对，2026-10-19）：

- 53 件 B 线来源在正典/权威/公开三处**逐字节相同**（`DimensionAlgebra` 除外）；
- 权威树**多** `BoundaryReportIdentity.lean`、`ReportCountermodels.lean`；
- 正典树与公开仓**多** `BoundaryTheory.lean`；
- 两版 `DimensionAlgebra.lean` 不同：权威树保留本地 `def sigmaStar`（10 def），正典树改为 `import BoundaryTheory`（9 def）——**正典是第 59 轮去重版**；
- 两版 `BoundaryTheory_sigma_bridge.lean` 不同：正典多 9 行“已被取代”头注，**正典较新**；
- 两版 `BoundaryProgramme.lean` 不同：权威多 `import BoundaryReportIdentity`，**权威较新**。

⇒ **双向分叉**，不是简单的新旧关系。逐项裁定见 §3。

---

## 二 · 并集后的一份内容

```
53 件 B 线（正典，含去重版 DimensionAlgebra）
  ＋ BoundaryReportIdentity（权威）
  ＋ ReportCountermodels（权威）
  ＋ BoundaryTheory（正典/公开/Godcore 三处同哈希）
  = 56 件统计开发体 ＋ 统一入口 BoundaryProgramme
```

**计数**：467 thm/lem · 90 def · 56 文件（推导见 `docs/counts.md`）。
**B 线全量**：434/83/55（比权威树的 434/84/55 少 1 个 def，因为不保留重复的 `sigmaStar`）。

---

## 三 · 逐件裁定表

| 件 | 采用 | sha256（前 16 位） | 理由 |
|---|---|---|---|
| 53 件 B 线公共件 | 正典树 | 逐件见 `MANIFEST.sha256` | 与权威/公开逐字节相同；正典为主仓工作树 |
| `DimensionAlgebra.lean` | **正典**（去重版） | `68bcaafda72589ca…` | 已 `import BoundaryTheory`，删除重复 `def sigmaStar`；统一仓含 A 模块，去重版可编译且不重复计数 |
| `BoundaryTheory.lean` | **正典** | `4f63b1e4e44c8d3f…a090cb` | 与公开仓、Godcore 上游逐字节相同；A 线硬证据（`C_H=π²/3`）载体 |
| `BoundaryReportIdentity.lean` | **权威树** | `5d7319b2eaa81bcb…` | 只在权威树；哈希与 `108` 登记值一致，自 2026-10-08 未变 |
| `ReportCountermodels.lean` | **权威树** | `8f628b47f513c289…` | 只在权威树；同上 |
| `BoundaryProgramme.lean` | **权威版 ＋ 1 行 import** | 合并后 `aaf886a975e14ee3…` | 权威版较新（已 import 同一性）；再补 `import ReportCountermodels`，使入口覆盖 56 件全部。头注同步说明 |
| `BoundaryTheory_sigma_bridge.lean` | **归档**（正典版 ＋ 权威旧版） | 正典 `c872f3e9764e7cc9…`；权威 `a9bb85b6324f0e6a…` | 已被 `ValueLayerExtension` 取代；按 append-only 保留，但不进 `lean/`、不参与构建、不计入统计 |
| 隐藏失败件 `DimensionAlgebra_v1_failed.lean` | **归档** | `f7ad0b0a78049bac…` | 失败版本，只作历史证据 |
| 顶格重复 `.lean` 五件（3 件同正典、2 件同权威旧版） | **不重复复制** | 与正典/权威同哈希 | `BoundaryBridge_layers`／`sigmaCoh`／`LanguageInterventions` 与正典相同；`sigma_bridge`／`DimensionAlgebra` 与权威旧版相同。哈希已验证，见 §5 |
| `build_lean_all.sh.bak-20261019` | **归档** | 见 `MANIFEST` | 安全回滚路径，按全局纪律保留 |
| `.try.sh`、`.scratch_sigma_bridge_r41_uncompiled.lean` | **归档** | 见 `MANIFEST` | 草稿/未编译候选，保留但不进主链 |

**唯一的源码改动**：`lean/BoundaryProgramme.lean` 增加 `import ReportCountermodels` 与三行头注。
**未改动任何定理、定义、证明。** 与权威版差异可用相对路径 `diff` 复核（旧树不在公开树内，路径仅作历史记录）：

```bash
diff -u exp/边界势推进_20261006/lean/BoundaryProgramme.lean \
        lean/BoundaryProgramme.lean
```

> 公开仓只包含合并后的 `lean/`、`vendor/CausModel/`、脚本与证据；三棵旧树、`archive/`、
> `logs/`、`docs/rounds/`、`docs/audits/` 留在本地完整目录，不进入公开树。

---

## 四 · 合并后的单一入口

`lean/BoundaryProgramme.lean` 现在 import 全部 56 件（B 线 55 ＋ A 模块 1），`scripts/build.py` 会检查
“每个开发件都从入口可达”。因此：

- 编译入口 = 全开发体互不冲突；
- 任何一件被移出/改名，入口构建即失败；
- 不再存在“某件只在另一棵树里、入口复现不出”的情况。

---

## 五 · 哈希与来源表

- 作者全量逐文件哈希：`MANIFEST.sha256`（含 `archive/`、`logs/`，不进入公开树）。
- 公开树逐文件哈希：`MANIFEST.public.sha256`（`sha256sum -c` 可复核）。
- 逐件来源表：`data/source_manifest.tsv`（作者全量；含 `archive/`/`crosscheck`，公开树不含）。
- 关键件完整哈希：

| 件 | sha256 |
|---|---|
| `lean/BoundaryTheory.lean` | `4f63b1e4e44c8d3fd02fd4d38299bfad55535398c26f8415273e2c6254a090cb` |
| `lean/BoundaryReportIdentity.lean` | `5d7319b2eaa81bcb969f7de1d673f4bfb14e55ea842d71515d7225dfb0677daa` |
| `lean/ReportCountermodels.lean` | `8f628b47f513c2891e222f783e12b9d139f7dfdba793f660cbd91e10e4a0c8f3` |
| `lean/BoundaryProgramme.lean` | `aaf886a975e14ee3196768b91f15d346b47a57ee36e5246cd22ceb2df3f65982` |
| `lean/DimensionAlgebra.lean` | `68bcaafda72589cac5df56d322e0bcb7cc886243967b6978cbafcc03fa94b212` |
| `archive/superseded/BoundaryTheory_sigma_bridge__canonical_superseded_header.lean` | `c872f3e9764e7cc9eca5b08bfa63ff22f281e7333650fafa924247740236956c` |
| `archive/superseded/BoundaryTheory_sigma_bridge__authority_old.lean` | `a9bb85b6324f0e6a8323c9c8b7b672c9fdcc4bce8bc6c62cbc058d9672157f6b` |
| `archive/superseded/DimensionAlgebra__authority_with_local_sigmaStar.lean` | `b59b947f4611384fd4aba36d0bd2406a88f7c25095e429ff09e0325afb41f09d` |
| `archive/failed/DimensionAlgebra_v1_failed.lean` | `f7ad0b0a78049bac049089e25d454d14f75db22aca10566ff1973894ec6867d2` |
| `vendor/Godcore_BoundaryTheory/BoundaryTheory.lean` | `4f63b1e4e44c8d3fd02fd4d38299bfad55535398c26f8415273e2c6254a090cb` |

---

## 六 · 从此以后

1. **本仓是唯一源**。旧的三棵树保留为历史快照；若需改动，在本仓改，按需导出到公开仓，**不要反向编辑旧树**（否则重新分叉）。
2. **计数只有一个真源**：`scripts/counts.py` ＋ `docs/counts.json`。对外引用一律走 `scripts/quote_counts.py`。
3. **公开发布**：公开仓 `boundary-axiom` 由本仓的 curated 公开树导出；旧三棵树与 `public/boundary-programme` 的 `lean/` 不再作为代码源。公开树不含 `archive/`、`logs/`、`docs/rounds/`、`docs/audits/`。
4. **未做**：旧树删除／改名；`exp` 树与 `lean_check` 的物理去重。都等高总裁定。
