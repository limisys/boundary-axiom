# 验证记录（统一仓）

**验证时间** 2026-10-19T15:29:18+08:00
**命令（作者离线审计）** `bash scripts/verify_all.sh`
**公网复现** GitHub Actions `verify` job（`scripts/ci_check.sh`）
**全量日志** `logs/verify/verify_20261019_152918.log`（sha256 `b0c446e66906fbe7ec6a68d609a0773a11f4c6823eff10441750d550a6d5c06f`；日志留在本地全量归档，不进入公开树）
**结论** **PASS 全部 9 步通过。**

---

## 一 · 环境

| 项 | 值 |
|---|---|
| Lean | 4.33.0（commit `d8b18978322de05a8f3dba51ef03cf5461676c17`） |
| 工具链 | `leanprover/lean4:v4.33.0`（通过 elan；公开环境用 `$HOME/.elan`） |
| Mathlib | v4.33.0，预构建 cache / oleans；第三方依赖，不在仓内 |
| 构建入口 | 作者离线审计：`scripts/build.py --clean --jobs 4`；公开复现：`lake update && lake exe cache get && lake build` |
| 源件 | `lean/` 56 件 ＋ `vendor/CausModel/` 15 件 |

---

## 二 · 九步结果

### 1/9 干净构建
```
== build 通过：71/71 件，入口覆盖 71 件，用时 112.9s
== dependency levels: [20, 12, 12, 5, 6, 5, 1, 1, 4, 2, 1, 1, 1]
== unreachable_from_entry: []
```
71 = 主开发体 56 ＋ CausModel 15。单一入口 `BoundaryProgramme` 可达全部 56 件主开发体。
manifest：作者离线生成 `data/build_manifest.json`（含本机路径，公开树不含；公开校验用 `MANIFEST.public.sha256`）。

### 2/9 0 `sorry` / 0 `axiom`（主开发体）
```
合计 thm/lem=467 def/str=90 文件=56
0 sorry / 0 axiom —— 通过
```

### 3/9 0 `sorry` / 0 `axiom`（冻结范畴层 CausModel）
```
合计 thm/lem=107 def/str=49 文件=15
0 sorry / 0 axiom —— 通过
```

### 4/9 四作用域计数对账
```
all.files: 56 (expected 56) ok        all.thm_lem: 467 ok        all.def: 90 ok
b_line.files: 55 ok                    b_line.thm_lem: 434 ok     b_line.def: 83 ok
a_module.files: 1 ok                   a_module.thm_lem: 33 ok    a_module.def: 7 ok
paper_b_canonical.files: 53 ok         …thm_lem: 417 ok           …def: 77 ok
PASS
```

### 5/9 主张索引
```
PASS 44 theorem references resolved
```
含新增 `C21`：`BoundaryReportIdentity.rep_eq_iff_closureOperator_eq`、`BoundaryReportIdentity.report_eq_fix_iff`、
`ReportCountermodels.nonUpClosed_not_canonical` 三条均可解析。

### 6/9 静态审计
```
{"root": "lean", "files": 56, "thm_lem": 467, "def": 90}
PASS
```

### 7/9 公理依赖（A 线硬证据 ＋ 同一性）
```
'BoundaryTheory.C_H_eq_pi_sq_div_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'ValueLayerMin.V_global_min' depends on axioms: [propext, Classical.choice, Quot.sound]
'ValueLayerMin.V_eq_min_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'BoundaryReportIdentity.rep_eq_iff_closureOperator_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'ReportCountermodels.nonUpClosed_not_canonical' depends on axioms: [propext, Classical.choice, Quot.sound]
PASS 公理依赖：5 条均为 [propext, Classical.choice, Quot.sound]，无 sorryAx
```
完整输出：`data/axioms.txt`。

### 8/9 独立数值复现（纯标准库）
- `repro_v3.py`：12/12 检查 `pass: true`；`θ* = 0.5378828427399902`。
- `repro_path_b.py`：`C_H(integral) = 3.2898681336955584`（rel_err `2.7e-13`）；`C_H(series) = 3.289868133696525`（rel_err `2.2e-14`）。
结果：`data/repro_v3_results.json`、`data/repro_path_b_results.json`。

### 9/9 跨工程对接件
```
'ChengbanVerification.kappaStar_link'  depends on axioms: [propext, Classical.choice, Quot.sound]
'ChengbanVerification.kappaStar_scale' depends on axioms: [propext, Classical.choice, Quot.sound]
PASS 跨工程对接件：2 条定理，仅标准三公理
```

---

## 三 · 关键件哈希

| 件 | sha256 |
|---|---|
| `lean/BoundaryTheory.lean` | `4f63b1e4e44c8d3fd02fd4d38299bfad55535398c26f8415273e2c6254a090cb` |
| `lean/BoundaryReportIdentity.lean` | `5d7319b2eaa81bcb969f7de1d673f4bfb14e55ea842d71515d7225dfb0677daa` |
| `lean/ReportCountermodels.lean` | `8f628b47f513c2891e222f783e12b9d139f7dfdba793f660cbd91e10e4a0c8f3` |
| `lean/BoundaryProgramme.lean` | `aaf886a975e14ee3196768b91f15d346b47a57ee36e5246cd22ceb2df3f65982` |
| `lean/DimensionAlgebra.lean` | `68bcaafda72589cac5df56d322e0bcb7cc886243967b6978cbafcc03fa94b212` |
| `data/counts.json` | `ba026434c58130ab199c92826d9c7d050f54d831dc8c5d63a116c399051cb9ed`（本次生成） |
| 全量日志 | `b0c446e66906fbe7ec6a68d609a0773a11f4c6823eff10441750d550a6d5c06f` |

> `data/counts.json` 与 `data/build_manifest.json` 每次验证会重新生成；上表是**本次**日志的值。
> 公开树逐文件哈希以 `MANIFEST.public.sha256` 为准：`sha256sum -c MANIFEST.public.sha256`。
> `MANIFEST.sha256` 是作者全量快照（含 `archive/`、`logs/`），不进入公开树。

---

## 四 · 复现

```bash
# 公网标准路径
git clone https://github.com/limisys/boundary-axiom.git
cd boundary-axiom
lake update && lake exe cache get && lake build
bash scripts/ci_check.sh

# 作者离线全量审计（可选；需预构建 Mathlib packages）
# bash scripts/verify_all.sh
```

---

## 五 · 限制

1. **Mathlib 外部**：公开构建用 `lake update && lake exe cache get`；离线审计依赖预构建 packages。两者读同一批 `lean/` 源件。
2. **Lake 路径**：本次 2026-10-19 日志由离线 `scripts/build.py` 产生；公开 CI 负责 `lake build` 路径。若 CI 未绿，不以“可复跑”对外。
3. **Z3 未跑**：默认九步不含 Z3；主链证据以 Lean ＋ 公理检查为准。
4. **历史文档**：`docs/rounds/` 的计数/路径是当时口径；不进入公开树。
5. **验证后改动**：本记录生成后，发布工程只改了 README/STATUS/scripts 的文字与路径；Lean 源件、定理与验证结果未变。

## Manifest scopes

Two manifests are published and they cover different trees:

- `MANIFEST.public.sha256` — 183 entries, frozen for the packaged tree at `f01cf6f`. Its SHA-256 is
  `1fb0301132e66edfd20d0286691db0f78d2a83e9029ee5fd35cf77fdb45fa59c`, the value bound in
  `genesis/GENESIS.json`. Verify it inside the extracted package directory only.
- `MANIFEST.attestation.sha256` — the current repository worktree, including `genesis/`, `ots/`,
  `release/` and page-metadata updates. Verify it at the repository root.

Running the packaged manifest at the repository root reports `site/evidence.html` as FAILED, because
the repository copy of that page has been updated since packaging. That is expected: the packaged
manifest is kept byte-identical to its packaged version so the genesis digest stays valid.
