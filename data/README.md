# 数据与生成物

| 文件 | 类型 | 产出者 | 说明 |
|---|---|---|---|
| `counts.json` | 生成 | `scripts/counts.py` | 四作用域计数；与 `docs/counts.json` 对账 |
| `claim_index.json` | 生成 | `scripts/claim_index.py` | `docs/claims.yaml` → Lean 声明名/文件/行 |
| `lean_static_audit.json` | 生成 | `scripts/lean_static_audit.py` | 逐件计数与违规词 |
| `build_manifest.json` | 生成 | `scripts/build.py` | 71 个模块（56 主 ＋ 15 CausModel）的源哈希/耗时/状态；入口可达检查 |
| `axioms.txt` | 生成 | `scripts/audit_C_H/run_check.sh` | 5 条承重声明的公理依赖 |
| `crosslink_axioms.txt` | 生成 | `scripts/check_crosslink.sh` | 跨工程对接件 2 条定理的公理依赖 |
| `no_sorry_lean.txt` | 生成 | `scripts/check_no_sorry.py` | 56 件 0 sorry/axiom 的逐件输出 |
| `no_sorry_causmodel.txt` | 生成 | `scripts/check_no_sorry.py` | CausModel 15 件 0 sorry/axiom |
| `repro_v3_results.json` | 生成 | `scripts/repro_v3.py` | B 线九组件独立数值复现 |
| `repro_path_b_results.json` | 生成 | `scripts/repro_path_b.py` | A 线路径 B 数值复现 |
| `source_manifest.tsv` | **静态** | 合并时生成 | 逐件来源树、角色、sha256 |

**复现**：`bash scripts/verify_all.sh`。生成物会覆盖同名文件；`source_manifest.tsv` 不被覆盖。
