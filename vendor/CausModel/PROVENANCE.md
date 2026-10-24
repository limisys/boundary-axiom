# CausModel 源码快照 · 依赖解析说明

**版本**：v1.0_enhanced · **日期**：2026-09-30

## 组成（本包内）
```
CausModel.lean            入口
lakefile.toml             工程配置
lean-toolchain            leanprover/lean4:v4.33.0
lake-manifest.json        依赖清单
CausModel/                12 个模块（见下）
```
12 个模块：`Probe` `Caus` `Attribution` `Boundary` `Idempotent` `Instance`
`Attractor` `Landau` `ModelClass` `Maintenance` `KernelModuli` `Orbit`

## 依赖（**不含在本包内**）
- **Lean 4.33.0** 工具链
- **Mathlib v4.33.0**（rev `db584cd6d46c92f209a44c0f1c829460d327499d`）

## 冷构建步骤
```bash
# 1) 取得 mathlib v4.33.0 并完成其自身构建（约 6.5 GB olean；本工程不自建 mathlib）
# 2) 让本工程解析到该 mathlib：
#    方式 A（推荐）：把 .lake/packages 符号链接到既有 packages 目录
mkdir -p .lake && ln -sfn /path/to/mathlib-lake-packages .lake/packages
#    方式 B：修改 lakefile.toml 中 mathlib 的 path 指向本地 checkout
# 3) 构建
export ELAN_HOME=/path/to/lean-runtime
export PATH="$ELAN_HOME/bin:$PATH"
rm -rf .lake/build && lake build CausModel
# 预期：Build completed successfully (3297 jobs)
```

## 证据
- 构建日志与零 `sorry`/`axiom` 核验：`../交付/构建日志_零sorry证据_20260930.txt`
- 证明↔主张映射（含文件路径与行号）：`../交付/证明-主张映射表.json`
- 完整性哈希：`../交付/MANIFEST.md`

## 冻结语料
本工程**不修改** Godcore `BoundaryTheory.lean`（33 条冻结声明），
仅通过 path 依赖读取。其 md5 为 `2fcac592e60512f9464c590772bfa118`。
