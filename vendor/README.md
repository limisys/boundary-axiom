# 第三方／冻结依赖（源件随仓，不随仓分发 Mathlib）

| 目录 | 内容 | 角色 |
|---|---|---|
| `CausModel/` | 15 件 Lean 范畴层模型（`CausModel.lean` ＋ `CausModel/*.lean`）＋ 交付映射表/构建日志/MANIFEST | 主开发体的构建依赖（`BoundaryProgramme` import `CausModel`） |
| `Godcore_BoundaryTheory/` | `BoundaryTheory.lean`、`BoundaryTheory.lean.bak_0829`、lake 配置 | A 模块上游出处与回滚备份 |

**Mathlib 不在仓内**：它是第三方依赖，版本由 `lean-toolchain`（Lean 4.33.0）与 Lake manifest 固定。
离线构建只读既有的 `packages/*/.lake/build/lib/lean`，不复制、不重跑（见 `scripts/build.py`）。

## 构建

- 默认 `scripts/build.py` 会从 `vendor/CausModel/` 源码编译 15 件，产出到 `lean/build/CausModel*.olean`。
- `vendor/Godcore_BoundaryTheory/BoundaryTheory.lean` 与 `lean/BoundaryTheory.lean` **逐字节相同**（sha256 `4f63b1e4…a090cb`），
  主构建只用后者；前者作为出处与备份保留，不参与构建、不计入 56 件。
- `vendor/CausModel/交付/*.tar.gz` 未入仓（打包副本，33 MB）；源件与交付映射表在仓内。
