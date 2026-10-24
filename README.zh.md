# Boundary Programme — 机检形式化仓

边界 = 闭包算子的不动点集；判据 = 核的阈值水平集。本仓用 Lean 4 机检二者在
`L(θ)=ln((2−θ)/θ)` 下的接缝关系，以及“只依赖水平的规范不变谓词不能唯一选出水平”
的弱 no-go。

**状态**：研究代码与证据发布；论文为预印本，未经同行评审。本仓不是论文，也不主张
哲学解释已被机检。

## 口径（唯一真源：`docs/counts.json`）

| 作用域 | 文件 | 定理/引理 | 定义 |
|---|---:|---:|---:|
| **统一仓审计体** | **56** | **467** | **90** |
| B 线全量 | 55 | 434 | 83 |
| 论文 B 正典 | 53 | 417 | 77 |
| A 模块 `BoundaryTheory` | 1 | 33 | 7 |

- 56 件主开发体与 15 件 `CausModel`：**0 `sorry` / 0 `admit`**。
- **无自定义公理**；5 条承重声明只依赖标准 `[propext, Classical.choice, Quot.sound]`。
- 71 个模块构建；单一入口 `BoundaryProgramme` 覆盖全部 56 件主开发体。

**不要把 417 当成全仓数字**：417 是论文 B 正典子集；统一仓是 467。

## 目录

```
lean/                    56 件开发体（入口 BoundaryProgramme）
vendor/CausModel/        15 件范畴层依赖
scripts/                 构建、计数、主张索引、审计、数值复现
docs/                    范围、计数、主张、合并记录、DAG
data/                    机检结果
```

## 快速开始

```bash
lake update
lake exe cache get
lake build

python3 -m pip install -r requirements.txt
bash scripts/ci_check.sh
```

干净 clone 应构建 71 个模块并通过 `scripts/ci_check.sh`。GitHub Actions 跑同一套检查；
CI 绿是公开复现记录。

## 机检了什么

- 接缝：`Fix(c_{Lθ}) = S_θ`，`L(θ)=ln((2−θ)/θ)`；
- 描述层唯一；
- 弱 no-go：只依赖水平 `w` 的规范不变 `P(w)` 不能选唯一 `w`；
- 三类闭包在类型层统一；
- A 模块 `C_H = π²/3` 链；
- `scripts/repro_v3.py` / `scripts/repro_path_b.py` 的独立数值复现。

## 没有主张什么

- 不主张所有边界都是闭包不动点；
- 不主张同一系统上组织边界=认知判据（只有条件桥与逆反例）；
- 不主张水平必须由外部观察者设定；no-go 只覆盖 level-only 规范不变谓词；
- 不主张经验适用性；无实测数据；
- 不主张本仓证明了某个哲学命题。

论文各自写明 scope；以 `docs/SCOPE.md`、`docs/counts.md` 与论文的“不主张”节为准。

## 论文与镜像

- 论文 B：how there is（闭包不动点、水平、识别）
- 论文 A：共享参数边界势与有效域纠错
- 论文 C：康德 Grenze/Schranke 区分的形式重构

论文链接在预印本公开后补入。

- GitHub（canonical）：<https://github.com/limisys/boundary-axiom>
- Gitee（只读镜像）：<https://gitee.com/limisys/boundary-axiom>
- 引用：`CITATION.cff`
- Zenodo 代码 DOI：归档后补入

## 许可

- 代码（`lean/`、`scripts/`、`vendor/`）：Apache-2.0，见 `LICENSE`。
- 文档与数据（`docs/`、`data/`、README）：CC BY 4.0，见 `LICENSE-docs`。

## AI 辅助披露

> 本文的 Lean 证明草稿、文献初筛及代码重构使用了 AI 辅助工具（如大模型），所有数学推导、形式化核心逻辑及最终结论均由人类作者独立验证并承担全部学术责任。

英文定稿见 `docs/ai-disclosure.md`。

## 联系

高学强（Xueqiang Gao）· 独立研究者 · <classgao@gmail.com>
