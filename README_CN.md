# 边界公理(统一边界公理)· Lean 4 形式化

对「边界认知假说」的 Lean 4 形式化:边界势 `V(κ)=c₀κ+απ²/(3κ)` 的最小作用量锐度 `κ*`、张力 `σ*`、以及沿运动方程的能量守恒(dE/dt≡0)三命题。

## 版本锚

- **v0.1**(本树)——三命题基于 `Mathlib` 完成形式化。
- 陈述对应工作稿:`docs/边界认知假说·边界概念的数学形式.md` §3(本仓库暂未附)。

## 文件

| 文件 | 内容 |
|---|---|
| `BoundaryTheory.lean` | 三命题的 Lean 4 定理(import `Mathlib`) |
| `VERSION.md` | 版本锚与变更记录 |

## 构建

```sh
leanproject get-mathlib-cache
lean --run BoundaryTheory.lean
```

(需 Lean 4 + Mathlib。)

## 状态

研究中(work in progress)。本仓为引用/派生锚点,**不构成已背书之科学论断**;伴随论文投稿中,出版后将在此补链接。

## 许可

Apache-2.0(见 `LICENSE`)。数学本身不受版权保护;本授权覆盖形式化代码与文档。

欢迎通过 Issue 反馈。
