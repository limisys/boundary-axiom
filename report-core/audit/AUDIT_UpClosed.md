# 审计：v1.0 的 `UpClosed` 条件是退化的

**日期** 2026-10-23
**对象** 上游 `BoundaryReportIdentity.lean`（v1.0，commit `dd329e6`）中的 `UpClosed`
**结论** `UpClosed R ↔ R = Set.univ`。前件退化，v1.0 的“相互决定”定理为重言式。
**状态** 已在上游之外更正；上游源件未修改。本审计件**不**作为结论引用。

---

## 1 · 原定义

```lean
def UpClosed (R : Report Ω) : Prop :=
  (∅ : Set Ω) ∈ R ∧ ∀ ⦃S T : Set Ω⦄, S ∈ R → S ⊆ T → T ∈ R
```

## 2 · 退化定理

```lean
theorem upClosed_eq_univ {R : Report Ω} (h : UpClosed R) : R = Set.univ := by
  ext T
  constructor
  · intro _; trivial
  · intro _
    exact h.2 h.1 (Set.empty_subset T)
```

证明只有一步：任意 `T` 都满足 `∅ ⊆ T`；由 `∅ ∈ R` 与“对超集封闭”，`T ∈ R`。

反向也成立：`Set.univ` 显然满足 `UpClosed`。因此：

```lean
theorem upClosed_iff_eq_univ (R : Report Ω) : UpClosed R ↔ R = Set.univ
```

---

## 3 · 为什么这使 v1.0 的结论退化

`BoundaryReportIdentity.lean` 的主结果：

- `rep_eq_iff_closureOperator_eq`：向上封闭 `R, R′` 下，`c_R = c_R′ ↔ R = R′`；
- `report_eq_fix_iff`：向上封闭 `R` 下，`R = Fix(c_I) ↔ c_R = c_I`。

若 `UpClosed R`，则 `R = Set.univ`：

- `repClosed R S = ⋂{T : S⊆T ∧ T∈R} = S`，故 `c_R = id`；
- `R = R′` 与 `c_R = c_R′` 都自动为真，第一条成为重言式；
- 第二条变成 `Set.univ = Fix(c_I) ↔ id = c_I`，只剩一个很窄的等价，不再是“报告族恰是闭元族”的实质判据。

`ReportCountermodels.nonUpClosed_not_canonical` 仍然为真（存在非向上封闭的 `R` 使 `R ≠ Fix(c_R)`），但由于**所有**非全幂集族都不是向上封闭，这条反例也失去了区分力。

**关键点**：Lean 验证了证明的每一步；它不检查前件是否只挑出一个平凡对象。`#check`、`#print axioms`、0 `sorry` 都不会报警。

---

## 4 · 更正

v1.1 用 Moore 族替换：

```lean
def Moore (R : Report Ω) : Prop :=
  ∀ F : Set (Set Ω), F ⊆ R → ⋂₀ F ∈ R
```

它等价于“`R` 是某个闭包算子的闭元族”（`moore_iff_exists_closure`），且非空：

- 任意闭包算子 `c` 的 `Fix c` 都是 Moore 族（`fix_moore`）；
- 非 Moore 反例仍然存在（`nonMoore_not_canonical`）。

这次更正使定理有内容，代价是承认其数学骨架是标准的闭包算子—Moore 族对应。

---

## 5 · 复现

```bash
cd 02_Lean仓库/audit
ELAN_HOME=/path/to/lean-home \
  lean AUDIT_UpClosed.lean
```

预期输出：

```
'Audit.upClosed_iff_eq_univ' depends on axioms: [propext, Quot.sound]
```

完整日志：`AUDIT_UpClosed.log`。

---

## 6 · 方法论备注

这类错误在“把哲学断言形式化”的工作里尤其容易发生：

1. 为了让前件“看起来自然”，选了一个过强的条件；
2. 定理确实被证明了，审稿人看到 0 `sorry` 就放行；
3. 没有人检查前件的模型是否非空、是否只包含平凡对象。

防御方式：

- 为每个前件至少构造一个**非平凡**模型；
- 证明前件的**存在性**与**非退化性**（例如 `moore_iff_exists_closure`）；
- 为前件写一个**反例**，确认删掉它会失败；
- 在论文中把前件与结论一起写，绝不省略。

本次发布把这条教训写进公开文本，而不是藏在脚注里。
