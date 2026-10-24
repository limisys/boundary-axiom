/-
城邦研究院 · 论文线 · B 阶段 · B5：装配吸引子 = 不动点定理
=============================================================

对应论文 `统一边界理论EN稿.md` **§3.5（assembly attractor）**（L289–L299）：

  "Each assembly event encapsulates a new module and expands carrying capacity,
   `C₀ → C₀(1+ε)`, updating the tension as
        σ_{n+1} = σ_n/(1+ε) + D,
   where `D` is the constant demand injected each round. The iteration has the unique
   fixed point
        σ_∞ = lim_{n→∞} A^n(σ₀) = D(1 + 1/ε),
   convergent when |∂A/∂σ| = 1/(1+ε) < 1."

原稿状态（L299）：*"mathematical derivation; confirmed by deterministic computation,
**not machine-checked in Lean**"*。

本模块把它升为**机器可证定理**，并补上原稿缺失的**收敛速率**：
  · `cascade_fixed`          —— σ_∞ 确为不动点
  · `cascade_fixed_unique`   —— 不动点唯一
  · `cascadeIter_sub_fixed`  —— 误差的**精确几何公式**：σ_n − σ_∞ = (σ₀ − σ_∞)/(1+ε)^n
  · `cascade_tendsto`        —— 迭代收敛到 σ_∞（原稿只有"收敛"二字，无速率）

同时闭合 `04_审稿文档评价_模拟稿与三把飞刀_20260926.md` §五.4 记录的 **T5 缺口**
（"说明 T5（压缩映射不动点）为何未纳入 Lean，或给出计划"）。

**假设精度说明（形式化增益）**：论文 §3.5 只用文字说 "assembly efficiency ε"。
形式化时必须显式取 **`0 < ε`**（装配效率为正）——因为 `ε ≠ 0` **不足以**保证 `1 + ε ≠ 0`
（`ε = −1` 即反例，此时级联映射分母为零、无定义）。这一条是形式化对论文表述的精确化。

**证据档位**：机器证明（本模块零 `sorry`）。
-/

import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.SpecificLimits.Basic

open Filter
open scoped Topology

namespace CausModel

noncomputable section

/-- 论文 §3.5 的装配级联映射：`A(σ) = σ/(1+ε) + D`（ε = 装配效率，D = 每轮注入的常需求）。 -/
def cascade (ε D σ : ℝ) : ℝ := σ / (1 + ε) + D

/-- 论文 §3.5 的极限张力：`σ_∞ = D(1 + 1/ε)`。 -/
def cascadeFixed (ε D : ℝ) : ℝ := D * (1 + 1 / ε)

/-- n 次级联迭代：`σ_n = A^n(σ₀)`。 -/
def cascadeIter (ε D : ℝ) (n : ℕ) (σ : ℝ) : ℝ := (cascade ε D)^[n] σ

/-- 装配效率为正时，`1 + ε ≠ 0`（级联映射的分母非零）。

**形式化增益**：论文未明写此假设；`ε ≠ 0` 不充分（`ε = −1` 是反例）。 -/
theorem one_add_ne_zero {ε : ℝ} (hε : 0 < ε) : (1 + ε) ≠ 0 := by
  positivity

/-- **关键恒等式**：级联映射与不动点的差，每一步恰好缩小 `(1+ε)` 倍。

这是全部结论的代数内核：收敛不是数值观察，而是**一步精确的除法**。 -/
theorem cascade_sub_fixed {ε : ℝ} (hε : 0 < ε) (D σ : ℝ) :
    cascade ε D σ - cascadeFixed ε D = (σ - cascadeFixed ε D) / (1 + ε) := by
  have h1 : (1 + ε) ≠ 0 := one_add_ne_zero hε
  have hε0 : ε ≠ 0 := ne_of_gt hε
  unfold cascade cascadeFixed
  field_simp
  ring

/-- **不动点存在性**：`σ_∞ = D(1+1/ε)` 是 `A` 的不动点。 -/
theorem cascade_fixed {ε : ℝ} (hε : 0 < ε) (D : ℝ) :
    cascade ε D (cascadeFixed ε D) = cascadeFixed ε D := by
  have h := cascade_sub_fixed hε D (cascadeFixed ε D)
  rw [sub_self, zero_div] at h
  exact sub_eq_zero.mp h

/-- **不动点唯一性**：`A` 的不动点唯一。 -/
theorem cascade_fixed_unique {ε : ℝ} (hε : 0 < ε) (D : ℝ) {σ : ℝ}
    (h : cascade ε D σ = σ) : σ = cascadeFixed ε D := by
  have h1 : (1 + ε) ≠ 0 := one_add_ne_zero hε
  have hε0 : ε ≠ 0 := ne_of_gt hε
  have h' := cascade_sub_fixed hε D σ
  rw [h] at h'
  have h2 : (σ - cascadeFixed ε D) * ε = 0 := by
    rw [eq_div_iff h1] at h'
    nlinarith
  have : σ - cascadeFixed ε D = 0 := (mul_eq_zero.mp h2).resolve_right hε0
  linarith

/-- **误差的精确几何公式**：`σ_n − σ_∞ = (σ₀ − σ_∞)/(1+ε)^n`。

⇒ 收敛速率是**指数级**的，常数 `1/(1+ε)`——正是论文 §3.5 所称的 `|∂A/∂σ|`。 -/
theorem cascadeIter_sub_fixed {ε : ℝ} (hε : 0 < ε) (D : ℝ) (n : ℕ) (σ : ℝ) :
    cascadeIter ε D n σ - cascadeFixed ε D
      = (σ - cascadeFixed ε D) / (1 + ε) ^ n := by
  induction n with
  | zero => simp [cascadeIter]
  | succ n ih =>
      have hstep : cascadeIter ε D (n + 1) σ = cascade ε D (cascadeIter ε D n σ) := by
        simp [cascadeIter, Function.iterate_succ_apply']
      rw [hstep, cascade_sub_fixed hε, ih, div_div, ← pow_succ]

/-- **收敛性（机器可证）**：ε > 0 时迭代收敛到唯一不动点 `σ_∞ = D(1+1/ε)`。

原稿 §3.5 只有 "convergent when |∂A/∂σ| < 1" 的断言；本定理给出证明。 -/
theorem cascade_tendsto {ε : ℝ} (hε : 0 < ε) (D σ : ℝ) :
    Tendsto (fun n : ℕ => cascadeIter ε D n σ) atTop (nhds (cascadeFixed ε D)) := by
  have h1 : (1 : ℝ) < 1 + ε := by linarith
  have hpow : Tendsto (fun n : ℕ => ((1 + ε : ℝ) ^ n)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt h1)
  have hmul : Tendsto (fun n : ℕ => (σ - cascadeFixed ε D) * ((1 + ε : ℝ) ^ n)⁻¹)
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hpow)
  have hev : (fun n : ℕ => cascadeIter ε D n σ - cascadeFixed ε D) =ᶠ[atTop]
      (fun n : ℕ => (σ - cascadeFixed ε D) * ((1 + ε : ℝ) ^ n)⁻¹) := by
    filter_upwards with n
    rw [cascadeIter_sub_fixed hε, div_eq_mul_inv]
  have hsub : Tendsto (fun n : ℕ => cascadeIter ε D n σ - cascadeFixed ε D) atTop (nhds 0) :=
    Tendsto.congr' hev.symm hmul
  have hconst : Tendsto (fun _ : ℕ => cascadeFixed ε D) atTop (nhds (cascadeFixed ε D)) :=
    tendsto_const_nhds
  have hsum : Tendsto
      (fun n : ℕ => (cascadeIter ε D n σ - cascadeFixed ε D) + cascadeFixed ε D)
      atTop (nhds (0 + cascadeFixed ε D)) := hsub.add hconst
  simpa using hsum

end

end CausModel
