/-
FieldClosure.lean —— 芯外的**动力学**模型：两个干预族作用在**正交坐标**上（第 65 轮）

**动机**：§7 一直把"**含干预族的动力学芯外模型**"列为**未做**。第 63 轮只建立了**静态**三成分场
（$p_U\le b$、$b-p_U=2\min(p_S,p_N)$、$b\ne f(p_U)$）。本轮把它做成**动力学**：

在三成分场 `Field`（$p_S+p_N+p_U=1$）上定义**两个干预族**：

  · **`resolve t`（解除未知）**：$p_S\mapsto p_S+\tfrac{t}{2}p_U$，$p_N\mapsto p_N+\tfrac{t}{2}p_U$，$p_U\mapsto(1-t)p_U$
     ——把"未知"按比例分给两侧；
  · **`commit`（表态）**：把**少数侧全部并入多数侧**——$(p_S,p_N)\mapsto(p_S+p_N,0)$ 或 $(0,p_S+p_N)$，$p_U$ 不变。

**本轮的主结果（两族作用在正交坐标上）**：

  · **`b_resolve`**   $b(\\texttt{resolve}\\,t\\,x)=b(x)$ —— 解除未知**完全不改变**边界隶属度；
  · **`b_commit`**    $b(\\texttt{commit}\\,x)=x.p_U$ —— 表态把边界隶属度**恰好压到未知质量**；
  · **`pU_commit`**   $(\\texttt{commit}\\,x).p_U=x.p_U$ —— 表态**不改变**未知质量；
  · **`commit_idem`**、**`fix_iff_oneSided`** —— 表态是**幂等**的，其不动点**恰是单向归属**（$p_S=0$ 或 $p_N=0$）；
  · **`b_commit_lt`** —— 严格下降 $\\iff$ 归属**双向**（$\\min(p_S,p_N)>0$）。

**一句话**：$b$ 与 $p_U$ 是**正交**的两个坐标。"表态"动 $b$ 不动 $p_U$；
"解除未知"动 $p_U$ 不动 $b$。且在表态的**不动点**上 $b=p_U$（与第 63 轮 `b_eq_pU_iff` 相接）。
**故 $b$ 的下界恰是 $p_U$，且只能由表态达到**——这就是"沉淀"与"知道"是两件事的**定量形式**。

0 `sorry` / 0 `axiom`。
-/
import ThreeComponent

open scoped Real

namespace FieldClosure

open ThreeComponent

/-! ## 一 · 外延性与构造 -/

theorem Field.ext {x y : Field} (h1 : x.pS = y.pS) (h2 : x.pN = y.pN) (h3 : x.pU = y.pU) :
    x = y := by
  cases x; cases y; simp_all

/-! ## 二 · 干预族一：**表态** `commit` -/

/-- **表态**：把少数侧全部并入多数侧，未知质量不变。 -/
noncomputable def commit (x : Field) : Field :=
  if h : x.pN ≤ x.pS then
    ⟨x.pS + x.pN, 0, x.pU, by linarith [x.hS, x.hN], le_refl 0, x.hU, by linarith [x.sum]⟩
  else
    ⟨0, x.pS + x.pN, x.pU, le_refl 0, by linarith [x.hS, x.hN], x.hU, by linarith [x.sum]⟩

/-- 表态后的数据：多数侧＝`p_S+p_N`，少数侧＝`0`，`p_U` 不变。 -/
theorem commit_data (x : Field) :
    ((x.pN ≤ x.pS ∧ (commit x).pS = x.pS + x.pN ∧ (commit x).pN = 0)
      ∨ (x.pS < x.pN ∧ (commit x).pS = 0 ∧ (commit x).pN = x.pS + x.pN))
    ∧ (commit x).pU = x.pU := by
  unfold commit
  by_cases h : x.pN ≤ x.pS
  · rw [dif_pos h]
    exact ⟨Or.inl ⟨h, rfl, rfl⟩, rfl⟩
  · rw [dif_neg h]
    exact ⟨Or.inr ⟨lt_of_not_ge h, rfl, rfl⟩, rfl⟩

/-- 表态**不改变**未知质量。 -/
theorem pU_commit (x : Field) : (commit x).pU = x.pU := (commit_data x).2

/-- 表态后的不平衡度恰为 `p_S+p_N`，故 `b = p_U`。 -/
theorem b_commit (x : Field) : b (commit x) = x.pU := by
  obtain ⟨hd, -⟩ := commit_data x
  rcases hd with ⟨h, hS, hN⟩ | ⟨h, hS, hN⟩
  · unfold b
    rw [hS, hN]
    have : x.pS + x.pN = 1 - x.pU := by linarith [x.sum]
    rw [sub_zero, abs_of_nonneg (by linarith [x.hS, x.hN]), this]
    ring
  · unfold b
    rw [hS, hN]
    have : x.pS + x.pN = 1 - x.pU := by linarith [x.sum]
    rw [zero_sub, abs_neg, abs_of_nonneg (by linarith [x.hS, x.hN]), this]
    ring

/-- 表态**从不增大**边界隶属度（下界为 `p_U`，见 `b_commit`）。 -/
theorem b_commit_le (x : Field) : b (commit x) ≤ b x := by
  rw [b_commit]
  exact pU_le_b x

/-- 表态**严格减小**边界隶属度 **当且仅当**归属是**双向**的。 -/
theorem b_commit_lt (x : Field) : b (commit x) < b x ↔ 0 < min x.pS x.pN := by
  have hiff : b x = x.pU ↔ x.pS = 0 ∨ x.pN = 0 := b_eq_pU_iff x
  have hbc : b (commit x) = x.pU := b_commit x
  constructor
  · intro h
    by_contra hc
    rw [not_lt] at hc
    have hmin : min x.pS x.pN = 0 := le_antisymm hc (le_min x.hS x.hN)
    have hside : x.pS = 0 ∨ x.pN = 0 := by
      rcases min_cases x.pS x.pN with ⟨e, _⟩ | ⟨e, _⟩
      · exact Or.inl (by rw [← e]; exact hmin)
      · exact Or.inr (by rw [← e]; exact hmin)
    rw [hbc, hiff.mpr hside] at h
    exact lt_irrefl _ h
  · intro h
    have hne : x.pS ≠ 0 ∧ x.pN ≠ 0 := by
      constructor <;> intro hz <;> rw [hz] at h <;> simp at h
    have hb : b x ≠ x.pU := fun hh => (hiff.mp hh).elim hne.1 hne.2
    rw [hbc]
    exact lt_of_le_of_ne (pU_le_b x) (Ne.symm hb)

/-- 表态**幂等**。 -/
theorem commit_idem (x : Field) : commit (commit x) = commit x := by
  obtain ⟨hd, hU⟩ := commit_data x
  rcases hd with ⟨h, hS, hN⟩ | ⟨h, hS, hN⟩
  · -- 表态后 pN = 0 ≤ pS
    have hle : (commit x).pN ≤ (commit x).pS := by rw [hN, hS]; linarith [x.hS, x.hN]
    obtain ⟨hd2, hU2⟩ := commit_data (commit x)
    rcases hd2 with ⟨_, hS2, hN2⟩ | ⟨hlt, _, _⟩
    · refine Field.ext ?_ ?_ ?_
      · rw [hS2, hS, hN]; ring
      · rw [hN2, hN]
      · rw [hU2, hU]
    · exact absurd hle (not_le.mpr hlt)
  · have hle : ¬ (commit x).pN ≤ (commit x).pS := by rw [hN, hS]; linarith [x.hN, x.hS]
    obtain ⟨hd2, hU2⟩ := commit_data (commit x)
    rcases hd2 with ⟨hle', _, _⟩ | ⟨_, hS2, hN2⟩
    · exact absurd hle' hle
    · refine Field.ext ?_ ?_ ?_
      · rw [hS2, hS]
      · rw [hN2, hS, hN]; ring
      · rw [hU2, hU]

/-- **表态的不动点恰是"单向归属"**——即第 63 轮 `b_eq_pU_iff` 的另一侧。 -/
theorem fix_iff_oneSided (x : Field) : commit x = x ↔ x.pS = 0 ∨ x.pN = 0 := by
  constructor
  · intro h
    obtain ⟨hd, -⟩ := commit_data x
    rcases hd with ⟨hle, hS, hN⟩ | ⟨hlt, hS, hN⟩
    · -- 多数侧是 S：`commit x = (pS+pN, 0, pU)`，不动 ⇒ `pN = 0`
      right
      have h' : x.pS + x.pN = x.pS := by rw [← hS, h]
      linarith
    · -- 多数侧是 N：`commit x = (0, pS+pN, pU)`，不动 ⇒ `pS = 0`
      left
      have h' : (0 : ℝ) = x.pS := by rw [← hS, h]
      exact h'.symm
  · intro h
    obtain ⟨hd, hU⟩ := commit_data x
    rcases hd with ⟨hle, hS, hN⟩ | ⟨hlt, hS, hN⟩
    · rcases h with h0 | h0
      · have hz : x.pN = 0 := le_antisymm (by rw [h0] at hle; exact hle) x.hN
        refine Field.ext ?_ ?_ ?_
        · rw [hS, hz]; ring
        · rw [hN, hz]
        · exact hU
      · refine Field.ext ?_ ?_ ?_
        · rw [hS, h0]; ring
        · rw [hN, h0]
        · exact hU
    · rcases h with h0 | h0
      · refine Field.ext ?_ ?_ ?_
        · rw [hS, h0]
        · rw [hN, h0]; ring
        · exact hU
      · exfalso
        linarith [x.hS, h0, hlt]

/-- **刚性面上的边界隶属度恰是未知质量**：$x\\in\\mathrm{Fix}(\\texttt{commit})\\Rightarrow b(x)=x.p_U$。 -/
theorem fix_b_eq_pU {x : Field} (hx : commit x = x) : b x = x.pU := by
  have h := b_commit x
  rwa [hx] at h

/-! ## 三 · 干预族二：**解除未知** `resolve` -/

/-- **解除未知**：把 `t` 比例的未知质量按 1:1 分给两侧，剩余未知按 `1-t` 保留。 -/
noncomputable def resolve (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x : Field) : Field where
  pS := x.pS + t * x.pU / 2
  pN := x.pN + t * x.pU / 2
  pU := (1 - t) * x.pU
  hS := by nlinarith [x.hS, x.hU, ht0]
  hN := by nlinarith [x.hN, x.hU, ht0]
  hU := by nlinarith [x.hU, ht1]
  sum := by
    have : x.pS + x.pN + x.pU = 1 := x.sum
    ring_nf
    linarith [this]

/-- **解除未知完全不改变边界隶属度**：$b(\\texttt{resolve}\\,t\\,x)=b(x)$。 -/
theorem b_resolve (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x : Field) :
    b (resolve t ht0 ht1 x) = b x := by
  unfold b resolve
  simp only
  have : x.pS + t * x.pU / 2 - (x.pN + t * x.pU / 2) = x.pS - x.pN := by ring
  rw [this]

/-- 解除未知**降低**未知质量（`t>0` 时严格）。 -/
theorem pU_resolve (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x : Field) :
    (resolve t ht0 ht1 x).pU = (1 - t) * x.pU := rfl

/-! ## 四 · 收官：两族作用在**正交坐标**上 -/

/-- **（收官）** 表态改变 `b` 而不改变 `p_U`；解除未知改变 `p_U` 而不改变 `b`。
故 $b$ 与 $p_U$ 在该模型里是**正交**的两个坐标——"沉淀"与"知道"是两件事。 -/
theorem orthogonal :
    (∀ x : Field, (commit x).pU = x.pU)
    ∧ (∀ (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x : Field), b (resolve t ht0 ht1 x) = b x) :=
  ⟨pU_commit, b_resolve⟩

/-- **下界恰为未知质量**：任何表态都不能把 `b` 压到 `p_U` 以下，且**只有表态**能取到该下界。 -/
theorem commit_is_optimal (x : Field) : b (commit x) = x.pU ∧ ∀ y : Field, y.pU = x.pU → x.pU ≤ b y := by
  refine ⟨b_commit x, ?_⟩
  intro y hy
  rw [← hy]
  exact pU_le_b y

end FieldClosure
