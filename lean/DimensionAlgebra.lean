/-
DimensionAlgebra.lean —— 量纲层的形式化与「两层分述」（第 56 轮）

对应件：`02-学术侦察/边界势量纲钻研.md` §二（显式量纲构造）与 §五.2：
  "**区分两个命题层级**（直接回应 §3.5 自审警告）：
     一般参数层：`σ* = π²α/(3C₀)`（量纲自洽成立）；
     规范参数层：数值 `=1`（解码选择）。
     **机器证明（P4）须在两层级分别陈述，禁止混用。**"
本文件把该要求**机检化**：
  · 量纲 = 基量指数对 (X, E) 上的阿贝尔群（`Dim`）；
  · 值层各量的量纲指派 + `V` 两项同量纲的**可加性方程**；
  · **D1** 该方程**唯一决定** `[c₀]`（原文 §二"可加条件"：`c₀` 与 `α` 不独立）；
  · **D2/D2′** 代入 `[κ]=X⁻¹`、`[C_F]=0` ⇒ `[c₀]=[α]+2X`、`[V]=[α]+X`；
  · **D3/D3′** 规范层**丢掉**一般层那条关系（而非"解除约束"——见 §三 的自纠注）；
  · **D4/D4′** `σ*=π²α/(3C₀)` **推不出** `σ*=1`——"禁止混用"的机检形式。

说明：本文件**不选定**物理锚定（nat／认知距离／其他），`X` 只作**抽象基量**；
高总未拍板前不作任何预测。
-/

import BoundaryTheory

open BoundaryTheory

namespace DimensionAlgebra

/-! ## 一 · 量纲群：基量指数对 -/

/-- 量纲 = 基量 `X`（归属轴单位）与 `E`（能量）的指数对。 -/
structure Dim where
  x : ℤ
  e : ℤ
  deriving DecidableEq, Repr

namespace Dim

/-- 量纲相乘 = 指数相加。 -/
def add (a b : Dim) : Dim := ⟨a.x + b.x, a.e + b.e⟩
/-- 量纲取逆 = 指数取负。 -/
def neg (a : Dim) : Dim := ⟨-a.x, -a.e⟩
/-- 整数幂。 -/
def smul (n : ℤ) (a : Dim) : Dim := ⟨n * a.x, n * a.e⟩
/-- 无量纲。 -/
def one : Dim := ⟨0, 0⟩

@[simp] theorem add_x (a b : Dim) : (add a b).x = a.x + b.x := rfl
@[simp] theorem add_e (a b : Dim) : (add a b).e = a.e + b.e := rfl
@[simp] theorem neg_x (a : Dim) : (neg a).x = -a.x := rfl
@[simp] theorem neg_e (a : Dim) : (neg a).e = -a.e := rfl
@[simp] theorem smul_x (n : ℤ) (a : Dim) : (smul n a).x = n * a.x := rfl
@[simp] theorem smul_e (n : ℤ) (a : Dim) : (smul n a).e = n * a.e := rfl
@[simp] theorem one_x : (one).x = 0 := rfl
@[simp] theorem one_e : (one).e = 0 := rfl

end Dim

/-! ## 二 · 值层的量纲指派与可加性方程 -/

/-- 基量 `X`（归属轴单位）。 -/
def dimX : Dim := ⟨1, 0⟩
/-- `κ` = 每单位轴的锐度 ⇒ `[κ] = X⁻¹`（sigmoid 的指数变元须无量纲）。 -/
def dimKappa : Dim := ⟨-1, 0⟩
/-- `C_F = ∫ h(F z) dz`：`h` 与 `F` 皆无量纲 ⇒ `[C_F] = 0`。 -/
def dimCF : Dim := Dim.one

/-- **可加性方程**：`V = c₀κ + αC_F/κ` 两项必须同量纲。写成分量形式（两基量各自平衡）：
左项 `[c₀]+[κ]`，右项 `[α]+[C_F]−[κ]`。 -/
def Additive (ec0 eα eCF eκ : Dim) : Prop :=
  ec0.x + eκ.x = eα.x + eCF.x - eκ.x ∧ ec0.e + eκ.e = eα.e + eCF.e - eκ.e

/-- **D1**：可加性方程**唯一决定** `[c₀]`——即"`c₀` 与 `α` 不是独立量纲"。 -/
theorem c0_dim_unique {ec0 ec0' eα eCF eκ : Dim}
    (h : Additive ec0 eα eCF eκ) (h' : Additive ec0' eα eCF eκ) : ec0 = ec0' := by
  obtain ⟨hx1, he1⟩ := h
  obtain ⟨hx2, he2⟩ := h'
  have h1 : ec0.x = ec0'.x := by omega
  have h2 : ec0.e = ec0'.e := by omega
  cases ec0; cases ec0'; simp_all

/-- **D1 的解**：`[c₀] = [α] + [C_F] − 2[κ]`。 -/
theorem c0_dim_solution {ec0 eα eCF eκ : Dim} (h : Additive ec0 eα eCF eκ) :
    ec0 = Dim.add (Dim.add eα eCF) (Dim.neg (Dim.smul 2 eκ)) := by
  obtain ⟨cx, ce⟩ := ec0
  obtain ⟨ax, ae⟩ := eα
  obtain ⟨fx, fe⟩ := eCF
  obtain ⟨kx, ke⟩ := eκ
  obtain ⟨hx, he⟩ := h
  simp only [Dim.add, Dim.neg, Dim.smul] at hx he
  rw [Dim.mk.injEq]
  simp only [Dim.add, Dim.neg, Dim.smul]
  exact ⟨by omega, by omega⟩

/-- **D2**：代入 `[κ]=X⁻¹`、`[C_F]=0` ⇒ `[c₀] = [α] + 2·X`（原文 `[c₀]=[α]·X²`）。 -/
theorem c0_dim_is_alpha_plus_2X {ec0 eα : Dim} (h : Additive ec0 eα dimCF dimKappa) :
    ec0 = Dim.add eα (Dim.smul 2 dimX) := by
  obtain ⟨cx, ce⟩ := ec0
  obtain ⟨ax, ae⟩ := eα
  obtain ⟨hx, he⟩ := h
  have hx' : cx + (-1) = ax + 0 - (-1) := by simpa [dimCF, dimKappa, Dim.add] using hx
  have he' : ce + 0 = ae + 0 - 0 := by simpa [dimCF, dimKappa, Dim.add] using he
  rw [Dim.mk.injEq]
  constructor <;> simp only [Dim.add, Dim.smul, dimX] <;> omega

/-- **D2′**：相应地 `[V] = [c₀]+[κ] = [α]+X`（原文 `[V]=[α]·X`）。 -/
theorem V_dim_is_alpha_plus_X {ec0 eα : Dim} (h : Additive ec0 eα dimCF dimKappa) :
    Dim.add ec0 dimKappa = Dim.add eα dimX := by
  rw [c0_dim_is_alpha_plus_2X h]
  rw [Dim.mk.injEq]
  constructor <;> simp only [Dim.add, Dim.smul, dimKappa, dimX] <;> ring

/-! ## 三 · D3：规范层**丢掉了**一般层那条确定关系（这才是"量纲断层"）

> ⚠️ **自纠**：本文件初稿把 D3 写成"规范层使约束消失（约束不唯一）"——**那是错的**。
> 事实相反：若其余量都无量纲，可加性方程**反而把 `[c₀]` 逼成 0**（D3）。
> 真正的内容是：**规范层表达不出**一般层那条 `[c₀]=[α]·X²` 的关系——信息被抹平，而非约束被解除（D3′）。 -/

/-- 规范层的平凡解：全部无量纲时可加性方程成立。 -/
theorem normalisation_trivial : Additive Dim.one Dim.one Dim.one Dim.one := by
  constructor <;> simp [Dim.one]

/-- **D3**：规范层（其余量全无量纲）中，可加性方程**唯一地把 `[c₀]` 逼成无量纲**。 -/
theorem normalisation_forces_dimensionless (ec0 : Dim) :
    Additive ec0 Dim.one Dim.one Dim.one ↔ ec0 = Dim.one := by
  constructor
  · intro h
    obtain ⟨hx, he⟩ := h
    simp only [Dim.one] at hx he
    have h1 : ec0.x = 0 := by omega
    have h2 : ec0.e = 0 := by omega
    cases ec0
    rw [Dim.mk.injEq]
    exact ⟨by simpa using h1, by simpa using h2⟩
  · intro h
    rw [h]
    exact normalisation_trivial

/-- **D3′**：一般层**确有非平凡解**（`[c₀] = 3X ≠ 0`），而规范层把它们全压成 0
⇒ 规范化不是保信息的重述，而是**丢弃**。 -/
theorem general_layer_nontrivial_solution :
    Additive (Dim.smul 3 dimX) dimX dimCF dimKappa ∧ (Dim.smul 3 dimX) ≠ Dim.one := by
  constructor
  · constructor <;> simp [dimX, dimCF, dimKappa, Dim.smul]
  · intro h
    have hx := congrArg Dim.x h
    simp [dimX, Dim.smul, Dim.one] at hx

/-! ## 四 · D4：一般参数层推不出规范层的数值 `σ* = 1` -/

/- 一般参数层的张力：`σ* = π²α/(3C₀)`（量纲自洽；见 D2′）。
**第 59 轮去重**：此处原有一个本地 `def sigmaStar`，与冻结值层 `BoundaryTheory.sigmaStar` **逐字相同**；
现改为 `import BoundaryTheory` + `open BoundaryTheory`，**不再重复声明**。 -/

/-- **D4（负面）**：`σ* = π²α/(3C₀)` **不蕴含** `σ* = 1`。
反例 `α=1, C₀=2` ⇒ `σ* = π²/6 > 1`。 -/
theorem sigmaStar_not_forced_one :
    ¬ (∀ α C₀ : ℝ, 0 < α → 0 < C₀ → sigmaStar α C₀ = 1) := by
  intro h
  have h1 := h 1 2 (by norm_num) (by norm_num)
  have hval : sigmaStar 1 2 = Real.pi ^ 2 / 6 := by
    unfold sigmaStar; norm_num
  rw [hval] at h1
  have h9 : (9 : ℝ) < Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have h6 : Real.pi ^ 2 = 6 := by linarith [h1]
  linarith

/-- **D4′**：规范层那条等式（`π²α = 3C₀`）是**额外条件**，不是从 D2′ 得来的。 -/
theorem sigmaStar_eq_one_iff (α C₀ : ℝ) (hC₀ : C₀ ≠ 0) :
    sigmaStar α C₀ = 1 ↔ Real.pi ^ 2 * α = 3 * C₀ := by
  unfold sigmaStar
  constructor
  · intro h
    field_simp at h
    linarith
  · intro h
    rw [h]
    field_simp

end DimensionAlgebra
