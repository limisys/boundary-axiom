import Mathlib
import ReportIdentityCore

set_option linter.unusedVariables false

namespace ReportCountermodelsCore

open LocusVsBoundary
open ReportIdentityCore

variable {Ω : Type*}

/-- An explicit non-Moore report family on `Fin 2`: all subsets except the empty set. -/
def RnoEmpty : Report (Fin 2) := Set.univ \ {∅}

theorem RnoEmpty_not_moore : ¬ Moore RnoEmpty := by
  intro h
  have h0 : ({0} : Set (Fin 2)) ∈ RnoEmpty :=
    ⟨Set.mem_univ _, by intro hc; exact absurd (hc ▸ Set.mem_singleton (0 : Fin 2)) (by simp)⟩
  have h1 : ({1} : Set (Fin 2)) ∈ RnoEmpty :=
    ⟨Set.mem_univ _, by intro hc; exact absurd (hc ▸ Set.mem_singleton (1 : Fin 2)) (by simp)⟩
  have hF : ({({0} : Set (Fin 2)), ({1} : Set (Fin 2))} : Set (Set (Fin 2))) ⊆ RnoEmpty := by
    intro T hT
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hT
    rcases hT with rfl | rfl
    · exact h0
    · exact h1
  have hinter : (⋂₀ ({({0} : Set (Fin 2)), ({1} : Set (Fin 2))} : Set (Set (Fin 2)))) ∈ RnoEmpty :=
    h _ hF
  have hempty : (∅ : Set (Fin 2)) ∈ RnoEmpty := by simpa using hinter
  exact absurd (Set.mem_sdiff _ |>.mp hempty).2 (by simp)

/-- `c_R` judges the empty set closed, although the empty set is not reported. -/
theorem RnoEmpty_closed_empty : repClosed RnoEmpty (∅ : Set (Fin 2)) = ∅ := by
  have hmem0 : ({0} : Set (Fin 2)) ∈ RnoEmpty :=
    ⟨Set.mem_univ _, by intro hc; exact absurd (hc ▸ Set.mem_singleton (0 : Fin 2)) (by simp)⟩
  have hmem1 : ({1} : Set (Fin 2)) ∈ RnoEmpty :=
    ⟨Set.mem_univ _, by intro hc; exact absurd (hc ▸ Set.mem_singleton (1 : Fin 2)) (by simp)⟩
  apply le_antisymm
  · intro x hx
    have hx0 : x ∈ ({0} : Set (Fin 2)) :=
      Set.mem_sInter.mp hx ({0} : Set (Fin 2))
        (show (∅ : Set (Fin 2)) ⊆ ({0} : Set (Fin 2)) ∧ ({0} : Set (Fin 2)) ∈ RnoEmpty from
          ⟨by intro y hy; exact absurd hy (by simp), hmem0⟩)
    have hx1 : x ∈ ({1} : Set (Fin 2)) :=
      Set.mem_sInter.mp hx ({1} : Set (Fin 2))
        (show (∅ : Set (Fin 2)) ⊆ ({1} : Set (Fin 2)) ∧ ({1} : Set (Fin 2)) ∈ RnoEmpty from
          ⟨by intro y hy; exact absurd hy (by simp), hmem1⟩)
    rw [Set.mem_singleton_iff] at hx0 hx1
    exact absurd (hx0 ▸ hx1) (by decide)
  · exact subset_repClosed _ ∅

/-- The corrected negative control: Moore-ness cannot be dropped. -/
theorem nonMoore_not_canonical :
    ∃ (R : Report (Fin 2)), ¬ Moore R ∧ R ≠ Fix (repClosed R) := by
  refine ⟨RnoEmpty, RnoEmpty_not_moore, ?_⟩
  intro h
  have hmem : (∅ : Set (Fin 2)) ∈ RnoEmpty := by
    rw [h]
    exact RnoEmpty_closed_empty
  exact absurd (Set.mem_sdiff _ |>.mp hmem).2 (by simp)

end ReportCountermodelsCore
