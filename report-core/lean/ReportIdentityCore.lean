import Mathlib
import ClosureFromInterventions
import ReportBridge

set_option linter.unusedVariables false

namespace ReportIdentityCore

open LocusVsBoundary
open ClosureFromInterventions

variable {Ω : Type*}

abbrev Report (Ω : Type*) := Set (Set Ω)

/-- A Moore family: closed under arbitrary intersections (including the empty one). -/
def Moore (R : Report Ω) : Prop :=
  ∀ F : Set (Set Ω), F ⊆ R → ⋂₀ F ∈ R

noncomputable def repClosed (R : Report Ω) : Set Ω → Set Ω :=
  fun S => ⋂₀ {T : Set Ω | S ⊆ T ∧ T ∈ R}

theorem repClosed_eq_sInter (R : Report Ω) (S : Set Ω) :
    repClosed R S = ⋂₀ {T : Set Ω | T ∈ R ∧ S ⊆ T} := by
  unfold repClosed
  congr 1
  ext T; exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

theorem subset_repClosed (R : Report Ω) (S : Set Ω) : S ⊆ repClosed R S :=
  fun x hx => Set.mem_sInter.mpr (fun t ht => ht.1 hx)

theorem repClosed_mono (R : Report Ω) : Monotone (repClosed R) :=
  fun S T h x hx => Set.mem_sInter.mpr
    (fun u hu => Set.mem_sInter.mp hx u ⟨h.trans hu.1, hu.2⟩)

theorem repClosed_mem {R : Report Ω} (hR : Moore R) (S : Set Ω) :
    repClosed R S ∈ R :=
  hR {T : Set Ω | S ⊆ T ∧ T ∈ R} (fun T hT => hT.2)

theorem repClosed_idem (R : Report Ω) (S : Set Ω) :
    repClosed R (repClosed R S) = repClosed R S := by
  have hfam : {T : Set Ω | S ⊆ T ∧ T ∈ R} ⊆ {T : Set Ω | repClosed R S ⊆ T ∧ T ∈ R} :=
    fun T hT => ⟨fun _ hy => Set.mem_sInter.mp hy T hT, hT.2⟩
  exact le_antisymm (Set.sInter_subset_sInter hfam) (subset_repClosed R (repClosed R S))

theorem isClosure_repClosed (R : Report Ω) : IsClosure (repClosed R) :=
  ⟨subset_repClosed R, repClosed_mono R, repClosed_idem R⟩

theorem repClosed_eq_self_of_mem {R : Report Ω} {T : Set Ω} (hT : T ∈ R) :
    repClosed R T = T :=
  le_antisymm
    (Set.sInter_subset_of_mem ⟨le_rfl, hT⟩)
    (subset_repClosed R T)

theorem mem_of_repClosed_eq_self {R : Report Ω} (hR : Moore R) {T : Set Ω}
    (h : repClosed R T = T) : T ∈ R := by
  rw [← h]
  exact repClosed_mem hR T

theorem repClosed_eq_self_iff {R : Report Ω} (hR : Moore R) {T : Set Ω} :
    repClosed R T = T ↔ T ∈ R :=
  ⟨mem_of_repClosed_eq_self hR, repClosed_eq_self_of_mem⟩

theorem rep_eq_iff_closureOperator_eq {R R' : Report Ω}
    (hR : Moore R) (hR' : Moore R') :
    repClosed R = repClosed R' ↔ R = R' := by
  constructor
  · intro h
    ext T
    exact ⟨fun hT => by
             have h1 : repClosed R T = T := repClosed_eq_self_of_mem hT
             exact (repClosed_eq_self_iff hR').mp (by rw [← h]; exact h1),
           fun hT => by
             have h1 : repClosed R' T = T := repClosed_eq_self_of_mem hT
             exact (repClosed_eq_self_iff hR).mp (by rw [h]; exact h1)⟩
  · intro h; rw [h]

theorem report_eq_fix_iff {I : Set (Ω → Ω)} {R : Report Ω} (hR : Moore R) :
    R = {T : Set Ω | Inv I T} ↔ repClosed R = clos I := by
  constructor
  · intro h
    funext S
    have hmem : clos I S ∈ R := by rw [h]; exact inv_clos I S
    apply le_antisymm
    · exact Set.sInter_subset_of_mem (show S ⊆ clos I S ∧ clos I S ∈ R from ⟨subset_clos I S, hmem⟩)
    · intro x hx
      exact Set.mem_sInter.mpr (fun T hT =>
        clos_subset hT.1 (by
          have hTR : T ∈ R := hT.2
          rw [h] at hTR
          exact hTR) hx)
  · intro h
    ext T
    constructor
    · intro hT
      have hfix : repClosed R T = T := repClosed_eq_self_of_mem hT
      have hcl : clos I T = T := by rw [← h]; exact hfix
      rw [← hcl]
      exact inv_clos I T
    · intro hT
      have hc : clos I T = T := le_antisymm (clos_subset le_rfl hT) (subset_clos I T)
      have hfix : repClosed R T = T := by rw [h]; exact hc
      exact (repClosed_eq_self_iff hR).mp hfix

/-- Every closure operator's fixed-point family is a Moore family. -/
theorem fix_moore {c : Set Ω → Set Ω} (hc : IsClosure c) : Moore (Fix c) := by
  intro F hF
  show c (⋂₀ F) = ⋂₀ F
  apply le_antisymm
  · intro x hx
    exact Set.mem_sInter.mpr (fun T hT => by
      have hTF : T ∈ Fix c := hF hT
      have hsub : ⋂₀ F ⊆ T := Set.sInter_subset_of_mem hT
      have hmono : c (⋂₀ F) ⊆ c T := hc.2.1 hsub
      have hxT : x ∈ c T := hmono hx
      rwa [show c T = T from hTF] at hxT)
  · exact hc.1 (⋂₀ F)

/-- Moore families are exactly fixed-point families of closure operators. -/
theorem moore_iff_exists_closure (R : Report Ω) :
    Moore R ↔ ∃ c : Set Ω → Set Ω, IsClosure c ∧ R = Fix c := by
  constructor
  · intro hR
    refine ⟨repClosed R, isClosure_repClosed R, ?_⟩
    ext T
    exact ⟨fun hT => repClosed_eq_self_of_mem hT,
           fun hT => (repClosed_eq_self_iff hR).mp hT⟩
  · rintro ⟨c, hc, rfl⟩
    exact fix_moore hc

end ReportIdentityCore
