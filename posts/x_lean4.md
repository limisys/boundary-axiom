# X thread — Lean 4

**Audience:** Lean/Mathlib, formal verification.
**Angle:** a small, auditable core with an explicit negative control and a
correction history.

---

**1/**
Lean 4 release: a report-identity core.

6 modules · 45 theorems/lemmas · 13 definitions · 0 sorry · no custom axioms.
Load-bearing declarations depend only on [propext, Classical.choice, Quot.sound].

**2/**
Main construction:

c_R(S) = ⋂ { T : S ⊆ T, T ∈ R }.

`isClosure_repClosed`: c_R is a closure operator for any R.
`rep_eq_iff_closureOperator_eq`: on Moore families, c_R determines R and vice
versa.

**3/**
`moore_iff_exists_closure`: Moore R ↔ ∃ c, IsClosure c ∧ R = Fix c.

Standard correspondence; the contribution is the operationalization, the
negative control, and the gate — not new math.

**4/**
The correction is part of the release:

v1.0 used `UpClosed` (∅ ∈ R, superset-closed). In Lean that forces
`R = Set.univ`, so v1.0's mutual determination is a tautology.

v1.1 uses Moore. The old files are under `audit/`, not imported.

**5/**
Negative control:

`nonMoore_not_canonical`: ∃ R, ¬ Moore R ∧ R ≠ Fix(repClosed R).

Witness: P(Fin 2) ∖ {∅}. The Moore precondition cannot be deleted.

**6/**
Build: Lean 4.33.0, Mathlib 4.33.0. Offline script and Lake path both documented.
The full corpus is 56 files / 467 / 90; this core is 6 / 45 / 13.

**7/**
Proof review welcome — especially the v1.1 Moore statements and the audit of the
v1.0 degeneration.

Code: github.com/limisys/boundary-axiom
Tech: limisys.github.io/boundary-axiom/technical.html

---

**Posting notes:** use `#Lean4 #Mathlib #FormalVerification`; attach OG card; if
someone asks for `#print axioms`, point to `docs/PUBLIC_EVIDENCE.md` and the
offline build script.
