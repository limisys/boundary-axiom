# Provenance — v1.1 corrected release

**Upstream corpus** the author's private verified corpus (path intentionally omitted)
**Upstream commit** `dd329e6` (tag `v1.0.0`; 56 files / 467 thm-lem / 90 def; 0 `sorry` / 0 `axiom`)
**Release date** 2026-10-23
**Toolchain** Lean 4.33.0 (`d8b1897…`), Mathlib 4.33.0

## What is copied verbatim

| File | Upstream | Changes |
|---|---|---|
| `lean/LocusVsBoundary.lean` | same | none |
| `lean/ClosureFromInterventions.lean` | same | none |
| `lean/ReportBridge.lean` | same | none |

These three files are dependencies and are unmodified. They total 29 theorems/lemmas and 9 definitions/abstractions.

## What is new in v1.1

| File | Origin | Why |
|---|---|---|
| `lean/ReportIdentityCore.lean` | new proofs; `repClosed` construction follows v1.0 | v1.0's `UpClosed` is degenerate; replaced by `Moore` (arbitrary intersections) |
| `lean/ReportCountermodelsCore.lean` | adapted from v1.0's `ReportCountermodels` | counterexample restated for the corrected condition |
| `lean/ReportIdentity.lean` | new umbrella | single import root |

## What is retained only for audit

`audit/` contains the v1.0 `BoundaryReportIdentity.lean` and `ReportCountermodels.lean`, plus:

- `AUDIT_UpClosed.lean` — an independent, self-contained proof that `UpClosed R ↔ R = Set.univ`;
- `AUDIT_UpClosed.log` — compiler output with axiom dependency.

These files are **not** imported by the v1.1 build and are **not** cited as results. They are kept because the correction is part of the record.

## The defect in one paragraph

v1.0 defined `UpClosed R := (∅ ∈ R) ∧ ∀ S T, S ∈ R → S ⊆ T → T ∈ R`. For any `T`, `∅ ⊆ T`; with `∅ ∈ R` and superset closure, `T ∈ R`. Hence `UpClosed R ↔ R = Set.univ`. Every `UpClosed` family is the full power set, every `c_R` is the identity, and the v1.0 mutual-determination theorem is a tautology. The proof is valid; the antecedent has no content. v1.1 uses `Moore R := ∀ F ⊆ R, ⋂₀ F ∈ R`, which is the exact condition for `R` to be the fixed-point family of a closure operator. The corrected theorem is non-vacuous; the standard nature of the closure-operator/Moore-family correspondence is stated explicitly.

## Build verification (this release)

```
Lean (version 4.33.0, x86_64-unknown-linux-gnu, commit d8b18978322de05a8f3dba51ef03cf5461676c17, Release)
== LocusVsBoundary
== ClosureFromInterventions
== ReportBridge
== ReportIdentityCore
== ReportCountermodelsCore
== ReportIdentity
PASS: 6 modules compiled (0 sorry / 0 axiom).
```

Axiom audit: all load-bearing declarations depend only on `[propext, Classical.choice, Quot.sound]`.

## Scope of the claim

The repository does **not** prove that every autonomous system has a Moore report family, nor that a general transition operator has a unique joint fixed point. It proves a conditional identity and an explicit negative control. The engineering protocol in `03_架构/` is a design, not a deployed system.

## License

Code: Apache-2.0 (`LICENSE`). Documentation: CC BY 4.0 (`LICENSE-docs`).
