# Audit — the v1.0 condition and why it was replaced

This directory is **not** imported by the v1.1 build. It exists so the correction
can be checked rather than taken on trust.

| File | What it is |
|---|---|
| `BoundaryReportIdentity.lean` | v1.0 module, copied verbatim from upstream commit `dd329e6` |
| `ReportCountermodels.lean` | v1.0 negative control, copied verbatim |
| `AUDIT_UpClosed.lean` | independent proof: `UpClosed R ↔ R = Set.univ` |
| `AUDIT_UpClosed.log` | compiler output with axiom dependency |
| `AUDIT_UpClosed.md` | explanation and reproduction |

## The finding

v1.0's `UpClosed R` is `(∅ ∈ R) ∧ (S ∈ R → S ⊆ T → T ∈ R)`. For any `T`, `∅ ⊆ T`,
so `T ∈ R`. Hence `UpClosed R ↔ R = Set.univ`. The v1.0 "mutual determination"
theorem is therefore a tautology: all admissible families are the full power set,
and all generated operators are the identity.

The proof was valid. The antecedent had no content. Lean does not warn about this.

## The correction

v1.1 uses `Moore R := ∀ F ⊆ R, ⋂₀ F ∈ R`, which is exactly the condition for `R`
to be the fixed-point family of a closure operator. The corrected statements are in
`../lean/ReportIdentityCore.lean`, with the counterexample in
`../lean/ReportCountermodelsCore.lean`.

## Reproduce

```bash
cd audit
ELAN_HOME=/path/to/lean-home lean AUDIT_UpClosed.lean
```

Expected:

```
'Audit.upClosed_iff_eq_univ' depends on axioms: [propext, Quot.sound]
```
