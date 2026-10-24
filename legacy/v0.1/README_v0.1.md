# Boundary Axiom (统一边界公理)

Lean 4 formalization of the **Unified Boundary Axiom** (boundary cognition hypothesis):
three propositions on boundary potential `V(κ) = c₀κ + απ²/(3κ)`, minimal-action boundary
sharpness `κ*`, tension `σ*`, and energy conservation along the equations of motion.

## Version anchor

- **v0.1** (this tree) — propositions κ\*, σ\* and dE/dt≡0 formalized over `Mathlib`.
- Formal statement correspondence: `docs/边界认知假说·边界概念的数学形式.md` §3 (working draft, not yet shipped in this repo).

## Files

| File | Content |
|------|---------|
| `BoundaryTheory.lean` | The three propositions, as Lean 4 theorems (imports `Mathlib`) |
| `VERSION.md` | Version anchor & changelog |
| `docs/ML_SCENARIO_MAPPING.md` | Hypothesis maps of H0–A5 & T1–T5 onto ML scenarios (falsifiable) |

## Build

```sh
leanproject get-mathlib-cache
lean --run BoundaryTheory.lean   # or: lake build if in a Mathlib project
```

(Requires Lean 4 + Mathlib; see leanprover-community for setup.)

## Status

Work in progress. This is a research anchor for citation/derivation, **not** an
endorsed scientific claim. A companion paper is under preparation/submission;
links will be added here on publication.

## License

Apache-2.0 (see `LICENSE`). Mathematics itself is not copyrightable; this grant
covers the formalization code and documents.

Feedback / issues are welcome in this repository.
