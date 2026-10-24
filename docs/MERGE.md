# Unified merge record (2026-10-19)

This record documents a **structural merge**, not a new mathematical claim. It
explains why the repository contains 56 main files rather than the historical
53/54/55 numbers.

## Before the merge

Three Lean trees existed with different scopes:

| Tree | Scope | Historical count |
|---|---|---|
| canonical | paper B development body | 417 / 77 / 53 |
| authority | canonical + two identity files | 434 / 84 / 55 |
| public copy | canonical + A module | 450 / 84 / 54 |

The trees had a two-way split: the authority tree had newer identity files and a
newer `BoundaryProgramme`; the canonical tree had the de-duplicated
`DimensionAlgebra` and a newer superseded-header note. No single tree reproduced
the whole body.

## What was done

1. Union: 53 canonical B files + `BoundaryReportIdentity` + `ReportCountermodels`
   + `BoundaryTheory` = 56 files.
2. De-duplication: `DimensionAlgebra` uses the canonical version without the
   duplicate local `sigmaStar`; the two old `sigma_bridge` variants and the old
   `DimensionAlgebra` variant are archived.
3. Single entry: `BoundaryProgramme.lean` imports all 56 files; the only source
   edit is the added `import ReportCountermodels` plus a header note.
4. Build: `scripts/build.py` resolves local imports, compiles in topological
   order, and checks entry coverage.
5. Counts: `scripts/counts.py` produces four scopes; `docs/counts.json` is the
   expected value and `--check` fails on drift.
6. Evidence: `scripts/verify_all.sh` chains build, 0-sorry/axiom, counts, claim
   index, static audit, axiom dependencies, numerical reproduction, and the
   cross-project check.

## Resulting counts

```
53 canonical                417 / 77 / 53
+ BoundaryReportIdentity     13 /  5 /  1
+ ReportCountermodels         4 /  1 /  1
= B line full               434 / 83 / 55
+ BoundaryTheory             33 /  7 /  1
= unified audit body        467 / 90 / 56
```

The B-line full definition count is 83 (not the historical 84) because the
unified tree does not retain the duplicate local `sigmaStar` definition.

## What this record does not claim

- It does not claim new theorems or definitions.
- It does not claim that the historical trees were wrong; they were snapshots
  with different scopes.
- It does not replace the paper's claim index; see `docs/claims.yaml`.

The full local archive and historical notes are kept outside the public Git tree.
