# BoundaryTheory — A-module (group 1) + B-line canonical subset (group 2)

This package is the published Lean layer of the Boundary Theory programme. It is
released in three groups; groups 1 and 2 are published here, group 3 is pending.

## The three groups

| Group | Content | Counts (files / theorems+lemmas / definitions) | Status |
|-------|---------|------------------------------------------------|--------|
| 1 | A-module `BoundaryTheory.lean` | 1 / 33 / 7 | **published** |
| 2 | B-line canonical subset (paper B formal spine) | 53 / 417 / 77 | **published** |
| 3 | Unified audit body (B + bridge) | 56 / 467 / 90 | pending — to be published only after the author's manual reproduction of all machine-checked results and written notice |

The group-2 counts (53 / 417 / 77) are the canonical subset; the full B line is
55 / 434 / 83. Group 3 (the unified audit body) is not included in this package.

## What is in this release

**Group 1** — `code/BoundaryTheory.lean` (928 lines, 33 theorems + lemmas,
7 definitions, 0 sorry; Lean 4.33.0 + Mathlib v4.33.0).

**Group 2** — 53 Lean files under `code/b/` (417 theorems + lemmas, 77
definitions), the canonical subset of the paper-B formal spine. The full set is
listed in `code/b/FILES.txt`; a download bundle is `code/b.tar.gz`.

## Build

```sh
cd code
lake build
```

This requires Lean 4.33.0 and the corresponding Mathlib; `lake-manifest.json`
and `lakefile.toml` / `lean-toolchain` are included so the exact dependency set
is reproducible.

## Files & integrity

```sh
sha256sum -c SHA256SUMS
```

## License & provenance

Licensed under the **Apache License, Version 2.0** — see `LICENSE`.

Copyright 2026 Xueqiang Gao (高学强), ORCID
https://orcid.org/0009-0008-3821-3454.

**Original publication source: caseos.cn/research — https://caseos.cn/research/**

First public release 2026-10-09; formal publication 2026-10-20.

Attribution headers were added to the source files at publication; proof bodies
are unchanged. Three comment appellations in the B-line sources were neutralised
(no proof content was changed). See `NOTICE`.

## Scope

This release contains groups 1 and 2. The corresponding papers are not published
here. Group 3 (the unified audit body) will be published only after the author's
manual reproduction of all machine-checked results and written notice.
