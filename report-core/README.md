# Report-identity core (v1.1)

This directory is the six-module report-identity core extracted from the full
`boundary-axiom` corpus. It is the minimal Lean development behind the public
technical edition.

**Counts:** 6 modules, 45 theorems/lemmas, 13 definitions; 0 `sorry`, no custom
axioms. The load-bearing declarations depend only on
`[propext, Classical.choice, Quot.sound]`.

**Entry:** `lean/ReportIdentity.lean`.

**Result:** on Moore report families, the report family `R` and the closure
operator `c_R` determine each other; `R = Fix(c_I) ↔ c_R = c_I`; a non-Moore
family is an explicit counterexample. The v1.0 `UpClosed` files are kept under
`audit/` only to document the correction and are not imported.

## Build

```bash
cd report-core
lake update
lake exe cache get
lake build
```

Offline, with prebuilt Mathlib oleans:

```bash
MATHLIB_PACKAGES=/path/to/.lake/packages ./scripts/verify_offline.sh
```

The `scripts/` directory is copied from the extracted repository; if it is not
present here, use the repository-level verification notes.

## Scope

This core does **not** construct the closure from the attribution presheaf. That
bridge is open; see [`../docs/OPEN_BRIDGE.md`](../docs/OPEN_BRIDGE.md). It also
does not prove production safety of the gate, a unique level parameter, or A7
from the free-category universal property.

The full 56-file / 467-theorem corpus is in `../lean/`; the public site is in
`../site/`. Code is Apache-2.0; documentation is CC BY 4.0. See the repository
root for licences and provenance.
