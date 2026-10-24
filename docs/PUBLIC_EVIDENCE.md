# Evidence ledger

**Release:** `boundary-axiom` v0.1.0 staging  
**Date:** 2026-10-23  
**Toolchain:** Lean 4.33.0 (`d8b18978322de05a8f3dba51ef03cf5461676c17`), Mathlib 4.33.0

This ledger separates what was machine-checked from what is design, and from what
is still open. Do not quote a count without its scope.

---

## 1. Scopes and counts

| Scope | Files | Theorems/lemmas | Definitions |
|---|---:|---:|---:|
| **Full verified corpus** (`lean/`) | **56** | **467** | **90** |
| **Report-identity core** (`report-core/`) | **6** | **45** | **13** |
| A-module (`lean/BoundaryTheory.lean`) | 1 | 33 | 7 |

The full corpus and the A-module are contained in this repository. The A-module's
33 declarations are the boundary-potential evidence; they are not the
report-identity core's 45. The full corpus's 467 is the whole 56-file development
body, not the six-module core.

## 2. Build evidence

The minimal core was built with the offline script:

```bash
MATHLIB_PACKAGES=/path/to/.lake/packages ./scripts/verify_offline.sh
```

Expected output:

```
PASS: 6 modules compiled (0 sorry / 0 axiom).
```

The six modules are:

1. `LocusVsBoundary`
2. `ClosureFromInterventions`
3. `ReportBridge`
4. `ReportIdentityCore`
5. `ReportCountermodelsCore`
6. `ReportIdentity` (umbrella import; no declarations)

Axiom audit: the load-bearing declarations depend only on
`[propext, Classical.choice, Quot.sound]`. No `sorry`, no `admit`, no custom
axioms.

The v1.0 `UpClosed` files are retained only under `audit/`. They are not imported
by the v1.1 build. The audit proves `UpClosed R ↔ R = Set.univ`; citing v1.0 as
a non-vacuous result would be an error.

## 3. Core file hashes

```
7535e77f296aba1fdb0c539472af967f5c9ae4da7d3e430ff0846baa21b035ff  architecture/gate_reference.py
f7d6feb67309a29d05777fca006306a2160e41cf6cd2875cf85eb949afb8e75e  report-core/audit/AUDIT_UpClosed.lean
32cca7b502c3f4e526766dd447b1de16e82a16d044b81fc0a8c566650a32d410  report-core/audit/AUDIT_UpClosed.log
b625ef07384b6bc273063073664df7ee09cf792fcbad62a701f342cfacd731e3  report-core/audit/AUDIT_UpClosed.md
5d7319b2eaa81bcb969f7de1d673f4bfb14e55ea842d71515d7225dfb0677daa  report-core/audit/BoundaryReportIdentity.lean
b2ac68221f1cf9a783f09007c5345cbe37a4c042c489cfa4ea046db091d02b44  report-core/audit/README.md
8f628b47f513c2891e222f783e12b9d139f7dfdba793f660cbd91e10e4a0c8f3  report-core/audit/ReportCountermodels.lean
68ba641bf58fec6a7772fb968500988b8ed03d6338a3760e94172525e70125c6  report-core/lean/ClosureFromInterventions.lean
b40ea2de57b0c56e5b84999f310c855568c366cd338cc67a5800c6989595f510  report-core/lean/LocusVsBoundary.lean
c3eaed0c74e0f704dbf2d2cfa219e4c5ce4eb911bfa923e252f9d7ee43752f6c  report-core/lean/ReportBridge.lean
4146190b2792a0f5ee5b81ad56389b510e10606a1a080d2dbd31792c187d5b13  report-core/lean/ReportCountermodelsCore.lean
90e9caf1d066ce69eb1c402ec098ede92290b925f8b31c13df0fb2bb14808a57  report-core/lean/ReportIdentityCore.lean
9513c058d8d2a207e2a2b7c17ebad30193f1fe55c80d349205fb39484440bce8  report-core/lean/ReportIdentity.lean
```

`SHA256SUMS` at the repository root is the release manifest; if it differs from
this table, `SHA256SUMS` is authoritative for the packaged tree.

## 4. Gate evidence

`architecture/gate_reference.py` is a standard-library finite-state reference.
The current release adds the R6 wrapper and passes **14/14** protocol checks:

```
RESULT: 14/14 protocol tests passed
PASS: 14/14 protocol tests
```

Coverage:

- G1: positive bundle accepted and committed; Moore + `c_R = C`.
- G2: non-Moore family → REVIEW (R2).
- G3: non-closure → REJECT (R1).
- G4: `c_R ≠ C` → REJECT (R3).
- G5: report outside `R` → REJECT (R4).
- G6: version/evidence mismatch → REVIEW (R5).
- G7: parent mismatch → REJECT (R7).
- G7b: zero/multiple candidates → REVIEW (R6); one candidate accepted.
- G8: simulated crash before atomic swap leaves head unchanged.
- G9: action gate ALLOW/DENY.
- G10: canonical `Fix(c_I)` is Moore and accepted.
- G11: per-state threshold family is not Moore → REVIEW.
- G12: `Fix(c_R)` of the threshold family is the threshold plus `Ω`.

This is a protocol check, not a production validation. It does not measure
acceptance/rejection rates on a real task.

## 5. What is not in this ledger

- No proof that the attribution presheaf induces the closure; see
  `docs/OPEN_BRIDGE.md`.
- No uniqueness theorem for the level parameter `w`; the gate must take `w` as
  an input or adopt a separate selection principle.
- No derivation of A7 or the potential form from the free category. The
  A-module is a separate model-class scope.
- No production deployment or adversarial runtime test.
- No peer review. The papers are preprints.

## 6. Reproduction notes

The Lean build requires Mathlib 4.33.0. A clean clone needs network on the first
`lake update` / `lake exe cache get`; the offline script requires a prebuilt
Mathlib package tree. The static site needs only Python 3 and a browser; MathJax
is vendored under `site/assets/mathjax`.

Site build:

```bash
python3 site/build_site.py
python3 -m http.server 8793 --bind 127.0.0.1 --directory site
```

Gate:

```bash
python3 architecture/gate_reference.py
```
