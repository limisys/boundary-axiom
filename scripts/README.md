# Scripts

| Script | Purpose | Public CI |
|---|---|---|
| `ci_check.sh` | counts, claims, 0-sorry/axiom, static audit, reproduction, axiom dependencies | yes |
| `public_scan.sh` | reject absolute local paths, credentials, stale placeholders | yes |
| `check_no_sorry.py` | strip comments/strings; find `sorry`/`admit`/custom `axiom` | yes |
| `counts.py` | four scopes: `all`, `b_line`, `a_module`, `paper_b_canonical`; `--check` against `docs/counts.json` | yes |
| `claim_index.py` | `docs/claims.yaml` → Lean declaration names; `--check` resolves every formalized claim | yes |
| `lean_static_audit.py` | per-file counts and forbidden-token audit | yes |
| `quote_counts.py` | generate a quoted count string from `data/counts.json`; do not hand-copy numbers | manual |
| `repro_v3.py` / `repro_path_b.py` | independent numerical reproduction (standard library only) | yes |
| `build.py` | offline topological build for authors with prebuilt Mathlib packages | optional |
| `audit_C_H/Check.lean` | axiom-dependency check for the load-bearing declarations | yes |

## Conventions

- Run from the repository root: `python3 scripts/...`; scripts locate the root
  via `__file__`.
- `build.py` does **not** download Mathlib; it reads prebuilt packages and is an
  author-side offline audit. Public users should use `lake update && lake build`.
- All generated artifacts are reproducible and may be overwritten.
- `verify_all.sh`, `check_crosslink.sh`, `legacy/` and `z3/` are author-local
  audit paths and are not part of the public tree.
