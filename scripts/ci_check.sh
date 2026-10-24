#!/usr/bin/env bash
# Public CI checks. Run after `lake build`.
set -euo pipefail

python3 scripts/check_no_sorry.py --root lean
python3 scripts/check_no_sorry.py --root vendor/CausModel --recursive
python3 scripts/counts.py --root lean --out data/counts.json --check docs/counts.json
python3 scripts/claim_index.py --root lean --claims docs/claims.yaml \
  --out data/claim_index.json --check
python3 scripts/lean_static_audit.py --root lean --out data/lean_static_audit.json
python3 scripts/repro_v3.py --data-dir data
python3 scripts/repro_path_b.py --data-dir data

lake env lean scripts/audit_C_H/Check.lean | tee data/axioms.txt
if grep -q 'sorryAx' data/axioms.txt; then
  echo "FAIL: sorryAx found" >&2
  exit 1
fi
if ! grep -q 'propext, Classical.choice, Quot.sound' data/axioms.txt; then
  echo "FAIL: expected standard axioms not found" >&2
  exit 1
fi

echo "PASS: ci_check"
