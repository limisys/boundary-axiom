#!/usr/bin/env bash
# Public-tree hygiene scan: no absolute local paths, credentials, or stale
# placeholders in files intended for publication.
set -euo pipefail

PATTERN='/home/joints|101\.96|101\.47|socks5|ghp_[A-Za-z0-9]|github_pat_|password=|OWNER|Gao, Ming'

matches="$(grep -RInE "$PATTERN" . \
  --exclude-dir=.git \
  --exclude-dir=archive \
  --exclude-dir=logs \
  --exclude-dir=rounds \
  --exclude-dir=audits \
  --exclude-dir=thematic \
  --exclude-dir=crosscheck \
  --exclude-dir=legacy \
  --exclude-dir=Godcore_BoundaryTheory \
  --exclude-dir=.lake \
  --exclude-dir=build \
  --exclude-dir=交付 \
  --exclude=public_scan.sh \
  --exclude=build_manifest.json \
  --exclude=source_manifest.tsv \
  --exclude=lake-manifest.json \
  --exclude=run_check.sh \
  --exclude=check_crosslink.sh \
  --exclude='依赖DAG_渲染器_20260926.py' \
  2>/dev/null || true)"

if [ -n "$matches" ]; then
  printf '%s\n' "$matches"
  echo "FAIL: public scan found local paths / credentials / placeholders" >&2
  exit 1
fi
echo "PASS: public scan"
