#!/usr/bin/env bash
# Preflight for the boundary-axiom public launch.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
BASE_URL="${BASE_URL:-http://127.0.0.1:8794}"

echo "== required launch files"
for f in posts/show_hn.md posts/lesswrong.md posts/alignment_forum.md \
         posts/x_ai_alignment.md posts/x_functional_programming.md posts/x_lean4.md \
         posts/LAUNCH_PLAN.md posts/reply_bank.md \
         site/index.html site/technical.html site/evidence.html site/open-bridge.html \
         site/assets/og.png docs/OPEN_BRIDGE.md; do
  test -s "$f" || { echo "MISSING: $f" >&2; exit 1; }
done

echo "== identity scan"
if grep -rInE 'Xueqiang|classgao|/home/|/Users/|指挥中心|论文线' \
     posts site --exclude-dir=mathjax ; then
  echo "FAIL: identity or local path found" >&2
  exit 1
fi

echo "== local site"
for path in / /technical.html /evidence.html /open-bridge.html /assets/og.png; do
  code="$(curl -s -o /dev/null -w '%{http_code}' "$BASE_URL$path" || true)"
  echo "  $code  $BASE_URL$path"
  test "$code" = "200" || { echo "FAIL: $BASE_URL$path" >&2; exit 1; }
done

echo "== social card"
python3 - <<'PY'
from PIL import Image
im = Image.open('site/assets/og.png')
assert im.size == (1200, 630), im.size
print('  1200x630  site/assets/og.png')
PY

echo "== scope strings"
grep -q '56' README.md
grep -q '467' README.md
grep -q '45' docs/TECHNICAL_PUBLIC.md
grep -q '13' docs/TECHNICAL_PUBLIC.md
echo "  counts present; quote scope with number"

echo "PASS: launch kit preflight"
