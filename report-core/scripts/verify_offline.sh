#!/usr/bin/env bash
# 离线复现：使用本机已构建的 Mathlib oleans，逐件编译发布包 Lean 源码。
#
# 用法：
#   MATHLIB_PACKAGES=/path/to/.lake/packages ./scripts/verify_offline.sh
#   ELAN_HOME=/path/to/.lean-home ./scripts/verify_offline.sh
#
# 退出码 0 = 6 个模块全部编译通过。
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LEAN_DIR="$ROOT/lean"
BUILD_DIR="$ROOT/build"

: "${MATHLIB_PACKAGES:=}"
if [[ -z "${MATHLIB_PACKAGES}" ]]; then
  echo "FAIL: 请设置 MATHLIB_PACKAGES 为含 mathlib/.lake/build/lib/lean/Mathlib.olean 的目录。" >&2
  exit 1
fi

if [[ -n "${LEAN_BIN:-}" ]]; then
  :
elif [[ -n "${ELAN_HOME:-}" && -x "$ELAN_HOME/bin/lean" ]]; then
  LEAN_BIN="$ELAN_HOME/bin/lean"
elif [[ -x "$HOME/.elan/bin/lean" ]]; then
  LEAN_BIN="$HOME/.elan/bin/lean"
else
  echo "FAIL: 找不到 lean。请设置 LEAN_BIN 或 ELAN_HOME。" >&2
  exit 1
fi

if [[ ! -f "$MATHLIB_PACKAGES/mathlib/.lake/build/lib/lean/Mathlib.olean" ]]; then
  echo "FAIL: 在 $MATHLIB_PACKAGES 下找不到预构建的 Mathlib.olean。" >&2
  exit 1
fi

PKG_PATHS="$(find "$MATHLIB_PACKAGES" -maxdepth 6 -type d -path '*/.lake/build/lib/lean' -print | paste -sd: -)"
export LEAN_PATH="$BUILD_DIR:$PKG_PATHS"

mkdir -p "$BUILD_DIR"
"$LEAN_BIN" --version

MODULES=(
  LocusVsBoundary
  ClosureFromInterventions
  ReportBridge
  ReportIdentityCore
  ReportCountermodelsCore
  ReportIdentity
)

cd "$ROOT"
for m in "${MODULES[@]}"; do
  echo "== $m"
  "$LEAN_BIN" -o "build/$m.olean" "lean/$m.lean"
done

echo "PASS: ${#MODULES[@]} modules compiled (0 sorry / 0 axiom)."
