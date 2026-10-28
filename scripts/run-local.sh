#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
E="$ROOT/execution-prototype"
P="${OPENAI_MATH_LEAN:-$HOME/eth-lean-check-20261027/openai-math/lean}"
export PATH="$HOME/.elan/bin:$PATH"
export ELAN_TOOLCHAIN="${ELAN_TOOLCHAIN:-eth-lean-4.34.1}"
export LEAN_PATH="$(cd "$P" && lake env printenv LEAN_PATH 2>/dev/null):$E:$E/paper-kernel-20261028:$E/general-ve-20261028"
cd "$E/general-ve-20261028"
case "${1:-}" in
  axioms) lean ConcreteInstance11Axioms.lean ;;
  proof) lean ConcreteInstance11.lean && lean ConcreteInstance11Axioms.lean ;;
  regression) python3 regression_general_memo.py ;;
  *) echo "Usage: scripts/run-local.sh axioms|proof|regression" >&2; exit 2 ;;
esac
