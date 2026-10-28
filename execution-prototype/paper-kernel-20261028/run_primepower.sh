#!/bin/sh
set -eu
ROOT="$HOME/eth-lean-check-20261027"
P="$ROOT/openai-math/lean"
E="$ROOT/execution-prototype"
R="$E/paper-kernel-20261028"
PATH="$HOME/.elan/bin:$PATH"
export PATH ELAN_TOOLCHAIN=eth-lean-4.34.1 ELAN_NO_OVERRIDE_NOTICE=1
LEAN_PATH="$(cd "$P" && lake env printenv LEAN_PATH 2>/dev/null):$E:$R"
export LEAN_PATH
cd "$R"
exec timeout 120 lean --run PrimePowerDimacs.lean "$@"
