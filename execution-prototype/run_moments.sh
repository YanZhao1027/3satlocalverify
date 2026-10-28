#!/bin/sh
set -eu
ROOT="$HOME/eth-lean-check-20261027"
R="$ROOT/execution-prototype"
PROJECT="$ROOT/openai-math/lean"
PATH="$HOME/.elan/bin:$PATH"
export PATH ELAN_NO_OVERRIDE_NOTICE=1 ELAN_TOOLCHAIN=eth-lean-4.34.1
LEAN_PATH="$(cd "$PROJECT" && lake env printenv LEAN_PATH 2>/dev/null):$R"
export LEAN_PATH
cd "$R"
exec timeout 90 lean --run MomentsSparseDimacs.lean "$@"
