#!/bin/sh
set -eu
ROOT="$HOME/eth-lean-check-20261027"
cd "$ROOT/openai-math/lean"
PATH="$HOME/.elan/bin:$PATH"
export PATH ELAN_NO_OVERRIDE_NOTICE=1
exec lake env lean --run "$ROOT/execution-prototype/SparseDimacs.lean" "$@"
