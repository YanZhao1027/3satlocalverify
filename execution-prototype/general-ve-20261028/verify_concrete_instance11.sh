#!/bin/sh
# Reproduce the exact 11-variable OpenAI CRT + Lean bucket-VE proof. No network.
set -eu
ROOT="$HOME/eth-lean-check-20261027"
P="$ROOT/openai-math/lean"
E="$ROOT/execution-prototype"
R="$E/general-ve-20261028"
export PATH="$HOME/.elan/bin:$PATH"
export ELAN_TOOLCHAIN=eth-lean-4.34.1 ELAN_NO_OVERRIDE_NOTICE=1
export LEAN_PATH="$(cd "$P" && lake env printenv LEAN_PATH 2>/dev/null):$E:$E/paper-kernel-20261028:$R"
cd "$R"
timeout 25 lean -o ConcreteInstance11.olean ConcreteInstance11.lean
timeout 25 lean ConcreteInstance11Axioms.lean
printf 'PASS: the original OpenAI CRT implementation is equal to SAT.count for the 11-variable connected instance.\n'
