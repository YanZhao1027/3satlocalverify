#!/usr/bin/env bash
P="${OPENAI_MATH_LEAN:-$HOME/eth-lean-check-20261027/openai-math/lean}"
E="$HOME/3satlocalverify/execution-prototype"
export PATH="$HOME/.elan/bin:$PATH"
export ELAN_TOOLCHAIN="${ELAN_TOOLCHAIN:-eth-lean-4.34.1}" ELAN_NO_OVERRIDE_NOTICE=1
export LEAN_PATH="$(cd "$P" && lake env printenv LEAN_PATH 2>/dev/null):$E:$E/native-leaf-execution-20261028:$E/native-leaf-nonterminal-20261028:$E/native-core-cost-20261028:$E/native-start-20261029:$E/native-code-parameters-20261029"
