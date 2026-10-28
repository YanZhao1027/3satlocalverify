#!/usr/bin/env bash
set -euo pipefail
SRC="${EXPERIMENT_ROOT:-$HOME/eth-lean-check-20261027/execution-prototype}"
DEST="${STAGING_ROOT:-$HOME/3satlocalverify-public}/execution-prototype"
[[ -d "$SRC" && -d "$DEST" ]] || { echo "Missing experiment or staging directory" >&2; exit 1; }
find "$SRC" -type f \( -name '*.lean' -o -name '*.py' -o -name '*.sh' -o -name '*.cnf' -o -name '*.md' -o -name '*summary.json' -o -name '*oracles.json' \) \
  -not -path '*/scratch/*' -not -path '*/__pycache__/*' -not -name '*.debug.lean' -not -name '*Trial.lean' \
  -not -name '*.log' -print0 | while IFS= read -r -d '' file; do
  rel="${file#"$SRC"/}"
  mkdir -p "$(dirname "$DEST/$rel")"
  install -m 644 "$file" "$DEST/$rel"
done
echo "Curated staging refreshed; review git diff and test before publishing."
