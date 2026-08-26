#!/bin/sh
# Inventory of `sorry` occurrences in the Lean sources. Excludes comments only
# heuristically; the release gate also audits public theorem axioms.
cd "$(dirname "$0")/.." || exit 1
grep -rn --include='*.lean' -w 'sorry' Anderson4D Anderson4D.lean 2>/dev/null
COUNT=$(grep -rn --include='*.lean' -w 'sorry' Anderson4D Anderson4D.lean 2>/dev/null | wc -l | tr -d ' ')
echo "---"
echo "sorry count: $COUNT"
