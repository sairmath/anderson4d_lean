#!/usr/bin/env bash
# Release gate: run every acceptance check in one command.
# Usage: bash scripts/release_gate.sh
# Exit status 0 means every check passed.

set -uo pipefail
cd "$(dirname "$0")/.."
ROOT=$(pwd)
FAIL=0
say() { printf '\n=== %s ===\n' "$1"; }
bad() { printf 'FAIL: %s\n' "$1"; FAIL=1; }

say "1. full build"
BUILD_LOG=$(mktemp)
if lake build >"$BUILD_LOG" 2>&1; then
  tail -2 "$BUILD_LOG"
else
  tail -20 "$BUILD_LOG"
  bad "lake build"
fi
JOBS=$(grep -o 'Build completed successfully ([0-9]*' "$BUILD_LOG" | grep -o '[0-9]*')
rm -f "$BUILD_LOG"
printf 'jobs: %s\n' "${JOBS:-unknown}"

say "2. sorry scan"
if bash scripts/sorries.sh 2>&1 | tail -2 | grep -q 'sorry count: 0'; then
  echo "0 sorries"
else
  bad "sorries.sh reports a nonzero count"
fi

say "3. banned declarations"
# Scan every tracked Lean file, including the two root entry points.  Strip
# line comments so explanatory text such as "no native_decide" is harmless.
BANNED=$(git grep -nE '^[[:space:]]*axiom[[:space:]]|\badmit\b|native_decide' -- '*.lean' \
         | sed 's/--.*$//' \
         | grep -E 'axiom|\badmit\b|native_decide' || true)
if [ -z "$BANNED" ]; then
  echo "clean"
else
  bad "banned declarations found"
  printf '%s\n' "$BANNED"
fi

say "4. file/import parity (orphans)"
# Compare the exhaustive umbrella import with every library module. Ignored
# local files are reported separately and do not enter the library.
ORPH=$(comm -23 \
  <(find Anderson4D -name '*.lean' | sed 's|/|.|g; s|\.lean$||' | sort) \
  <(grep '^import Anderson4D' Anderson4D.lean | sed 's/^import //' | sort))
UNTRACKED=$(git ls-files --others --exclude-standard Anderson4D | sed 's|/|.|g; s|\.lean$||' | sort)
REAL=$(comm -23 <(printf '%s\n' "$ORPH" | sed '/^$/d') <(printf '%s\n' "$UNTRACKED" | sed '/^$/d'))
if [ -z "$REAL" ]; then
  echo "no tracked orphans"
  [ -n "$ORPH" ] && { echo "(untracked local files:"; printf '%s\n' "$ORPH" | sed 's/^/  /'; echo ")"; }
else
  bad "tracked but unimported:"; printf '%s\n' "$REAL"
fi

say "5. axiom audit of the load-bearing theorems"
AUD=$(mktemp -d)/AxiomAudit.lean
cat > "$AUD" <<'LEAN'
import Anderson4D
#print axioms Anderson4D.mainConditional_of_deterministic_bounds
#print axioms Anderson4D.mainConditional_of_secondMoment_and_deterministic_bounds
#print axioms Anderson4D.R322AnalyticResidualPrefix.exists_r322_renormC2q_bound
#print axioms Anderson4D.nonempty_noiseModel
#print axioms Anderson4D.NoiseModel.integral_xiEps_mul_eq_etaEpsT4
#print axioms Anderson4D.PartialPairing.xi_comp_parametrix
#print axioms Anderson4D.MainGoodEvent.nonempty_fixedModeGoodEventData_of_deterministic_bounds
#print axioms Anderson4D.Prop36.tendsto_fullResolventChar_of_second_moment_and_goodEvent
#print axioms Anderson4D.permSum_estimate
#print axioms Anderson4D.volume_estimate
#print axioms Anderson4D.proposition41
#print axioms Anderson4D.proposition41_at_truncation
#print axioms Anderson4D.SmoothCutoff.exists_r324PaperHighWholeSeriesWeightedMajorantBound
#print axioms Anderson4D.deterministic_second_moment_bound
#print axioms Anderson4D.main_conditional
#print axioms Anderson4D.main_conditional_law
LEAN
OUT=$(lake env lean "$AUD" 2>&1)
LEAN_STATUS=$?
AUDIT_COUNT=$(printf '%s\n' "$OUT" | grep -cE 'depends on axioms:|does not depend on any axioms' || true)
UNEXPECTED_AXIOMS=$(printf '%s\n' "$OUT" \
  | grep 'depends on axioms:' \
  | sed -E 's/^.*depends on axioms: \[//; s/\].*$//' \
  | tr ',' '\n' \
  | sed -E 's/^[[:space:]]+//; s/[[:space:]]+$//' \
  | grep -vE '^(propext|Classical\.choice|Quot\.sound|)$' || true)
if [ "$LEAN_STATUS" = "0" ] && [ "$AUDIT_COUNT" = "16" ] && [ -z "$UNEXPECTED_AXIOMS" ]; then
  printf 'audited: %s theorems, standard axioms only\n' "$AUDIT_COUNT"
else
  bad "axiom audit (Lean status $LEAN_STATUS, reports $AUDIT_COUNT/16)"
  [ -n "$UNEXPECTED_AXIOMS" ] && printf 'unexpected axioms:\n%s\n' "$UNEXPECTED_AXIOMS"
  printf '%s\n' "$OUT" | head -30
fi

say "6. paper index"
# Reports coverage; a stale index is a failure, untagged modules are not
# (backfill is incremental).
python3 scripts/paper_index.py --check || bad "docs/PAPER_INDEX.md is stale"

say "7. documentation links"
python3 scripts/check_doc_links.py || bad "documentation links are stale or broken"

say "8. blueprint declarations"
# Blueprint rendering is optional in the local Lean-only gate and mandatory
# in the separate Pages-preview workflow.  Never skip it silently.
if command -v plastex >/dev/null 2>&1 && command -v leanblueprint >/dev/null 2>&1; then
  leanblueprint web >/dev/null 2>&1 || bad "leanblueprint web"
else
  echo "SKIP: blueprint renderer not installed (enforced by Pages preview CI)"
fi
if lake exe checkdecls blueprint/lean_decls; then
  printf 'checkdecls: PASS (%s declarations)\n' "$(grep -c '' blueprint/lean_decls)"
else
  bad "checkdecls"
fi

say "9. verdict"
if [ "$FAIL" = "0" ]; then
  echo "ALL CHECKS PASSED — the gate's mechanical conditions are met."
  echo "This is a mechanical gate only; the precise conditional scope is"
  echo "specified by the blueprint."
else
  echo "SOME CHECKS FAILED — see above."
fi
exit "$FAIL"
