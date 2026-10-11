#!/usr/bin/env bash
# Build the round-eleven Lean proof from source and run the statement checks.
# Run from this directory (lean/round11) with elan installed; Lean v4.34.1 comes from lean-toolchain.
# Certificate modules are built one per `lake build`, so that two kernel checks of the certificate never run
# together (peak 10.5 GB measured for one scalar module; 16 GiB was enough).
# Usage: scripts/build_and_check.sh [LOGDIR]
set -u
LOGDIR=${1:-build-logs}
mkdir -p "$LOGDIR"
LOG="$LOGDIR/build.log"
: > "$LOG"
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-4}

run() { echo "=== $* ($(date -u +%FT%TZ))" | tee -a "$LOG"; "$@" >> "$LOG" 2>&1; local rc=$?; echo "=== exit $rc" | tee -a "$LOG"; return $rc; }

run lake exe cache get || exit 1
mods="GCert.Data.Gen.R11.S0 GCert.Data.Gen.R11.S1 GCert.Data.Gen.R11.S2 GCert.Data.Gen.R11.S3
GCert.Data.Gen.R11.S4 GCert.Data.Gen.R11.S5 GCert.Data.Gen.R11.S6 GCert.Data.Gen.R11.S7 GCert.Data.Gen.R11
GCert.Data.Gen.R11Par GCert.Data.Gen.R11Tab0 GCert.Data.Gen.R11Tab1 GCert.Data.Gen.R11Tab2 GCert.Data.Gen.R11Tab3
GCert.Data.Gen.R11Seg0 GCert.Data.Gen.R11Seg1 GCert.Data.Gen.R11Seg2 GCert.Data.Gen.R11Seg3 GCert.Data.Gen.R11SegF
GCert.Data.Gen.R11End GCert.Data.Gen.R11Hist GCert.Data.Gen.R11YChk GCert.Data.Gen.R11Scal0 GCert.Data.Gen.R11Scal1
GCert.Data.InstB2GR11 GCert.Data.RateB2GR11 GCert.Data.RateB2GR11x GCert.Data.ChallengeB2GR11x GCert.Data.R11Price
GCert.Data.R11Cert GCert.Data.R11ScalOK GCert.Data.B2GR11 GCert.Data.B2GR11Main GCert.Data.SolutionB2GR11x
FourierR11.Seam FourierR11.UniformFourierChallenge FourierR11.Main FourierR11.Axioms FourierR11Neg.UniformFourierChallenge"
for m in $mods; do
  run lake build "Work.$m" || { echo "BUILD FAILED at Work.$m" | tee -a "$LOG"; exit 1; }
done
if grep -q "sorryAx" "$LOG"; then echo "FAIL: sorryAx in an axiom report" | tee -a "$LOG"; exit 1; fi
grep -E "depends on axioms" "$LOG" | grep -E "mainX'|hillsX_program'|wht_main_block_B2GR11x'" | sort -u | tee -a "$LOGDIR/axioms.txt"

cmp() { lake env lean --run tools/Compare.lean "$@" > "$LOGDIR/compare-$3.log" 2>&1; local rc=$?; tail -1 "$LOGDIR/compare-$3.log"; return $rc; }
echo "--- Compare: Walsh-Hadamard kernel theorem (expected PASS)" | tee -a "$LOG"
cmp Work.GCert.Data.ChallengeB2GR11x Work.GCert.Data.SolutionB2GR11x OAI.PowerSaving.WHT.wht_main_block_B2GR11x | tee -a "$LOG"
r1=${PIPESTATUS[0]}
echo "--- Compare: Fourier and convolution theorems (expected PASS)" | tee -a "$LOG"
cmp Work.FourierR11.UniformFourierChallenge Work.FourierR11.Main OAI.PowerSaving.transform_mainX OAI.PowerSaving.convolution_mainX | tee -a "$LOG"
r2=${PIPESTATUS[0]}
echo "--- Compare: negative control, challenge one unit stronger (expected FAIL)" | tee -a "$LOG"
lake env lean --run tools/Compare.lean Work.FourierR11Neg.UniformFourierChallenge Work.FourierR11.Main \
  OAI.PowerSaving.transform_mainX > "$LOGDIR/compare-negative.log" 2>&1
r3=$?
tail -1 "$LOGDIR/compare-negative.log" | tee -a "$LOG"
if [ "$r1" -eq 0 ] && [ "$r2" -eq 0 ] && [ "$r3" -ne 0 ]; then
  echo "ALL CHECKS PASSED" | tee -a "$LOG"
else
  echo "CHECKS FAILED (wht=$r1 fourier=$r2 negative=$r3)" | tee -a "$LOG"; exit 1
fi
