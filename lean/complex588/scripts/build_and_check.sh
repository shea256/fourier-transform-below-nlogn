#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
log_dir="${1:-build-logs}"
mkdir -p "$log_dir"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}"
python_bin="${PYTHON:-python3.11}"
"$python_bin" scripts/check_provenance.py
"$python_bin" scripts/regenerate.py > "$log_dir/regenerate.log" 2>&1
lake exe cache get > "$log_dir/cache.log" 2>&1
lake build Work.FourierC588.Main Work.FourierC588.UniformFourierChallenge \
  Work.FourierC588Neg.UniformFourierChallenge Work.GCert.Data.C588Controls \
  Work.FourierC588.Axioms > "$log_dir/build.log" 2>&1
lake env lean Work/FourierC588/Axioms.lean > "$log_dir/axioms.log" 2>&1
lake env lean --run tools/Compare.lean Work.FourierC588.UniformFourierChallenge \
  Work.FourierC588.Main OAI.PowerSaving.transform_mainC588 \
  OAI.PowerSaving.convolution_mainC588 > "$log_dir/compare-fourier.log" 2>&1
if lake env lean --run tools/Compare.lean Work.FourierC588Neg.UniformFourierChallenge \
    Work.FourierC588.Main OAI.PowerSaving.transform_mainC588 \
    OAI.PowerSaving.convolution_mainC588 > "$log_dir/compare-negative.log" 2>&1; then
  echo "ERROR: the stronger challenge was accepted"
  exit 1
fi
"$python_bin" - "$log_dir" <<'PY'
from pathlib import Path
import sys
p=Path(sys.argv[1])
assert 'RESULT: PASS' in (p/'compare-fourier.log').read_text()
bad=(p/'compare-negative.log').read_text()
assert 'definition body differs' in bad and 'decimalExponentC588' in bad
assert 'sorryAx' not in (p/'axioms.log').read_text()
assert (p/'axioms.log').read_text().count('[propext, Classical.choice, Quot.sound]')==3
PY
echo "ALL CHECKS PASSED"
