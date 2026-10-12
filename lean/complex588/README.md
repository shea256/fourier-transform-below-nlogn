# Exact all-length DFT with saving 0.0012331685

This Lean project proves, in OpenAI's exact complex RAM model,

    T(n) = O(n (log n)^(1 - 12331685/10^10))

for every positive length, including scalar preparation and indexing. It also
proves the corresponding exact convolution bound. The supplied-root and
unrestricted-coefficient assumptions are unchanged. This is an asymptotic
arithmetic result, not a measured improvement to numerical FFT software.

The saving is about 20.65% larger than the pinned prior Lean-verified saving
`0.0010221076`; the percentage compares exponents, not elapsed running times.

## What is new

The construction uses **PR588's atm3 local circuit** with 112 explicit source
copies, in the existing #401/#377 dedicated-bank layout. A cyclic schedule uses
5,040 helper banks, giving `W = 12208`, `m = 73`, and deficit `2560`. The kernel
saving is `12331686/10^10`; the Fourier saving is one unit smaller.

The full native #588 and #596 verifiers were replayed successfully. Their larger
native exponents remain conditional and use a different hosting scheme; they
are not the exponents proved here. #596's hyperplane endpoints are also outside
the reused invocation interface. See [the proof map](../../research/complex-transfer-588-596/ATTEMPT.md)
and [baseline audit](../../research/complex-transfer-588-596/BASELINE.md).

Sussman's Lean checker definitions and soundness proofs were not weakened.
The Python preflight handles cyclic target shears by checking their exact
product, as the existing Lean `GS.yCheck` already does. The Lean kernel checks
the complete local circuit, entering-helper cancellation, frame labels, counts,
the actual bank table, and the finite-fill rate. The #401 engine and OpenAI
reduction then prove the universal statement.

## Theorems and checks

* `OAI.PowerSaving.transform_mainC588 : DFTGoalC588`
* `OAI.PowerSaving.convolution_mainC588 : ConvGoalC588`
* `OAI.PowerSaving.RAM.hillsC588_program`, the kernel interface at saving
  `12331686/10^10`.

These three theorems use only `propext`, `Classical.choice` and `Quot.sound`.
The full Fourier challenge is OpenAI's original file with just the exponent
and seven names changed. Statement/dependency comparisons pass for DFT and
convolution. A challenge one unit stronger fails. Lean also proves that a
corrupted source-copy coefficient and a duplicate bank owner are rejected.

The initial build reused only previously compiled modules whose source and
entire local dependency closure were byte-identical. Every new module compiled
from source. The official comparator's separate fresh build, full-statement
comparison, **nanoda replay and Lean kernel replay all passed** (exit 0).
Its output is in `receipt/official-comparator.log`, with tool pins and hashes
in `receipt/verification.json`. Local verification does not imply that the
leaderboard has reviewed or accepted this submission.

## Reproduce

Requires Lean 4.34.1, Python 3.11+, the locked Mathlib revision, and approximately
16 GiB RAM. Use one worker. From this directory:

```sh
python3.11 scripts/check_provenance.py
python3.11 scripts/regenerate.py
bash scripts/build_and_check.sh build-logs
```

The finite checks, including regeneration of the circuit and bank table:

```sh
python3.11 ../../research/complex-transfer-588-596/verification/check_candidate.py \
  --artifacts artifacts --gx tools/gx/gx.py --out build-logs/finite.json
```

`scripts/regenerate.py` reproduces all 63 new Lean modules byte for byte. The
291 general dependency modules are pinned to the prior submission and checked
by reversing the import-prefix transformation. Sources, generators, and witness
files are covered by `SOURCE_MANIFEST.json`. The full upstream replay commands
are in [RUNLOG.md](../../research/complex-transfer-588-596/RUNLOG.md).

With the official comparator and its exporters installed, run:

```sh
lake env comparator comparator/fourier.json
```

The local comparator run uses a pass-through `landrun` wrapper because this VM
cannot provide its Linux sandbox. That changes process isolation, not the
proof, permitted axioms, comparison or kernel checks. The wrapper and tool
revisions are recorded in the receipt. Human mathematical review is pending.

## Credits

The circuit and its community predecessors retain their credits; Jeremy Kothe
submitted #588. Sussman supplies the formal engine and checkers; Dugongue and
jacklightChen supply the #401/#377 geometry; Mamano's submission supplies the
published gauged Lean extension; OpenAI supplies the model and Fourier
reduction. This project's contribution is the new checked instantiation and
its supporting conversion, schedule and verification. See
[NOTICE.complex588](NOTICE.complex588) and the preserved upstream notices.
