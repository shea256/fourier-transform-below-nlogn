# complex588 verification audit

The selected all-length exact DFT and convolution saving is
`12331685/10^10 = 0.0012331685`. Its kernel saving is `12331686/10^10`.

## Verified mathematical statement

`transform_mainC588 : DFTGoalC588` and `convolution_mainC588 : ConvGoalC588`
are proved by the bundled Lean project. They preserve OpenAI's exact model,
all-positive-length quantifier, fixed programs, supplied root, scalar preparation,
work accounting and polynomial integer bounds. The original full challenge is
unchanged except for the exponent and seven suffixed names. The recursive
statement/dependency comparison passed for both theorems, including all 125
challenge-local declarations. The tensor-program interface and both final
theorems use only `propext`, `Classical.choice` and `Quot.sound`.

## Evidence and scope

* The untouched PR588 verifier passed all 43 stages; PR596's complete untouched
  verifier also passed. Both retain their original conditional scope. Their
  larger native exponents are not proved by this package.
* The source-copy conversion is regenerated exactly. Exact rational checks cover
  every source, every target and every entering-helper basis vector. The
  historical Python E4 shortcut rejects cyclic target shears; Lean's existing
  `GS.yCheck` checks their product and accepts this circuit. No Lean checker
  definition or soundness theorem was changed.
* Lean accepts four source batches, target preservation, three entering-helper
  batches, frame-table and segment checks, all counts, and the endpoint checks.
* The explicit 72-call, 5,040-bank table passes Lean's original schedule checker.
  Its padding, complete invoice, and finite-fill rate are proved in Lean.
* The unchanged #401 engine and the renamed OpenAI Fourier chain prove the
  universal theorem. Local finite checks alone are not the argument for it.
* A one-unit-stronger Fourier challenge fails the statement comparison. Lean
  also proves that a doubled source-copy coefficient and duplicate owner are
  rejected. Four Python mutations and interval boundary checks pass.
* All 63 new Lean modules regenerate byte for byte. The other 291 modules are
  unchanged from the pinned record submission after removing import prefixes.

## Build and official-tool audit

The first successful source build reused only previously compiled modules whose
source and complete local dependency closure were byte-identical; it compiled
every new module. The later official comparator run completed its own fresh
project build with the locked Mathlib cache, checked both full statements,
and reported **nanoda accepts**, **Lean default kernel accepts**, and
**Your solution is okay!**, exit 0. It took 2175.68 seconds including the fresh
build, with peak reported RSS 9,174,708 KiB. The exact tool pins and log hash
are in `lean/complex588/receipt/verification.json`; full output is in
`lean/complex588/receipt/official-comparator.log`.

The local official run replaces only the unavailable `landrun` process sandbox
with a pass-through wrapper, as in the earlier round-eleven audit. The comparator,
Lean exporter, permitted-axiom configuration and proof kernels are unchanged.
This proves no GitHub/leaderboard acceptance, independent human mathematical
review, practical crossover or numerical-stability claim. The site must run
its own submission review before labelling the result there.

## Attribution and source identity

See `lean/complex588/SOURCE_MANIFEST.json`, `NOTICE.complex588`, the preserved
third-party notices and `research/complex-transfer-588-596/BASELINE.md`.
The local additions instantiate credited upstream work; they do not claim
authorship of the native circuit, general geometry, soundness proofs or OpenAI
reduction. The receipt identifies exactly which files and commands were checked.
Same-agent second-pass verification is not independent peer review.
