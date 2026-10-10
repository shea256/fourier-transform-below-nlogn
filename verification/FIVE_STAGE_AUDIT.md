# Five-stage program and Fourier proof reproduction

## Selected sources and attribution

The selected source is Chafik Boukhalfa's [CrocSwap PR256](https://github.com/CrocSwap/integer-mult-bounds/pull/256), commit `db3f75cdc5f03f3131d48fb220f6bf1958404ff3`, paired with his [Fourier proof PR](https://github.com/jacobalansussman/wht-power-saving-lean/pull/2), commit `fd19e46b728faa414cbfbf91b01a6a0b7903375d`. The latter extends Jacob Sussman's `f010392c923279e3dd59ef3aa5fedad23affc5fd` framework. The [source manifest](vendor/five_stage/SOURCE.json) binds both; the complete proof sources and self-contained finite certificate package are vendored. Original licenses and notices are unchanged.

The layout, formal frame/adapter theory, certificate framework and original formal Fourier connection are Sussman's. The PR233 pairing, PR256 emitter and stronger instantiation are Boukhalfa's. The circuit retains icekylinx, eumemic, Avi Eisenberg and the predecessors named in [the attribution audit](../ATTRIBUTION.md). OpenAI supplies the original model and Fourier reduction. This is an incorporation and reproduction of an already published upstream result, not a newly discovered exponent by this project.

The certified tensor saving is `7547361/10^10`; the Fourier saving is `7547360/10^10`, with strict gap `1/10^10`. The latter is about 12.6472% above our previous `0.00067`. Neither ratio is a runtime measurement. The stronger source PRs were unmerged at the checked revisions; commit pins, rather than merge status or moving titles, identify the reviewed artifacts.

The queue also contains larger numerical targets. [PR246](https://github.com/CrocSwap/integer-mult-bounds/pull/246), checked at `545665b62a922890cf63b83ae5970013a41c3cdc`, prices a complex saving near `0.00083465065`, but explicitly labels it a target rather than a witness and supplies none of the six required export bodies. It is a research lead, not a substitute for the complete program and Fourier proof incorporated here. Later bit-side improvements alone do not raise the Fourier exponent. This selection records a verified source pair, not an assertion that every open research claim has been settled.

## Local finite checks

The standard-library [verifier](verify_five_stage.py) checks every manifest hash and invokes the unmodified Sussman reference checker on the explicit PR233 program: 12,052 registers, 18,248 frames, 52,300 gates and 69,683 invocation blocks. The label checks cover nested frames and actual gate chronology. Its exact scalar replay covers the response of every source, not every arbitrary dirty-input column; the formal invocation theorem supplies dirty-response subtraction and inverse cleanup. This scope differs from our round-eleven backpropagation check and must not be conflated with it.

The verifier independently forms the five-stage histogram from all invocation classes and the four bridge terms, checks `m=110`, `W=14692`, rank `1613040`, deficit `3080`, 358,975 children and maximum width 46. It uses this repository's rational logarithm/exponential bounds to certify both the contracting moment and the Lean engine's finite-fill inequality at `s=40`. The fixed histogram fails at `7547365/10^10`. This is a negative control, not a universal optimality claim.

It also binds the explicit program and histogram to the vendored Lean input, verifies the exponent literals, and compares the challenge with the vendored OpenAI statement after accounting for comments, seven renamed declarations and the changed exponent. The mathematical certificate data match exactly between the two packages; only their descriptive provenance string differs.

We separately fetched the 89 imported `OAI/` Lean modules, the original Fourier challenge and the toolchain file directly from OpenAI commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`: **all 91 files were byte-identical**. The [origin ledger](certificates/five_stage_openai_origin.json) records their paths and hashes; the default verifier binds every one to the archived proof sources. This checks the unchanged model and definition sources in addition to comparing the challenge and solution environments. To reproduce the origin comparison, check out that OpenAI revision and compare the ledger's `upstream_path` with its named path in the extracted proof archive.

The full PR256 regeneration rebuilds its 308 pinned baseline files, reruns the source-aligned producer, frame flow and exact local lifts for both the baseline control and improved word, emits both programs, checks both, and requires exact agreement with the committed certificates. It passed from the vendored package in 188.6 seconds; the [receipt](certificates/five_stage_regeneration_receipt.json) binds the preserved log. Its discovery dependencies are pinned to NumPy 2.3.5 and SciPy 1.17.0; this extra regeneration is separate from the default standard-library checks.

## Lean reproduction gate

**Passed.** The [retained receipt](certificates/five_stage_lean_receipt.json) records a fresh project build from the archived source, with Mathlib's pinned compiled cache. Project compilation took 2625.5 seconds; the WHT and Fourier statement comparisons took 33.7 and 42.6 seconds. All commands exited successfully, every archived source byte still matched afterward, and the three audited final theorems used only the standard axioms. The [compressed logs](receipts/five_stage/) are SHA-256-bound to the receipt. Only after this gate passed was the registry changed from candidate to formalized and the improvement-history entry incorporated.

The [reproduction script](verify_five_stage_lean.py) checks every source file against the vendored archive, uses Lean 4.34.1 and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, regenerates 41 certificate/proof/configuration files and 14 Fourier-chain files, and builds the WHT and all-length DFT/convolution statements and solutions. It then checks the theorem axioms and runs upstream `tools/Compare.lean` on the WHT and both Fourier statements. That tool compares theorem statements, their transitive definition dependencies and permitted proof axioms in separate challenge/solution environments.

The challenge modules intentionally state their goals with `sorry`; they are not the solution proofs. Successful solution checks must report only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx` or extra assumed theorem. The default Python suite does not run Lean. The registry's `formalized` status requires the successful pinned receipt and hashes of its retained logs.

## Reproduction commands

From the repository root:

```sh
python3 verification/verify_five_stage.py
uv run --python 3.11 --with numpy==2.3.5 --with scipy==1.17.0 \
  python -B verification/vendor/five_stage/gcert-program-233/verify.py
python3 verification/verify_five_stage_lean.py \
  --work-dir /tmp/fourier-five-stage-rebuild --lake lake --threads 2
```

Install the pinned `leanprover/lean4:v4.34.1` toolchain first, or supply an absolute `--lake` path. Its executable directory is added to the child process's `PATH` for Mathlib's helper programs. The script extracts sources into a fresh work directory or verifies every existing source byte before reuse. An empty project build is identified in the receipt. Mathlib's compiled cache is downloaded, not rebuilt from source. A build needs several GB of storage and substantial memory; the reference environment has 32 GiB RAM and uses two Lean worker threads.

The initial reproduction used one combined target build. During the two large scalar reductions, one process was temporarily paused and automatically resumed after the other finished, to limit simultaneous memory use; no proof source was altered. The reproduction script now stages those two scalar targets sequentially before building the remaining targets, following upstream's memory guidance. The retained receipt records the actual commands of the initial run.

## Evidence boundaries

- The fresh build checks the upstream project proof with Lean's kernel. The exact Python checks and source-generation checks establish additional provenance and arithmetic, not a replacement for the proof.
- The source theorem is the complete all-positive-length exact DFT statement in OpenAI's RAM model, including supplied-root preparation and bounded integer/index values. The local written exposition and previous Jain transfers have not thereby all been formalized.
- `tools/Compare.lean` is Sussman's checker. This reproduction does not run OpenAI's official Linux comparator, a second independent kernel, or `leanchecker`.
- Mathlib and the Lean toolchain are trusted pinned dependencies. The macOS arm64 Lean release archive was checked against its published SHA-256 `65f22a4f047738ec742667b3247e836a86ebf06eabc12655c3dee00637e37866`.
- No large-array DFT, full cover enumeration, numerical-stability claim, practical speedup, or independent human review is supplied. Earlier witnesses and their own narrower validation remain available unchanged.
