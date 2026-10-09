# Finite Network Improvements for the Exact Discrete Fourier Transform

A living research project on **OpenAI Math Problem #130**, *An explicit power saving for the exact discrete Fourier transform*. We study how improvements to the complex networks developed around integer multiplication (#109) transfer to all-length Fourier bounds.

<!-- current-result:start -->

Current selection: **[Jain round-eleven retired-copy refinement](results/round11.md)**, recorded 2026-10-09.

```math
T(n)=O\left(n(\log n)^{1-\delta}\right),\qquad \delta=0.00067.
```

This is a **proposed conditional transfer**, supported by a written argument and finite checks. Independent mathematical review and end-to-end formal verification remain pending.

The proposed exponent saving is approximately **6.7 billion times** OpenAI's [published headline](https://github.com/openai/math/blob/main/preprints/An-explicit-power-saving-for-the-exact-discrete-Fourier-transform-September-25-2026/main.pdf) of `delta=1e-13`. It is about **9.18 times** our [round-six result](results/round6.md) of `delta=0.000073`. These ratios compare exponent parameters, not measured runtimes.

The Fourier saving is chosen below the upstream complex-tensor witness `a=0.00067147467`, leaving a positive gap to absorb the Fourier reduction's overhead. The integer-multiplication headline `kappa` is a separate parameter.

The [finite certificate](verification/certificates/round11_reference.json) records exact rational checks of **17,057,040 scalar output coefficients**, covering the input response, cancellation of initial dirty-scratch contributions, and preservation of arbitrary target values. This is a scalar-map check; the general physical-network and Fourier arguments remain written proof dependencies.

<!-- current-result:end -->

The model uses exact complex arithmetic, unrestricted coefficients, a specified supplied root of unity, and unit-cost logarithmic-word indexing. Scalar preparation and array organization are included. These are asymptotic exponent improvements; **no practical FFT speedup is claimed**.

## Read the paper and result history

- [Current manuscript](manuscript.pdf), [Markdown](manuscript.md), and [LaTeX](tex/manuscript.tex).
- [Improvement log](IMPROVEMENTS.md): dated results, exact parameters, provenance and changes.
- [Reusable transfer theorem](paper/framework.md): the finite-network contract, recurrence, array adapters, and all-length reduction.
- [Versioned result records](results/README.md): construction arguments and the process for adding future updates.

The paper title and general theorem stay stable as new networks arrive. Each update gets its own record, pinned sources, verifier and reference certificate. A candidate is not promoted by a numerical certificate alone. `results/registry.json` explicitly selects the current proposed result and generates the headline and log.

## What this project contributes

The finite-network improvements belong to their cited authors. This project supplies proposed transfers into #130's uniform array model and additional finite checks. It does not infer a Fourier bound from an integer-multiplication running time or add successive networks' savings together.

The selected round-eleven word and optimization integration come from Swapnil Jain. The construction builds on icekylinx's frame, cover, paired-cube and retirement-reuse work; jamesyc's terminal-target compiler and birth reuse; eumemic's modules and frame/late-compensation lineage; an664's completed-core sharing principle; and DaysSky's carrier/scheduling work. Douglas Colkitt's community repository and the original OpenAI research supply the underlying framework. The preserved [NOTICE](verification/vendor/jain_round11/NOTICE) contains the fuller lineage; the [result record](results/round11.md) explains the adopted dependencies, and the [audit record](verification/ROUND11_AUDIT.md) states the review boundary.

This work is AI-assisted. Additional verifiers written with the same assistant are not independent mathematical review. External Lean files certify arithmetic predicates; they do not formally prove the complete network or our Fourier transfer. Preserved upstream notices retain contributor-specific AI disclosures. Earlier project work used GPT-6 Pro and GPT-6-Astra Max; the current integration and checks were developed with Codex.

## Reproduce and update

Standard-library Python **3.10+**:

```sh
python3 verification/run_checks.py
```

For the round-eleven witness only:

```sh
python3 verification/verify_round11.py
```

The full suite includes the exact decoder coefficient matrix, complete rational scalar output map and compensation-read checks, the imported full-size frame/role replay, small exhaustive Gaussian-integer Clifford checks, and rigorous rational moments. The small Clifford checks run in the round-ten suite and support the round-ten and round-eleven arguments. These are finite checks of the constructions; the full DFT algorithm is not executed. The Python runner also does not execute Lean. See [verification scope](verification/README.md).

Rebuild the paper, generated result summary and log with Pandoc and pdfLaTeX:

```sh
python3 scripts/build_manuscript.py
```

`--markdown-only` regenerates text without compiling the PDF; `--check` checks registry/certificate agreement and generated text freshness. The [update workflow](results/README.md) explains how to preserve prior artifacts and incorporate a new witness.

## Preserved results

- [Round-ten record](results/round10.md), with its [assembled draft snapshot](archive/round10/README.md), captured before incorporating round eleven in the same update.
- [Round-six record](results/round6.md), with its unchanged [publication PDF](archive/round6/manuscript.pdf) and source snapshot.
- [Earlier shared-sum record](results/legacy-shared-sum.md), with its unchanged [publication PDF](archive/three-stage/manuscript.pdf).
- [Short core proof](core-proof.pdf), retaining the simpler `5.2e-10` and `5.3e-10` fallbacks.

All previous verification suites remain runnable. Historical audit records apply only to their named constructions.

## Original sources

OpenAI's [#130 Fourier manuscript](https://github.com/openai/math/blob/main/preprints/An-explicit-power-saving-for-the-exact-discrete-Fourier-transform-September-25-2026/main.pdf) supplies the exact-arithmetic model, Fourier compiler and all-length reduction. The network research originates in [#109](https://github.com/openai/math/blob/main/preprints/Integer-multiplication-below-n-log-n-September-23-2026/paper.pdf) and [Douglas Colkitt's community repository](https://github.com/CrocSwap/integer-mult-bounds). Construction-specific sources, immutable commits, licenses and contribution credit are recorded with each version.
