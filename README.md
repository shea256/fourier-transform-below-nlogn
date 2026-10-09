# Finite Network Improvements for the Exact Discrete Fourier Transform

A living research project on **OpenAI Math Problem #130**, *An explicit power saving for the exact discrete Fourier transform*. We study how improvements to the complex networks developed around integer multiplication (#109) transfer to all-length Fourier bounds.

<!-- current-result:start -->

Current selection: **[Jain round-eleven retired-copy refinement](results/round11.md)**, recorded 2026-10-09.

```math
T(n)=O\left(n(\log n)^{1-\delta}\right),\qquad \delta=0.00067.
```

The exact tensor witness is `a=0.00067147467` and the chosen Fourier saving is `delta=0.00067`. This is a **proposed conditional transfer**, supported by a written argument and finite checks. Independent mathematical review and end-to-end formal verification remain pending.

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

The selected round-eleven network comes from Swapnil Jain, with the community lineage preserved in its [NOTICE](verification/vendor/jain_round11/NOTICE). It uses icekylinx's three-stage covers and arbitrary-subspace frames, paired cubes, completed-core sharing, retired-copy subtraction, terminal-target compilation, and the attributed module, birth-reuse and frame-refinement work. The [result record](results/round11.md) explains each dependency and the [audit record](verification/ROUND11_AUDIT.md) states the review boundary.

This work is AI-assisted. Additional verifiers written with the same assistant are not independent mathematical review. External Lean files certify arithmetic predicates; they do not formally prove the complete network or our Fourier transfer. Preserved upstream notices retain contributor-specific AI disclosures. Earlier project work used GPT-6 Pro and GPT-6-Astra Max; the current integration and checks were developed with Codex.

## Reproduce and update

Standard-library Python **3.10+**:

```sh
python3 verification/run_checks.py
```

For the new witness only:

```sh
python3 verification/verify_round11.py
```

The checks include the exact decoder coefficient matrix, complete rational scalar output map and compensation-read checks, the imported full-size frame/role replay, small exhaustive Gaussian-integer Clifford checks, and rigorous rational moments. They are finite evidence, not an execution of the enormous DFT algorithm. See [verification scope](verification/README.md).

Rebuild the paper, generated result summary and log with Pandoc and pdfLaTeX:

```sh
python3 scripts/build_manuscript.py
```

`--markdown-only` regenerates text without compiling the PDF; `--check` checks registry/certificate agreement and generated text freshness. The [update workflow](results/README.md) explains how to preserve prior artifacts and incorporate a new witness.

## Preserved results

- [Round-six record](results/round6.md), with its unchanged [publication PDF](archive/round6/manuscript.pdf) and source snapshot.
- [Earlier shared-sum record](results/legacy-shared-sum.md), with its unchanged [publication PDF](archive/three-stage/manuscript.pdf).
- [Short core proof](core-proof.pdf), retaining the simpler `5.2e-10` and `5.3e-10` fallbacks.

All previous verification suites remain runnable. Historical audit records apply only to their named constructions.

## Original sources

OpenAI's [#130 Fourier manuscript](https://github.com/openai/math/blob/main/preprints/An-explicit-power-saving-for-the-exact-discrete-Fourier-transform-September-25-2026/main.pdf) supplies the exact-arithmetic model, Fourier compiler and all-length reduction. The network research originates in [#109](https://github.com/openai/math/blob/main/preprints/Integer-multiplication-below-n-log-n-September-23-2026/paper.pdf) and [Douglas Colkitt's community repository](https://github.com/CrocSwap/integer-mult-bounds). Construction-specific sources, immutable commits, licenses and contribution credit are recorded with each version.
