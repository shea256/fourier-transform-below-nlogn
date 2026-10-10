# Finite Network Improvements for the Exact Discrete Fourier Transform

A living research project on **OpenAI Math Problem #130**, *An explicit power saving for the exact discrete Fourier transform*. We study how improvements to the complex networks developed around integer multiplication (#109) transfer to all-length Fourier bounds.

<!-- current-result:start -->

## Latest paper

**[Read the latest paper (PDF)](manuscript.pdf)** · [Read online (Markdown)](manuscript.md) · [LaTeX source](tex/manuscript.tex)

This is the complete current paper: the reusable Fourier argument, the selected network construction and the improvement history. These links stay the same as the paper is updated; earlier versions are preserved under [archive/](archive/).

Current selection: **[Sussman and Boukhalfa five-stage complex network](results/five-stage-pr233.md)**, recorded 2026-10-09.

```math
T(n)=O\left(n(\log n)^{1-\delta}\right),\qquad \delta=0.000754736.
```

**An incorporated upstream result with a reproduced Lean proof.** The bound comes from Jacob Sussman's five-stage framework and Chafik Boukhalfa's stronger instantiation of the community circuit. Independent human mathematical review remains pending.

The exponent saving is approximately **7.547 billion times** OpenAI's [published headline](https://github.com/openai/math/blob/main/preprints/An-explicit-power-saving-for-the-exact-discrete-Fourier-transform-September-25-2026/main.pdf) of `delta=1e-13`. It is **12.65% above** the [previous selection](results/round11.md) of `delta=0.00067`. These ratios compare exponent parameters, not measured runtimes.

The Fourier saving is chosen below the upstream complex-tensor witness `a=0.0007547361`, leaving a positive gap to absorb the Fourier reduction's overhead. The integer-multiplication headline `kappa` is a separate parameter.

The [finite certificate](verification/certificates/five_stage_reference.json) binds the pinned witness, recursive cost certificate, exact rate and absorption gap to the Lean source. The [Lean reproduction receipt](verification/certificates/five_stage_lean_receipt.json) records the build and theorem/definition comparisons for the all-length DFT and convolution. See [the audit](verification/FIVE_STAGE_AUDIT.md) for its scope and limits.

<!-- current-result:end -->

The model uses exact complex arithmetic, unrestricted coefficients, a specified supplied root of unity, and unit-cost logarithmic-word indexing. Scalar preparation and array organization are included. These are asymptotic exponent improvements; **no practical FFT speedup is claimed**.

## Paper structure and result history

- [Improvement log](IMPROVEMENTS.md): dated results, exact parameters, provenance and changes.
- [Reusable transfer theorem](paper/framework.md): the finite-network contract, recurrence, array adapters, and all-length reduction.
- [Versioned result records](results/README.md): construction arguments and the process for adding future updates.

The paper title and general theorem stay stable as new networks arrive. Each update gets its own record, pinned sources, verifier and reference certificate. A candidate is not promoted by a numerical certificate alone. `results/registry.json` explicitly selects the current result and generates the headline and log.

## What this project contributes

The finite-network improvements belong to their cited authors. This project supplies earlier proposed transfers into #130's uniform array model and additional finite checks. The current update incorporates and reproduces an already published upstream formal Fourier theorem; it does not claim a new exponent of our own. It does not infer a Fourier bound from an integer-multiplication running time or add successive networks' savings together.

We acknowledge **OpenAI** for the original framework and Fourier reduction; **Douglas (Doug) Colkitt** for early network research, the independently sized complex construction that informed our first paper, and community integration; **Rohan Arun** for fixed-basis/corner composition and the weighted-matching precedent explicitly credited by Jain; and **Swapnil Jain** for our adopted round-six, round-ten and round-eleven complex witnesses. This order introduces the research context; it is not a ranking of contributors.

Our adopted Jain constructions also depend on **icekylinx** (batching, frames, covers, paired cubes and retirement reuse), **eumemic** (producers, modules, frames and late compensation), **an664** (completed-core sharing), **James Chang / jamesyc** (birth reuse and terminal compilation), **DaysSky** (carrier extensions), and **Chafik Boukhalfa / chafreaky** (the terminal paired-cube lineage and a related local configuration). **Aurel Prosz / Paureel**, **Avi Eisenberg / ikeboy**, **Zhihao Chen / jacklightChen**, and other earlier contributors retain their specific source credits.

The current bound comes from **Jacob Sussman's** five-stage geometry, certificate framework and formal Fourier development, instantiated with **Chafik Boukhalfa's** stronger PR233 pairing and PR256 program. It retains **icekylinx's** source-assisted flow, **eumemic's** modules and frames, and **Avi Eisenberg's** reconstruction and pairing, with **SovereignSteak** and **hcg890** credited for the cited composition and ledger lineage. The [attribution audit](ATTRIBUTION.md) traces the history and specific contributions. The [source manifest and preserved notices](verification/vendor/five_stage/README.md), [result record](results/five-stage-pr233.md), and [verification audit](verification/FIVE_STAGE_AUDIT.md) give the current witness's provenance and proof boundary.

This work is AI-assisted. Additional verifiers written with the same assistant are not independent mathematical review. The current imported all-length Fourier theorem has a reproduced Lean proof. The earlier Jain arithmetic certificates do not formalize those earlier transfers, and the reusable written exposition has not thereby all been formalized. Preserved upstream notices retain contributor-specific AI disclosures. Earlier project work used GPT-6 Pro and GPT-6-Astra Max; the current integration and checks were developed with Codex.

## Reproduce and update

Standard-library Python **3.10+**:

```sh
python3 verification/run_checks.py
```

For the selected five-stage finite witness only:

```sh
python3 verification/verify_five_stage.py
```

Reproduce the Lean proof separately with Lean 4.34.1 installed:

```sh
python3 verification/verify_five_stage_lean.py \
  --work-dir /tmp/fourier-five-stage-rebuild --lake lake --threads 2
```

The full suite includes the five-stage program, histogram and finite-fill rate checks, followed by registry validation of the retained Lean receipt and logs. It also retains the earlier exact decoder coefficient matrix, complete rational scalar output map and compensation-read checks, the imported full-size frame/role replay, small exhaustive Gaussian-integer Clifford checks, and rigorous rational moments. The small Clifford checks run in the round-ten suite and support the round-ten and round-eleven arguments. These are finite checks of the constructions; the full DFT algorithm is not executed. The main Python runner does not execute Lean; the separate reproduction command above does. See [verification scope](verification/README.md).

Rebuild the paper, generated result summary and log with Pandoc and pdfLaTeX:

```sh
python3 scripts/build_manuscript.py
```

`--markdown-only` regenerates text without compiling the PDF; `--check` checks registry/certificate agreement and generated text freshness. The [update workflow](results/README.md) explains how to preserve prior artifacts and incorporate a new witness.

## Preserved results

- [Round-eleven record](results/round11.md), with its [unchanged publication snapshot](archive/round11/README.md).
- [Round-ten record](results/round10.md), with its [assembled draft snapshot](archive/round10/README.md), captured before incorporating round eleven in the same update.
- [Round-six record](results/round6.md), with its unchanged [publication PDF](archive/round6/manuscript.pdf) and source snapshot.
- [Earlier shared-sum record](results/legacy-shared-sum.md), with its unchanged [publication PDF](archive/three-stage/manuscript.pdf).
- [Short core proof](core-proof.pdf), retaining the simpler `5.2e-10` and `5.3e-10` fallbacks.

All previous verification suites remain runnable. Historical audit records apply only to their named constructions.

## Original sources

OpenAI's [#130 Fourier manuscript](https://github.com/openai/math/blob/main/preprints/An-explicit-power-saving-for-the-exact-discrete-Fourier-transform-September-25-2026/main.pdf) supplies the exact-arithmetic model, Fourier compiler and all-length reduction. The network research originates in [#109](https://github.com/openai/math/blob/main/preprints/Integer-multiplication-below-n-log-n-September-23-2026/paper.pdf) and [Douglas Colkitt's community repository](https://github.com/CrocSwap/integer-mult-bounds). Construction-specific sources, immutable commits, licenses and contribution credit are recorded with each version.
