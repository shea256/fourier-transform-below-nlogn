# An Improved Exponent Bound for the Exact Discrete Fourier Transform

The fast Fourier transform has computed the length-`n` discrete Fourier transform in `O(n log n)` operations since 1965. In September 2026, **OpenAI Math Problem #130** (*An explicit power saving for the exact discrete Fourier transform*) showed that the exact transform can beat that bound by a small power of `log n`, with a published saving of `1e-13` in the exponent. This repository contains a research draft proposing a much larger saving.

Under #130's exact-complex-arithmetic, specified-root, and logarithmic-word address model, the proposed all-length bound is

```math
T(n) = O\left( n (\log n)^{1-\delta} \right), \qquad \delta = 7.3 \times 10^{-5}
```

where `T(n)` is the cost of computing the exact DFT of a length-`n` input.

> **Research status:** A written argument and exact finite checks support this proposed result. Independent mathematical review and end-to-end formal verification remain outstanding. The external Lean source checks numerical certificates and the integer-multiplication parameter assembly; it does not formalize this Fourier theorem. The earlier, separately reviewable result is preserved as a fallback.

> **This is not a faster FFT.** The result is an asymptotic exponent. The factor `(log n)^delta` only reaches 2 when `log n` is around `2^13,700`, far beyond any input that could exist. No practical FFT speedup, finite-precision stability, bounded-coefficient theorem, or new integer-multiplication bound is claimed.

## Who did what

- **The network:** Swapnil Jain's round-six complex network, building on work by Douglas Colkitt, icekylinx, eumemic, and Aurel Prosz / Paureel. The network improvements belong to their cited authors. The source is pinned to [`f2176bc`](https://github.com/Swapnil-jain/integer-mult-kappa/tree/f2176bc1124821bf17eb63725bd366d7bdc020a3).
- **This draft:** a proposed transfer of that network into the Fourier paper's uniform array model, plus additional finite checks.
- **AI assistance:** this draft was developed with GPT-6 Pro and GPT-6-Astra Max. The full record is in the manuscript and the [external NOTICE](verification/vendor/jain_round6/NOTICE).

## Quantitative comparison

| Construction                                   | Tensor saving                               | Proposed or published pure-power Fourier saving |
| ---------------------------------------------- | ------------------------------------------- | ----------------------------------------------- |
| OpenAI #130 explicit construction              | Critical saving approximately `2.10644e-13` | `1e-13` (published headline)                    |
| Earlier reduced-centre fallback                | Critical saving approximately `5.22970e-10` | `5.2e-10`                                       |
| Earlier reduced centre with remainder batching | Critical saving approximately `5.30776e-10` | `5.3e-10`                                       |
| Earlier shared-sum construction                | Critical saving approximately `5.51273e-10` | `5.5e-10`                                       |
| Attributed round-six complex network           | **Strict witness `a=7.3852222e-5`**         | **`delta=7.3e-5`**, using the proposed transfer |

These are asymptotic exponent parameters, **not measured runtime speedups**. The earlier construction's gains are not added to the imported network's saving.

The new tensor value is a certified strict witness, not the critical root. It gives a bound with an additional `(log log n)^(4-theta)` factor, where `theta=1-a`. Choosing `delta<a` absorbs that factor. The certificate verifies both the strict moment inequality and the positive gap `a-delta=8.52222e-7`.

## The construction

The common ingredient in Problems #109 and #130 is a finite network for tensor powers of

```math
C = \frac{1}{2} \begin{pmatrix} 1+i & 1-i \\ 1-i & 1+i \end{pmatrix}
```

It is not an integer-multiplication subroutine. The new construction applies the same tensor transform to arbitrary inputs, while grouping each residual block into one recursive call. Three features carry the improvement:

- **Whole-residual batching:** the pair-exclusion producer shares the disjointness computation.
- **Two-stage topology:** the two stages use `m=h^2=576`.
- **Copied-centre scheduling:** retained centres supply readouts through temporary copies whose transformations are explicitly charged.

The [manuscript](manuscript.md) gives the two-stage endpoint correction, linear-time array layout, unequal-width recurrence with incomplete batches, and transfer through #130's existing compiler and all-length reduction. Integer-specific precision, tape-layout and Gaussian-resampling improvements are not dependencies of this transfer.

## Verification

Run with standard-library Python **3.10+**:

```
python3 verification/run_checks.py
```

The checks rebuild all `4,096,576` local coefficient entries, check binary labels and actual auxiliary frame paths in both orientations, reconstruct the complete child-width histogram, and certify the moment using exact rational logarithm bounds. They also test the scalar and endpoint identities and reject missing-copy, missing-endpoint and excessive-saving controls. The earlier suites continue to run and match their original reference certificates.

The checks are finite evidence. They are not an independent referee report or an execution of the enormous complete DFT algorithm.

Rebuild the PDF and LaTeX with `python3 scripts/build_manuscript.py` (requires Pandoc and pdfLaTeX).

## Where review is most needed

1. The copied-read schedule.
2. The two-stage data-frame interfaces and endpoint correction.
3. The linear-time full-residual layout.
4. The recurrence's remainder costs.

The [earlier audit](verification/AUDIT.md) applies to the archived three-stage result. It is not an audit of this new theorem.

## Files

| File | Purpose |
| ---- | ------- |
| [manuscript.pdf](manuscript.pdf), [manuscript.md](manuscript.md) | Proposed `delta=7.3e-5` argument and attribution |
| [tex/manuscript.tex](tex/manuscript.tex) | PDF source |
| [core-proof.pdf](core-proof.pdf) | Unchanged short `5.2e-10` / `5.3e-10` fallback |
| [archive/three-stage/](archive/three-stage) | Unchanged earlier `5.5e-10` manuscript, PDF and LaTeX source |
| [verification/README.md](verification/README.md) | Reproduction and exact scope of the checks |
| [verification/ROUND6_AUDIT.md](verification/ROUND6_AUDIT.md) | Review record for this transfer |
| [verification/vendor/jain_round6/SOURCE.json](verification/vendor/jain_round6/SOURCE.json) | External commit pin and SHA-256 manifest |
| [announcement.md](announcement.md) | Draft announcement |

## Sources

The shared network originates in OpenAI's [#109 manuscript](https://github.com/openai/math/blob/main/preprints/Integer-multiplication-below-n-log-n-September-23-2026/paper.pdf). The transfer uses the separate [#130 explicit Fourier manuscript](https://github.com/openai/math/blob/main/preprints/An-explicit-power-saving-for-the-exact-discrete-Fourier-transform-September-25-2026/main.pdf), especially Proposition 4.2 and Section 5.4.

The new finite construction is [Swapnil Jain's round-six complex network](https://github.com/Swapnil-jain/integer-mult-kappa/tree/f2176bc1124821bf17eb63725bd366d7bdc020a3/independent/complex-twostage), building on Douglas Colkitt's framework and prior contributions including icekylinx's [whole-residual batching](https://github.com/CrocSwap/integer-mult-bounds/pull/10) and [copied centres](https://github.com/CrocSwap/integer-mult-bounds/pull/36), eumemic's full complex batching, and Aurel Prosz / Paureel's two-stage topology and endpoint correction. Full attribution and licenses are retained in the manuscript and the [external NOTICE](verification/vendor/jain_round6/NOTICE).
