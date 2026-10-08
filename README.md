# An Improved Exponent Bound for the Exact Discrete Fourier Transform

This repository contains a research draft proposing a quantitative refinement of **OpenAI Math Problem #130**, *An explicit power saving for the exact discrete Fourier transform*.

Under its exact-complex-arithmetic, specified-root, and logarithmic-word address model, the updated proposed all-length bound is

$$
T(n)=O\!\left(n(\log n)^{1-\delta}\right),
\qquad \boxed{\delta=7.3\times10^{-5}}.
$$

The update transfers **Swapnil Jain's round-six complex network**, including attributed whole-residual batching, two-stage topology and copied-centre scheduling, into the Fourier paper's uniform array model. The source is pinned to [`f2176bc`](https://github.com/Swapnil-jain/integer-mult-kappa/tree/f2176bc1124821bf17eb63725bd366d7bdc020a3). The network improvements belong to their cited authors; this draft supplies a proposed Fourier transfer and additional finite checks.

> **Research status:** A written argument and exact finite checks support this proposed result. Independent mathematical review and end-to-end formal verification remain outstanding. The external Lean source checks numerical certificates and the integer-multiplication parameter assembly; it does not formalize this Fourier theorem. The earlier, separately reviewable result is preserved as a fallback.

## What changed

The common ingredient in Problems #109 and #130 is a finite network for tensor powers of

$$
C=\frac12\begin{pmatrix}1+i&1-i\\1-i&1+i\end{pmatrix}.
$$

It is not an integer-multiplication subroutine. The new construction applies the same tensor transform to arbitrary inputs, while grouping each residual block into one recursive call. Its pair-exclusion producer shares the disjointness computation; its two stages use `m=h^2=576`; and retained centres supply readouts through temporary copies whose transformations are explicitly charged.

The [manuscript](manuscript.md) gives the two-stage endpoint correction, linear-time array layout, unequal-width recurrence with incomplete batches, and transfer through #130's existing compiler and all-length reduction. Integer-specific precision, tape-layout and Gaussian-resampling improvements are not dependencies of this transfer.

## Quantitative comparison

| Construction | Tensor saving | Proposed or published pure-power Fourier saving |
| --- | ---: | ---: |
| OpenAI #130 explicit construction | Critical saving approximately `2.10644e-13` | `1e-13` (published headline) |
| Earlier reduced-centre fallback | Critical saving approximately `5.22970e-10` | `5.2e-10` |
| Earlier reduced centre with remainder batching | Critical saving approximately `5.30776e-10` | `5.3e-10` |
| Earlier shared-sum construction | Critical saving approximately `5.51273e-10` | `5.5e-10` |
| Attributed round-six complex network | **Strict witness `a=7.3852222e-5`** | **`delta=7.3e-5`**, using the proposed transfer |

The new tensor value is a certified strict witness, not the critical root. It gives a bound with an additional `(log log n)^(4-theta)` factor, where `theta=1-a`. Choosing `delta<a` absorbs that factor. The certificate verifies both the strict moment inequality and the positive gap `a-delta=8.52222e-7`.

The proposed Fourier exponent saving is about **132,727 times** the previous `5.5e-10` value, and **730,000,000 times** OpenAI's published `1e-13` headline. These compare asymptotic exponent parameters, **not measured runtime speedups**. The earlier construction's gains are not added to the imported network's saving.

## Verification and files

Run with standard-library Python **3.10+**:

```sh
python3 verification/run_checks.py
```

Rebuild the current PDF and LaTeX with `python3 scripts/build_manuscript.py` (requires Pandoc and pdfLaTeX).

The new checks rebuild all `4,096,576` local coefficient entries, check binary labels and actual auxiliary frame paths in both orientations, reconstruct the complete child-width histogram, and certify the moment using exact rational logarithm bounds. They also test the scalar and endpoint identities and reject missing-copy, missing-endpoint and excessive-saving controls. The earlier suites continue to run and match their original reference certificates.

| File | Purpose |
| --- | --- |
| [manuscript.pdf](manuscript.pdf), [manuscript.md](manuscript.md) | Updated proposed `delta=7.3e-5` argument and attribution |
| [tex/manuscript.tex](tex/manuscript.tex) | Updated PDF source |
| [core-proof.pdf](core-proof.pdf) | Unchanged short `5.2e-10` / `5.3e-10` fallback |
| [archive/three-stage/](archive/three-stage/) | Unchanged earlier `5.5e-10` manuscript, PDF and LaTeX source |
| [verification/README.md](verification/README.md) | Reproduction and exact scope of the checks |
| [verification/ROUND6_AUDIT.md](verification/ROUND6_AUDIT.md) | Review record for this transfer |
| [verification/vendor/jain_round6/SOURCE.json](verification/vendor/jain_round6/SOURCE.json) | External commit pin and SHA-256 manifest |
| [announcement.md](announcement.md) | Updated draft announcement |

The checks are finite evidence, not an independent referee report or an execution of the enormous complete DFT algorithm. No practical FFT speedup, finite-precision stability, bounded-coefficient theorem, or new integer-multiplication bound is claimed.

## Sources and review priorities

The shared network originates in OpenAI's [#109 manuscript](https://github.com/openai/math/blob/main/preprints/Integer-multiplication-below-n-log-n-September-23-2026/paper.pdf). The transfer uses the separate [#130 explicit Fourier manuscript](https://github.com/openai/math/blob/main/preprints/An-explicit-power-saving-for-the-exact-discrete-Fourier-transform-September-25-2026/main.pdf), especially Proposition 4.2 and Section 5.4.

The new finite construction is [Swapnil Jain's round-six complex network](https://github.com/Swapnil-jain/integer-mult-kappa/tree/f2176bc1124821bf17eb63725bd366d7bdc020a3/independent/complex-twostage), building on Douglas Colkitt's framework and prior contributions including icekylinx's [whole-residual batching](https://github.com/CrocSwap/integer-mult-bounds/pull/10) and [copied centres](https://github.com/CrocSwap/integer-mult-bounds/pull/36), eumemic's full complex batching, and Aurel Prosz / Paureel's two-stage topology and endpoint correction. Full attribution, licenses, and recorded AI assistance are retained in the manuscript and the [external NOTICE](verification/vendor/jain_round6/NOTICE).

Review should prioritize the copied-read schedule, two-stage data-frame interfaces and endpoint correction, the linear-time full-residual layout, and the recurrence's remainder costs. The [earlier audit](verification/AUDIT.md) applies to the archived three-stage result; it is not an audit of this new theorem.
