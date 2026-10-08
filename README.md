# An Improved Exponent Bound for the Exact Discrete Fourier Transform

This repository contains a research draft proposing a quantitative refinement of **OpenAI Math Problem #130**, *An explicit power saving for the exact discrete Fourier transform*.

Under the exact-complex-arithmetic, specified-root, and logarithmic-word address model of the original paper, and using its downstream Fourier compilation and all-length reduction, the strongest proposed bound is

$$
T(n)=O\!\left(n(\log n)^{1-\delta}\right),
\qquad \delta=5.5\times10^{-10}.
$$

OpenAI's published headline corollary gives the same form with $\delta=10^{-13}$. This is a **5,500-fold increase in the stated exponent-saving parameter**, **not** a 5,500-fold measured runtime speedup.

> **Research status:** This is a proposed result supported by a written argument and exact-arithmetic computational checks. It has undergone same-assistant adversarial review, **not independent mathematical review or formal verification**. Its novelty and publication priority have not been established. The strongest claim depends on the correctness of the new phase-schedule argument and the upstream results it invokes.

## What's being improved?

The common ingredient in Problems **#109** (integer multiplication) and **#130** (Fourier transforms) is **not an integer-multiplication subroutine**. It is a finite arithmetic network for more efficiently applying tensor powers of a fixed complex two-coordinate transformation:

$$
C=\frac12\begin{pmatrix}1+i&1-i\\1-i&1+i\end{pmatrix}.
$$

The usual tensor-axis method for $C^{\otimes k}$ takes $O(k2^k)$ operations. The network and its recursion give $O(2^k k^\theta)$ for $\theta<1$. OpenAI's #130 paper explicitly reuses the finite complex network from #109, but **does not** import #109's later tape, precision, or integer bit-complexity arguments. The two papers share a mathematical component, not their complete algorithms.

The proposed refinements address that finite network and how its saving propagates through #130's separate all-length Fourier reduction.

## Proposed changes

1. **Ground-size retuning:** Use $h=24$ rather than the original explicit Fourier paper's $h=100$. **This general retuning idea is not claimed as new**: Douglas Colkitt had already investigated the unchanged complex network at $h=25$.
2. **Rank-reduced central correction:** Remove one redundant central coordinate, replacing the readout with an equivalent linear map while preserving arbitrary initial scratch values. This is the simplest independently reviewable new argument.
3. **Unpadded recursive batching:** Recurse over complete batches and handle the bounded remainder directly, instead of padding the role count to a power of two.
4. **Shared-sum correction circuit:** Reuse partial sums for an intersection-two correction. This offers an additional saving but requires the more involved forward and inverse phase-label schedules.

The modifications are separable: concerns about the shared-sum construction do not automatically invalidate the shorter rank-reduction argument.

## Quantitative comparison

| Construction | Critical saving $a=1-\theta$ | Conservative pure-power saving $\delta$ |
| --- | ---: | ---: |
| OpenAI #130 explicit network ($h=100$, padded) | $2.10643843\times10^{-13}$ | $10^{-13}$ (published headline) |
| Original network retuned to $h=24$, padded | $3.95761002\times10^{-10}$ | — |
| Reduced center, original padded batching | $5.22969896\times10^{-10}$ | $5.2\times10^{-10}$ |
| Reduced center, unpadded batching | $5.30775793\times10^{-10}$ | $5.3\times10^{-10}$ |
| Reduced center + shared sums, unpadded batching | $5.51272588\times10^{-10}$ | **$5.5\times10^{-10}$** |

The *critical* saving $a$ initially yields a bound with an additional $(\log\log n)^{4-\theta}$ factor. Any fixed $\delta<a$ absorbs that factor asymptotically. Therefore $\delta$ and $a$ should not be compared as though they were identical. The proposed critical saving is approximately **2,617 times** the original paper's critical saving; that ratio also **does not** indicate a measured runtime speedup.

## What this does *not* claim

- A speedup for ordinary finite-precision FFT implementations or practical-size inputs. The implicit constants are enormous.
- A better **integer multiplication** bit-complexity bound for #109. Carrying these changes into that result would require a separate tape/precision analysis.
- A finite-field, bounded-coefficient, stable numerical, or bit-complexity theorem.
- An independently refereed, Lean-verified, or priority-checked theorem.

## Repository files

| File | Purpose |
| --- | --- |
| [`manuscript.pdf`](manuscript.pdf) | Full proposed $\delta=5.5\times10^{-10}$ argument, including shared sums and phase schedules |
| [`manuscript.md`](manuscript.md) | Markdown version of the full manuscript |
| [`core-proof.pdf`](core-proof.pdf) | Shorter rank-reduced-center argument; $5.2\times10^{-10}$ with original batching and $5.3\times10^{-10}$ with the separate batching lemma |
| [`announcement.md`](announcement.md) | Proposed public announcement / X post |
| [`verification/`](verification/README.md) | Reproducible finite checks, reference certificates, and audit report |
| [`tex/`](tex/) | LaTeX sources for both PDF manuscripts |

The exact-arithmetic checkers and reference certificates live in [`verification/`](verification/README.md). Run `python3 verification/run_checks.py` from the repository root (Python 3.10+; standard library only). Manuscript LaTeX sources are in [`tex/`](tex/). The results are **finite checks, not a Lean proof or independent validation of the entire Fourier theorem**.

## Review priorities

In decreasing order of simplicity:

1. Check the reduced-center matrix identity, arbitrary-scratch cancellation, and retention of the original center gate labels.
2. Check the unpadded-batch recurrence and the charging of leftover work at every recursive level.
3. Check the shared-sum circuit's global role accounting, especially its inverse middle stage, residual orthonormal bases, and tensor lifting.
4. Verify that each claimed finite improvement satisfies #130's complete network interface and propagates through the existing local Fourier compiler and all-length reduction with all costs charged.
5. Check publication priority separately from mathematical correctness.

## Original sources and attribution

- [OpenAI Math repository and manuscript map](https://github.com/openai/math) — [CONTENTS.md](https://github.com/openai/math/blob/main/CONTENTS.md).
- [OpenAI #130: *An explicit power saving for the exact discrete Fourier transform*](https://github.com/openai/math/blob/main/preprints/An-explicit-power-saving-for-the-exact-discrete-Fourier-transform-September-25-2026/main.pdf). In particular, its introduction and Section 2 identify the complex network reused from #109.
- [OpenAI #130 companion: *Finite tensor savings and exact Fourier circuits*](https://github.com/openai/math/blob/main/preprints/Finite-tensor-savings-and-exact-Fourier-circuits-September-25-2026/main.pdf). It gives a separate qualitative nonuniform existence route; the explicit exponent refinement here does not rely on that route.
- [OpenAI #109: *Integer multiplication below n log n*](https://github.com/openai/math/blob/main/preprints/Integer-multiplication-below-n-log-n-September-23-2026/paper.pdf) — original development of the shared finite complex network (see its Proposition 8 and Section 3.5).
- [Douglas Colkitt / @0xdoug: `integer-mult-bounds`](https://github.com/CrocSwap/integer-mult-bounds), especially [`notes/independent-complex.tex`](https://github.com/CrocSwap/integer-mult-bounds/blob/main/notes/independent-complex.tex) for earlier ground-size retuning.

This work is an investigation of quantitative improvements to those results. Attribution of the shared construction and previous retuning is intentional; neither should be presented as an independent discovery here.
