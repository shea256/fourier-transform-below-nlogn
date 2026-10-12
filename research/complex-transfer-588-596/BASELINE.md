# Baseline audit, 2026-10-12

This track compares **uniform exact complex DFT at every positive length**.
The target is one deterministic program, supplied a specified root of unity,
with scalar preparation, array work, and polynomially bounded integer indexing
charged. Complex arithmetic is exact and coefficients are unrestricted. Integer
bit complexity, bounded-coefficient circuits, and floating-point FFT performance
are different questions.

## Primary starting points

OpenAI's [CONTENTS.md](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/CONTENTS.md)
lists both #130 manuscripts. Both PDFs were downloaded and their theorem
statements read at commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

* [An explicit power saving for the exact discrete Fourier transform](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-explicit-power-saving-for-the-exact-discrete-Fourier-transform-September-25-2026/main.pdf), September 25, 2026:
  Theorem 1.1 gives `O(n (log n)^theta (log log n)^(4-theta))` for all
  positive lengths, where the exactly defined `theta` is approximately
  `0.99999999999978935616`. Corollary 1.2 gives saving `10^-13`.
  Corollary 1.3 covers exact convolution. The supplied root has order less
  than `1024 n^3`. PDF SHA-256:
  `670d0115ea2553e65f22167c176d2f31218d4d41726fe4e5702e2b149cad0896`.
* [Finite tensor savings and exact Fourier circuits](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Finite-tensor-savings-and-exact-Fourier-circuits-September-25-2026/main.pdf), September 25, 2026:
  Theorem 1.1 gives `liminf L(n)/(n log2 n) = 0` for exact nonuniform
  linear circuits with prechosen unrestricted coefficients. This is an
  unbounded-subsequence statement with coefficient generation uncharged;
  it is not the all-length baseline. PDF SHA-256:
  `e2165b9f6796f0189292220c7edc0c6e19789bd8329a127a24d404da1e81e06b`.

The stronger uniform follow-up is the comparator theorem in the Lean
development, not just the original `10^-13` abstract. Its statement is retained
in the Fourier comparison checks. Root exploratory notes are not premises.

## Strongest verified comparator baseline

The [exact-DFT leaderboard](https://bigospeedrun.com/exact-dft) lists Nil Mamano's
all-length saving `2555269/2500000000 = 0.0010221076` as Lean verified.
The actual [submission](https://github.com/bigospeedrun/verifier/tree/025396033eede56e3af6e02ed2679ba828381bd5/submissions/dft/nmamano-dft-record)
at verifier commit `025396033eede56e3af6e02ed2679ba828381bd5` proves `Race.bound`
with that exact rational exponent. It uses the #401 entrance-gauge extension,
#377 compressed nine-stage geometry, and Sussman's exact program/recursion and
OpenAI Fourier framework. Those general Lean definitions and proofs are reused
unchanged, except for stripping the submission's import prefix.

Other checked sources do not improve that verified baseline:

* [jacobalansussman/wht-power-saving-lean](https://github.com/jacobalansussman/wht-power-saving-lean/tree/9c94857bbaee886f8649edee0bc2d3c738f9555e):
  E8 all-length saving `0.0008762478`; the earlier #233 instantiation is
  `0.000754736`.
* [eumemic/exact-dft-bounds](https://github.com/eumemic/exact-dft-bounds):
  main's `0.0004856` with log-log overhead, and PR1's approximately `0.0007099`,
  are smaller. The separate `0.000754736` formal result mentioned there is also
  below Mamano's.

Leaderboard HTML was obtained directly when the browsing renderer failed.
It is discovery/provenance evidence; the pinned Lean statement supplies the
mathematical baseline. No scientific-priority inference is made from site dates.

## Newer integer-multiplication witnesses

| Source | Frozen head | Reported integer kappa | Native complex lower bound | Evidence reproduced here |
| --- | --- | ---: | ---: | --- |
| [CrocSwap #588](https://github.com/CrocSwap/integer-mult-bounds/pull/588) | `6d0e53b66c29abd17981881a09eaff41ac862d85` | `0.001602278921983212` | `802425169927850686731 / 500000000000000000000000` | Complete unchanged verifier, exit 0 |
| [CrocSwap #596](https://github.com/CrocSwap/integer-mult-bounds/pull/596) | `7732dd5e46863ff294b5e443661cb9d99abf4e01` | `0.0016127213726553` | `1615326444135573078563 / 10^24` | Complete unchanged verifier, exit 0 |

Both receipts explicitly retain conditional all-size realization, hosting,
precision/tape, and analytic-transfer obligations. Neither native headline is
an existing all-length DFT theorem or full Lean proof. The #596 improvement
also uses helpers ending on hyperplanes, outside the current `GInvE` interface.
The integer leaderboard lagged these source updates. We use the frozen source
and recomputed ledgers, not its rounded display.

The packages pin #568, #569, #571, #575 and #583 dependencies; `replay_upstream.py`
fetches those exact commits and leaves the upstream verifier unchanged. See the
retained source manifest and replay receipts for the full pins and scope.

## Recheck during integration

A fresh fetch of both leaderboards still puts the exact-DFT verified record at
`0.0010221076`. The integer board now also lists:

* [#600](https://github.com/CrocSwap/integer-mult-bounds/pull/600), head
  `dfb7b827990d7b586b3cd778e3d750c050dd4778`, conditional kappa
  `0.001612722852614221`: the #596 providers with a changed native owner map.
* [#601](https://github.com/CrocSwap/integer-mult-bounds/pull/601), head
  `529ab7dcb59d5ea7a5798e9e06cf5b3aee8a1550`, conditional kappa
  `0.001614202339036103`: 46 rather than 38 hyperplane-ended helpers, via
  commuting terminal cleanup gates. Its PR description cites a separate local
  endpoint lemma; it does not supply an all-length DFT theorem.

Their source descriptions and frozen heads were read; they were **not replayed
in full** here. These updates do not change the strongest verified DFT baseline
or supply a direct substitute for the full-ended `GInvE` used in our proof.
Extending that interface is a separate follow-up, not a reason to substitute
either integer headline into the checked Fourier theorem.

### Final refresh, 18:32 UTC

The exact-DFT board still reports the same Lean-verified maximum. The integer
board now lists the following larger **conditional claims**. Their PR bodies
and exact head IDs were read, but these packages were not replayed here:

| PR | Frozen head | Reported integer kappa | New ingredient |
| --- | --- | ---: | --- |
| [#603](https://github.com/CrocSwap/integer-mult-bounds/pull/603) | `c64200242bedc5256dee992de0a0c500be0567d3` | `0.001614217970939911` | #601 owner-map refinement |
| [#604](https://github.com/CrocSwap/integer-mult-bounds/pull/604) | `1b795c5d7dea746ba310572585c0ef067574b4a6` | `0.00162128508944984` | 14 cold helpers per call end in dimension 4 |
| [#607](https://github.com/CrocSwap/integer-mult-bounds/pull/607) | `ddd81bcc0be9c81ba253096a22d2da72dc9f9172` | `0.001620246754858718` | Owner-map refinement of an earlier #604 head |
| [#609](https://github.com/CrocSwap/integer-mult-bounds/pull/609) | `10255d48152ed9f159f7c51028b1fc34a4ccc982` | `0.001622285497914735` | Per-time-Hall owner map on #604 |
| [#610](https://github.com/CrocSwap/integer-mult-bounds/pull/610) | `b7c680ea38b9a25a89fce189bb927b45842362d0` | `0.00162536523418317` | #604 cold words, jp8-heavy dispatch and a new owner map |

#604/#610 build on #601's 46 hyperplane endings and add non-full cold endings.
They cite the local endpoint lemmas in #593/#599; those are not a complete
all-length DFT theorem. The #610 score also uses its native hosting map rather
than our dedicated-bank schedule. Thus none of these reported numbers is a
replacement Fourier exponent in the proved `complex588` theorem. Generalizing
the end-frame interface is the next proof task. The final board extraction is
retained in [verification/leaderboard-2026-10-12.json](verification/leaderboard-2026-10-12.json).
