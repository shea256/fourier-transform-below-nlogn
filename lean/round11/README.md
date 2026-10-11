# Lean proof: exact DFT of every length with saving δ = 6.7e-4, from the round-eleven circuit

This directory is a Lean 4 project that proves OpenAI's all-length exact discrete Fourier transform statement
(openai/math, family 130, `lean/ComparatorChallenges/UniformFourier.lean`) with the exponent

    1 - 6700000/10^10,   i.e.   T(n) = O(n (log n)^(1 - δ)),  δ = 6.7e-4,

the saving of this repository's [round-eleven result](../../results/round11.md). The helper circuit is the one that
result adopted: Swapnil Jain's round-eleven complex word (dead-copy recycling on the paired-cube word). The proof is
checked by Lean's kernel and uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

**What is and is not formalized.** The circuit is ours by adoption (Jain's). The layout, the certified-program
engine, the frame lemma and the certificate checker with its soundness proofs are Jacob Sussman's
([wht-power-saving-lean](https://github.com/jacobalansussman/wht-power-saving-lean)), as extended by Chafik
Boukhalfa; the step from the kernel program to every length is OpenAI's reduction. The circuit is placed in
Sussman's five-stage bridged layout, not in the three-stage layout of our written transfer, so this is a machine
check of the round-eleven *saving* with the round-eleven *circuit*, not a formalization of our written argument.
In that layout the same circuit certifies a kernel saving of 7150885/10^10; the Fourier statement is proved at the
round-eleven value 6.7e-4, below it.

## Theorems

| theorem | statement module | proof module |
|---|---|---|
| `OAI.PowerSaving.transform_mainX : DFTGoalX` | `Work.FourierR11.UniformFourierChallenge` | `Work.FourierR11.Main` |
| `OAI.PowerSaving.convolution_mainX : ConvGoalX` | same | same |
| `OAI.PowerSaving.WHT.wht_main_block_B2GR11x` (kernel, `1 - 7150885/10^10`) | `Work.GCert.Data.ChallengeB2GR11x` | `Work.GCert.Data.SolutionB2GR11x` |

The Fourier challenge is OpenAI's challenge file with the exponent `1 - 1/(10^(13:ℕ))` replaced by
`1 - 6700000/(10^(10:ℕ))`, seven names given the suffix `X` and a header comment; nothing else differs.

## Reproduce

Needs `elan`, about 10 GB of disk and 16 GiB of memory (one certificate module peaks at 10.5 GB).

    cd lean/round11
    scripts/build_and_check.sh build-logs        # Mathlib cache, build, axiom report, statement comparisons
    python3 scripts/check_provenance.py          # upstream files byte-identical to the vendored archive
    python3 converter/check_conversion.py        # certificate from Jain's word; ledger and negative controls
    python3 tools/gx/regen_check.py tools/certificate/gcert1-p11-jain-r11.json.gz R11 B2GR11
    python3 tools/fourier/regen_checkR11.py      # generated Lean files reproduced byte for byte

`build_and_check.sh` ends with `ALL CHECKS PASSED` only if every module builds, no axiom report mentions
`sorryAx`, `tools/Compare.lean` passes for the WHT theorem and for both Fourier theorems, and it **fails** for the
negative control `Work.FourierR11Neg.UniformFourierChallenge` (the same challenge with saving 6700001/10^10).

## How the certificate was made

1. `converter/word_to_gcert.py` lowers Jain's frozen word
   (`../../verification/vendor/jain_round11/word.json.gz`) to Sussman's certificate format gcert/1: one
   explicit program, 2,640 port registers and 10,282 slots, 43,508 gates. It follows the conventions of the
   upstream emitter `tools/emit/gcert_emit.py` and the semantics of Jain's own checker.
2. Sussman's reference checker `gx.check1` accepts it (every frame nesting and the exact scalar identity).
3. Its block ledger, in Jain's three-stage convention, equals Jain's claimed child histogram rank by rank,
   with W = 12,922; that histogram is what certifies his 6.7147467e-4.
4. Five corrupted conversions (gauge-read sign, sink-write sign, skipped or sign-flipped recycling mix,
   dropped pre-shear) are each rejected.
5. The unmodified generators `tools/gx/gxgen.py` and `gxrate.py` turn it into the Lean data and check modules;
   `tools/fourier/mkchainR11.py` (mkchain233.py with new constants) makes the Fourier chain.

## Measured

On 2026-10-11, Linux x86_64, 8 cores, 16 GiB, Lean 4.34.1, Mathlib `d13f23b` from its compiled cache, every
project module compiled from source, `scripts/build_and_check.sh` ran from 18:02 to 18:54 UTC and printed
`ALL CHECKS PASSED`. Its log, the axiom report and the three comparison outputs are in `receipt/`; `receipt/tested-files.SHA256`
lists the 359 files of that run (README.md, NOTICE.round11, `scripts/check_provenance.py` and `receipt/` were added afterwards).
Longest module in this run: gate replay `Gen.R11Seg3`, about 10 minutes. Memory was not sampled in this run; in an
earlier build of the same modules the scalar replays `Gen.R11Scal0`/`Scal1` peaked at 10.5 GB.

## Not done

The official `comparator` and `leanchecker` were not run; `tools/Compare.lean` is Sussman's comparison script.
No human has reviewed these additions. The round-six result (δ = 7.3e-5) is not covered: its circuit is in a
different format and needs its own converter.

## Credits

OpenAI (model, Fourier reduction, the 89 files under `OAI/`); Jacob Sussman (five-stage layout, engine, frame
lemma, certificate format, checker and soundness proofs, generators, `Compare.lean`); Chafik Boukhalfa
(fourth-result emitter and Fourier chain this adapts); Swapnil Jain (the round-eleven circuit) and the
CrocSwap/integer-mult-bounds contributors behind it (see [ATTRIBUTION.md](../../ATTRIBUTION.md)). See `NOTICE`
(upstream, unchanged) and `NOTICE.round11` (what this directory adds). The additions were developed with
Anthropic Claude (Claude Code).
