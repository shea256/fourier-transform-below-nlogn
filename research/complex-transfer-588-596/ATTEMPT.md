# Attempts and proof map

## 1. Literal native transfer: rejected by the existing interface

The native #588/#596 schedules host helpers in idle data registers. Mamano's
Lean proof instead uses dedicated banks. Locally, both newer constructions also
mutate source roles and precondition target roles. A literal #588 conversion
fails the unchanged Python `gx.py` E3 condition at gate A97 (`s -> x` before
scatter). Checking its clean source response or its histogram is insufficient
to conclude that the existing invocation theorem applies.

#596 has another mismatch: 38 helpers end at rank 8 instead of 9. `GInvE`
requires helper endpoints at the full frame. A literal #596 lowering also failed
the histogram-preservation check. No #596 DFT exponent is claimed from that
attempt, and no checker condition was weakened to admit it.

## 2. Source copies in dedicated banks

Use #588's `atm3` local provider uniformly in all 72 calls. Introduce 112 helpers,
one per mutable source. Initially copy the real source into its helper, perform
all native source reads/writes on that helper, and leave the real sources
read-only. Charge each new helper's rank-1 entrance climb and the real source's
remaining rank-8 climb. Terminal native cleanup now writes only helpers;
invocation helpers need not be restored, so these terminal scalar adds can be
omitted **after all charged final climbs**. Every source/target output and the
movement histogram is checked again after this transformation.

Target preconditioning `P` commutes with phase A. Moving it after scatter changes
the scatter matrix to `P^-1 S`; the preconditioner remains explicitly in B.
Nonzero register scales are absorbed into rational register units. This is a
certificate construction: the resulting full rational circuit and frame labels,
not a promise of algebraic equivalence, are sent to the existing Lean checks.

The historical Python E4 shortcut rejects cycles among target shears even when
their product is the identity. The existing Lean `GS.yCheck` checks the actual
product. Our Python preflight now does the same exact rational calculation and
chooses packed units `(ux, us, uy) = (1, 8, 8)`. It does not change `GS.yCheck`
or any soundness theorem. Lean checks all source batches, all target basis
vectors, and all 228 entering-helper basis vectors. Labels, centre frames,
frame nesting, and movement counts are checked separately by the kernel.

The local parameters are:

* `h = 9`, `v = 112`, `R = 616`, centre-copy rank sum `cst = 64`.
* Entrance rank sum `476`; charged movement `616*9 + 2*112*8 + 64 - 476 = 6924`.
* Local histogram: `{1:2596, 2:492, 3:280, 4:232, 5:56, 6:56, 8:120}`.
* Residual helper widths: `{4:48, 5:8, 7:32, 8:140, 9:388}`.

Keeping the now-unnecessary terminal helper cleanup also passed the rational
identities but inflated uncancelled checker digits. Dropping that cleanup is
valid because none of those terminal gates writes a source or target; it is not
a claim that native cleanup may generally be ignored.

## 3. Explicit cyclic bank packing

An initial chronological greedy schedule used 5,340 banks and priced at an
arithmetic root about `0.001223612103072`. A denser construction partitions the
616 helper widths into 70 bins of capacity 73. For each bin create 72 banks.
At call `t`, helper number `j` within a bin uses bank `(t+j) mod 72` in that bin.
Each call is injective, and each bank sees exactly one copy of every helper in
its bin over the 72 calls. The generated literal table is independently summed
and then checked by the unchanged Lean `GX.schedK` predicate.

This uses 5,040 helper banks. Padding is 2,520 zeroes, 2,448 rank-1 blocks and
72 rank-8 blocks. `W = 64*112 + 5040 = 12208`, `m = 73`, and the deficit is
`64*112 - 72*64 = 2560`. Every physical bank is charged, including padding.

The #401 unit invoice is

    H = 72 H_local + 112 H_idle + H_padding,
    H_idle = {8:48, 16:32, 32:32, 48:32}.

It evaluates to

    {1:189360, 2:35424, 3:20160, 4:16704, 5:4032,
     6:4032, 8:14088, 16:3584, 32:3584, 48:3584}.

The total rank is `888624 = 12208*73 - 2560`; all child ranks are strictly below
73. A separate rational interval calculation puts the uncorrected moment root
in `(0.001233169825152, 0.001233169825153)`.

The actual engine premise includes finite fill with `s = 40`:

    (1 - 2^-40) * sum_r H[r]*(r/73)^(1-a)/12208
      + 2^-40 * ((72/73)^(1-a) + (1/73)^(1-a)) < 1.

Sussman's rational proof generator certifies this at
`a = 12331686/10^10`, with relative rational slack about `5.00074e-11`.
The proposed Fourier exponent uses `delta = 12331685/10^10`, leaving a positive
`10^-10` gap for the all-length reduction's log-log overhead. The standalone
moment root is not the final theorem's exponent.

With the same source-copy and cyclic-packing method, the other #588 providers
price lower: `ck` about `0.001229398806147`, `jp8` about `0.001231728936726`.
These tests justify choosing `atm3` within this menu; they do not prove global
optimality among all networks or packings.

## Universal proof dependencies

`C588Cert` + `C588ScalOK` + `C588EChk` -> `GXD.ginvOf` -> `C588Glue401.ginv`.
The literal bank certificate -> `BankSched.ofTab_fits`; its invoice and the
kernel-checked rate lemma feed `GX.engine_of_ginv_401` for every required mode,
colour and input batch. `FourierC588.Seam` exposes OpenAI's tensor-program
interface; the renamed Fourier chain supplies all-length DFT and convolution.
Those latter assembly and statement comparisons must pass before the candidate
is recorded as a theorem. Same-agent recalculation is not independent review.
