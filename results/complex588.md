## 6. PR588 circuit in the gauged nine-stage Fourier layout

### 6.1 Statement and comparison

One fixed deterministic program computes the exact DFT at every positive length
with saving `delta = 12331685/10^10 = 0.0012331685`, in OpenAI's exact complex
arithmetic RAM model. Scalar preparation, array and index work, and the
specified-root interface are included. A companion theorem proves exact
convolution. Coefficients are unrestricted; integer indices have a polynomial
bound and logarithmic-size words. No floating-point, bit-complexity or practical
crossover claim follows.

The all-length saving is about **20.65% above** the strongest verified baseline
we found, Nil Mamano's `2555269/2500000000 = 0.0010221076`, from the pinned Big O
Speedrun submission. It is a new instantiation assembled in this project, not
a theorem already contained in CrocSwap PR588. The comparison concerns the
logarithmic exponent, not measured speed.

The proof is in [lean/complex588](../lean/complex588/). The theorems
`OAI.PowerSaving.transform_mainC588`, `convolution_mainC588`, and
`RAM.hillsC588_program` report only `propext`, `Classical.choice` and `Quot.sound`.
DFT and convolution pass the full OpenAI statement/dependency comparison; a
one-unit-stronger challenge fails. The official comparator also accepts the
exported proof in both nanoda and Lean's kernel. Human mathematical review
remains pending.
The [verification audit](../verification/COMPLEX588_AUDIT.md) records the exact
scope, build and independent-kernel status.

### 6.2 Construction and exact invoice

The local provider is `atm3` from Jeremy Kothe's PR588 at commit
`6d0e53b66c29abd17981881a09eaff41ac862d85`. It incorporates the cited community
entrance promotions, cold kernels, joint prefixes and frame coalescences.
We introduce 112 source-copy helpers so its mutable sources fit the existing
invocation interface. Target preconditioning is moved across scatter with its
inverse applied to the scatter matrix; rational register units absorb scales.
The resulting certificate is checked in full by the unchanged Lean predicates.

The local parameters are `h=9`, `v=112`, `R=616`, entrance rank sum `476`, and
eight rank-8 centre copies (`cst=64`). Its histogram is
`{1:2596, 2:492, 3:280, 4:232, 5:56, 6:56, 8:120}`, with total rank `6924`.
The 112 extra source-copy helpers and the remaining rank-8 climbs of the real
sources are fully charged. Terminal cleanup now affects helpers only and is
omitted after the final charged climbs; Lean checks all required outputs and
dirty-helper conditions after this change.

Place this circuit in all 72 calls of the #401/#377 dedicated-bank layout. A
cyclic bank schedule packs the 616 residual helper widths into 70 bins of
capacity 73 and replicates each bin 72 times. Within a bin, helper position `j`
uses bank `(t+j) mod 72` in call `t`. The literal table is injective in every
call and satisfies every bank's exact load equation, checked by Lean.

There are 5,040 helper banks, `W=12208` live roles and `m=73` coordinates per
unit. The fully charged global histogram is:

| Rank | Count | Rank | Count |
| ---: | ---: | ---: | ---: |
| 1 | 189360 | 6 | 4032 |
| 2 | 35424 | 8 | 14088 |
| 3 | 20160 | 16 | 3584 |
| 4 | 16704 | 32 | 3584 |
| 5 | 4032 | 48 | 3584 |

Its total rank is `888624 = 12208*73 - 2560`, and every child rank is below 73.
The native integer witness's idle-data hosting has been replaced by the explicit
dedicated banks; no unproved hosting lemma is an assumption of this theorem.

### 6.3 Rate and all-length transfer

An exact rational interval calculation brackets the ordinary moment root
between `0.001233169825152` and `0.001233169825153`. The formal engine requires
a stricter finite-fill inequality, with fill parameter `s=40`. Its rational
Lean certificate proves that premise at `a=12331686/10^10`. The Fourier saving
is `delta=a-10^-10`, absorbing the all-length reduction's overhead.

The invocation checks, bank table, invoice and rate feed the unchanged
`GX.engine_of_ginv_401`. The resulting tensor-program interface is substituted
into the existing OpenAI all-length reduction. The full challenge comparison
checks its original computational model and quantifiers, not just a displayed
asymptotic formula. Finite Python checks alone are not used to assert this
universal conclusion.

### 6.4 Provenance and alternatives checked

The full unchanged PR588 and PR596 verifiers passed locally. PR596 reports a
larger native complex exponent, but its hyperplane endpoints and native hosting
scheme do not fit the reused Lean interface. Its headline is not claimed here.
Within the source-copy and cyclic-bank construction tested here, PR588's other
providers `ck` and `jp8` price below `atm3`. No global optimality claim is made.

The source circuit belongs to its credited upstream authors. Sussman supplies
the formal engine/checkers; Dugongue and jacklightChen the #401/#377 geometry;
Mamano's submission supplies the published gauged Lean extension; OpenAI supplies
the model and Fourier reduction. This project's contribution is the new checked
instantiation, conversion, bank schedule and verification. Full predecessor
credits and AI disclosures are preserved in `lean/complex588/NOTICE.complex588`
and its third-party notices.

The scripts regenerate all 63 new Lean modules byte for byte. The other 291
dependency modules match the pinned prior submission after reversing the import
prefix change. Reproduction commands and failed attempts are retained in
`research/complex-transfer-588-596/`; the source manifest and hashed check logs
bind the selected result to the exact proof bundle.
