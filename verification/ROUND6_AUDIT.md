# Review of the proposed round-six Fourier transfer

**Date:** October 8, 2026.  
**Result under review:** Proposed `delta=7.3e-5` in the exact arithmetic/root/address model of OpenAI #130.  
**Review status:** Same-assistant mathematical review and additional finite checks. No independent mathematical review, full theorem formalization, or practical runtime claim.

## Sources and construction boundary

The numerical network is pinned to Swapnil Jain's `integer-mult-kappa`, commit `f2176bc1124821bf17eb63725bd366d7bdc020a3`. Nine unmodified source, certificate and attribution files are recorded in [vendor/jain_round6/SOURCE.json](vendor/jain_round6/SOURCE.json). The original Apache-2.0 license and NOTICE are preserved.

The written endpoint and copy arguments were also checked against icekylinx's PR #36, commit `11817ccacb564bb7f98789c20dc11d3fece207e3`, and the whole-residual interface against PR #10, commit `62691e3`. The original Fourier paper's Lemmas 2.2 and 2.5, Proposition 2.4, Theorem 2.6, Proposition 4.2 and Section 5.4 were inspected. The Fourier compiler and all-length reduction are invoked, not independently re-proved.

This update replaces the finite network rather than adding the old construction's gains to the imported result. It does not use Jain's integer-specific epsilon stack, bit-interchange bound, Gaussian recovery or tape precision analysis.

## Mathematical issues examined

- **Arbitrary scratch:** The source-dependent identity is `JLV=I`. The old/new readout difference cancels arbitrary old scratch without imposing the omitted-total relation on it. Every mixer gate is a reversible shear.
- **Copied centres:** A retained carrier is a distinct terminal output use. Forward reads use a copy moved from `U` to zero while the original moves directly to the full frame for cleanup. The complementary inverse schedule advances the original first, then copies it for the read. Both copy transforms are included in the histogram.
- **Two-stage endpoint:** The physical outputs are `A=-Fy` and `B=FT^-2 x+Ey`. One paid inverse-`T` call on a copy of `A` cancels `Ey`. Since `T^2=R_u`, a final address translation produces `Fx`. All auxiliary source/sink quotients remain `F`.
- **Residual geometry:** Local paths are checked with actual symmetric binary projectors. Nondegenerate, nonalternating residuals have orthonormal bases. Exterior and interstage data residuals have the stated tensor-complement forms and explicit norm-one witnesses outside the triple supports.
- **Whole-residual calls:** One simultaneous binary basis change collects all residual directions into `rf` bits. Inverse factors use `C^-1=XC`, so translations suffice. The array model avoids an uncharged per-entry scan through columns by the prefix traversal of the layout lemma.
- **Remainders:** Complete groups of `W` fibers recurse; fewer than `W` remaining fibers are handled directly. Their normalized work is bounded because every child has `r<m`. A strict weighted moment proves the unequal-width recurrence by strong induction.
- **All-length transfer:** The tensor routine has the arbitrary-input, scalar-preparation, movement and word-address guarantees used in #130's Proposition 4.2. The existing all-length estimate then permits every fixed `delta<a`; the witness here keeps a positive gap.

## Finite evidence

[verify_round6.py](verify_round6.py) rebuilds the support DAG, full local coefficient matrix, compiled input map and physical auxiliary schedules, then matches the histogram to two external representations. It checks the rank mass `119453132304`, deficit `1858032`, maximum child width `552<576`, and the strict rational moment. It also includes exact dirty-scratch trials, endpoint identities and negative controls.

The chosen tensor witness is `a=36926111/500000000000=7.3852222e-5`, the conservative complex value in the pinned Lean input. The Fourier choice is `delta=73/1000000=7.3e-5`. The new exact log calculation gives a moment gap greater than `7/10^14`, and `a-delta=426111/500000000000>0`.

The stronger `7.3861113e-5` value from the external Python moment bisection is not needed for this update. The external integer-multiplication headline is a different parameter and is not substituted into the Fourier proof.

## What remains outside these checks

The producer is imported source, not a new independent implementation. The projector replay reuses earlier local binary algebra. The scalar dirty-scratch executions are finitely many rational examples; the universal statement follows from the written linear identity. The endpoint identities are checked in exact Gaussian-integer arithmetic. The large ambient network and complete DFT are not executed, and the checker does not formalize the infinite recursion or run Lean.

The included Lean source proves facts about finite histograms and numerical constraints. Its relationship to executable networks and analytic bounds still uses written premises. It supplies neither an end-to-end proof of #109 nor a formal proof of this Fourier extension.

Independent review should focus on the actual lifted role interface, copied-read timing, endpoint correction, complete cost recurrence and downstream substitution. The earlier `5.5e-10` manuscript and its original suites are preserved unchanged, with their own [historical audit](AUDIT.md).
