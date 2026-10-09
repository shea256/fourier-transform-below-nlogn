## Round-six result record

- Date incorporated: October 8, 2026.
- Status: proposed Fourier transfer; preserved after the round-ten update.
- Tensor witness: `36926111/500000000000 = 7.3852222e-5`.
- Fourier saving: `73/1000000 = 7.3e-5`.
- Source: Jain commit `f2176bc1124821bf17eb63725bd366d7bdc020a3`.

The complete unchanged [manuscript](../archive/round6/manuscript.md), [PDF](../archive/round6/manuscript.pdf), and [LaTeX](../archive/round6/manuscript.tex) preserve the two-stage transfer, copied-centre schedule, endpoint correction and unequal-width recurrence. Historical README and announcement copies are also preserved in that directory; their relative links and “current” language describe the original publication snapshot.

Run `python3 verification/verify_round6.py` from the repository root. The [reference certificate](../verification/certificates/round6_reference.json) and [review record](../verification/ROUND6_AUDIT.md) retain their original evidence boundaries. The sources and attribution are in [the pinned vendor manifest](../verification/vendor/jain_round6/SOURCE.json).

This result replaced the earlier shared-sum construction. Its exponent saving was not obtained by adding the two constructions' savings. The version remains independently runnable as a fallback; this does not mean independently reviewed.
