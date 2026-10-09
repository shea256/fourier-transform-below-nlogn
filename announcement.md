# Announcement draft: round-eleven integration

This is a draft, not a posting record. Verify the current selection in `results/registry.json` before publishing. The original round-six announcement is preserved under `archive/round6/`.

## Main post

We're updating our research draft on OpenAI Problem #130: computing the exact discrete Fourier transform below n log n.

Building on Swapnil Jain's round-eleven complex network and its cited predecessors, our draft now proposes the all-length bound

T(n) = O(n(log n)^(1−δ)), with δ = 6.7×10⁻⁴.

That's about 9.18 times our previous published exponent saving of 7.3×10⁻⁵, and 6.7 billion times OpenAI's published headline of 10⁻¹³.

These are comparisons of the exponent saving, not measured runtime speedups. The Fourier transfer remains conditional on the cited upstream interfaces, with independent review and formal verification pending.

## Follow-up

The paper now separates the reusable Fourier transfer from versioned network witnesses, with an improvement log, immutable source pins and preserved earlier drafts.

For round eleven, our additional verifier checks every scalar output coefficient over exact rational arithmetic, including arbitrary dirty registers and targets. This is a finite check, not a formal proof of the full physical network or Fourier theorem.

The model uses exact complex arithmetic, unrestricted coefficients, a specified supplied root of unity and unit-cost logarithmic-word indexing. Scalar preparation and array organization are charged. No practical FFT speedup is claimed.

Draft, LaTeX, exact certificates, verification scope and improvement log:
https://github.com/shea256/fourier-transform-below-nlogn

Network credit belongs to Jain and the cited community contributors, including icekylinx's frame/cover and retirement-reuse work, jamesyc's terminal-target compiler, eumemic's modules and compensated-reuse lineage, and an664's completed-core sharing. Douglas Colkitt's repository and the original OpenAI work provide the underlying research framework. Full attribution is in the paper and preserved source notices.
