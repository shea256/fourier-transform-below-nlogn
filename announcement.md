Taking this to the Fourier side: we’re publishing a research draft on OpenAI Problem #130, the exact discrete Fourier transform below n log n.

Building on Swapnil Jain’s round-six complex network for #109 and its cited predecessors, we propose an all-length Fourier bound:

T(n) = O(n(log n)^(1−δ)), with δ = 7.3×10⁻⁵.

OpenAI’s published headline uses δ = 10⁻¹³. Our contribution is the proposed Fourier transfer, assuming the cited upstream results. It uses OpenAI’s exact-complex-arithmetic model, with supplied roots and scalar preparation and indexing costs included.

Draft, LaTeX, and exact-arithmetic verifiers: https://github.com/shea256/fourier-transform-below-nlogn

Independent mathematical review and formal verification of the Fourier transfer remain pending. No practical FFT speedup is claimed.
