We’re publishing a research draft tightening the result from OpenAI Problem #130: the exact discrete Fourier transform.
Using OpenAI’s existing methods for turning a faster arithmetic circuit into a Fourier algorithm, our refinements give the proposed all-length bound:
T(n) = O(n(log n)^(1−δ))
with δ = 5.5×10⁻¹⁰, up from 10⁻¹³ in OpenAI’s headline corollary.
This represents a 5,500-fold increase in the exponent-saving parameter—not a 5,500-fold runtime speedup. Comparing the sharper critical savings underlying both bounds gives approximately 2,617-fold.
OpenAI’s Fourier proof reuses a fixed arithmetic circuit from its integer-multiplication paper (#109). Building on @0xdoug’s retuning of that shared circuit, we remove a redundant intermediate quantity, avoid unnecessary recursive batch padding, and reuse partial sums.
Our draft carries these improvements through to a stronger Fourier bound at every input length, preserving OpenAI’s exact-arithmetic model, specified-root assumptions, and accounting for scalar preparation and indexing costs.
We’re releasing the proof draft and reproducible exact-arithmetic checks. Independent mathematical review remains pending.
