# Announcement text: complex588 Fourier theorem

Prepared text, not a posting record. The selected sources and proof receipt are recorded in `results/registry.json` and `verification/COMPLEX588_AUDIT.md`.

## Main post

We've updated our paper on OpenAI Problem #130: computing the exact discrete Fourier transform below n log n.

We've built a new Lean-checked instantiation from Jeremy Kothe's PR588 circuit and the community's formal Fourier machinery:

T(n) = O(n(log n)^(1−δ)), with δ = 0.0012331685.

That's about a 20.65% increase in the exponent saving over the strongest verified DFT baseline we found, Nil Mamano's 0.0010221076. Both DFT and convolution pass the full OpenAI statement comparison.

Our contribution is the source-copy conversion, cyclic bank schedule and checked instantiation, with reproducible proof sources and exact certificates. The larger native integer-network headlines are not the Fourier exponents proved here.

## Follow-up

Sussman supplies the formal engine and checkers, Dugongue and jacklightChen the #401/#377 geometry, and Mamano's submission the published gauged Lean extension. Kothe's circuit retains the complete community predecessor credits in its source notices. Boukhalfa and Sussman's earlier five-stage theorem remains archived as the previous selected publication.

We also preserve the research lineage through OpenAI, Doug Colkitt, Rohan Arun and Swapnil Jain. OpenAI supplies the original Fourier model and reduction; Jain's networks supplied earlier selected witnesses.

The all-length theorem uses OpenAI's exact-complex-arithmetic RAM model, with a specified supplied root of unity and scalar/index preparation included. The comparison is of exponent savings. No practical FFT speedup is claimed; independent human review remains pending.

Paper, LaTeX, pinned sources, exact certificates, Lean reproduction receipt and improvement history:
https://github.com/shea256/fourier-transform-below-nlogn
