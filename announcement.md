# Announcement text: five-stage Fourier incorporation

Prepared text, not a posting record. The selected source and proof receipt are recorded in `results/registry.json` and `verification/FIVE_STAGE_AUDIT.md`.

## Main post

We've updated our paper on OpenAI Problem #130: computing the exact discrete Fourier transform below n log n.

We're incorporating the stronger Fourier result published by Jacob Sussman and Chafik Boukhalfa, built on the community's integer-multiplication networks:

T(n) = O(n(log n)^(1−δ)), with δ = 0.0007547360.

That's a 12.65% increase in the exponent saving over our previous 0.00067. We've reproduced the pinned Lean project build and theorem comparisons.

This update credits their upstream theorem; our contribution is incorporation, a source-history audit, and reproducible checks.

## Follow-up

Sussman supplies the five-stage geometry and formal framework. Boukhalfa supplies the stronger PR233 pairing, PR256 explicit program and Fourier instantiation. The circuit retains work by icekylinx, eumemic, Avi Eisenberg, an664 and the other contributors named in our audit.

We also preserve the research lineage through OpenAI, Doug Colkitt, Rohan Arun and Swapnil Jain. OpenAI supplies the original Fourier model and reduction; Jain's networks supplied our earlier selected witnesses.

The all-length theorem uses OpenAI's exact-complex-arithmetic RAM model, with a specified supplied root of unity and scalar/index preparation included. The comparison is of exponent savings. No practical FFT speedup is claimed; independent human review remains pending.

Paper, LaTeX, pinned sources, exact certificates, Lean reproduction receipt and improvement history:
https://github.com/shea256/fourier-transform-below-nlogn
