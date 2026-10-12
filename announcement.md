# Announcement draft: improved exact DFT bound

Prepared for posting; this file does not record an external announcement. Links
below pin the verified proof commit, so they work before the PR is merged. The
comparison uses the [October 12 baseline audit](research/complex-transfer-588-596/verification/leaderboard-2026-10-12.json).

## Main post

We've proved an improved exact DFT bound for OpenAI Problem #130:

T(n) = O(n (log n)^(1 - delta)), with delta = 0.0012331685.

The exponent saving is about 20.65% larger than Nil Mamano's 0.0010221076, the
strongest verified DFT baseline in our October 12 audit. This is an asymptotic
result in the exact-complex-arithmetic RAM model.

The Lean proof covers DFT and convolution at every positive length. It passes
the full OpenAI statement comparison and local proof replays in both Lean's
kernel and nanoda.

Built on Jeremy Kothe's PR588 circuit and the community's formal Fourier
framework, with our source-copy conversion, cyclic helper-bank schedule and
checked instantiation. The updated paper, exact certificates and reproduction
instructions are ready for review.

[Paper](https://github.com/shea256/fourier-transform-below-nlogn/blob/52394849c7ecf3412d39b925d75fc7fdb98994d8/manuscript.pdf)
· [Proof and receipts](https://github.com/shea256/fourier-transform-below-nlogn/tree/52394849c7ecf3412d39b925d75fc7fdb98994d8/lean/complex588)

## Follow-up: credits and verification scope

Jacob Sussman supplies the formal engine and checkers; Dugongue and jacklightChen
the #401/#377 geometry; Nil Mamano's submission the published gauged Lean
extension; and OpenAI the original model and Fourier reduction. Jeremy Kothe's
circuit preserves the complete community predecessor credits in its source
notices. The earlier Sussman–Boukhalfa theorem remains archived, with the research
lineage through Doug Colkitt, Rohan Arun and Swapnil Jain recorded in the
[attribution](https://github.com/shea256/fourier-transform-below-nlogn/blob/52394849c7ecf3412d39b925d75fc7fdb98994d8/ATTRIBUTION.md).

The theorem assumes the specified supplied root of unity and charges scalar
preparation, indexing and output work. The 20.65% comparison measures exponent
savings; practical FFT performance has not been measured.

The official comparator passed locally using its pinned code and both proof
kernels. This VM required a pass-through replacement for the unavailable
`landrun` process sandbox; the proof checks were unchanged. The result has not
yet been accepted by the leaderboard or independently reviewed by a human.

[Verification audit](https://github.com/shea256/fourier-transform-below-nlogn/blob/52394849c7ecf3412d39b925d75fc7fdb98994d8/verification/COMPLEX588_AUDIT.md)
· [Pinned baseline](https://github.com/bigospeedrun/verifier/blob/f9ffbc1f9dfbfaf84d819b087c999361d0fa3372/submissions/dft/nmamano-dft-record/Submission.lean)
