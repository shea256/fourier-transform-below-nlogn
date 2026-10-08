# Pinned round-six complex network

The source files listed in [SOURCE.json](SOURCE.json) are copied **without modification** from Swapnil Jain's `integer-mult-kappa`, commit `f2176bc1124821bf17eb63725bd366d7bdc020a3`. Their original Apache-2.0 [LICENSE](LICENSE) and full [NOTICE](NOTICE) are included.

`producer.py`, `frames.py`, `hist.py`, `cert.py` and `run.py` come from `independent/complex-twostage/`. `Round6.lean` and `round6-histograms.json` come from `lean/`. The Lean source and inputs are retained for provenance and comparison, not as a formal proof of the local Fourier theorem. The root verification runner does not run Lean.

The local [round-six checker](../../verify_round6.py) validates source hashes, replays the physical schedule using local binary-projector code, checks the entire local coefficient identity, and rebuilds the histogram before comparing it with the external numerical input. The finite producer itself remains imported code; this is not an independent reimplementation of it.
