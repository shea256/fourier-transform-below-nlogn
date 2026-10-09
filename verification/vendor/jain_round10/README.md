# Pinned round-ten complex witness

The unmodified files in [SOURCE.json](SOURCE.json) come from Swapnil Jain's `integer-mult-kappa` at `d2f6146ffbbd893e69b8fb06bc53b82af36d8032`. Their SHA-256 hashes are checked before execution. The Apache-2.0 license, NOTICE and upstream description are retained.

`word.json.gz` is the complete frozen finite word used for verification; `inventory.json.gz` is its released histogram. `check_word.py` and `mutate_word.py` are upstream programs. The local checker adds exact all-coefficient and compensation-target checks, small exact frame tests, and rational moment bounds. It does not rerun the optimization/search pipeline.

`Round10.lean` and its inputs are included for provenance and numerical comparison. The default Python verifier does not run Lean. The file checks arithmetic predicates, not a formal proof of the full network or the Fourier transfer. The bit-side entries in those unchanged files are not dependencies of our Fourier result.
