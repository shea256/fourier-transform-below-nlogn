# Reproducing the finite checks for Problem #130

This directory contains the verification suite from the research packages and a second, differently implemented suite. The two underlying suites were both written and audited with AI assistance; the second is a different implementation, **not independent human review**.

They check finite mathematical identities and quantitative parameters appearing in [`../manuscript.md`](../manuscript.md) and [`../core-proof.pdf`](../core-proof.pdf). Passing these checks **does not establish the full all-length Fourier-transform theorem**.

## Quick start

Requirements: Python **3.10+**, using only the standard library. From the repository root:

```bash
python3 verification/run_checks.py
```

The shorter `python verify_extension.py` command printed in the manuscript is run from the `verification/` directory. The command above runs both suites from the repository root.

Or run the programs individually:

```bash
python3 verification/verify_extension.py
python3 verification/clean_room_audit.py
python3 verification/compare_certificates.py
```

Both verifier scripts generate `certificate.json` and `clean_room_certificate.json` in this directory. The comparison script checks that they match the archived reference certificates under [`certificates/`](certificates/), excluding only elapsed wall time in the clean-room suite. The runner writes console transcripts under ignored `outputs/` files. Do **not** assume an old, checked-in transcript reflects your own machine's execution.

Historical console transcripts are under [`expected-results/`](expected-results/). Their certificate destination paths have been normalized to paths relative to the repository root; the recorded check results and timings are retained. They are historical records, not transcripts of the current run.

The October 8 repository cleanup corrected the manuscript path in `verify_extension.py` and reduced `rational_bounds.py` to the exact logarithm, exponent-bound, and serialization helpers used by the suite. Its unused standalone audit of the older `h+1`-center model was removed; that historical code remains in Git commit `eb832424c13c7ab963ea1a5b210ac8c8478392a7`. The retained helper implementations and reference certificates are unchanged. `clean_room_audit.py` is also unchanged, including the script hash recorded in its reference certificate. Current manuscript hashes and the earlier audit's distinct historical digest are documented in [AUDIT.md](AUDIT.md#source-identifiers).

## What each program checks

| Script | Scope | What it does **not** prove |
| --- | --- | --- |
| [`verify_extension.py`](verify_extension.py) | Reconstructs the original network constants, verifies rank-reduced center identities, checks rational exponent witnesses; checks the complete local shared-sum coefficient matrices, role-support traces and representative binary-frame paths at ground sizes 24 and 25; tests full three-shear scalar exchange on **seeded rational examples** at small sizes 7 and 8. | A mechanically checked all-length algorithm or independent verification of the global tensor-space phase schedule. Its small-size scalar trials are not universal symbolic checks. |
| [`clean_room_audit.py`](clean_room_audit.py) | Reimplements relevant checks using topological role allocation, sparse rational operators, and binary projectors; tests full symbolic scalar transformations at sizes 7 and 8, full multi-pair local graph/phase checks at 24 and 25, exact bounds and batching arithmetic; includes negative controls. | An independent referee review, a Lean proof, or exhaustive enumeration of the astronomical tensor network. |
| [`rational_bounds.py`](rational_bounds.py) | Provides exact rational logarithm enclosures, derived exponent bounds, and output formatting for `verify_extension.py`. | A standalone network model or verifier. |
| [`compare_certificates.py`](compare_certificates.py) | Confirms regenerated finite-check JSON exactly matches the recorded reference, ignoring only machine-dependent wall-clock duration. | Any claim stronger than the outputs of those finite checks. |

The longer [adversarial audit](AUDIT.md) records which arguments were reviewed and what remains conditional or unchecked.

## Numerical claims and their dependencies

The critical saving `a = 1 - theta` is distinct from the conservative pure-power saving `delta` after absorbing a `(log log n)` factor.

| Claimed pure-power saving `delta` | Proposed construction | Required arguments beyond upstream #130 |
| --- | --- | --- |
| `5.2e-10` | `h=24`, reduced central coordinate, original padded recursion | Modified central correction and phase-label compatibility |
| `5.3e-10` | Above, with direct handling of incomplete recursive batches | Also the recurrence and cost accounting for remainders |
| `5.5e-10` | Above, with shared intermediate correction sums | Also the forward and inverse phase schedules and their tensor lifting |

All three are **research claims pending independent mathematical review**. Reference certificates support local algebra and exact numerical bounds. Correctness still depends on the written arguments plus the specified upstream compiler and all-length reduction.

## What is not tested

- The enormous complete transform implementation at arbitrary lengths.
- Every global frame and every recursive tensor instance by enumeration.
- A full proof of the asymptotic recursion, the downstream exact-width Fourier compiler, or the upstream all-length reduction.
- Publication priority, bit complexity, bounded coefficients, numerical stability, practical running time, or a bound for integer multiplication.

## Layout

```text
verification/
├── README.md
├── AUDIT.md
├── run_checks.py                 # Orchestrator only
├── compare_certificates.py       # Reference comparison only
├── verify_extension.py           # Original suite
├── local_circuit.py              # Helper used by original suite
├── rational_bounds.py            # Exact logarithm and exponent-bound helpers
├── clean_room_audit.py           # Second implementation
├── certificates/
│   ├── extension_reference.json
│   └── clean_room_reference.json
└── expected-results/
    ├── extension_original_log.txt
    └── clean_room_original_log.txt
```

The LaTeX source files used for the manuscript and core note are separately included under [`../tex/`](../tex/). Their presence is for reproducibility of typesetting, not mathematical verification.
