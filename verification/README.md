# Reproducing the finite checks for Problem #130

Run from the repository root with **Python 3.10+**, standard library only:

```sh
python3 verification/run_checks.py
```

The runner executes the earlier two suites and their reference comparison, then the new round-six verifier. It writes fresh console transcripts under ignored `outputs/` files. Finite checks support the written proofs; they do not establish an end-to-end formal theorem or constitute independent review.

## Round-six transfer: proposed Fourier saving `7.3e-5`

```sh
python3 verification/verify_round6.py
```

The new checker:

1. Verifies SHA-256 hashes of unmodified external sources pinned to `f2176bc1124821bf17eb63725bd366d7bdc020a3`.
2. Rebuilds every producer support and all `4,096,576` local coefficient entries at `h=24`, including the retained totals.
3. Propagates the fresh input map through the actual compiled role shears and verifies designated output carriers, including separation and final-use timing for retained totals.
4. Reproduces the external label checker and separately replays the physical auxiliary frame paths in both orientations with local binary projectors.
5. Charges centre-copy transforms and combines the local histogram with exterior, data-front and endpoint-copy classes. It matches the resulting histogram to both a fresh external reconstruction and the pinned Lean inputs.
6. Checks exact rational dirty-scratch scalar trials, Gaussian-integer endpoint cancellation, and the final weight-nine translation identity.
7. Certifies the recursive moment by exact rational logarithm bounds, using `a=36926111/500000000000`, and verifies `delta=73/1000000<a`.
8. Rejects negative controls with unpaid centre copies, an omitted endpoint correction, and an excessive saving.

The output is `round6_certificate.json`, compared with [certificates/round6_reference.json](certificates/round6_reference.json). The reported moment upper bound is strictly below `1-7e-14`; rational values, not decimal rounding, determine success.

The third-party code is in [vendor/jain_round6/](vendor/jain_round6/), with its original license, NOTICE and source manifest. The new checker reuses the earlier local projector library and imports the external producer. It is an additional implementation of some checks, **not an independent implementation or independent review of the entire construction**.

The included `Round6.lean` checks numerical certificates and the integer-multiplication assembly. The runner does not execute Lean, and the file does not prove the Fourier transfer. The infinite recurrence, linear-time index layout, arbitrary-column lifting, and all-length theorem use the written arguments in [manuscript.md](../manuscript.md). See [ROUND6_AUDIT.md](ROUND6_AUDIT.md) for the review boundary.

## Earlier three-stage result and fallbacks

The original verification scripts have not been modified. Their full manuscript is preserved under [archive/three-stage/](../archive/three-stage/); the short [core proof](../core-proof.pdf) is also unchanged.

| Script | What it checks | Principal limits |
| --- | --- | --- |
| [verify_extension.py](verify_extension.py) | Original/reduced-centre counts, rational exponent witnesses, shared-sum coefficient matrices, role supports and representative frame paths at `h=24,25`; seeded rational scalar trials at `h=7,8`. | Does not mechanically prove the global tensor schedule or all-length theorem. |
| [clean_room_audit.py](clean_room_audit.py) | A differently implemented role compiler, sparse rational operators and binary projectors; symbolic scalar maps at `h=7,8`, full local frame checks at `h=24,25`, numerical bounds and negative controls. | Same-assistant work, not independent human review; does not enumerate the complete tensor network. |
| [compare_certificates.py](compare_certificates.py) | Regenerated earlier certificates match archived references, ignoring only elapsed wall time. | Establishes agreement with the recorded finite checks, not a stronger theorem. |

Their original JSON references remain in [certificates/](certificates/), and their earlier reference consoles remain in `expected-results/`. Fresh runs produce ignored `certificate.json` and `clean_room_certificate.json`. The [earlier audit](AUDIT.md) concerns only that construction.

| Proposed Fourier saving | Construction and extra dependencies |
| --- | --- |
| `5.2e-10` | Reduced central coordinate; original padded recursion |
| `5.3e-10` | Also the earlier incomplete-batch recurrence |
| `5.5e-10` | Also the earlier shared-sum schedules |
| **`7.3e-5`** | **Attributed round-six two-stage network, paid copies and endpoint correction, whole-residual recurrence, and the new Fourier transfer** |

None of these checks establishes novelty, priority, practical runtime, finite-precision stability, bounded coefficients, or a new integer-multiplication theorem.
