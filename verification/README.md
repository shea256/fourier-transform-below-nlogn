# Reproducing the finite checks for Problem #130

Run from the repository root with **Python 3.10+**, standard library only:

```sh
python3 verification/run_checks.py
```

The runner executes the earlier suites, round-six, round-ten, round-eleven and five-stage verifiers, and generated-document/registry consistency checks. It writes fresh console transcripts under ignored `outputs/` files. Finite checks support the written proofs; they do not establish an end-to-end formal theorem or constitute independent review. The separate Lean workflow below reproduces the imported formal theorem. Incorporated versions are listed in [the improvement log](../IMPROVEMENTS.md).

## Five-stage Fourier result: `0.0007547360`

```sh
python3 verification/verify_five_stage.py
```

The [source manifest](vendor/five_stage/SOURCE.json) pins Boukhalfa's PR256 explicit program and his stronger Fourier instantiation in Sussman's framework. The verifier checks hashes, invokes Sussman's exact scalar/label checker, independently constructs the five-stage histogram, and checks its rational moment, finite-fill rate, negative control and Fourier absorption gap. It binds the program, ledger, exponent and OpenAI challenge to the archived Lean source. The reference is [five_stage_reference.json](certificates/five_stage_reference.json).

The scalar replay checks every source column. Arbitrary dirty-scratch restoration comes from the Lean invocation theorem, not from this Python test alone. The full program regeneration also reruns the upstream flow and exact local lifts; it passed with both emitted certificates identical to the pinned originals. Its [receipt](certificates/five_stage_regeneration_receipt.json) and compressed log are retained.

Reproduce the formal theorem separately, with the pinned Lean 4.34.1 toolchain installed:

```sh
python3 verification/verify_five_stage_lean.py \
  --work-dir /tmp/fourier-five-stage-rebuild --lake lake --threads 2
```

This extracts the archived sources, obtains the pinned Mathlib cache, checks regeneration of 41 certificate/proof files and 14 Fourier-chain files, builds the WHT and all-length DFT/convolution targets, audits their axioms, and runs Sussman's theorem/definition comparator. It writes a receipt only after all checks pass. The standard Python suite checks the retained receipt and log hashes when the registry selects `formalized`; it does not rerun Lean. See [FIVE_STAGE_AUDIT.md](FIVE_STAGE_AUDIT.md) for exact commands, results and boundaries.

## Round-eleven transfer: proposed Fourier saving `0.00067`

```sh
python3 verification/verify_round11.py
```

The [source manifest](vendor/jain_round11/SOURCE.json) pins the new C1 word, retirement-host matching, 42 terminals, imported checker, notices and Lean inputs. The verifier checks the complete decoder identity and imports the full-size role/frame/target-chain recount. It then separately emits the aliased scalar transcript and checks **all 17,057,040 output coefficients over the rationals**: source response, zero initial dirty-scratch response, and identity on arbitrary dirty targets. Each retained physical mixer is invertible; the written cleanup reverses those actual mixers and source loads.

The independent rational moment bound accepts `67147467/100000000000`, rejects the next `1e-12` grid point, and checks the positive gap to `67/100000`. Its output must match [round11_reference.json](certificates/round11_reference.json). Additional exact controls reject wrong mix sign, omitted gauge correction and missing terminal post-shear. The imported modular trials and controls remain clearly identified.

The complete scalar check does not materialize full-size complex frames or the global cover. Those and the Fourier reduction remain explicit mathematical dependencies, as described in [ROUND11_AUDIT.md](ROUND11_AUDIT.md) and the [result record](../results/round11.md). The Python runner does not execute Lean. The round-ten suite below retains the small exhaustive Clifford checks used by both records.

## Round-ten transfer: proposed Fourier saving `0.00061`

```sh
python3 verification/verify_round10.py
```

The checker verifies hashes of the pinned word, upstream checker, Lean inputs and adopted proof sources. It then expands **all 1,742,400 decoder coefficients over the integers**, checks 32,071 compiled carrier operations and the exact supports of 5,170 compensation coefficients, runs the imported full-size frame/chain/alias checker, and reconstructs the complete histogram. The histogram must match the released inventory and the Lean input.

The shared [network_contract.py](network_contract.py) uses the earlier local logarithm routine and rational exponential bounds. It proves a strict moment at `15402419/25000000000`, rejects the next grid point with a lower bound, and checks the positive gap to the Fourier choice `61/100000`. The reference is [round10_reference.json](certificates/round10_reference.json).

[clifford_checks.py](clifford_checks.py) enumerates all 67 binary subspaces in dimension four, checks 4,489 frame-distance pairs and 513 nested transitions using exact Gaussian-integer matrices, and checks the full-frame translation square. These small exhaustive tests supplement the general written lemma; they are not a full-size physical replay.

The upstream aliased dirty-scratch runs are exact **modular samples**, not universal symbolic proofs. Our complete integer coefficient check establishes the decoder identity, while the arbitrary-scratch and cover statements still use the [written transfer](../results/round10.md). The general Clifford elimination and cover/sharing results are explicit upstream dependencies. The full cover and DFT are not executed. The Python runner does not execute Lean.

To run the four additional upstream word mutations, generate them into a temporary directory with `verification/vendor/jain_round10/mutate_word.py WORD.json.gz OUTDIR`, then run `verification/vendor/jain_round10/check_word.py` on each `mut_*.json.gz`; all four must return nonzero. The normal verifier already checks its own sign, compensation-target and next-grid controls and the upstream replay's three timing/read controls.

See [ROUND10_AUDIT.md](ROUND10_AUDIT.md) and the [source manifest](vendor/jain_round10/SOURCE.json) for attribution and exact scope. The optimization search is not rerun; the complete frozen word is checked directly.

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

The included `Round6.lean` checks numerical certificates and the integer-multiplication assembly. The runner does not execute Lean, and the file does not prove the Fourier transfer. The infinite recurrence, linear-time index layout, arbitrary-column lifting, and all-length theorem use the written arguments in the [archived round-six manuscript](../archive/round6/manuscript.md). See [ROUND6_AUDIT.md](ROUND6_AUDIT.md) for the review boundary.

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
| `0.00061` | **Round-ten paired-cube cover, generalized exact frames, shared completed cores, and birth reuse** |
| **`0.00067`** | **Round-eleven retired copies, terminal targets and exact scalar map** |

The separate five-stage record has Fourier saving `0.0007547360`; its formal verification status is recorded in the registry and [proof reproduction audit](FIVE_STAGE_AUDIT.md).

None of these checks establishes novelty, priority, practical runtime, finite-precision stability, bounded coefficients, or a new integer-multiplication theorem.
