# Improvement log

Generated from [results/registry.json](results/registry.json). Dates identify project records, not priority claims. `proposed` means a written conditional transfer with finite checks; it does not mean independent review or formal verification. Candidate values never replace the current result automatically.

Current selection: **[Jain round-eleven retired-copy refinement](results/round11.md)**, with proposed `delta=0.00067`.

| Date | Result | Status | Fourier saving $\delta$ | Tensor witness $a$ |
| --- | --- | --- | ---: | ---: |
| 2026-10-08 | [Earlier shared-sum construction](results/legacy-shared-sum.md) | historical-proposed | `0.00000000055` | `see record` |
| 2026-10-08 | [Jain round-six two-stage network](results/round6.md) | proposed | `0.000073` | `0.000073852222` |
| 2026-10-09 | [Jain round-ten paired-cube cover](results/round10.md) | proposed | `0.00061` | `0.00061609676` |
| 2026-10-09 | [Jain round-eleven retired-copy refinement](results/round11.md) | proposed | `0.00067` | `0.00067147467` |

## 2026-10-08: Earlier shared-sum construction

Reduced-centre and shared-sum refinements; full publication preserved under archive/three-stage.

[Result record](results/legacy-shared-sum.md) · [Reference certificate](verification/certificates/extension_reference.json) · [Verifier](verification/verify_extension.py)

## 2026-10-08: Jain round-six two-stage network

Copied centres, retained totals and whole-residual batching; full publication preserved under archive/round6.

[Result record](results/round6.md) · [Reference certificate](verification/certificates/round6_reference.json) · [Verifier](verification/verify_round6.py)

The Fourier exponent saving is approximately **132,727.27 times** the preceding incorporated result. This compares exponent parameters, not running times.

## 2026-10-09: Jain round-ten paired-cube cover

Three-stage cover, arbitrary-subspace frames, shared completed cores, nested-prefix modules, and 3,180 birth-reuse pairs. New transfer argument and exact finite checks.

[Result record](results/round10.md) · [Reference certificate](verification/certificates/round10_reference.json) · [Verifier](verification/verify_round10.py)

The Fourier exponent saving is approximately **8.36 times** the preceding incorporated result. This compares exponent parameters, not running times.

## 2026-10-09: Jain round-eleven retired-copy refinement

Re-chosen cube circuit, 386 retired-copy hosts and 42 terminal deletions. Recomputed compensation and exact checks of all 17,057,040 scalar output coefficients; frame and cover dependencies inherited explicitly.

[Result record](results/round11.md) · [Reference certificate](verification/certificates/round11_reference.json) · [Verifier](verification/verify_round11.py)

The Fourier exponent saving is approximately **1.10 times** the preceding incorporated result. This compares exponent parameters, not running times.

The original OpenAI #130 published headline is `delta=1e-13`. The older short proof also retains the `5.2e-10` and `5.3e-10` fallbacks. See [the update workflow](results/README.md) before adding or promoting a result.
