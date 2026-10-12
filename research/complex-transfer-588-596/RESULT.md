# Result

**Accepted by Lean locally:** an all-positive-length exact DFT and convolution
bound with saving `12331685/10^10 = 0.0012331685`, in OpenAI's original exact
complex RAM model. This is about 20.65% above the strongest verified baseline
found in the final site recheck, `0.0010221076`. It is a new instantiation of
credited existing machinery, not a claim of a new general Fourier reduction.

The full Lean build and exact statement/dependency comparisons pass; the kernel
interface and both final theorems use only the three standard axioms. All 63
new Lean modules regenerate byte for byte. See
[the proof package](../../lean/complex588/README.md),
[selected result record](../../results/complex588.md), and
[audit](../../verification/COMPLEX588_AUDIT.md).

The changed construction is #588 `atm3`, with explicit source copies and 5,040
cyclic helper banks in the existing #401/#377 layout. Its full scalar and frame
checks, bank schedule, invoice and finite-fill rate pass Lean's existing
predicates. The local conversion is the new step that permits a stronger
community circuit to enter that already-formalized universal framework.

The native #588/#596 finite verifiers also passed, but their larger native
exponents remain conditional. Literal mutable-source and hyperplane-ended
conversions were rejected. The ordinary moment root near `0.001233169825152`
is an arithmetic quantity, not the proved Fourier saving. Global optimality of
the chosen provider or packing is not established.

The official comparator completed its fresh build and full-statement check;
both nanoda and Lean's kernel accepted the exported proof, exit 0. Tool pins,
the process-sandbox limitation and the hashed log are recorded in
`lean/complex588/receipt/verification.json`. Leaderboard acceptance and human
review have not been obtained. Same-agent verification is not peer review.
