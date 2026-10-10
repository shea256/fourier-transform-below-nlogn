## 6. Sussman and Boukhalfa's five-stage Fourier result

### 6.1 Sources, theorem and status

This record incorporates the community complex circuit exported by Chafik Boukhalfa in CrocSwap PR256 [CB], in Jacob Sussman's five-stage construction and formal Fourier framework [JS]. The explicit-program package is pinned to `db3f75cdc5f03f3131d48fb220f6bf1958404ff3`; the corresponding Fourier proof is pinned to `fd19e46b728faa414cbfbf91b01a6a0b7903375d`. The latter instantiates Sussman's framework with the stronger PR233 circuit. These are upstream constructions and theorems. This project's contribution in this update is their incorporation, source audit and reproducible checks.

The selected exponents are

\[
a=\frac{7547361}{10^{10}}=0.0007547361,\qquad
\delta=\frac{7547360}{10^{10}}=0.0007547360,
\qquad a-\delta=10^{-10}.
\]

In OpenAI's exact-complex-arithmetic RAM model, the imported theorem states that one fixed program computes the exact DFT for every positive length in

\[
T(n)=O\!\left(n(\log n)^{1-\delta}\right).
\]

It includes scalar preparation, array/index work and the supplied-root interface. The root order is computed by a program and is less than $1024n^3$; the solver receives that specified root. Integer values and indices have a polynomial bound in $n$. A separate theorem supplies exact convolution. This changes neither the model nor the absence of a practical FFT-speed claim.

The pinned Lean project was rebuilt from source, using the pinned Mathlib cache. The WHT and all-length DFT/convolution statement comparisons passed, and the Fourier and tensor-program theorems report only the standard Lean axioms. The result is selected as **formalized**, referring to that imported theorem. The receipt, exact commands and limits are recorded in `verification/FIVE_STAGE_AUDIT.md`; independent human review remains pending.

### 6.2 The explicit complex program

The underlying lineage is icekylinx's paired cubes and source-assisted flow, eumemic's PR168 v4 modules and frames, Avi Eisenberg's PR191/193/194 reconstruction and pairing, and Boukhalfa's PR200/233 maximum-weight reuse pairing. PR233 retains the operation frames and replaces the reuse pairing. Sussman supplies the general frame formalization, certificate format and checker; Boukhalfa's PR256 emitter lowers the flow witness and exact local lifts into that format. an664's sharing principle and the earlier carrier, producer and endpoint work retain their source credits.

The certificate has $h=22$, $v=1320$, $R=9412$ helper slots, $12052$ numbered registers, $18248$ frames, and $52300$ gates across its two phases. Its $69683$ transformation blocks have total rank $262944$. The retained-center contribution is $440$ units of rank. These counts include the retained-center copies; no center-return or dirty-register work is silently discarded.

The Python reference checker verifies nested frame labels, gate shape and scatter conditions, the block ledger, and the exact response of every source column. It checks that each target receives the required source and that the sources are restored. This scalar check alone is not a replay of every dirty input column. The formal invocation theorem derives the dirty-response subtraction and inverse cleanup from the checked invertible program and the scalar identities. The full proof, rather than the Python source-column test alone, establishes the arbitrary-scratch behavior.

The certificates supplied to the Python and Lean pipelines have identical mathematical fields. Only their descriptive provenance string differs. The local verifier checks that equality, as well as the source hashes and the numerical parameters used by the formal rate theorem.

### 6.3 Five-stage construction and its ledger

Sussman's bridged construction gives each source pair a twin and arranges compatible labels so that two exchanges use five helper invocations in place of six. The helpers are shared across completed stages. Per finite-cover vertex,

\[
m=5h=110,\qquad W_0=4v+R=14692.
\]

If $H_{\mathrm{inv}}$ is the complete block histogram of one certified invocation, the five-stage histogram is

\[
H_5=5H_{\mathrm{inv}}+2v(e_{42}+e_{21}+e_{46}+e_4),
\]

where $e_r$ denotes one child of width $r$. The extra terms are the twins' remaining frame transitions. The resulting per-vertex histogram is:

| $r$ | $n_r$ | $r$ | $n_r$ | $r$ | $n_r$ |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 145890 | 9 | 2020 | 17 | 195 |
| 2 | 63335 | 10 | 4025 | 18 | 13200 |
| 3 | 49940 | 11 | 1765 | 19 | 7205 |
| 4 | 21835 | 12 | 5705 | 20 | 110 |
| 5 | 9880 | 13 | 840 | 21 | 2640 |
| 6 | 7455 | 14 | 3625 | 42 | 2640 |
| 7 | 3210 | 15 | 3025 | 46 | 2640 |
| 8 | 7390 | 16 | 405 | | |

Thus there are $358975$ children, the largest width is $46<110$, and

\[
\sum_r r n_r=1613040=110\cdot14692-3080.
\]

The cover multiplier cancels in the normalized moment but remains part of the finite algorithm's stock and constants. The imported proof constructs the network over the orthogonal group in dimension $110$ and proves its routing and adapter costs. Neither this integration nor the upstream implementation enumerates that enormous cover on actual arrays.

### 6.4 Exact rate and the formal tensor-to-Fourier connection

Our rational checker verifies

\[
\Psi(1-a)=\frac1{14692}\sum_r n_r(r/110)^{1-a}<1,
\qquad 1-\Psi(1-a)>8.05\cdot10^{-10}.
\]

The imported recursion engine uses a finite-fill correction with $s=40$. We separately check its actual rate premise:

\[
(1-2^{-40})\Psi(1-a)+2^{-40}
\left((109/110)^{1-a}+(1/110)^{1-a}\right)<1.
\]

The formal lemma `BlockAccounting.fold_B2Gp233x` proves this rate inequality using its own rational bounds. At $a=7547365/10^{10}$ the ordinary moment is greater than one, providing a negative control for this fixed histogram. This is not a ceiling on other networks.

The formal chain applies the checked certificate to the generalized frame/recursion engine. `RAM.hillsY_program` supplies OpenAI's tensor-program interface, with exponent $1-a$, for every required mode, color and input batch. The subsequent files under `Work/Fourier233/` reproduce OpenAI's Fourier reduction with the exponent and declaration names changed. Its overhead is absorbed using the positive gap $a-\delta=10^{-10}$. The final theorem is `OAI.PowerSaving.transform_mainY : DFTGoalY`; `convolution_mainY` proves the companion convolution statement.

The challenge file is OpenAI's complete uniform Fourier statement with its exponent and seven declaration names changed, plus explanatory comments. Our source comparison checks those limited differences. The theorem comparison additionally checks the declarations on which the statement depends and the axioms used by its proof. The original model, supplied root, preparation costs and integer bounds remain in the statement.

Sections 1--5 give this paper's reusable written transfer argument. The selected result is also available directly through the imported formal theorem and its own recursion engine; the local Python moment check is not presented as a replacement proof of that theorem.

### 6.5 Reproduction and attribution

Run `python3 verification/verify_five_stage.py` for source hashes, exact scalar/label checks, the histogram, both rate inequalities, the absorption gap and binding to the Lean sources. Full PR256 regeneration additionally requires its pinned NumPy/SciPy environment. The complete upstream Lean source is preserved in `verification/vendor/five_stage/fourier-proof-source.tar.gz`, with immutable repository pins and licenses in the accompanying manifest.

The separate `verification/verify_five_stage_lean.py` rebuilds the formal development with Lean 4.34.1 and the pinned Mathlib revision, regenerates the 41 certificate/proof files and 14 Fourier files, checks the reported axioms, and runs the upstream theorem/definition comparator. Its receipt distinguishes fresh project compilation from the downloaded Mathlib cache. These checks do not constitute independent human review, an execution of the DFT on large arrays, or a run of an independent proof kernel.

Sussman receives credit for the five-stage geometry and formal framework; Boukhalfa for the stronger pairing, explicit program and Fourier instantiation; Eisenberg, icekylinx, eumemic and the named predecessors for the underlying circuit and algorithms. SovereignSteak's PR250 and hcg890's PR234 are credited in the incoming package's five-stage composition and ledger lineage. OpenAI supplies the original Fourier model and all-length reduction. The source audit preserves the broader community and our earlier Jain-based history. This update does not claim a newly discovered exponent or authorship of the imported proof.
