# Adversarial audit of the proposed #130 Fourier extension

**Date:** October 8, 2026  
**Reviewed draft:** `fourier130_v2/PROOF.md` from the preceding conversation  
**Outcome:** No theorem-changing error found in the three proposed modifications. The `5.5e-10` pure-power saving survives this audit, relative to the specified upstream results. The simpler `5.2e-10` and `5.3e-10` extensions remain separately reviewable.

**Review boundary:** This is a same-assistant adversarial review and a second implementation of finite verifiers. It is **not independent review**, not a Lean proof, and not a fresh proof of every upstream theorem. Publication priority and practical performance are not established.

## 1. What was actually reviewed

The sources were the uploaded 31-page *An explicit power saving for the exact discrete Fourier transform* (OpenAI, September 25, 2026), called **[O]** below; the preceding proposed proof note; and the code in `fourier130_proof_extension.zip`. The source PDFs' SHA-256 hashes match the previous package's source manifest. The uploaded 49-page finite-win companion describes a separate route and is not a dependency of this explicit quantitative extension.

I read the complete preceding proof note, inspected its verifiers, reran the existing suite, and wrote a second program that imports **no code from that package**. The new program uses topological role allocation instead of union-find, ordinary sparse integer/rational coefficient propagation, and exact binary projection matrices instead of the old nullspace-based edge checks.

I visually checked the gate-label table on [O], page 8, and the residual table and dimension-loss argument on page 9. I also traced how the tensor exponent is used in [O], Proposition 4.2 and Sections 5.2–5.4. That last task is a dependency/parameter audit, not independent verification of the entire Fourier compiler.

The public `independent-complex.tex` and `current-status.md` pages in Douglas Colkitt's repository were inspected for provenance. The inspected note still uses the unchanged complex network at `h=25`, with `h+1` central wires. This does **not** establish that no other person or branch has proposed our modifications.

## 2. Numerical claims after the review

The convention is `T(n)=O(n (log n)^(1-delta))`. A critical saving `a=1-theta` initially gives an additional `(log log n)^(4-theta)` factor; every **fixed** `delta<a` absorbs that factor. Equality `delta=a` does not follow from that argument.

| Extension | Critical saving `a` | Safe pure-power `delta` | New dependencies beyond ground-size retuning |
|---|---:|---:|---|
| Reduced center; original padded recursion | `5.22969896327091e-10` | `5.2e-10` | Central matrix identity and unchanged surviving labels |
| Reduced center; unpadded recursion | `5.30775793289321e-10` | `5.3e-10` | Also the remainder-batching lemma |
| Reduced center and shared sums; unpadded recursion | `5.51272588493243e-10` | `5.5e-10` | Also both orientations of the shared-sum label schedule |

These are proposed extensions of [O], not independently accepted literature results. No numerical downgrade was required by this review. All rows were recalculated with exact rational logarithm enclosures. The short proof is provided separately as `CORE_PROOF.pdf` and `CORE_PROOF.tex`; the strongest construction remains in the archived full proof draft.

## 3. Central-wire reduction: the short argument survives

The original center has `h` incidence sums and one total sum. At the level of the **source-dependent map**, the total equals one third of the incidence sums, because every input is indexed by a triple. Replace the original readout by

\[
(G'x)_j=\sum_{T\ni j}x_T,
\qquad
(R'c)_S=\frac12\sum_{j\in S}c_j-\frac16\sum_{j=1}^h c_j.
\]

Then

\[
(R'G')_{S,T}=\frac{|S\cap T|-1}{2}.
\]

The strongest elementary objection is that arbitrary dirty scratch does not obey the averaging relation. That objection does not invalidate the construction: it never substitutes an averaging relation for dirty data. The two readouts cancel it:

\[
-R'c+R'(c+G'x)=R'G'x,
\qquad(c+G'x)-G'x=c.
\]

The next objection is that `R'` is denser, so it might require incompatible gate labels. In [O], the original central readout is already a gate with a common label on the entire target bank and center. The denser readout touches no new class of wire, and the same full local-space label is available. Its extra scalar operations are fixed before the input length varies, so they enter the charged linear-work constant rather than the recurrence multiplier.

The chronological central labels remain `B tensor D`, `E tensor D`, `B tensor D`, `E tensor D`. Each surviving wire decreases exactly once by `h` dimensions. This also holds for the physical chronology of the inverse middle invocation. Therefore

\[
L=3v^2h^2,
\qquad \Delta=2v^2(v-3h^2),
\qquad v=\binom h3.
\]

At `h=24`, the original side-wire construction has

\[
W=34,666,930,287,616,
\quad m=13,824,
\quad \Delta=2,425,172,992.
\]

Padding to `2^45` retains [O]'s exact-batch proof. Its exact normalized saving is

\[
\varepsilon_* = \frac{2,368,333}{474,989,023,199,232}.
\]

The inequalities `log(13,824)<9.54` and `epsilon_* > (5.2e-10)*9.54` certify the conservative exponent. Both are supplied as rational certificates in the short proof and code.

**Assessment:** High confidence in this modification relative to the cited upstream frame and transfer lemmas. It does not depend on the shared-sum graph or on the new batching lemma.

## 4. Remainder batching: the cost is charged correctly

The relevant concern is not whether fewer than `W` fibers remain. It is whether their repeated direct treatment adds an extra logarithmic factor across recursion levels.

For `f=floor(k/m)`, a directional step has `F=2^(k-f)` fibers of length `2^f`. Run `floor(F/W)` full recursive batches and treat the remaining `F mod W` fibers directly. The exact cost inequality is

\[
T(k)\le A_0 W2^k+s\left\lfloor\frac{2^{k-f}}W\right\rfloor T(f)
       +B s(W-1)f2^f.
\]

After normalizing `t(k)=T(k)/(W2^k)`, the full-batch coefficient is at most `s/W`, and the remainder costs at most `Bs f2^(f-k)`. Since

\[
f2^{f-k}\le f2^{-(m-1)f}\le 1,
\]

that work is absorbed into a constant independent of `k`. The resulting recurrence is

\[
t(k)\le A+(s/W)t(\lfloor k/m\rfloor).
\]

All costs recur through this inequality; they are not silently discarded after one level. Its ordinary unrolling gives `theta=log_m(s/W)` at the critical exponent. Integer quotient/remainder calculation and batch setup can be charged within the same per-step linear bound. Packed fibers and full batches are contiguous under [O], Lemma 2.5. Serial recursion and workspace reuse preserve logarithmic-size addresses. The base range `k<m` is finite.

The new code additionally checks 18,620 integer batching cases covering non-power-of-two widths, including cases with no full recursive batch. These tests supplement the inequality above; they do not prove its asymptotic consequence.

**Assessment:** High confidence in the written recurrence argument under the complete finite-network interface. This supports `5.3e-10` without the shared-sum replacement.

## 5. Shared-sum integration: stronger coverage, no additional loss found

The old verifier checked an entire coefficient matrix and global support traces, but its actual binary-space edge audit used one canonical pair group. The written proof supplied the argument for combining groups. That was a limit on test coverage, not by itself a logical defect in the proof.

The second verifier now constructs **the complete multi-pair graph**, not just one pair. It checks every shared-scratch path, every bank path and every reduced-center path through the whole local invocation for all three stage dimensions. Source fan-out across pair groups is part of this run.

For a binary subspace, it constructs the actual symmetric idempotent projection matrix. For every distinct projector it checks symmetry, idempotence, rank, and the nondegeneracy of its range using a Gram matrix. For an edge it checks nesting by projector multiplication, computes the residual projector, checks its rank, and tests whether the nonzero total residual is nonalternating. The constructive classification in [O], Lemma 2.3, then supplies an orthonormal basis. This is a different representation from the first verifier.

The physically relevant stage label is represented by its two orthogonal components, `B tensor A` and `P tensor Z`, with exact multiplicity `dim(B)=h^(j-1)-1`. The earlier and future tensor factors still use the written tensor-product argument. Thus this is **not** a literal enumeration of all global `h^3`-dimensional arrays or all trillions of invocations.

The central inverse-stage question is answered by complementing the support spaces in reverse scalar order:

\[
U_A\subset U_S
\quad\Longrightarrow\quad
U_S^\perp\subset U_A^\perp.
\]

The readout's target indicator is orthogonal to the partial source support, allowing the crossing from the target frame into that complementary path. Splitting the outputs preserves an unused coordinate, hence a norm-one vector in the critical residual. The full graph checks found no source-fan-out path that invalidates these inclusions.

| Ground size | Shared roles | Forward scratch shears | H2 matrix entries covered | Wire-edge checks, all 3 stages | Distinct binary projectors |
|---|---:|---:|---:|---:|---:|
| `h=24` | 22,632 | 31,096 | 4,096,576 | 1,045,296 | 26,131 |
| `h=25` | 25,800 | 35,500 | 5,290,000 | 1,191,975 | 29,803 |

The edge counts include zero-residual touches and the explicitly represented bank/center gate boundaries. The unchanged disjointness-scratch paths are checked by an actual canonical disjoint-pair projector calculation plus the coordinate-permutation argument; they are not included as millions of separately enumerated side wires.

In every stage, the only decreasing dimension was `h^2` on the center: `576` at `h=24` and `625` at `h=25`. Shared scratch and banks contributed no decreases. The absolute dimension sum equaled the signed terminal increase plus twice this central loss, as required.

**Assessment:** Moderate-to-high confidence in the shared-sum integration after this second implementation and written review. It remains the most intricate new part, and its tensor lifting deserves an independent referee's attention.

## 6. Arbitrary scratch is now tested symbolically, not only with examples

At `h=7` and `h=8`, the second program executes the **complete local scalar operator** using sparse rational coefficients for every initial input and every dirty scratch coordinate. It checks the exact linear operator after the first word, after the reversed middle word, and after the final word.

| Ground size | Scalar registers | Elementary shears in the forward word | Matrix coefficients covered at each checkpoint |
|---|---:|---:|---:|
| `h=7` | 511 | 3,122 | 261,121 |
| `h=8` | 1,184 | 6,720 | 1,401,856 |

Every final scratch row is the corresponding identity row, and the banks have exactly the signed-exchange rows. There is no random sampling in these checks. These smaller values verify scalar identities; they do not have a positive asymptotic-saving budget and do not constitute a run of the full Fourier transform.

## 7. Negative controls and issues that were tightened

Four explicit negative controls expose the expected failures:

- The unsplit full pair-family output at odd ground size `h=25` leaves a nonzero, two-dimensional alternating residual. It fails the required orthonormal-basis condition.
- Blind reversal of a strictly increasing support path introduces a downward edge; the zero-added-loss assertion cannot be retained.
- Replacing the central coefficient `-1/6` with `-1/3` fails the identity for intersection sizes.
- Omitting the dirty-scratch compensating replay produces a nonzero output from dirty scratch even when the source is zero.

These are targeted counterexamples/negative controls, not an assertion that all possible incorrect circuits are detected by the test suite.

No theorem-changing error was found. The main corrections are in presentation and evidence: the canonical-pair test boundary is now replaced by a full multi-pair local audit; the current review is explicitly not called independent review; and the short proof distinguishes the critical saving from its pure-power corollary. A display typo (`rac` instead of `\frac`) in the old note's numerical-certificate section is corrected in the short typeset note; the prior code used the intended quantity. The archived original draft has not been silently rewritten.

## 8. A useful new scoped lower bound

We cannot continue deleting center coordinates merely by refactoring the same central matrix through fewer scalar coordinates. Let `G` be the `h by v` incidence matrix and `J_h` the all-ones matrix. Then

\[
GG^T=\frac{(h-2)(h-3)}2 I_h+(h-2)J_h
\]

is invertible for `h>=4`, and the central matrix is

\[
M=G^T\left(\frac12I_h-\frac1{18}J_h\right)G.
\]

The middle factor is invertible for `h != 9`, so at `h=24,25`, `rank(M)=h`. Any **single factorization** `M=RG` through `r` coordinates has rank at most `r`, forcing `r>=h`. Thus the removed coordinate exhausts this particular redundancy.

This is not a lower bound for all schedules or Fourier algorithms. Time reuse, additional passes, a different central matrix with different side corrections, or a different finite network remain outside its scope.

## 9. The all-length dependency check

The remaining dependency is not a mysterious loss factor:

`finite interface -> C tensor powers -> Proposition 4.2 -> Section 5`.

[O], Proposition 3.1, depends on the fixed two-coordinate kernel `C`, not on `h`, `W`, or the original decimal exponent. Our modifications leave `C` unchanged. Proposition 4.2 uses the tensor cost through `2^k(k+1)^theta`, with `k` at most the number of odd-prime axes. Its bound therefore remains valid for the new `0<theta<1`. The Section 5 prime-count, CRT, chirp, and root-order arguments are unchanged. They yield

\[
O(n(\log n)^\theta(\log\log n)^{4-\theta}),
\]

with all fixed-operand transforms and preparations still charged. New rational coefficients require no new roots. The logarithmic factor is absorbed only after choosing `delta<1-theta` strictly.

I did not independently formalize or mechanically verify the upstream exact-width compiler, the prime estimates, CRT/chirp reduction, or every assertion in the original manuscripts. The current result remains an extension relative to those specified results. The independent finite-win/price argument in the 49-page paper is not needed for this route.

## 10. What is ready for review

The package separates a five-page short proof (`CORE_PROOF.pdf`) from the full shared-sum draft. The short theorem obtains `5.2e-10`; one further standalone batching lemma gives `5.3e-10`. An expert can accept or reject those without first auditing the shared-sum graph. The more involved full draft claims `5.5e-10` and survived the expanded projector-based checks.

My current recommendation is to lead review with the short proof, while supplying the stronger argument as an extension. The priority questions for a referee are the retained center gate labels, the inverse middle orientation, applicability of the upstream compiler/transfer, and then the tensor lifting of the full shared-sum schedule.

### Reproduction

Run `python clean_room_audit.py` with Python 3.10 or later; no third-party packages are required. The original package and rerun log are included under `previous_draft/` and `PREVIOUS_SUITE_RERUN.txt`. The second run's detailed rational bounds and counters are in `clean_room_certificate.json`; the console output is `CLEAN_ROOM_RUN.txt`. The PDF is built from `CORE_PROOF.tex` with `pdflatex`.

### Source identifiers

- [O] OpenAI, *An explicit power saving for the exact discrete Fourier transform*, September 25, 2026; uploaded `main (1).pdf`. SHA-256: `670d0115ea2553e65f22167c176d2f31218d4d41726fe4e5702e2b149cad0896`.
- [F] OpenAI, *Finite tensor savings and exact Fourier circuits*, September 25, 2026; uploaded `main.pdf`. SHA-256: `e2165b9f6796f0189292220c7edc0c6e19789bd8329a127a24d404da1e81e06b`. This paper's separate existence argument is not a dependency.
- [P] Previous `fourier130_v2/PROOF.md`. SHA-256: `26357c80fb07b4fb1f7121b0b4284ed2137f98895045bfb530e92b268ab89926`.
- [D] Douglas Colkitt, `CrocSwap/integer-mult-bounds`, `notes/independent-complex.tex` and `docs/research/current-status.md`, inspected October 8, 2026. https://github.com/CrocSwap/integer-mult-bounds/blob/main/notes/independent-complex.tex and https://github.com/CrocSwap/integer-mult-bounds/blob/main/docs/research/current-status.md . Limited provenance check, not a comprehensive priority search.
