# An Improved Exponent Bound for the Exact Discrete Fourier Transform

**Research draft, October 8, 2026.**

The candidate conclusion, in precisely the upstream arithmetic/root/address model, is

\[
\boxed{T(n)=O\!\left(n(\log n)^{1-5.5\times10^{-10}}\right).}
\]

There is a simpler fallback with exponent saving `5.2e-10` that does **not** depend on the shared-sum replacement or the new batching lemma. A middle version obtains `5.3e-10` without the shared-sum replacement.

## 1. Source, attribution, and the exact target

Write [O] for the uploaded 31-page *An explicit power saving for the exact discrete Fourier transform*. Its main quantitative proof is Sections 2–5. The uploaded 49-page companion, *Finite tensor savings and exact Fourier circuits*, gives an independent finite-win existence route; that argument is not required for the explicit quantitative modification here. [O], Introduction and Section 1.2, explicitly separates these routes.

The model counts exact complex field operations, preparation of input-independent coefficients, schedule construction, array organization, and unit-cost operations on logarithmic-size integer addresses. A specified root of unity is supplied as in [O]. No bounded-coefficient, stable floating-point, or integer bit-complexity conclusion is asserted.

[O] fixes `h=100` and proves

\[
T(n)=O\!\left(n(\log n)^{\theta_0}(\log\log n)^{4-\theta_0}\right),
\qquad 1-\theta_0=2.10643843004018\ldots\times10^{-13}.
\]

Its headline `1e-13` saving is a weaker rounded corollary. Comparisons must use both quantities honestly.

Douglas Colkitt already identified the usefulness of the unchanged complex network at `h=25`, and gave its parameters and compatibility argument in `notes/independent-complex.tex` in `CrocSwap/integer-mult-bounds`. We do **not** claim the independent-ground-size idea or that parameter choice as new. His displayed complex construction still has `h+1` central wires. The present draft removes a redundant central wire, supplies a no-padding recurrence, and completes a proposed phase-label integration for the earlier shared-sum circuit. Originality beyond the sources checked has not been established.

## 2. Remove one redundant central wire

Let

\[
\mathcal T=\binom{[h]}3,\quad v=\binom h3,\quad m=h^3,\quad N=v^3,\quad I=3v^2.
\]

One invocation acts on source and target banks indexed by triples. [O], Section 2.1, uses central coordinates `c_1,...,c_h,c_*`, with

\[
(Gx)_j=\sum_{T\ni j}x_T,\qquad (Gx)_*=\sum_Tx_T,
\quad (Rc)_S=\frac{\sum_{j\in S}c_j-c_*}{2}.
\]

But every source triple contributes to exactly three of the first `h` sums. Thus **the source-dependent part** of `c_*` is redundant. This is not a claim that arbitrary initial scratch obeys a linear relation.

Use only `h` central coordinates, and define

\[
(G'x)_j=\sum_{T\ni j}x_T,
\qquad
(R'c)_S=\frac12\sum_{j\in S}c_j-\frac16\sum_{j=1}^h c_j.
\]

For each source triple `T` and target triple `S`,

\[
(R'G')_{S,T}=\frac{|S\cap T|}{2}-\frac36
=\frac{|S\cap T|-1}{2}.
\]

This is exactly the old central matrix. The arbitrary-scratch argument is also exact:

\[
-R'c+R'(c+G'x)=R'G'x,
\qquad(c+G'x)-G'x=c.
\]

No initially-zero or constrained center is required.

Keep the side corrections `+1/2` for intersection zero and `-1/2` for intersection two. Their sum with the central coefficient is zero for intersection sizes `0,1,2`, and one for intersection size `3`. The scalar invocation remains the bank shear, and the three invocations remain the signed bank exchange.

All surviving central gates retain their full local-space labels in [O], Table (2.7). The sole central decrease still has dimension `h` per central wire, but there are now `h` such wires rather than `h+1`. Therefore the total loss is

\[
\boxed{L=Ih^2=3v^2h^2.}
\]

The denser expression for `R'` increases a fixed number of scalar operations. Since `h` and the entire network are fixed before the input length is chosen, these operations enter the additive linear-work constant, not the recursion exponent. Its coefficients are explicit rationals with nonzero denominators.

## 3. The shared-sum replacement and its reversible role compiler

Let

\[
(H_2x)_T=\sum_{S:\,|S\cap T|=2}x_S.
\]

For each fixed pair `Q`, list the `r=h-2` remaining vertices, and abbreviate `x_i=x_{Q union {i}}`. Compute prefixes up to index `r-3` and suffixes from index `2`:

\[
P_i=x_0+\cdots+x_i\ (0\le i\le r-3),
\qquad S_i=x_i+\cdots+x_{r-1}\ (2\le i\le r-1).
\]

Inject two separate partial outputs into target `t`:

- `t=0`: `x_1` and `S_2`;
- `1 <= t <= r-2`: `P_(t-1)` and `S_(t+1)`;
- `t=r-1`: `P_(r-3)` and `x_(r-2)`.

Every required ordered source–target pair occurs exactly once, in its unique common pair group. Every partial support has at most `h-4` source triples. Do not combine the two partial outputs into one scratch output.

The number of addition nodes and output uses is

\[
c=\binom h2(2h-10),\qquad q=2\binom h2(h-2).
\]

Assign a provisional physical role to every directed use, including output uses. At each addition, identify its first incoming role with its first outgoing role. The compiler first fans out sources, then processes additions topologically: add the second incoming role into the first, then copy that pivot into its other outgoing roles. Copies mean reversible additions into arbitrary scratch, not overwrites. This defines an invertible linear map `A` on the scratch roles. The dirty contents will be canceled below.

There are `2c+q` directed uses and `c` pivot identifications, so

\[
\boxed{R_2=c+q=\binom h2(4h-14).}
\]

Let `V_2` inject each source into its pivot and let `J` read the designated partial-output roles. Exact coefficient propagation gives `J A V_2=H_2`. Write `J_2=-J/2`.

The two-pass computation

\[
Az\ \longrightarrow\ \text{subtract }J_2Az\ \longrightarrow\ z,
\]

followed by injection `z += V_2x`, a second application of `A`, positive output injection, reversal, and removal of `V_2x`, restores arbitrary scratch and adds

\[
J_2A(z+V_2x)-J_2Az=-\tfrac12H_2x.
\]

This proves the scalar identity. The next two sections address the additional phase-label obligation; the scalar identity alone would not suffice.

## 4. Binary spaces and a complete forward invocation schedule

Use the local binary space `D=F_2^h`. Retain [O]'s stage factors

\[
E=B\perp P,\qquad \dim P=1,\qquad\dim B=h^{j-1}-1,
\]

and its future norm-one line `Q_f`. Suppress tensoring every displayed label with `Q_f`. For a local subspace `U`, write

\[
\ell(U)=B\otimes U,\qquad
M(U)=(B\otimes D)\perp(P\otimes U),\qquad
H=E\otimes D=M(D).
\]

For the pair family `Q={a,b}`, its triple labels are `t_i=e_a+e_b+e_i`. They are orthonormal. For a partial support `S`, let `U_S=span{t_i:i in S}`. The label attached to a reversible addition or copy is the support of its underlying DAG node, including both predecessors of an addition.

Along each physical role during the forward compiler, these supports only grow. Each output role has one designated readout and its last support is precisely the support it injects. The tagged compiler checks these properties on the complete multi-pair graph, including fan-out of a source into different pair groups.

Let `z` denote new shared scratch and `a_0` the unchanged disjointness side roles. `V_0,J_0` are the original disjointness injection and signed readout maps. The following sequence realizes one **forward** invocation. A label in a bank-specific row uses that bank entry's triple `t`.

| Step | Scalar operation | Common label on touched roles |
|---:|---|---|
| 1 | `y -= J_0 a_0` | `ell(t_Y)` |
| 2 | `z <- A z` | `ell(D)` on each elementary gate |
| 3 | `y -= J_2 z` | `ell(D)` |
| 4 | `z <- A^-1 z` | `ell(D)` |
| 5 | `y -= R' c` | `ell(D)` |
| 6 | `a_0 += V_0 x`, `z += V_2 x` | `M(t_X)` |
| 7 | `z <- A z` | `M(U_S)` for each tagged gate |
| 8 | `c += G' x` | `H` |
| 9 | `y += R' c` | `ell(D)` |
| 10 | `y += J_0 a_0`, `y += J_2 z` | `M(t_Y^perp)` |
| 11 | `c -= G' x` | `H` |
| 12 | `z <- A^-1 z` | `H` |
| 13 | `a_0 -= V_0 x`, `z -= V_2 x` | `H` |

The disjointness negative readout is deliberately performed before the new negative readout raises the Y-bank labels to `ell(D)`.

The input bank labels are `(E tensor <t>)` on X and `ell(t)` on Y. They finish at `H` on X and `M(t^perp)` on Y, exactly the boundaries in [O]. All scratch begins at label zero and finishes at `H` before its unchanged extension through the future-space complement to the global sink label.

Every new-scratch edge is increasing. In particular, support propagation in step 7 gives `M(U_A) subset M(U_S)` when `A subset S`. An output supported on `S` contains only sources orthogonal to its target `t`, so `U_S subset t^perp`, permitting its step-10 readout. Step 12 raises any remaining label to `H` before uncomputation.

## 5. The inverse invocation: do not reverse labels blindly

Stage 2 uses the inverse scalar invocation with logical source Y and target X. Reversing the scalar updates is necessary; reversing the forward label sequence would introduce decreases and is **not** what is done.

The following chronological schedule is exactly the inverse scalar word after exchanging logical source and target:

| Step | Scalar operation | Common label |
|---:|---|---|
| 1 | `a_0 += V_0 y`, `z += V_2 y` | `ell(t_Y)` |
| 2 | `z <- A z` | `ell(U_S)` for each tagged gate |
| 3 | `c += G' y` | `ell(D)` |
| 4 | `x -= J_0 a_0`, `x -= J_2 z` | `M(t_X)` |
| 5 | `x -= R' c` | `H` |
| 6 | `c -= G' y` | `ell(D)` |
| 7 | `z <- A^-1 z` | `M(U_S^perp)` in reverse tagged-gate order |
| 8 | `a_0 -= V_0 y`, `z -= V_2 y` | `M(t_Y^perp)` |
| 9 | `x += R' c` | `H` |
| 10 | `z <- A z` | `H` |
| 11 | `x += J_2 z` | `H` |
| 12 | `z <- A^-1 z` | `H` |
| 13 | `x += J_0 a_0` | `H` |

A growing support path `U_A subset U_S` becomes an increasing complementary path `U_S^perp subset U_A^perp` under reverse order in step 7. At a designated output, the target `t_X` is orthogonal to its source support `U_S`, so `M(t_X) subset M(U_S^perp)`. At a source pivot the final transition to `M(t_Y^perp)` is also increasing.

Thus the inverse invocation preserves the required physical X/Y boundary labels and adds no shared-scratch decreases. Its center alone drops from `H` to `ell(D)` at steps 5 to 6, once per central wire, of dimension `h`.

## 6. Nondegeneracy, residual orthonormal bases, and the full interface

The previous inclusions must also have the residual bases required by [O], Lemma 2.2. Here is a classification, rather than an assumption that nondegeneracy alone is enough in characteristic two.

**Subset and complement paths.** Every `U_S` is spanned by an orthonormal subset. Residuals for `U_A subset U_S` and `U_S^perp subset U_A^perp` have the explicit orthonormal basis indexed by `S minus A`.

**Complements of partial supports.** A partial support has at most `h-4` members of one pair family. Its union of coordinate supports misses at least two local coordinate units. Therefore `U_S^perp` is nondegenerate and contains a norm-one coordinate vector.

**Readout residuals.** The target label is a member of the same orthonormal pair family, outside `S`. The space

\[
(U_S\perp\langle t\rangle)^\perp
\]

is nondegenerate and contains a coordinate unit outside both the partial support and the target: at least one such coordinate remains. Consequently it is nonalternating and has an orthonormal basis by the constructive unit-line/alternating-plane argument in [O], Lemma 2.3.

**Crossings between lower and upper levels.** For example,

\[
\ell(U_A)\subset M(U_B^\perp)
\]

has residual

\[
(B\otimes U_A^\perp)\perp(P\otimes U_B^\perp).
\]

Both local complements are of the preceding kind. The analogous crossing to `M(t)` has residual `(B tensor U_A^perp) orthogonal-sum (P tensor <t>)`. All nonzero summands have norm-one vectors and orthonormal bases. Zero-dimensional factors are omitted.

The relevant nonzero `B` spaces and future complements retain the upstream norm-one-coordinate argument: their excluded tensor indicators have support `3^r<h^r`. Tensoring orthonormal bases and taking orthogonal sums preserves an orthonormal basis. This includes the final auxiliary extension to the full ambient `h^3`-dimensional space.

The old disjointness-side edges are exactly the upstream edges, whose two triple supports occupy at most six coordinates; `h=24` is more than enough. Every surviving central edge has the original label and residual type. The only downward edges are therefore still the central crossings, now on `h` wires per invocation.

The source/sink labels and signed scalar exchange remain unchanged. The exceptional terminal vector has weight `3^3=27`, so the same endpoint translations in [O], Proposition 2.4, give `C^(tensor mf)` on **every** physical role, including all new scratch roles. Each scalar gate has a common frame on all roles it touches, so the cancellation identity [O], Equation (2.6), applies without assuming anything about scratch values.

This establishes the proposed modified finite-network interface: `s` directional steps, each implementable as copies of `C^(tensor f)`, and a fixed number of pointwise operations and address permutations, uniformly for every integer `f>=1` and spectator bits.

## 7. Exact network counts

For the reduced center plus shared-sum network,

\[
\begin{aligned}
W&=2v^3+3v^2\left(v\binom{h-3}{3}+\binom h2(4h-14)+h\right),\\
L&=3v^2h^2,\\
\Delta&=2(N-L)=2v^2(v-3h^2),\\
s&=Wm-\Delta.
\end{aligned}
\]

The first term in `W` counts the two banks; the next terms count disjointness roles, shared intersection-two roles, and central roles in all `3v^2` invocations.

At `h=24`,

\[
\begin{aligned}
v&=2024,&m&=13824,&N&=8291469824,\\
I&=12289728,&L&=7078883328,\\
W&=33377983614976,&\Delta&=2425172992,\\
s&=461417243068255232.
\end{aligned}
\]

In particular `Delta>0`, and `1<s/W<m`.

The `h=24` choice was selected by a finite parameter exploration, not by a proof of global optimality. No optimality claim is needed for the asserted upper bound.

## 8. A no-padding tensor recurrence

[O], Section 2.6, pads `W` to a power of two to make every recursive batch full. Reducing `W` alone need not improve its exponent: both old and new widths may pad to the same power of two. This is why the earlier local width reduction was not automatically an exponent improvement.

**Batching lemma.** Suppose a fixed finite network with `W` roles and `s` directional steps satisfies the complete interface above for a fixed `m>=2`, with `1<s/W<m`. Then its tensor transform has deterministic charged cost

\[
O\!\left(2^k(k+1)^\theta\right),\qquad \theta=\log_m(s/W),
\]

without requiring that `W` be a power of two.

**Proof.** First transform `W` arbitrary arrays at once. For `k>=m`, put `f=floor(k/m)` and `r=k-mf`. Process the fewer than `m` leftover axes directly. One directional step contains `F=2^(k-f)` independent fibers of length `2^f`. After the upstream linear-time permutation, process `floor(F/W)` full batches recursively. Process the remaining `F mod W<W` fibers with the ordinary coordinate-by-coordinate tensor algorithm, at cost at most

\[
B(W-1)f2^f
\]

for an absolute `B`. The quotient, remainder, batch boundaries, and the ordinary leftover transforms use the same logarithmic-word model; discovery and movement remain linear in array length.

Let `T(k)` be the cost for `W` arrays and `t(k)=T(k)/(W2^k)`. With all nonrecursive fixed-network work charged,

\[
T(k)\le A_0W2^k+s\left\lfloor\frac{2^{k-f}}W\right\rfloor T(f)
+B s(W-1)f2^f.
\]

Using the upper bound on the floor gives

\[
t(k)\le A_0+\frac{s}{W}t(f)+B s f2^{f-k}.
\]

Since `k>=mf` and `m>=2`,

\[
f2^{f-k}\le f2^{-(m-1)f}\le1.
\]

Thus the leftover work is a bounded additive term in this normalized recurrence:

\[
\boxed{t(k)\le A+\frac{s}{W}t(\lfloor k/m\rfloor).}
\]

Its constants are fixed independently of `k`. The finite range `k<m` is handled directly. The same recurrence unrolling as in [O], Theorem 2.6, gives the critical exponent `theta=log_m(s/W)`. The recursive arrays can be processed serially with workspace reuse, and their address fields require `O(k+1)` bits. A single requested transform initializes the other `W-1` roles once, at cost `O(W2^k)=O(2^k)` because `W` is fixed. This proves the lemma.

This is a deterministic remainder-handling argument, not an assumption of free padding, fractional batches, or average-case input data.

## 9. Propagation to all Fourier lengths

The tensor interface is exactly the input consumed by [O], Proposition 4.2. Its local Fourier compiler in Section 3 uses the same fixed two-coordinate complex matrix `C`; none of its local-width, scalar-preparation, nonzero-denominator, or root requirements change.

The sector packing work is unchanged. It gives cost

\[
O\!\left(R(\ell+1)^\theta(1+\log r_{\max})^4\right)
+\operatorname{poly}(\ell,r_{\max},\log R).
\]

The small-prime working length, CRT permutations, and charged chirp convolution in Section 5 are likewise unchanged. Substituting `ell=Theta(log n/log log n)` gives

\[
\boxed{T(n)=O\!\left(n(\log n)^\theta(\log\log n)^{4-\theta}\right).}
\]

This also accounts for the transformed fixed convolution operand. The specified root of order less than `1024 n^3` remains sufficient. New fixed rational coefficients introduce no additional root requirement.

Write

\[
a=1-\theta=-\frac{\log(1-\Delta/(mW))}{\log m}.
\]

For **every fixed** `0<delta<a`, the `log log` factor is absorbed by `(log n)^(a-delta)`, yielding `O(n(log n)^(1-delta))`. There is no mandatory factor-of-two loss in `delta`; the upstream headline's halving was a convenient conservative corollary.

## 10. A rational certificate for the proposed exponent

The new critical saving is

\[
a=5.5127258849324290013\ldots\times10^{-10}.
\]

A safe witness is `delta=55/10^11=5.5e-10`. This is certified without a floating-point comparison.

Set `epsilon=Delta/(mW)`. The verifier establishes by exact fractions that

\[
\epsilon>\frac{55}{10^{11}}\frac{477}{50},\qquad \log(13824)<\frac{477}{50}=9.54.
\]

For the latter inequality, the positive finite sum

\[
\sum_{j=0}^{40}\frac{(477/50)^j}{j!}>13824
\]

certifies `exp(9.54)>13824`. Therefore

\[
a=\frac{-\log(1-\epsilon)}{\log m}
>\frac{\epsilon}{9.54}>\frac{55}{10^{11}}.
\]

The reported finer numerical values are computed using exact rational atanh-series enclosures, with an explicit tail bound. The JSON contains the actual rational interval endpoints. Decimal endpoints can round to the same displayed string; the rational endpoints remain distinct rigorous enclosures.

## 11. Separate the improvements and their proof dependencies

Here `a=1-theta` is the critical saving **before** absorbing the `log log` factor. Any smaller positive `delta` gives a pure-power corollary.

| Construction | Critical saving `a` | Additional proof ingredients |
|---|---:|---|
| Uploaded paper, `h=100`, padded | `2.10643843004018e-13` | Upstream |
| Original network, `h=24`, padded | `3.95761002385911e-10` | Generalize the displayed fixed-size network to this valid `h` |
| Reduced center, `h=24`, padded | `5.22969896327091e-10` | Section 2 of this note; upstream batching retained |
| Reduced center, `h=24`, unpadded | `5.30775793289321e-10` | Also the remainder-handling lemma |
| Reduced center + shared sums, `h=24`, unpadded | `5.51272588493243e-10` | Also the two-orientation phase schedules |

The first reduced-center version supports the simpler `delta=5.2e-10` claim without relying on the proposed shared-sum phase integration. The next supports `5.3e-10`. Thus a flaw in the shared-sum argument would not, by itself, revoke the simpler candidates.

Most of the gain relative to the uploaded paper comes from a better ground size. That must not be portrayed as a new fundamental Fourier method. The shared-sum component adds about **3.8617%** to the reduced-center unpadded critical saving. Relative to the already-retuned `h=25` complex-network threshold of `4.18479903721200e-10`, the new critical saving is only about **31.73% larger**, not thousands of times larger. The direct all-length transfer and the new finite modifications must be distinguished from the ground-size retuning already present in Colkitt’s work. All ratios concern asymptotic exponent savings, **not measured speedups**.

## 12. Reproduction, evidence, and remaining review

Run with Python 3.10 or later, using only its standard library:

```sh
python verify_extension.py
```

The program performs:

1. Exact reconstruction of the uploaded `h=100` counts, exact new counts, and rational witness comparisons.
2. The reduced-center coefficient identity for all intersection sizes, and the general dirty-scratch cancellation argument recorded in its output.
3. Exact verification of every local `H_2` coefficient at `h=24` and `h=25`, plus dirty-scratch executions and agreement of tagged and untagged compiler implementations.
4. A support-label trace for every role of each full multi-pair graph, including source fan-out and unique designated readout roles.
5. Actual binary linear algebra on every canonical-pair wire edge in the forward first/third stages and inverse middle stage at both ground sizes. It verifies inclusions, nondegeneracy, residual dimensions, and orthonormal bases for the relevant nonalternating components. Coordinate permutations cover the other pair groups; the global support trace checks the shared source fan-out between groups.

6. Execution of the complete modified local scalar word, its reversed middle word, and their three-shear signed bank exchange on arbitrary rational scratch examples at `h=7,8`. These small sizes test the scalar identities only, not positive asymptotic savings.

At `h=24`, the shared graph has `22,632` roles, `31,096` elementary operations in its forward scratch map, and `12,144` output reads. Its local `H_2` matrix has `2,024^2=4,096,576` entries; `127,512` are nonzero. At `h=25` the prior corresponding counts are also reproduced.

**Limits of these checks.** They are not a numerical execution of the astronomical complete DFT algorithm. They do not mechanically prove the asymptotic recurrence, the upstream exact-width compiler, the entire global `h^3`-dimensional phase network, or the all-length reduction. Those conclusions use the written arguments and identified upstream results. The canonical frame audit is a symmetry-reduced check of the modified component, not a claim to enumerate every global role of the full network.

Before presenting this publicly as an established advance, independent review should prioritize the two orientation schedules, the transfer from full support traces to global residual classification, the arbitrary-scratch interpretation, and the no-padding recurrence. A comparison with other follow-ups is still needed for priority. The formulas in Sections 2 and 8 are short enough to review separately from the larger shared-sum construction.

## References

[O] OpenAI. *An explicit power saving for the exact discrete Fourier transform*. September 25, 2026. Uploaded file `main (1).pdf`. Especially Sections 2.1–2.6, Proposition 3.1, Proposition 4.2, and Section 5.4.

[F] OpenAI. *Finite tensor savings and exact Fourier circuits*. September 25, 2026. Uploaded file `main.pdf`. The independent finite-win route is not a dependency of the proposed explicit quantitative extension.

[D] Douglas Colkitt. `CrocSwap/integer-mult-bounds`, `notes/independent-complex.tex` and `docs/research/current-status.md`, accessed October 8, 2026. The latter states that his results remain conditional and not independently/formally verified.

https://github.com/CrocSwap/integer-mult-bounds/blob/main/notes/independent-complex.tex

https://github.com/CrocSwap/integer-mult-bounds/blob/main/docs/research/current-status.md

[P] The October 7 local shared-sum working note and executable verifiers supplied earlier in this conversation. They explicitly did not establish the Fourier transfer. The present note supersedes that uncertainty with the proposed complete schedules and transfer argument; it does not retrospectively strengthen what the earlier checks established.
