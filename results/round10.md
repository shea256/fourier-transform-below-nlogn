## 6. Base construction: round-ten paired cubes

**Record date:** October 9, 2026. **Status:** proposed conditional Fourier transfer with finite checks; independent mathematical review and end-to-end formal verification remain pending.

The complex word is pinned to Swapnil Jain's `integer-mult-kappa`, commit `d2f6146ffbbd893e69b8fb06bc53b82af36d8032` [J10]. Its tensor witness and our Fourier choice are

\[
a=\frac{15402419}{25000000000}=0.00061609676,
\qquad \delta=\frac{61}{100000}=0.00061.
\tag{6.1}
\]

This record replaces the round-six finite network. It does not add successive networks' savings or substitute the integer-multiplication headline $\kappa$ into the Fourier theorem. Its new dependencies include icekylinx's arbitrary-subspace frames and three-stage covers [C130], paired cubes and completed-core sharing [C144], and the birth-reuse and module lineage retained in [J10]'s NOTICE.

### 6.1 Finite word and scalar identity

There are $p=11$ coordinate pairs, $h=22$ local binary coordinates and $v=8\binom{11}{3}=1320$ ports. A port chooses one coordinate in each of three distinct pairs; its address $q_S$ has norm one. The eight selectors on a fixed triple of pairs form a cube. The ambient cover has $m=3h=66$ coordinates.

For ports $T,S$, define

\[
B_{T,S}=\frac{|T\cap S|-1}{2},\quad
B_{\rm block}=\bigoplus_I B|_I,\quad
K=I-B_{\rm block},\quad H=B_{\rm block}-B.
\]

Then $K+H+B=I$. Within each cube, $K=(P-A)/2$, where $P$ is antipodal permutation and $A$ is adjacency at selector distance one. Its Walsh eigenvalues are $-1,-1,1,1$, according to selector weight, so $K^2=I$. The opposite-parity blocks are signed $4\times4$ Hadamard matrices divided by two.

The frozen signed addition DAG supplies $H$ and the coordinate-star contribution $B$. It uses a searched restriction of eumemic's PR117 triple module, the unchanged G37 pair module from eumemic's PR168, nested-prefix all-but-one modules, merged face/edge reads, and compatible carrier arcs. Jain's pair-aware gauge choice and operation-frame refinement are part of the pinned word. Re-running the search is unnecessary to specify this finite witness; verifying its final word is essential.

The word has 18,259 addition nodes, 4,477 output uses, 15,132 logical auxiliary roles and 32,071 compiled operations. A coordinate-star role is read through a paid copy at frame zero while its original remains on its ascending chain. The total copied-star loss is $\ell=h(h-2)=440$. The source registers themselves implement $K$: their parity blocks meet at a common three-dimensional frame, deliver their contributions at the assigned target hyperplanes, and undo $K$ at the full frame before source-subtraction cleanup. Each source contributes widths $[2,h-4,1]$; no extra $K$ bank is free or required. These are the exact scalar and geometric interfaces of [C144], instantiated on the new word.

Our verifier expands the signed DAG as integer coefficient vectors. After multiplying output coefficients by six, it checks **every** entry of $6(H+B+K)=6I$ and every cube's $K^2=I$. The full $1320^2=1742400$ coefficient check supplements the upstream random modular decoder trials. Conservative address spans include visited inputs even if signed coefficients cancel.

### 6.2 Arbitrary-subspace frames and exact adapters

The round-six projector argument is insufficient for the degenerate subspaces in this word. We instead use [C130]'s preimage-frame construction. In the binary symplectic space $\mathbb F_2^h\oplus\mathbb F_2^h$, put

\[
L_0=\{(0,z)\},\qquad
F=\begin{pmatrix}I&I\\0&I\end{pmatrix},\qquad
L_U=\{(u,u+v):u\in U,\ v\in U^\perp\}.
\]

Here $F$ also denotes the exact operator $C^{\otimes h}$; its exact square is a translation, although its binary symplectic square is identity. The spaces $L_U$ are Lagrangian, including for degenerate $U$, and

\[
d(L_U,L_V)=\dim U+\dim V-2\dim(U\cap V),\qquad
FL_U=L_{U^\perp},
\tag{6.2}
\]

where $d(L,L')=h-\dim(L\cap L')$. Indeed the intersection is parameterized by $u\in U\cap V$ and $v\in(U+V)^\perp$, and the symplectic pairings vanish.

For an invertible binary matrix $G$ with $GE_r=U$, choose an exact Gaussian-dyadic lift of

\[
K_G=\begin{pmatrix}G&0\\G+G^{-T}&G^{-T}\end{pmatrix},
\qquad T_U=K_G C_{E_r}K_G^{-1}.
\]

The lift $K_G$ is a binary permutation followed by a quadratic phase. In coordinates its phase matrix is $I+(GG^T)^{-1}$. Use $T_0=I$, $T_H=F$, the inherited norm-one source representatives, and block-factored representatives for cover offsets. The preimage convention is $L(T)=T^{-1}L_0$, so a physical transition $T_VT_U^{-1}$ has Fourier rank $d(L_U,L_V)$. For $U\subseteq V$ this is $r=\dim V-\dim U$.

The exact Clifford elimination interface of [C130] factors that transition into two rank-zero adapters and $r$ coordinate Fourier factors. No new irrational constant is needed, since

\[
\frac{1+i}{2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}
=SCS,\qquad S=\operatorname{diag}(1,i).
\]

All $rf$ coordinate factors are gathered into one recursive child. The adapters are the finite permutations and quadratic phases charged in Section 3. Registers participating in a scalar gate use the **same exact representative**; matching subspaces alone does not authorize the gate. Differently transported representatives with the same preimage are reconciled by their actual rank-zero quotient. Thus transitions telescope without assuming that distinct partial frames commute.

For the reverse/complement word use $D_U=T_UF^{-1}$. Its preimage is $L_{U^\perp}$ and $D_UD_V^{-1}=T_UT_V^{-1}$ exactly. Reverse every scalar operation, compensation read and cleanup, not merely the positive producer. Reconcile full endpoints by the actual Pauli and phase adapters. This preserves the transition widths while fixing their physical orientations.

The arbitrary-dimensional Clifford factorization is an explicit upstream proof dependency. Our exhaustive four-dimensional checks cover all 67 subspaces, the distance and complement identities, exact nested transitions, and the full-frame translation square; they do not prove the general factorization by enumeration.

### 6.3 Delayed compensation and physical register reuse

A reversible scalar program with source injection $V$, mixer $M$ and readout $J$ satisfies

\[
JM(z+Vx)-JMz=JMVx
\]

for arbitrary dirty $z$, and its inverse mixer and source subtraction restore $z$. When centre outputs are read at an intermediate clock, the same identity uses the sum of their linear responses at the actual read clocks. Back-propagating their exact coefficients through the signed gates gives the compensation coefficient for each initial role.

**Reuse lemma.** Suppose a recipient role has no incident operation before clock $t$, and its old-value read occurs at $t$ before its first incident operation. Its initial scalar value can be any $w$: the output response to $w$ is exactly its back-propagated coefficient times $w$, canceled by that old-value read. Now suppose a donor has finished all incident operations and is not an output role. Place the recipient on that physical register after the donor's last operation. The current donor value is a permissible $w$, even though it depends on earlier data and scratch. The recipient's compensation removes its entire contribution. The earlier part of the computation is unaffected because the recipient had not been touched and the donor is no longer read. This argument iterates down an acyclic chain of reuse pairs.

The actual sequence consists only of invertible gates on distinct physical registers. After the readouts, reverse that sequence at the full frame, then subtract the original source injections. This restores every initial physical scratch value. Hence reuse does not require zero scratch, an extra fresh array or a data-dependent erasure. This is the birth/late-compensation mechanism of PR124 and PR143, specialized to the checked word.

The physical hand-off additionally requires the donor's last frame to lie inside the recipient's entrance gauge, and all later frames on the joined chain to remain nested. The donor frame moves to the recipient frame before the read. Every positive rank difference is paid. If the subspace representatives differ, their exact quotient is implemented as in Section 6.2.

For the selected witness every one of the 3,180 gauged roles is a recipient. The 15,132 logical roles therefore occupy 11,952 physical auxiliary registers. All physical chains start at a zero gauge: source-carrier loads from zero to their norm-one line are explicitly included. No unpaired gauge tail remains, and nullity-dependent sharing contributes no additional saving to this selected complex word.

The finite checker verifies matching, acyclicity through strict time ordering, final donor use, the absence of donor output roles, first recipient use, exact compensation-target support, frame containment and every joined chain. It also checks the carrier payloads at centre and final read clocks. The imported aliased scalar replay uses two exact modular trials and negative controls; the universal arbitrary-scratch conclusion uses the reuse lemma, not those trials alone.

### 6.4 Three-stage cover and arbitrary-array endpoints

Use [C130]'s three-stage data cover, embedded in the $m=3h$ space of [C144]. Let $E_0=A\perp B\perp D$ have dimensions $h,h-1,h-1$ and embed it as a nondegenerate subspace of the 66-dimensional ambient space. For each norm-one port vector $q$, choose the explicit orthogonal involutions $R_{12,q},R_{23,q}$ exchanging $A\cap q^\perp$ with $B$ or $D$ and fixing $q$. Extend them by identity outside $E_0$. Invocation vertices are the finite group $\mathcal G=O(66,2)$; a data port $(g,q)$ visits $gR_{12,q},g,gR_{23,q}$.

The forward, reverse/complement, forward sequence has scalar action

\[
(X,Y)\mapsto(X,Y+X)\mapsto(-Y,X+Y)\mapsto(-Y,X).
\]

The transported exit preimage of each stage equals the next entrance preimage. Exact rank-zero adapters reconcile representatives, so there are no omitted positive-width interstage connectors. In $E_0$ the physical outputs are $(-F_0y,F_0T_q^{-2}x)$. Since $T_q^2$ is the actual binary translation by $q$, a paid translation, sign and bank permutation remove this source gauge. Each data bank also pays the rank-two complement call for $E_0^\perp$, obtaining the full ambient transform. No two-stage mixed-term correction is silently reused from round six.

Independently partition the ambient space into three orthogonal $h$-blocks $P_1,P_2,P_3$. Fixed orthogonal maps $H_j$ carry $A$ to $P_j$. Route physical auxiliary register $(g,r)$ to vertex $gH_j$ in stage $j$. Each stage routing is a bijection of the full finite register stock, and stages execute serially. These are [C144]'s shared **completed** cores: each includes all compensation, copied-centre work, scalar inverse cleanup and source subtraction.

Because all physical entrance gauges are zero, a forward completed core acts as $F_h$ on each arbitrary auxiliary stream and the reversed core as its exact inverse, with the endpoint reconciliation included. Transported into the three orthogonal blocks, these actions tensor. The inverse block differs from its forward version by a translation because $F_h^2$ is Pauli. The conjugated full transform and canonical ambient transform have the same symplectic action; their exact Pauli and scalar-phase difference is implemented. Thus every auxiliary input, not just the two data banks, receives the full $C^{\otimes66f}$.

This applies the exact core-sharing and cover lemmas of [C130, C144]. The generic gauge-tail construction needs block-factored representatives; here all tails disappear only because every gauge is paired and the physical chain recount includes the replacement hand-offs. We retain compatible block-factored representatives rather than inferring physical phases from subspace dimensions alone.

### 6.5 Complete histogram and moment

Let $H_r$ be the local histogram of joined auxiliary chains, including source loads and paid centre copies; let $D_r$ and $Q_r$ count source and target data chains. The actual calls per cover vertex are

\[
n_r^{(0)}=3(H_r+D_r+Q_r)+2v\,\mathbf1_{r=2},
\qquad W_0=2v+11952=14592.
\]

The factor three pays all three core invocations, and the final term pays both data-bank complements. There are no unpaired-gauge exterior children. The selected table is:

| $r$ | $n_r^{(0)}$ | $r$ | $n_r^{(0)}$ |
| ---: | ---: | ---: | ---: |
| 1 | 81012 | 11 | 1446 |
| 2 | 53466 | 12 | 2643 |
| 3 | 30099 | 13 | 1188 |
| 4 | 10314 | 14 | 2901 |
| 5 | 8394 | 15 | 5343 |
| 6 | 4788 | 16 | 1737 |
| 7 | 3396 | 18 | 6480 |
| 8 | 2742 | 19 | 1311 |
| 9 | 2067 | 20 | 6006 |
| 10 | 3396 | | |

Unlisted widths have zero multiplicity. The recount gives

\[
\sum_r r n_r^{(0)}=961752,\qquad
66W_0-961752=1320=2v-3\ell,\qquad \max r=20<66.
\]

The actual stock is $W=|\mathcal G|W_0$, not 14,592 arrays. The full role count has 2,159 bits. The finite orthogonal group can be constructed by enumeration of binary matrices and exact orthogonality tests; its order is

\[
|O(66,2)|=2^{65+32^2}\prod_{i=1}^{32}(4^i-1).
\]

Its size is independent of the requested Fourier length. Fixed role permutations, scalar work and all frame adapters are charged by Section 3 with this full stock. Its constants are not claimed practical. The group factor cancels only from the normalized moment.

The local rational verifier gives

\[
1-\Psi(1-a)>5.5931322116649\times10^{-13}
\]

at (6.1), using rational endpoints rather than this rounded display. At $a+10^{-12}$ its lower moment is greater than one, rejecting that next grid point for this histogram. The positive absorption gap is

\[
a-\delta=\frac{152419}{25000000000}=0.00000609676.
\]

The physical program is finite, every child is narrower, and its adapters are charged linear array passes. Sections 6.1--6.4 discharge the finite-network contract subject to the named upstream frame, cover and sharing lemmas. Sections 2--4 then give the proposed all-length saving $\delta=0.00061$.

### 6.6 Reproduction, limits and attribution

Run `python3 verification/verify_round10.py` for this record, or `python3 verification/run_checks.py` for all incorporated witnesses. The new verifier checks source hashes, the exact decoder matrix, compiled carriers and compensation targets, the imported full-size schedule and histogram replay, small exhaustive exact Clifford tests, independent rational moment bounds, absorption slack and negative controls. The regenerated certificate must match `verification/certificates/round10_reference.json`.

The frozen word and checker are imported source. Our integer coefficient and frame checks are additional same-assistant implementations. We do not enumerate the full 66-dimensional cover, execute the complete DFT, rerun the network optimization search, or formally prove the infinite recurrence. The small exact frame tests do not certify every full-size physical phase. Their universal justification is the written exact-representative argument and cited factorization. The included Lean file checks numerical histogram/assembly predicates; this project's default runner does not execute Lean, and Lean does not prove the Fourier transfer.

Independent review should prioritize the general Clifford factorization and uniform adapter cost, exact representative choices at shared gates, arbitrary-scratch birth reuse in both orientations, the shared completed-core endpoints, and the full-stock recurrence. A missing physical interface cannot be repaired by a successful moment certificate.

Jain supplies the selected word and optimization integration. The three-stage cover, paired-cube identity and frame machinery are attributed to icekylinx; completed-core sharing to an664; the DAG, modules, merged reads, physical frame descent and late-compensation lineage include eumemic; birth reuse includes jamesyc; relaxed carrier arcs include DaysSky. Douglas Colkitt maintains the community framework, with additional predecessors recorded in the preserved NOTICE. This draft supplies the proposed Fourier transfer and local checks, not authorship of those network improvements. Original licenses and AI-assistance disclosures are retained.

### References for the framework and round-ten record

[O] OpenAI. *An explicit power saving for the exact discrete Fourier transform*, September 25, 2026. Lemmas 2.2 and 2.5, Proposition 2.4, Theorem 2.6, Proposition 4.2 and Section 5.4. [Public manuscript](https://github.com/openai/math/blob/main/preprints/An-explicit-power-saving-for-the-exact-discrete-Fourier-transform-September-25-2026/main.pdf).

[J10] Swapnil Jain. *Integer multiplication: round ten*, commit `d2f6146ffbbd893e69b8fb06bc53b82af36d8032`. [Construction and proof boundaries](https://github.com/Swapnil-jain/integer-mult-kappa/blob/d2f6146ffbbd893e69b8fb06bc53b82af36d8032/README.md), [frozen complex word](https://github.com/Swapnil-jain/integer-mult-kappa/blob/d2f6146ffbbd893e69b8fb06bc53b82af36d8032/certificates/round10/cx_prefix_word_p11.json.gz), and [Lean numerical certificate](https://github.com/Swapnil-jain/integer-mult-kappa/blob/d2f6146ffbbd893e69b8fb06bc53b82af36d8032/lean/Round10.lean). Research and implementation assistance is disclosed in the preserved upstream NOTICE.

[C130] icekylinx. [PR130: three-stage Cayley covers](https://github.com/CrocSwap/integer-mult-bounds/pull/130). The [general Clifford frames](https://github.com/icekylinx/integer-mult-bounds/blob/c8b22bc5c10dba497ac25804e27d9647d818e2ff/notes/general-clifford-frames.tex) and [cover proof](https://github.com/icekylinx/integer-mult-bounds/blob/c8b22bc5c10dba497ac25804e27d9647d818e2ff/notes/three-stage-cover-complex.tex) are pinned in this repository at the subsequent paired-cube commit.

[C144] icekylinx. [PR144: paired cubes and shared completed cores](https://github.com/CrocSwap/integer-mult-bounds/pull/144), commit `c8b22bc5c10dba497ac25804e27d9647d818e2ff`. [Paired-cube construction](https://github.com/icekylinx/integer-mult-bounds/blob/c8b22bc5c10dba497ac25804e27d9647d818e2ff/notes/paired-cube-construction.tex) and [exact core sharing](https://github.com/icekylinx/integer-mult-bounds/blob/c8b22bc5c10dba497ac25804e27d9647d818e2ff/notes/paired-cube-sharing.tex). These sources record GPT-6 Astra and Codex assistance and credit an664's PR128 sharing principle.

[BR] jamesyc's [PR124](https://github.com/CrocSwap/integer-mult-bounds/pull/124) and eumemic's [PR143](https://github.com/CrocSwap/integer-mult-bounds/pull/143): birth reuse and late compensation. [J10] pins and attributes their use in its construction. The module and refinement lineage also includes eumemic's PR117, PR161 and PR168 and DaysSky's PR162; the exact adopted data pins and notices are retained in `verification/vendor/jain_round10/NOTICE`.
