## 7. Round-eleven refinement: retiring copies and terminal targets

**Record date:** October 9, 2026. **Status:** proposed conditional Fourier transfer with finite checks; independent mathematical review and end-to-end formal verification remain pending.

This record uses Swapnil Jain's round-eleven complex word at commit `1a580dcc91dad5fbcffb5c80b7641a96bfa24e16` [J11]. It inherits the frame, paired-cube, cover and sharing interfaces of Sections 6.1--6.4, with the changed scalar word and physical ledger below. Its parameters are

\[
a=\frac{67147467}{100000000000}=0.00067147467,
\qquad \delta=\frac{67}{100000}=0.00067.
\tag{7.1}
\]

The integer-multiplication announcement reports a different parameter, $\kappa=0.0006685733$. We use the complex tensor witness $a$, together with a positive Fourier absorption gap. The bit-side cyclic all-but-one program and integer assembly are not imported into this argument.

### 7.1 Changes to the finite word

The dimensions remain $p=11$, $h=22$, $m=66$ and $v=1320$. The cube-local circuit changes to Jain's C1 configuration on the attributed PR168 v4 modules. Reverse-scan carrier matching, operation-frame descent and late birth reads are retained. The new signed DAG has 21,249 addition nodes. Its 13,042 logical auxiliary roles have 2,332 gauged birth pairs, 42 deleted terminal roles and 386 hosted births. Thus

\[
R_{\rm physical}=13042-2332-42-386=10282,
\qquad W_0=2v+R_{\rm physical}=12922.
\tag{7.2}
\]

All gauged roles are paired. Hosting introduces no unpaired gauge or exterior tail. The source-bank cube involution $K$, copied coordinate-star loss $\ell=440$, source-return calls and two data-bank rank-two complements remain charged as in Section 6. The full scalar identity is checked afresh; the old coefficient and histogram certificates do not certify the changed program.

### 7.2 Retired-copy subtraction with arbitrary dirty contents

Suppose two retired copies $P,Q$ carry the same input response. Move both to the **same exact** representative of a containing frame $V$, and execute $P\leftarrow P-Q$. The input response cancels; arbitrary dirty contents need not vanish. A fresh nongauged role $B$ is assigned to $P$ immediately before its first operation at $V$. The control $Q$ remains a physical register and pays its climb to $V$ and subsequent exit. This is the zero-source-control specialization of the compatible zero-fresh reuse mechanism credited to icekylinx's PR184 [R184]. It does not create a physically zero register for free.

The adopted hosts are disjoint triples $(P,Q,B)$. The birth is not a source, gauge or deleted sink; the retired copies are not output or gauged roles. Their original uses finish before the mix, the control is never used afterward, and the pivot's subsequent uses are the renamed birth. Both prior frames lie inside $V$. The source record excludes pairs whose dirty part depends on a late-read value. Our complete scalar-map check below additionally verifies the actual interaction with every compensated alias; equality of abstract DAG labels alone is not the correctness argument.

Recompute the nongauged entrance compensation from the **new** transcript, including all subtraction gates. Retain each gauged role's correctly timed suffix compensation, checking its exact target support. The initial reads are available at frame zero. The complete output-coefficient identity verifies that no residual input or dirty response is hidden in a hosted birth. Every surviving physical mixer has the form

\[
z_d\leftarrow c_a z_d+c_b z_c,\qquad d\ne c,\quad c_a\in\{1,-1\}.
\]

After the readouts and paid moves to the full frame, reverse these actual mixers in reverse order, then subtract the original source loads. This restores arbitrary physical scratch exactly. The new inverse program, including the subtraction gates, is required.

For one host, write $u_0,u_1$ for the dimensions of the retired-copy frames and $s=\dim V$. In each of the three stages, the pivot loses widths $h-u_0$ and $s$ and gains $s-u_0$; the control loses $h-u_1$ and gains $s-u_1$ and $h-s$. Zero widths are omitted. Rank mass drops by $h$ per stage and one persistent register disappears, so the deficit is unchanged. This pays both copies' moves. The physical verifier reconstructs the complete changed chains rather than applying this formula in isolation.

### 7.3 Deleting destination-only terminal registers

The 42 deletions use jamesyc's dirty-target terminal compiler [T166], as incorporated by [J11]. A terminal role $s$ is written only by additive updates $s\leftarrow s+b_jz_j$, is never a control, and contributes the same coefficient $u$ to a target set $T$. Choose a pivot $c\in T$ with no intervening compensation read during the terminal-write interval. All writes occur after the centre-read cut. The role is neither source, gauge nor reuse participant, and the selected target sets are disjoint.

At the cut, perform $y_t\leftarrow y_t-y_c$ for $t\in T\setminus\{c\}$. Replace each terminal write by $y_c\leftarrow y_c+ub_jz_j$. After its last write, perform $y_t\leftarrow y_t+y_c$ for the same targets. If $w=\sum_j ub_jz_j$, the pivot and every other target gain exactly $w$, regardless of their original contents. Independent corrections to nonpivot targets survive these shears. A correction to the pivot inside the interval would be distributed incorrectly and is excluded. All target frame transitions, including these shears and replacement writes, must follow the checked descending chains.

The omitted terminal's own initial dirty value no longer exists. Nevertheless, compensation columns for all **retained** roles must come from the full original decoder, after inserting the retirement mixes. They cannot be recomputed by deleting terminal outputs first: the replacement target writes still carry those roles' output responses. Full source return and reverse cleanup of retained mixers remain necessary.

For a terminal at root-frame dimension $r$, the three-stage histogram loses $3$ children at each of widths $r$ and $h-r$, and $W_0$ drops by one. The full chain recount verifies these differences simultaneously for all 42 sinks, as well as pivot cleanliness and disjoint target groups.

### 7.4 Complete scalar map and inherited physical lift

The local checker expands every decoder coefficient over the integers and verifies $6(H+B+K)=6I$ on all $1320^2$ entries. It then separately emits the actual aliased scalar read program: entrance corrections, source loads, centre reads, delayed gauge corrections, terminal target shears, retirement subtractions, renamed births and surviving final reads.

Pulling the target coordinates backward through this program uses integer vectors scaled by six. All root coefficients have denominator dividing six; target shears are integral. The resulting map is checked to be

\[
y_{\rm final}=y_{\rm initial}+(H+B)x
\]

for **every** source coordinate, initially arbitrary physical scratch coordinate and initially arbitrary target coordinate. This is a finite coefficient identity over $\mathbb Q$, not a random modular trial. There are 10,282 dirty auxiliary coordinates and 1,320 coordinates in each data bank, hence 17,057,040 scalar output coefficients including zeros. Every retained mixer is checked invertible on distinct physical registers; its literal chronological inverse restores scratch after source subtraction. The separate cube check accounts for the source-bank $K$ contribution.

For the physical lift, use the exact representatives and charged monomial adapters of Section 6.2 at every changed gate. Both retirement operands reach the same $V$; each target shear and replacement write uses the event frame certified by the frozen word. The imported full-size checker reconstructs all role and target chains and width differences. The arbitrary-array lift, source-bank $K$ execution, completed-core reversal and orthogonal routing remain the explicit dependencies from Section 6. The complete new scalar map and paid new paths are substituted into those interfaces. No literal full-size complex frame matrix or global cover is materialized by these checks.

### 7.5 Histogram and Fourier saving

The complete per-vertex child counts are:

| $r$ | $n_r^{(0)}$ | $r$ | $n_r^{(0)}$ |
| ---: | ---: | ---: | ---: |
| 1 | 91131 | 11 | 981 |
| 2 | 44583 | 12 | 3285 |
| 3 | 29850 | 13 | 552 |
| 4 | 10122 | 14 | 2229 |
| 5 | 7404 | 15 | 3360 |
| 6 | 4116 | 16 | 516 |
| 7 | 2706 | 17 | 69 |
| 8 | 3630 | 18 | 8631 |
| 9 | 1350 | 19 | 3201 |
| 10 | 2871 | 20 | 1302 |

They include all three completed cores and both data-bank complements. With $W_0=12922$,

\[
\sum_r r n_r^{(0)}=851532,\qquad
66W_0-851532=1320,\qquad\max r=20<66.
\tag{7.3}
\]

The full stock is still $W=|O(66,2)|W_0$, with the group and routing charged as in Section 6.5. At (7.1), the rational moment bound gives

\[
1-\Psi(1-a)>1.6106187822204\times10^{-12}.
\]

A lower moment bound exceeds one at $a+10^{-12}$. Exact endpoints are stored in the reference certificate; the display is rounded downward. This rejects that next grid point for this histogram, not all possible networks. The positive absorption gap is

\[
a-\delta=\frac{147467}{100000000000}=0.00000147467.
\tag{7.4}
\]

The framework gives the proposed all-length saving $\delta=0.00067$, conditional on the inherited physical interfaces and the transfer argument. This is approximately $9.18$ times the previous published round-six Fourier saving and $1.10$ times our incorporated round-ten choice. These ratios compare exponent parameters, not measured runtimes.

### 7.6 Reproduction and review boundary

Run `python3 verification/verify_round11.py`; its report must match `verification/certificates/round11_reference.json`. Source hashes, the published inventory and the Lean input histogram are checked. The upstream replay and its negative controls are identified as imported; the local checker additionally rejects a wrong subtraction sign, omitted gauge correction, missing terminal post-shear and the excessive next tensor grid point.

The default Python suite does not rerun the network search or Lean compiler. The supplied Lean file certifies numerical predicates, not this scalar compiler, the physical network or Fourier transfer. Same-assistant implementations are not independent review. General exact-frame compatibility, cover and completed-core interfaces, the uniform cost model and the all-length reduction remain mathematical review obligations. Earlier witnesses and checks remain available independently.

Jain supplies the round-eleven integration, C1 word and selected matching. Retirement reuse is credited to icekylinx, terminal-target compilation to jamesyc, and the retained modules and frame/late-read lineage to eumemic and the other authors in [J11]'s NOTICE. Section 6 retains the original frame, cover, paired-cube and sharing credit, including an664, DaysSky, Douglas Colkitt and OpenAI. We propose the Fourier transfer and supply additional checks; we do not claim those network improvements as our own.

### References added for round eleven

[J11] Swapnil Jain. *Integer multiplication: round eleven*, commit `1a580dcc91dad5fbcffb5c80b7641a96bfa24e16`. [Complex construction and validation boundary](https://github.com/Swapnil-jain/integer-mult-kappa/blob/1a580dcc91dad5fbcffb5c80b7641a96bfa24e16/independent/round11-cx-recycle-gate/README.md), [frozen word](https://github.com/Swapnil-jain/integer-mult-kappa/blob/1a580dcc91dad5fbcffb5c80b7641a96bfa24e16/certificates/round11/cx_recycle_word_p11.json.gz), and [Lean numerical inputs](https://github.com/Swapnil-jain/integer-mult-kappa/blob/1a580dcc91dad5fbcffb5c80b7641a96bfa24e16/lean/round11-histograms.json). Unmodified files, licenses and notices are under `verification/vendor/jain_round11/`.

[R184] icekylinx. [PR184: source-assisted common-frame compression](https://github.com/CrocSwap/integer-mult-bounds/pull/184), [proof note](https://github.com/icekylinx/integer-mult-bounds/blob/4b5fc7fb45a77b6c7b9d886d30ad5b57eae553fa/notes/source-assisted-note.tex), Sections 2--3. The present word uses the zero-source-control retirement specialization described in [J11], not PR184's numerical supplier. The note discloses substantial GPT-6 Astra and Codex assistance.

[T166] jamesyc. [PR166: dirty-target terminal compiler](https://github.com/CrocSwap/integer-mult-bounds/pull/166). The actual 42-sink selection and checker are pinned through [J11]. The target-shear identity is restated above; no numerical witness from PR166 is substituted into this ledger.
