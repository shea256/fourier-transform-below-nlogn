## 1. Scope and the finite-network interface

This is a living research draft for OpenAI Problem #130. Its reusable argument transfers finite tensor-network improvements to an all-length exact discrete Fourier transform. Each selected network is a separate, pinned result record. A passing numerical certificate alone is not a transfer proof. The result history records which networks have a written transfer and which remain candidates.

We use the exact-complex-arithmetic model of OpenAI's *An explicit power saving for the exact discrete Fourier transform* [O]. Complex field operations have unit cost, coefficients and intermediate magnitudes are unrestricted, and a specified root of unity of order less than $1024n^3$ is supplied. Integer operations and random access on a fixed number of $O(\log(n+2))$-bit words have unit cost. Scalar preparation, index construction, initialization and data movement are charged. This is not a bit-complexity, numerical-stability, bounded-coefficient or practical FFT claim.

The fixed kernel is

\[
C=\frac12\begin{pmatrix}1+i&1-i\\1-i&1+i\end{pmatrix},
\qquad C^2=X=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
\]

**Finite-network contract.** Fix integers $m\ge2$, $W\ge1$, and nonnegative integer multiplicities $n_r$ for $1\le r<m$. For every column count $f\ge1$, require a constructively specified finite algorithm that applies $C^{\otimes mf}$ to **all $W$ arbitrary complex input arrays**, including arrays used as dirty auxiliary registers. It must have the following properties.

1. Its positive-width operations consist of $n_r$ calls on $rf$ binary axes in one array, independently on every fiber of the remaining axes. Each such call is $C^{\otimes rf}$, up to explicitly implemented adapters.
2. Everything outside these calls costs at most $A W2^k$ for $k=mf+b$, $0\le b<m$, with arbitrary spectator axes allowed. The constant $A$ is independent of $k$ and $f$. Temporary copies, scalar gates, phase corrections, layout passes and their inverses are included.
3. The schedule and fixed tables have constructive finite preparation procedures. Serial execution uses $O(W2^k)$ live complex registers and addresses represented by a fixed number of $O(k+1)$-bit words.
4. The specified input-output map is exact on arbitrary data and scratch. The histogram counts actual recursive calls, including copied-register transformations and endpoint corrections. A rank budget or aggregate scalar identity by itself does not satisfy this condition.

This contract makes no particular choice of number of stages, producer DAG, frame system or network optimizer. Different witnesses may discharge it by different arguments. A fixed finite cover is permitted: if a cover has $V$ vertices and counts $W_0,n_r^{(0)}$ per vertex, the actual values are $W=VW_0$, $n_r=Vn_r^{(0)}$. The factor cancels in the normalized moment, but the algorithm still allocates and routes the full finite stock. Rational per-vertex counts require an explicitly justified common integer replication; they are not fractional physical registers.

## 2. A reusable transfer theorem

**Conditional transfer theorem.** Suppose the finite-network contract holds and, for a rational $0<a<1$,

\[
\Psi(1-a)=\frac1W\sum_{r=1}^{m-1} n_r\left(\frac rm\right)^{1-a}<1.
\tag{2.1}
\]

Then the network supplies a uniform arbitrary-input tensor algorithm of cost

\[
O\!\left(2^k(k+1)^{1-a}\right).
\tag{2.2}
\]

Under [O]'s Fourier compiler and all-length reduction, every fixed $0<\delta<a$ gives

\[
T(n)=O\!\left(n(\log n)^{1-\delta}\right)
\tag{2.3}
\]

in the model of Section 1. The constants and eventual thresholds may depend on the entire finite witness. This theorem is conditional on the actual algorithmic contract, not solely on the finite inequality (2.1).

### 2.1 Incomplete batches and unequal child widths

Let $T(k)$ denote the simultaneous cost on $W$ arbitrary arrays, and set $t(k)=T(k)/(W2^k)$. Handle the fixed range $k<m$ directly. For $k\ge m$, let $f=\lfloor k/m\rfloor$ and process the fewer than $m$ leftover axes directly. A width-$r$ call has $2^{k-rf}$ fibers. Pack complete groups of $W$ fibers and recurse; apply the ordinary coordinate algorithm to the fewer than $W$ leftover fibers. Thus

\[
\begin{split}
T(k)\le{}& A W2^k+
\sum_r n_r\left\lfloor\frac{2^{k-rf}}W\right\rfloor T(rf)\\
&+B(W-1)\sum_r n_r\,rf\,2^{rf}.
\end{split}
\tag{2.4}
\]

Every child has $r<m$, so

\[
rf\,2^{rf-k}\le rf\,2^{-(m-r)f}\le r.
\]

The last line of (2.4), after normalization, is bounded by a constant independent of $k$. Consequently

\[
t(k)\le A'+\frac1W\sum_r n_r\,t(r\lfloor k/m\rfloor).
\tag{2.5}
\]

Put $\theta=1-a$. Choose $K$ for the finite base range and so that
$K(1-\Psi(\theta))m^\theta\ge A'$. Since $rf\le(r/m)k<k$, strong induction gives

\[
t(k)\le A'+K k^\theta\Psi(\theta)\le K k^\theta.
\]

A single requested transform initializes $W-1$ additional arrays and keeps its own output. Because $W$ is a fixed integer, this remains $O(2^k(k+1)^\theta)$. Serial children have at most half their parent's array length, so reusable buffers give a geometrically summable $O(W2^k)$ live stock. The axis count contracts by the fixed factor $\max r/m<1$, giving $O(\log(k+2))$ stack depth.

### 2.2 Propagation to every Fourier length

The proof of [O], Proposition 4.2 consumes the arbitrary-input tensor bound, including scalar and address work. Substitution of (2.2) gives its working-length bound

\[
O\!\left(R(\ell+1)^\theta(1+\log r_{\max})^4\right)
+\operatorname{poly}(\ell,r_{\max},\log(R+2)).
\]

Its exact-width Fourier compiler, denominator conditions and supplied root are unchanged. Its small-prime working lengths, CRT permutations and charged chirp convolution, with $\ell=\Theta(\log n/\log\log n)$, yield

\[
T(n)=O\!\left(n(\log n)^{1-a}(\log\log n)^{3+a}\right).
\tag{2.6}
\]

The fixed convolution operand remains charged. For every positive gap $a-\delta$, eventually $(\log\log n)^{3+a}\le(\log n)^{a-\delta}$, proving (2.3). The compiler and all-length reduction are invoked with their hypotheses, not re-proved here. Integer-multiplication bit-network constraints, stopping losses and tape precision estimates are not premises of this transfer.

## 3. Implementing finite adapters in the array model

The layout argument extends [O], Lemma 2.5. For fixed $m$, a binary basis change on each of $f$ columns and a selection of $r$ output slots per column can be implemented in $O(2^k)$ word and movement operations. Regard each column as a digit of fixed radix $2^m$. A finite table gives that digit's contributions to source and destination addresses, including the gathered $rf$-bit active field. Precompute displaced tables in $O(f+1)$ work. Traverse the digit-prefix tree while maintaining address sums; it has fewer than $2^{k+1}$ nodes. Each extension and leaf requires a fixed number of word operations. This includes both gathering and scattering without scanning all $f$ columns separately for each entry.

Translations are incorporated into the tables. A fixed diagonal quadratic phase with values in $\{1,i,-1,-i\}$ on each column is handled by retaining its accumulated exponent modulo four during the same traversal. Products of these column phases and fixed scalar multipliers are therefore charged linear work. Fixed permutations of the finite role stock and finite cover vertices similarly require a fixed number of array passes. These constants may be enormous.

Finite binary linear algebra, frame representatives, gate coefficients and cover tables are computed constructively once. All of their dimensions are fixed independently of $k$. Neither free data movement nor free per-entry address reconstruction is assumed. A witness using other adapters must supply an additional cost argument.

## 4. Exact moment certificates

For a given physical histogram, write

\[
\Psi(1-a)=\sum_r\frac{rn_r}{Wm}
\exp\!\left(a\log\frac mr\right).
\]

The checker uses rational upper and lower logarithm bounds obtained by range reduction and the atanh series. For $0\le x<3$,

\[
\sum_{j=0}^{6}\frac{x^j}{j!}\le e^x
\le1+x+\frac{x^2}{2(1-x/3)}.
\tag{4.1}
\]

The upper bound follows because successive terms from the quadratic term onward have ratio at most $x/3$. Lower and upper logarithm endpoints are rounded outward to a rational grid before use. Every inequality determining acceptance is rational; decimal displays are explanatory only. The earlier round-six certificate uses a looser geometric exponential bound, which remains valid and unchanged.

A result record contains its exact tensor witness $a$, Fourier choice $\delta$, positive absorption gap, physical histogram, immutable source pins, verifier, and explicit proof dependencies. A lower moment above one at a larger $a$ rejects that value for the same histogram; it is not an optimality theorem over other networks.

## 5. Versioning and evidence boundaries

The stable source of Sections 1--5 is `paper/framework.md`. Network-specific arguments live under `results/`; `results/registry.json` selects the current proposed result explicitly. The build assembles the selected record into this paper and generates the improvement log. It never selects the largest upstream number automatically.

An incorporated result requires a written discharge of the network contract, a pinned complete witness, exact moment and absorption checks, a reproducible finite verifier, and a review record stating its limitations. The status **proposed** does not mean independently reviewed or formally verified. Candidates remain visibly separate from incorporated results. Earlier proofs, certificates and publication artifacts remain available even after a newer result is selected.

This work is AI-assisted. Additional checks written in this repository are not independent mathematical review. Vendor checkers are identified as such; random exact or modular trials are not described as universal identities. Lean arithmetic certificates are distinguished from a formal network or Fourier theorem. No novelty or priority is claimed for imported network improvements.

The following selected witness supplies the construction-specific arguments and attribution. Its status and source pins belong to that record; future updates need not rewrite the general transfer theorem.
