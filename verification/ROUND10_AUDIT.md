# Review record: proposed round-ten Fourier transfer

Date: October 9, 2026. Status: same-assistant written review and finite checks, not independent mathematical review or full formalization.

## Contract and exact values

The [general framework](../paper/framework.md) separates the arbitrary-input finite-network contract from its numerical moment. The [round-ten record](../results/round10.md) supplies the new construction argument and explicit upstream dependencies.

The selected Jain commit is `d2f6146ffbbd893e69b8fb06bc53b82af36d8032`; frame and cover notes are pinned at icekylinx commit `c8b22bc5c10dba497ac25804e27d9647d818e2ff`. The tensor witness is `15402419/25000000000`; the Fourier choice is `61/100000`. Their gap is `152419/25000000000`.

The dimension is 66. Per cover vertex, there are 14,592 persistent arrays, rank mass 961,752 and deficit 1,320. The full stock multiplies these counts by `|O(66,2)|`; it is not omitted from workspace or routing costs. Every child has width at most 20. The exact normalized moment upper gap exceeds `5.5931322116649e-13`, and a lower bound rejects the next `1e-12` grid point for this histogram.

## Reviewed mathematical dependencies

- Arbitrary-subspace preimage frames replace the earlier orthogonal-projector restriction. The Lagrangian distance formula handles degenerate subspaces. General exact Clifford elimination into one coordinate child and monomial adapters remains a cited upstream lemma.
- Quadratic phases and basis maps on each fixed-width column extend the existing prefix-traversal layout with a phase accumulator modulo four. This pays linear array cost and does not multiply work by the column count per entry.
- The exact scalar identity is `K+H+B=I`. The original source bank performs and undoes the cube-local involution at common frames; the copies, source moves and terminal complements are included in the histogram.
- All 3,180 gauges are recipients. Compensation is evaluated before the recipient's first use and after the donor's final use. Its suffix response cancels for arbitrary donor contents, and reversing the aliased gate sequence restores the physical scratch. All physical initial gauges are zero after accounting for source-carrier loads.
- The full three-stage cover and shared completed-core contracts are taken from pinned PR130/PR144 sources. Exact representative reconciliation is required, including phases and reverse orientation. Subspace dimensions alone do not establish these contracts.
- The normalized recurrence uses the full constant role stock, explicitly handles incomplete fiber batches, and invokes the original #130 all-length reduction with its unchanged hypotheses.

## Finite checks and limits

`verify_round10.py` checks every signed decoder coefficient (1,742,400 entries), 32,071 compiled carrier operations, and exact support of 5,170 compensation coefficients. It compares the reconstructed histogram with both the published inventory and Lean inputs. Source hashes are checked first.

The imported full-size checker verifies all role chains, birth pairs, read order and the physical width ledger. Its aliased scalar replay and its original decoder trial are exact modular samples. The local complete decoder check removes sampling from the coefficient identity; it does not turn the sampled scratch runs into a formal theorem.

`clifford_checks.py` enumerates every binary subspace in dimension four and checks Lagrangian distances, complement labels, exact Gaussian-integer nested-transition support, unitarity, and the full-frame translation square. This is finite coverage of the proposed general interface, not enumeration at dimension 22 or 66.

Negative controls cover a changed DAG sign, removed compensation targets, improper birth timing through the upstream checker, and an excessive moment saving. The separate four upstream word mutations can be run as documented in the verification README.

We do not run the huge global cover or entire DFT, re-execute the search that found the frozen word, or claim that Lean formalizes the network or Fourier theorem. No bit-side tape, rare-class fallback, precision grid, NDS or integer parameter assembly is imported into the Fourier argument. The selected complex word has no unpaired gauge tails, so NDS adds nothing.

Independent review should focus on exact representative compatibility, the full arbitrary-scratch reuse and reversed-core argument, the inherited cover and sharing contracts, and the uniform cost of all adapters. A failure in any of these is a proof issue even if all finite checks pass. The [round-six result](../results/round6.md) remains separately available.
