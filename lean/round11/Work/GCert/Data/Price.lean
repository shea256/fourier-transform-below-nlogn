import Work.Combine.Hist
import Work.GCert.Data.Count

/-!
# (key: gx-data) The price of an explicit rank list from its kernel counts

`rcost_wsumK`: if the kernel has counted `wsumK (SSC.wGt B) l 0 = 0` (no rank above `B`), then
`rcost φ l = ∑ r ≤ B, (wsumK (SSC.wEq r) l 0) * bcost φ r`.  Used by the generated modules
`Work/GCert/Data/<Name>Price.lean` on the rank lists `rA`, `rB`, `rF` of a gcert/1 certificate.
-/

namespace GXD
open OAI.PowerSaving.CB Finset

/-- a kernel count at rank `r` is `List.count` -/
theorem wsumK_wEq (r : ℕ) (l : List ℕ) : wsumK (SSC.wEq r) l 0 = l.count r := by
  rw [wsumK_eq, Nat.zero_add]
  exact SSC.wsum_wEq r l

/-- **the price of a rank list from the kernel-evaluated counts** -/
theorem rcost_wsumK (φ : ℕ → ℝ) (l : List ℕ) (B : ℕ) (hB : wsumK (SSC.wGt B) l 0 = 0) :
    rcost φ l = ∑ r ∈ range (B+1), (wsumK (SSC.wEq r) l 0 : ℝ) * bcost φ r := by
  have h0 : SSC.wsum (SSC.wGt B) l = 0 := sum_of_wsumK hB
  rw [SSC.rcost_count φ l B (SSC.wsum_wGt B l h0)]
  refine sum_congr rfl (fun r _ => ?_)
  rw [wsumK_wEq]

end GXD

#print axioms GXD.rcost_wsumK
