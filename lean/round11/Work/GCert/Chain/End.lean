import Work.GCert.Chain.Geom
import Work.GFrame.Engine.Group

/-!
# (key: gx-chain) THE END THEOREM (spec statement 7): two halves + rate fact => Walsh-Hadamard

`wht_of_halves S L ...`: for a certificate given by its scalar half `S : Scal T Sl C` and its
label half `L : Lab H S`, the bridged five-stage word B_2 (`bridge2_gcert`, label dimension
`u = 5 h`, `W = 4 v + R` live roles per unit, unit price
`5 * L.cost φ + v * BG.bankPrice h φ`) and the generalised engine
(`BlockWHT.wht_main_of_ggroup_list`) give a Walsh-Hadamard program with `WHTTimeBoundsAt z`,
for every exponent `z` at which the rate fact `hnum` of the unit block list `U` holds.

`wht_of_ginv`: the same for any generalised invocation package.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace GX
open Binary Matrix Finset RAM SS CB RF BR BG GF FoldRate
noncomputable section

section End
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]

/-- **Walsh-Hadamard transform from a generalised invocation package and a rate fact.** -/
theorem wht_of_ginv (I : GInv H T Sl C) (hH : 1 ≤ Fintype.card H)
    (u W : ℕ) (hu : 5 * Fintype.card H = u)
    (hW : 4 * Fintype.card T + Fintype.card Sl = W) (hW1 : 1 ≤ W)
    (U : List (ℕ × ℕ))
    (hU : ∀ φ : ℕ → ℝ,
      5 * I.cost φ + (Fintype.card T : ℝ) * bankPrice (Fintype.card H) φ = listCost φ U)
    (s : ℕ) (z : ℝ) (hz : 0 ≤ z) (hz1 : z < 1)
    (hnum : ((2:ℝ)^s - 1) * BlockAccounting.moment u z U
        + (W:ℝ) * (BlockAccounting.T u z (u - 1) 1 + BlockAccounting.T u z 1 1)
        < (2:ℝ)^s * (W:ℝ)) :
    ∃ solve W', WHT.WHTProgram solve W' ∧ BlockWHT.WHTTimeBoundsAt z W' :=
  BlockWHT.wht_main_of_ggroup_list u (card_L5.trans hu) (by omega)
    (Sum.inl : BLive (Orth (L5 H)) T Sl → BRole (Orth (L5 H)) T Sl C) Sum.inl_injective
    (Fintype.card (Orth (L5 H))) W Orth.card_pos hW1 (by rw [card_BLive, hW])
    _ (bridge2_gcert I hH) U (fun φ => by rw [hU φ]) s z hz hz1 hnum

/-- **THE END THEOREM.**  Scalar half + label half + rate fact of the unit block list
=> a Walsh-Hadamard program at the exponent of the rate fact. -/
theorem wht_of_halves (S : Scal T Sl C) (L : Lab H S) (hH : 1 ≤ Fintype.card H)
    (u W : ℕ) (hu : 5 * Fintype.card H = u)
    (hW : 4 * Fintype.card T + Fintype.card Sl = W) (hW1 : 1 ≤ W)
    (U : List (ℕ × ℕ))
    (hU : ∀ φ : ℕ → ℝ,
      5 * L.cost φ + (Fintype.card T : ℝ) * bankPrice (Fintype.card H) φ = listCost φ U)
    (s : ℕ) (z : ℝ) (hz : 0 ≤ z) (hz1 : z < 1)
    (hnum : ((2:ℝ)^s - 1) * BlockAccounting.moment u z U
        + (W:ℝ) * (BlockAccounting.T u z (u - 1) 1 + BlockAccounting.T u z 1 1)
        < (2:ℝ)^s * (W:ℝ)) :
    ∃ solve W', WHT.WHTProgram solve W' ∧ BlockWHT.WHTTimeBoundsAt z W' :=
  wht_of_ginv L.inv hH u W hu hW hW1 U hU s z hz hz1 hnum

/-- the generalised certificate of one certificate (for a per-instance engine statement). -/
theorem gcert_of_halves (S : Scal T Sl C) (L : Lab H S) (hH : 1 ≤ Fintype.card H) :
    GCert (L5 H) (Sum.inl : BLive (Orth (L5 H)) T Sl → BRole (Orth (L5 H)) T Sl C)
      (fun φ => (Fintype.card (Orth (L5 H)) : ℝ)
        * (5 * L.cost φ + (Fintype.card T : ℝ) * bankPrice (Fintype.card H) φ)) :=
  bridge2_gcert L.inv hH

end End
end
end GX
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.GX.wht_of_ginv
#print axioms OAI.PowerSaving.GX.wht_of_halves
#print axioms OAI.PowerSaving.GX.gcert_of_halves
