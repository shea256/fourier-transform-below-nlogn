import Work.Gauge.Defs

/-!
# (key: gauge-401) The entrance step of a gauged slot (K2')

DFT Bridge3, 2026-10-11.  For ANY stage-B frame map `X : BXMap H α` and any label `U` of `H`, the step from the frame
of `U` to the frame of the full label in the same base (`U.top`) is ONE pure-kernel factor between free adapters:

    X.Φ U.top = (kg G' * pk R * kg G'⁻¹) * X.Φ U,   G' = X.liftG U.G,   |R| = |H| - dim U,

and `X.Φ U` has a right inverse.  This is the form the bank lemmas of L2 consume (`Wn q = C * pk R * Ci`, `Ci * C = 1`).
Base: Jacob Sussman's `core_nested` (`Work/GFrame/Clifford/Core.lean`).  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace GX
open Binary Matrix Finset RAM GF
noncomputable section

section
variable {H α : Type} [Fintype H] [DecidableEq H] [Fintype α] [DecidableEq α]

/-- a right inverse of a stage-B frame. -/
lemma core_rinv (G : APerm α) (s : Finset α) :
    core G s * (kg G * (pk s * shift (indv s)) * kg (apInv G)) = 1 := by
  unfold core
  have e : kg G * pk s * kg (apInv G) * (kg G * (pk s * shift (indv s)) * kg (apInv G))
      = kg G * ((pk s * ((kg (apInv G) * kg G) * pk s)) * shift (indv s)) * kg (apInv G) := by
    simp only [Matrix.mul_assoc]
  rw [e, kg_inv_mul, Matrix.one_mul, pk_sq, shift_sq, Matrix.mul_one, kg_mul_inv]

/-- **The entrance step (K2').** -/
theorem gauge_step (X : BXMap H α) (U : SLbl H) :
    ∃ (N : CMat α) (R : Finset α), X.Φ U * N = 1 ∧
      X.Φ U.top = (kg (X.liftG U.G) * pk R * kg (apInv (X.liftG U.G))) * X.Φ U ∧
      R.card = Fintype.card H - U.dim := by
  have hs : X.liftS U.s ⊆ X.liftS univ := X.mono (Finset.subset_univ _)
  refine ⟨_, X.liftS univ \ X.liftS U.s, core_rinv (X.liftG U.G) (X.liftS U.s), ?_, ?_⟩
  · show core (X.liftG U.G) (X.liftS univ) = _ * core (X.liftG U.G) (X.liftS U.s)
    rw [core_nested _ hs, ← pk_eq_blockMat]
  · rw [X.card (Finset.subset_univ U.s), Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ]
    rfl

end
end
end GX
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.GX.gauge_step
