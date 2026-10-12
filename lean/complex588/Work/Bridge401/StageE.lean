import Work.Gauge.Defs
import Work.GCert.Chain.Stage

/-!
# (key: bridge-401) A stage of gauged invocations (`GInvE`)

Copy of Jacob Sussman's `gistage_fwd` / `gistage_bwd` (Work/GCert/Chain/Stage.lean) for the gauged invocation
package `GInvE` (DFT Bridge3, Work/Gauge/Defs.lean): every slot `q` of the invocation `d` has its own entrance step
`Wn d q`; the helper sets are not permuted (`εS = refl`: the bank `(d, b)` serves the invocation `d`).
Entrance gauges: Dugongue (CrocSwap/integer-mult-bounds PR #401).  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace GX
open Binary Matrix Finset RAM SS CB RF BR GF
noncomputable section

section Pkg
variable {H T Sl C α Γ : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] [Fintype α] [DecidableEq α]
  [Fintype Γ] [DecidableEq Γ]
variable (I : GInvE H T Sl C)

/-- the second idle climb of an x role (copy of `GInv.climbX`). -/
lemma GInvE.climbX (Xm : XMap H α) (t : T) :
    XReach (Xm.Φ (tt (I.tv t))) (Xm.Φ 1) (fun φ => bcost φ (Fintype.card H - 1)) := by
  obtain ⟨p, hp⟩ := I.hgap t
  obtain ⟨A, k, hA⟩ := exists_base_one (I.tv t) (I.hunit t) p hp
  have h := Xm.up A {k} univ (Finset.subset_univ _)
  rw [mat_single, OBase.mat_univ, hA] at h
  refine h.cast (fun φ => ?_)
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    Finset.card_singleton]

/-- the second idle climb of a y role (copy of `GInv.climbY`). -/
lemma GInvE.climbY (Xm : XMap H α) (t : T) :
    XReach (Xm.Φ 0) (Xm.Φ (1 + tt (I.tv t))) (fun φ => bcost φ (Fintype.card H - 1)) := by
  obtain ⟨p, hp⟩ := I.hgap t
  obtain ⟨A, k, hA⟩ := exists_base_one (I.tv t) (I.hunit t) p hp
  have h := Xm.up A ∅ (univ \ {k}) (Finset.empty_subset _)
  rw [mat_empty, mat_compl_single, hA] at h
  refine h.cast (fun φ => ?_)
  rw [Finset.sdiff_empty, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    Finset.card_singleton]

/-- **A forward stage of gauged invocations.** -/
theorem gistageE_fwd (εX : T → Γ ≃ Γ) (M : Γ → GWin H α) (N Wn : Γ → Sl → CMat α)
    (hN : ∀ d q, (M d).X.Φ (I.ent q) * N d q = 1)
    (hW : ∀ d q, (M d).X.Φ (I.ent q).top = Wn d q * (M d).X.Φ (I.ent q))
    (Z : Γ → Sl → CMat α) (c0 c1 : Γ → C → CMat α) :
    GRoute (bIn I.tv εX (fun d => (M d).Xm) Z c0)
      (bOut I.tv εX (fun d => (M d).Xm) (fun g q => Wn g q * Z g q) c1)
      GF (fun φ => (Fintype.card Γ : ℝ) * I.cost φ) := by
  refine gsstage εX (Equiv.refl Γ) (h := shearF) (cost := I.cost) (fun d => ?_) (fun d x => ?_)
  · rw [bIn_sem, bOut_sem]
    exact I.fwd (M d) (N d) (Wn d) (hN d) (hW d) _ _ _
  · funext b
    rcases b with ((t|t)|(q|k)) <;> rfl

/-- **A backward stage of gauged invocations.** -/
theorem gistageE_bwd (εX : T → Γ ≃ Γ) (M : Γ → GWin H α) (N Wn : Γ → Sl → CMat α)
    (hN : ∀ d q, (M d).X.Φ (I.ent q) * N d q = 1)
    (hW : ∀ d q, (M d).X.Φ (I.ent q).top = Wn d q * (M d).X.Φ (I.ent q))
    (Z : Γ → Sl → CMat α) (c0 c1 : Γ → C → CMat α) :
    GRoute (bIn I.tv εX (fun d => (M d).Xm) Z c0)
      (bOut I.tv εX (fun d => (M d).Xm) (fun g q => Wn g q * Z g q) c1)
      GB (fun φ => (Fintype.card Γ : ℝ) * I.cost φ) := by
  refine gsstage εX (Equiv.refl Γ) (h := shearB) (cost := I.cost) (fun d => ?_) (fun d x => ?_)
  · rw [bIn_sem, bOut_sem]
    exact I.bwd (M d) (N d) (Wn d) (hN d) (hW d) _ _ _
  · funext b
    rcases b with ((t|t)|(q|k)) <;> rfl

end Pkg
end
end GX
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.GX.gistageE_fwd
#print axioms OAI.PowerSaving.GX.gistageE_bwd
