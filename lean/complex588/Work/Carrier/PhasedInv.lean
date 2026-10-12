import Work.Carrier.Phases

/-!
# (key: carrier-thm) THE CARRIER INVOCATION THEOREM (general scope): `Phased.inv`

For a carrier circuit given by its phases (`Phased H T Sl C`, `Work.Carrier.Phases`) the forward
word is

    erase | y -= K s (label 0) | phase A | c += Cc s | copies down | y += Jr c | phase B |
    final climbs | slots := slot rows of the inverse (top) | erase

and the backward word is the transposed inverse, gate by gate, on the same labels (the copies
start at 0 and climb).  `fwd_erased` / `bwd_erased`: both are exact block routes, for EVERY block
frame map, with scalar maps `shearF` / `shearB` and the price `K.cost`.  `Phased.inv`: the
invocation package `BR.Inv` for the bridged network (dirty helper slots by re-framing).

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace CR
open Binary Matrix Finset RAM SS CB BR
noncomputable section

section Thm
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]
variable {α : Type} [Fintype α] [DecidableEq α]

/-- at the start all roles that are not x roles have the frame of 0. -/
lemma start_frames (Xm : XMap H α) (tv : T → Space H) (i j : L3 T Sl) (hi : iX i = 0)
    (hj : iX j = 0) : Xm.Φ (lab3 tv i).P = Xm.Φ (lab3 tv j).P := by
  rcases i with ((t|t)|q)
  · exact absurd (show (1:ℚ) = 0 from hi) one_ne_zero
  · rcases j with ((t'|t')|q')
    · exact absurd (show (1:ℚ) = 0 from hj) one_ne_zero
    · rfl
    · rfl
  · rcases j with ((t'|t')|q')
    · exact absurd (show (1:ℚ) = 0 from hj) one_ne_zero
    · rfl
    · rfl

namespace Phased
variable (K : Phased H T Sl C)

/-- at the end a slot and any role that is not a y role have the frame of 1. -/
lemma end_frames (Xm : XMap H α) (i j : L3 T Sl) (hi : iX i = 0) (hi' : iY i = 0)
    (hj : iY j = 0) : Xm.Φ (K.labF i).P = Xm.Φ (K.labF j).P := by
  rcases i with ((t|t)|q)
  · exact absurd (show (1:ℚ) = 0 from hi) one_ne_zero
  · exact absurd (show (1:ℚ) = 0 from hi') one_ne_zero
  · have h1 : (K.labF (Sum.inr q)).P = 1 := K.hFs q
    rcases j with ((t'|t')|q')
    · have h2 : (K.labF (Sum.inl (Sum.inl t'))).P = 1 := K.hFx t'
      rw [h1, h2]
    · exact absurd (show (1:ℚ) = 0 from hj) one_ne_zero
    · have h2 : (K.labF (Sum.inr q')).P = 1 := K.hFs q'
      rw [h1, h2]

/-- **Forward word on clean frames**: erase ; dirt gate ; A ; scatter through the copies ; B ;
final climbs ; top gate ; erase. -/
theorem fwd_erased (Xm : XMap H α) (c0 c1 : C → CMat α) :
    XRoute (iin Xm K.tv (fun _ : Sl => Xm.Φ 0) c0) (iout Xm K.tv (fun _ : Sl => Xm.Φ 1) c1)
      shearF K.cost := by
  have a1 : XRoute (fun r : L3 T Sl => Xm.Φ (lab3 K.tv r).P)
      (fun r : L3 T Sl => Xm.Φ (lab3 K.tv r).P)
      (actPoint (g1 K.Mt)) (fun _ => 0) :=
    XRoute.gate (g1 K.Mt) _ _ (fun i j hij => by
      by_cases e : i = j
      · subst e; rfl
      · obtain ⟨h1, h2⟩ := offdiag_x (g1_x K.Mt).1 (g1_x K.Mt).2 hij e
        exact start_frames Xm K.tv i j h1 h2)
  have b3 : XRoute (fun r => Xm.Φ (K.labF r).P) (fun r => Xm.Φ (K.labF r).P)
      (actPoint (g8 K.Mti)) (fun _ => 0) :=
    XRoute.gate (g8 K.Mti) _ _ (fun i j hij => by
      by_cases e : i = j
      · subst e; rfl
      · have f := g8_facts K.hiy
        obtain ⟨h1, h2, h3⟩ := offdiag_s f.1 f.2.1 f.2.2 hij e
        exact K.end_frames Xm i j h1 h2 h3)
  have seg1 := a1.trans (K.pA Xm).1
  have seg2 := ((K.pB Xm).1.trans (K.pF Xm)).trans b3
  have e0 : XRoute (iin Xm K.tv (fun _ : Sl => Xm.Φ 0) c0)
      (glue (fun r : L3 T Sl => Xm.Φ (lab3 K.tv r).P) (fun k => Xm.Φ (K.cen k).P))
      eraseC (fun _ => 0) :=
    xerase (fun t => rfl) (fun t => rfl) (fun q => rfl)
  have L1 := lift_live (fun k => Xm.Φ (K.cen k).P) seg1
  have m1 : XRoute (glue (fun r => Xm.Φ (K.labA r).P) (fun k => Xm.Φ (K.cen k).P))
      (glue (fun r => Xm.Φ (K.labA r).P) (fun k => Xm.Φ (K.cen k).P))
      (fun z => addBlk bC (ap K.Cc (z ∘ bS)) z) (fun _ => 0) :=
    xgate_shear bC bS bS_inj K.Cc (fun k q h => congrArg Xm.Φ (K.hAc k q h))
  have m2 := copies_descend Xm (fun r => Xm.Φ (K.labA r).P) K.cen K.kc
  have m3 : XRoute (glue (fun r => Xm.Φ (K.labA r).P) (fun _ : C => Xm.Φ 0))
      (glue (fun r => Xm.Φ (K.labA r).P) (fun _ : C => Xm.Φ 0))
      (fun z => addBlk bY (ap K.Jr (z ∘ bC)) z) (fun _ => 0) :=
    xgate_shear bY bC bC_inj K.Jr (fun t k _ => congrArg Xm.Φ (K.hAy t))
  have L2 := lift_live (fun _ : C => Xm.Φ 0) seg2
  have e1 : XRoute (glue (fun r => Xm.Φ (K.labF r).P) (fun _ : C => Xm.Φ 0))
      (iout Xm K.tv (fun _ : Sl => Xm.Φ 1) c1) eraseC (fun _ => 0) :=
    xerase (fun t => (congrArg Xm.Φ (K.hFx t)).symm) (fun t => (congrArg Xm.Φ (K.hFy t)).symm)
      (fun q => (congrArg Xm.Φ (K.hFs q)).symm)
  have tot := (((((e0.trans L1).trans m1).trans m2).trans m3).trans L2).trans e1
  refine (tot.castg (g' := shearF) (funext fun z => K.fwd_scalar z)).cast (fun φ => ?_)
  simp only [Phased.cost, zero_add, add_zero]
  ring

/-- **Backward word on clean frames**: the transposed inverse gates, same labels; the copies
start at 0 and climb. -/
theorem bwd_erased (Xm : XMap H α) (c0 c1 : C → CMat α) :
    XRoute (iin Xm K.tv (fun _ : Sl => Xm.Φ 0) c0) (iout Xm K.tv (fun _ : Sl => Xm.Φ 1) c1)
      shearB K.cost := by
  have a1 : XRoute (fun r : L3 T Sl => Xm.Φ (lab3 K.tv r).P)
      (fun r : L3 T Sl => Xm.Φ (lab3 K.tv r).P)
      (actPoint (g1i K.Mt)ᵀ) (fun _ => 0) :=
    XRoute.gate (g1i K.Mt)ᵀ _ _ (fun i j hij => by
      by_cases e : i = j
      · subst e; rfl
      · have hij' : g1i K.Mt j i ≠ 0 := hij
        obtain ⟨h1, h2⟩ := offdiag_x (g1i_x K.Mt).1 (g1i_x K.Mt).2 hij' (Ne.symm e)
        exact start_frames Xm K.tv i j h2 h1)
  have b3 : XRoute (fun r => Xm.Φ (K.labF r).P) (fun r => Xm.Φ (K.labF r).P)
      (actPoint (h8 K.Mt)ᵀ) (fun _ => 0) :=
    XRoute.gate (h8 K.Mt)ᵀ _ _ (fun i j hij => by
      by_cases e : i = j
      · subst e; rfl
      · have hij' : h8 K.Mt j i ≠ 0 := hij
        have f := h8_facts K.hmy
        obtain ⟨h1, h2, h3⟩ := offdiag_s f.1 f.2.1 f.2.2 hij' (Ne.symm e)
        exact (K.end_frames Xm j i h1 h2 h3).symm)
  have seg1 := a1.trans (K.pA Xm).2
  have seg2 := ((K.pB Xm).2.trans (K.pF Xm)).trans b3
  have e0 : XRoute (iin Xm K.tv (fun _ : Sl => Xm.Φ 0) c0)
      (glue (fun r : L3 T Sl => Xm.Φ (lab3 K.tv r).P) (fun _ : C => Xm.Φ 0))
      eraseC (fun _ => 0) :=
    xerase (fun t => rfl) (fun t => rfl) (fun q => rfl)
  have L1 := lift_live (fun _ : C => Xm.Φ 0) seg1
  have m1 : XRoute (glue (fun r => Xm.Φ (K.labA r).P) (fun _ : C => Xm.Φ 0))
      (glue (fun r => Xm.Φ (K.labA r).P) (fun _ : C => Xm.Φ 0))
      (fun z => addBlk bC (ap K.Jrᵀ (z ∘ bY)) z) (fun _ => 0) :=
    xgate_shear bC bY bY_inj K.Jrᵀ (fun k t _ => (congrArg Xm.Φ (K.hAy t)).symm)
  have m2 := copies_climb Xm (fun r => Xm.Φ (K.labA r).P) K.cen K.kc
  have m3 : XRoute (glue (fun r => Xm.Φ (K.labA r).P) (fun k => Xm.Φ (K.cen k).P))
      (glue (fun r => Xm.Φ (K.labA r).P) (fun k => Xm.Φ (K.cen k).P))
      (fun z => addBlk bS (ap (-K.Ccᵀ) (z ∘ bC)) z) (fun _ => 0) :=
    xgate_shear bS bC bC_inj (-K.Ccᵀ)
      (fun q k h => (congrArg Xm.Φ (K.hAc k q (ne_of_negT K.Cc h))).symm)
  have L2 := lift_live (fun k => Xm.Φ (K.cen k).P) seg2
  have e1 : XRoute (glue (fun r => Xm.Φ (K.labF r).P) (fun k => Xm.Φ (K.cen k).P))
      (iout Xm K.tv (fun _ : Sl => Xm.Φ 1) c1) eraseC (fun _ => 0) :=
    xerase (fun t => (congrArg Xm.Φ (K.hFx t)).symm) (fun t => (congrArg Xm.Φ (K.hFy t)).symm)
      (fun q => (congrArg Xm.Φ (K.hFs q)).symm)
  have tot := (((((e0.trans L1).trans m1).trans m2).trans m3).trans L2).trans e1
  refine (tot.castg (g' := shearB) (funext fun z => K.bwd_scalar z)).cast (fun φ => ?_)
  simp only [Phased.cost, zero_add, add_zero]
  ring

/-- **THE CARRIER INVOCATION THEOREM (general scope).**  Every carrier circuit given by its
phases is an invocation package for the bridged network, with the price `K.cost`. -/
def inv : Inv H T Sl C where
  tv := K.tv
  kx := K.kx
  ky := K.ky
  cost := K.cost
  fwd := fun Xm N0 Wn hN hW Z c0 c1 =>
    dirty_of_erased Xm K.tv N0 Wn hN hW Z c0 c1 (K.fwd_erased Xm c0 c1)
      (shearF_comm (fun _ => 1) (fun q => N0 * Z q) (fun _ => 1))
  bwd := fun Xm N0 Wn hN hW Z c0 c1 =>
    dirty_of_erased Xm K.tv N0 Wn hN hW Z c0 c1 (K.bwd_erased Xm c0 c1)
      (shearB_comm (fun _ => 1) (fun q => N0 * Z q) (fun _ => 1))

@[simp] lemma inv_cost (φ : ℕ → ℝ) : K.inv.cost φ = K.cost φ := rfl
@[simp] lemma inv_tv : K.inv.tv = K.tv := rfl

end Phased
end Thm
end
end CR
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.CR.Phased.fwd_erased
#print axioms OAI.PowerSaving.CR.Phased.bwd_erased
#print axioms OAI.PowerSaving.CR.Phased.inv
