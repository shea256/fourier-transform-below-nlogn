import Work.GFrame.Labels.StageA
import Work.Carrier.Pack

/-!
# GFrame labels, part 11 (key: eng-labels): the carrier invocation theorem, generalised

`Work/Carrier/Pack.lean` (`Carrier`, `Carrier.inv`) with generalised schedules (stage A): the
forward and the backward invocation are lists of `GSt (Lbl H) (Box T Sl C)` whose moves are
`GMv` (nested steps with ANY nondegenerate residual, orthonormal-type or alternating).

* `GRoute.reframe`     re-framing a generalised route (copy of `XRoute.reframe`);
* `groute_erased`      erase ; schedule ; erase, as a `GRoute`, for every `GXMap`;
* `gdirty_of_erased`   from clean frames to DIRTY helper slots;
* `GCarrier`           the hypothesis structure; `GCarrier.fwd_route`, `GCarrier.bwd_route`:
                       the invocation is a `GRoute` with scalar map `shearF` / `shearB` and
                       price `rcost φ (gschedRanks fwd)`: ONE block per move;
* `Carrier.toG`        every old `Carrier` is a `GCarrier` with the same block ranks.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.GF
open Binary Matrix Finset RAM SS CB BR CR RF
noncomputable section

section
variable {α ρ : Type} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

/-- **Re-framing a generalised route.**  Same word, same price. -/
theorem GRoute.reframe {S T : ρ → CMat α} {g : (ρ→ℂ) → (ρ→ℂ)} {c : (ℕ → ℝ) → ℝ}
    (D : ρ → CMat α) (h : GRoute S T g c)
    (hg : ∀ (f : ℕ) (x : Data α ρ f), point f g (multiAct f D x) = multiAct f D (point f g x)) :
    GRoute (fun r => S r * D r) (fun r => T r * D r) g c := by
  obtain ⟨w, hw, hc, hwalk⟩ := h
  refine ⟨w, hw, hc, fun f x => ?_⟩
  have h1 := multiAct_mulR f S D x
  have h2 := multiAct_mulR f T D (point f g x)
  rw [h1, hwalk, hg, h2]

end

section Pack
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]
variable {α : Type} [Fintype α] [DecidableEq α]

/-- **Erase ; generalised schedule ; erase.** -/
theorem groute_erased (X : GXMap H α) (tv : T → Space H) (c : C → Lbl H)
    (l : List (GSt (Lbl H) (Box T Sl C))) (ok : ASchedOk (fun p => [2 * p]) (lab0 tv c) l)
    (fin : Final tv (gschedOut (lab0 tv c) l))
    (g : (Box T Sl C → ℂ) → (Box T Sl C → ℂ))
    (hg : ∀ z, eraseC (gschedAct l (eraseC z)) = g z) (c0 c1 : C → CMat α) :
    GRoute (iin X.toXMap tv (fun _ => X.Φ 0) c0) (iout X.toXMap tv (fun _ => X.Φ 1) c1) g
      (fun φ => rcost φ (gschedRanks l)) := by
  have e0 : GRoute (iin X.toXMap tv (fun _ => X.Φ 0) c0)
      (fun r : Box T Sl C => X.Φ (lab0 tv c r).P) eraseC (fun _ => 0) :=
    GRoute.ofX (xerase (fun t => rfl) (fun t => rfl) (fun q => rfl))
  have e1 : GRoute (fun r => X.Φ (gschedOut (lab0 tv c) l r).P)
      (iout X.toXMap tv (fun _ => X.Φ 1) c1) eraseC (fun _ => 0) :=
    GRoute.ofX (xerase (fun t => (congrArg X.Φ (fin.1 t)).symm)
      (fun t => (congrArg X.Φ (fin.2.1 t)).symm) (fun q => (congrArg X.Φ (fin.2.2 q)).symm))
  have tot := (e0.trans (asched_groute X l (lab0 tv c) ok)).trans e1
  have hg' : eraseC ∘ (gschedAct l ∘ eraseC) = g := funext hg
  rw [hg'] at tot
  exact tot.cast (fun φ => by simp)

/-- **From clean frames to DIRTY helper slots**, for a generalised route. -/
theorem gdirty_of_erased (Xm : XMap H α) (tv : T → Space H)
    {g : (Box T Sl C → ℂ) → (Box T Sl C → ℂ)} {cost : (ℕ → ℝ) → ℝ}
    (N0 Wn : CMat α) (hN : Xm.Φ 0 * N0 = 1) (hW : Xm.Φ 1 = Wn * Xm.Φ 0)
    (Z : Sl → CMat α) (c0 c1 : C → CMat α)
    (h : GRoute (iin Xm tv (fun _ => Xm.Φ 0) c0) (iout Xm tv (fun _ => Xm.Φ 1) c1) g cost)
    (hcomm : ∀ (f : ℕ) (x : Data α (Box T Sl C) f),
      point f g (multiAct f (stamp (fun _ : T => (1 : CMat α)) (fun _ : T => (1 : CMat α))
          (fun q => N0 * Z q) (fun _ : C => (1 : CMat α))) x)
        = multiAct f (stamp (fun _ : T => (1 : CMat α)) (fun _ : T => (1 : CMat α))
          (fun q => N0 * Z q) (fun _ : C => (1 : CMat α))) (point f g x)) :
    GRoute (iin Xm tv Z c0) (iout Xm tv (fun q => Wn * Z q) c1) g cost := by
  have h' := GRoute.reframe
    (stamp (fun _ : T => (1 : CMat α)) (fun _ : T => (1 : CMat α)) (fun q => N0 * Z q)
      (fun _ : C => (1 : CMat α))) h hcomm
  have e0 : iin Xm tv Z c0 = fun r => iin Xm tv (fun _ => Xm.Φ 0) c0 r *
      stamp (fun _ : T => (1 : CMat α)) (fun _ : T => (1 : CMat α)) (fun q => N0 * Z q)
        (fun _ : C => (1 : CMat α)) r := by
    funext r
    rcases r with ((t|t)|(q|k))
    · show Xm.Φ (tt (tv t)) = Xm.Φ (tt (tv t)) * 1
      rw [Matrix.mul_one]
    · show Xm.Φ 0 = Xm.Φ 0 * 1
      rw [Matrix.mul_one]
    · show Z q = Xm.Φ 0 * (N0 * Z q)
      rw [← Matrix.mul_assoc, hN, Matrix.one_mul]
    · show c0 k = c0 k * 1
      rw [Matrix.mul_one]
  have e1 : iout Xm tv (fun q => Wn * Z q) c1 = fun r => iout Xm tv (fun _ => Xm.Φ 1) c1 r *
      stamp (fun _ : T => (1 : CMat α)) (fun _ : T => (1 : CMat α)) (fun q => N0 * Z q)
        (fun _ : C => (1 : CMat α)) r := by
    funext r
    rcases r with ((t|t)|(q|k))
    · show Xm.Φ 1 = Xm.Φ 1 * 1
      rw [Matrix.mul_one]
    · show Xm.Φ (1 + tt (tv t)) = Xm.Φ (1 + tt (tv t)) * 1
      rw [Matrix.mul_one]
    · show Wn * Z q = Xm.Φ 1 * (N0 * Z q)
      rw [hW, Matrix.mul_assoc, ← Matrix.mul_assoc (Xm.Φ 0), hN, Matrix.one_mul]
    · show c1 k = c1 k * 1
      rw [Matrix.mul_one]
  rw [e0, e1]
  exact h'

end Pack

/-- **The hypotheses of the generalised carrier invocation theorem** (stage A). -/
structure GCarrier (H T Sl C : Type) [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
    [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] where
  tv : T → Space H
  cF : C → Lbl H
  cB : C → Lbl H
  fwd : List (GSt (Lbl H) (Box T Sl C))
  bwd : List (GSt (Lbl H) (Box T Sl C))
  okF : ASchedOk (fun p => [2 * p]) (lab0 tv cF) fwd
  okB : ASchedOk (fun p => [2 * p]) (lab0 tv cB) bwd
  finF : Final tv (gschedOut (lab0 tv cF) fwd)
  finB : Final tv (gschedOut (lab0 tv cB) bwd)
  scF : ∀ z, eraseC (gschedAct fwd (eraseC z)) = shearF z
  scB : ∀ z, eraseC (gschedAct bwd (eraseC z)) = shearB z
  hcost : ∀ φ : ℕ → ℝ, rcost φ (gschedRanks bwd) = rcost φ (gschedRanks fwd)

section Thm
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]
variable {α : Type} [Fintype α] [DecidableEq α]

/-- block ranks of one invocation. -/
def GCarrier.ranks (K : GCarrier H T Sl C) : List ℕ := gschedRanks K.fwd

/-- **Generalised carrier invocation theorem, forward.** -/
theorem GCarrier.fwd_route (K : GCarrier H T Sl C) (X : GXMap H α) (N0 Wn : CMat α)
    (hN : X.Φ 0 * N0 = 1) (hW : X.Φ 1 = Wn * X.Φ 0) (Z : Sl → CMat α) (c0 c1 : C → CMat α) :
    GRoute (iin X.toXMap K.tv Z c0) (iout X.toXMap K.tv (fun q => Wn * Z q) c1) shearF
      (fun φ => rcost φ K.ranks) :=
  gdirty_of_erased X.toXMap K.tv N0 Wn hN hW Z c0 c1
    (groute_erased X K.tv K.cF K.fwd K.okF K.finF shearF K.scF c0 c1)
    (shearF_comm (fun _ => 1) (fun q => N0 * Z q) (fun _ => 1))

/-- **Generalised carrier invocation theorem, backward** (same price). -/
theorem GCarrier.bwd_route (K : GCarrier H T Sl C) (X : GXMap H α) (N0 Wn : CMat α)
    (hN : X.Φ 0 * N0 = 1) (hW : X.Φ 1 = Wn * X.Φ 0) (Z : Sl → CMat α) (c0 c1 : C → CMat α) :
    GRoute (iin X.toXMap K.tv Z c0) (iout X.toXMap K.tv (fun q => Wn * Z q) c1) shearB
      (fun φ => rcost φ K.ranks) :=
  gdirty_of_erased X.toXMap K.tv N0 Wn hN hW Z c0 c1
    ((groute_erased X K.tv K.cB K.bwd K.okB K.finB shearB K.scB c0 c1).cast K.hcost)
    (shearB_comm (fun _ => 1) (fun q => N0 * Z q) (fun _ => 1))

/-- **Every old carrier is a generalised carrier**, with the same block ranks. -/
def Carrier.toG (K : Carrier H T Sl C) : GCarrier H T Sl C where
  tv := K.tv
  cF := K.cF
  cB := K.cB
  fwd := emb (lab0 K.tv K.cF) K.fwd
  bwd := emb (lab0 K.tv K.cB) K.bwd
  okF := emb_aok _ _ _ K.okF
  okB := emb_aok _ _ _ K.okB
  finF := by rw [emb_out]; exact K.finF
  finB := by rw [emb_out]; exact K.finB
  scF := by rw [emb_act]; exact K.scF
  scB := by rw [emb_act]; exact K.scB
  hcost := fun φ => by rw [emb_ranks, emb_ranks]; exact K.hcost φ

theorem Carrier.toG_ranks (K : Carrier H T Sl C) : (Carrier.toG K).ranks = K.ranks :=
  emb_ranks _ _

end Thm
end
end PowerSaving.GF
end OAI

#print axioms OAI.PowerSaving.GF.GCarrier.fwd_route
#print axioms OAI.PowerSaving.GF.GCarrier.bwd_route
#print axioms OAI.PowerSaving.GF.Carrier.toG
