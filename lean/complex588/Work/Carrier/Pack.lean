import Work.Carrier.Sched

/-!
# (key: carrier-thm) THE CARRIER INVOCATION THEOREM: a pair of schedules is an invocation package

`Carrier H T Sl C` is the hypothesis structure: lines `tv`, a FORWARD and a BACKWARD schedule
(`List (Step H (Box T Sl C))`, see `Work.Carrier.Sched`) on ALL roles of one invocation (banks
`x`, `y`, helper slots, scratch copies), each

* legal when started at the labels `lab0 tv c` (`x_t` on its line, `y_t` and every slot at 0,
  the copies at ANY labels `c` of the certificate's choice),
* ending with `x_t` and every slot at the full label and `y_t` at `t^⊥` (`Final`; the copies end
  anywhere),
* with the scalar identity  `eraseC ∘ schedAct ∘ eraseC = shearF` (resp. `shearB`):
  started with zero copies and ARBITRARY contents of the helper slots, the gates of the schedule
  do `y += x` (resp. `x -= y`), restore every slot, and the copies are erased;
* `hcost`: both schedules have the same price for every price list.

There is NO restriction on which roles the gates join: bank roles may be read and written at any
label of their chains (carriers), slots may be chained, values may be read in place.

`Carrier.inv : Inv H T Sl C` (the package of `Work.Bridge.Inv`): started on helper slots that
carry ARBITRARY frame matrices `Z q`, the forward / backward invocation is an exact block route
with scalar map `shearF` / `shearB` and price `rcost φ (ranks of the forward schedule)`: ONE
block per `Step.move`.

Proof: `xerase ; sched_route ; xerase`, then the re-framing argument of
`Work.Reframe.Shared` (`dirty_of_erased`).

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace CR
open Binary Matrix Finset RAM SS CB BR
noncomputable section

section Pack
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]

/-- labels at the START of an invocation: `x_t` on its line, `y_t` and the slots at zero, the
copies at `c`. -/
def lab0 (tv : T → Space H) (c : C → Lbl H) : Box T Sl C → Lbl H :=
  stamp (fun t => lineL (tv t)) (fun _ => zeroL) (fun _ => zeroL) c

/-- the labels `lab` are those of the END of an invocation on the banks and the slots: `x_t` and
every slot full, `y_t` at `t^⊥` (projectors only; the copies are free). -/
def Final (tv : T → Space H) (lab : Box T Sl C → Lbl H) : Prop :=
  (∀ t, (lab (bX t)).P = 1) ∧ (∀ t, (lab (bY t)).P = 1 + tt (tv t)) ∧ ∀ q, (lab (bS q)).P = 1

variable {α : Type} [Fintype α] [DecidableEq α]

/-- **Erase ; schedule ; erase.**  The slots go from the frame of 0 to the frame of 1, the copies
enter and leave with ARBITRARY frame matrices. -/
theorem route_erased (Xm : XMap H α) (tv : T → Space H) (c : C → Lbl H)
    (l : List (Step H (Box T Sl C))) (ok : SchedOk (lab0 tv c) l)
    (fin : Final tv (schedOut (lab0 tv c) l))
    (g : (Box T Sl C → ℂ) → (Box T Sl C → ℂ))
    (hg : ∀ z, eraseC (schedAct l (eraseC z)) = g z) (c0 c1 : C → CMat α) :
    XRoute (iin Xm tv (fun _ => Xm.Φ 0) c0) (iout Xm tv (fun _ => Xm.Φ 1) c1) g
      (fun φ => rcost φ (schedRanks (lab0 tv c) l)) := by
  have e0 : XRoute (iin Xm tv (fun _ => Xm.Φ 0) c0)
      (fun r : Box T Sl C => Xm.Φ (lab0 tv c r).P) eraseC (fun _ => 0) :=
    xerase (fun t => rfl) (fun t => rfl) (fun q => rfl)
  have e1 : XRoute (fun r => Xm.Φ (schedOut (lab0 tv c) l r).P)
      (iout Xm tv (fun _ => Xm.Φ 1) c1) eraseC (fun _ => 0) :=
    xerase (fun t => (congrArg Xm.Φ (fin.1 t)).symm) (fun t => (congrArg Xm.Φ (fin.2.1 t)).symm)
      (fun q => (congrArg Xm.Φ (fin.2.2 q)).symm)
  have tot := (e0.trans (sched_route Xm l (lab0 tv c) ok)).trans e1
  have hg' : eraseC ∘ (schedAct l ∘ eraseC) = g := funext hg
  refine (tot.castg hg').cast (fun φ => ?_)
  simp

/-- **From clean frames to DIRTY helper slots** (the argument of
`CB.xinvocation_fwd_dirty`, for any route).  `N0` is an inverse of the frame of the base, `Wn`
the frame of the window; the slots start at ARBITRARY matrices `Z q` and end at `Wn * Z q`. -/
theorem dirty_of_erased (Xm : XMap H α) (tv : T → Space H)
    {g : (Box T Sl C → ℂ) → (Box T Sl C → ℂ)} {cost : (ℕ → ℝ) → ℝ}
    (N0 Wn : CMat α) (hN : Xm.Φ 0 * N0 = 1) (hW : Xm.Φ 1 = Wn * Xm.Φ 0)
    (Z : Sl → CMat α) (c0 c1 : C → CMat α)
    (h : XRoute (iin Xm tv (fun _ => Xm.Φ 0) c0) (iout Xm tv (fun _ => Xm.Φ 1) c1) g cost)
    (hcomm : ∀ (f : ℕ) (x : Data α (Box T Sl C) f),
      point f g (multiAct f (stamp (fun _ : T => (1 : CMat α)) (fun _ : T => (1 : CMat α))
          (fun q => N0 * Z q) (fun _ : C => (1 : CMat α))) x)
        = multiAct f (stamp (fun _ : T => (1 : CMat α)) (fun _ : T => (1 : CMat α))
          (fun q => N0 * Z q) (fun _ : C => (1 : CMat α))) (point f g x)) :
    XRoute (iin Xm tv Z c0) (iout Xm tv (fun q => Wn * Z q) c1) g cost := by
  have h' := XRoute.reframe
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

/-- **The hypotheses of the carrier invocation theorem.**  See the file header. -/
structure Carrier (H T Sl C : Type) [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
    [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] where
  tv : T → Space H
  kx : ∀ t, Climb (lineL (tv t)) fullL
  ky : ∀ t, Climb zeroL (perpL (tv t))
  cF : C → Lbl H
  cB : C → Lbl H
  fwd : List (Step H (Box T Sl C))
  bwd : List (Step H (Box T Sl C))
  okF : SchedOk (lab0 tv cF) fwd
  okB : SchedOk (lab0 tv cB) bwd
  finF : Final tv (schedOut (lab0 tv cF) fwd)
  finB : Final tv (schedOut (lab0 tv cB) bwd)
  scF : ∀ z, eraseC (schedAct fwd (eraseC z)) = shearF z
  scB : ∀ z, eraseC (schedAct bwd (eraseC z)) = shearB z
  hcost : ∀ φ : ℕ → ℝ, rcost φ (schedRanks (lab0 tv cB) bwd)
    = rcost φ (schedRanks (lab0 tv cF) fwd)

section Thm
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]

/-- block ranks of one invocation (those of the forward schedule, in order). -/
def Carrier.ranks (K : Carrier H T Sl C) : List ℕ := schedRanks (lab0 K.tv K.cF) K.fwd

/-- price of one invocation (forward or backward): one block per move of the schedule. -/
def Carrier.cost (K : Carrier H T Sl C) (φ : ℕ → ℝ) : ℝ := rcost φ K.ranks

/-- **THE CARRIER INVOCATION THEOREM.**  Every `Carrier` is an invocation package for the
bridged network, with the price `K.cost φ = rcost φ K.ranks`. -/
def Carrier.inv (K : Carrier H T Sl C) : Inv H T Sl C where
  tv := K.tv
  kx := K.kx
  ky := K.ky
  cost := K.cost
  fwd := fun Xm N0 Wn hN hW Z c0 c1 =>
    dirty_of_erased Xm K.tv N0 Wn hN hW Z c0 c1
      (route_erased Xm K.tv K.cF K.fwd K.okF K.finF shearF K.scF c0 c1)
      (shearF_comm (fun _ => 1) (fun q => N0 * Z q) (fun _ => 1))
  bwd := fun Xm N0 Wn hN hW Z c0 c1 =>
    dirty_of_erased Xm K.tv N0 Wn hN hW Z c0 c1
      ((route_erased Xm K.tv K.cB K.bwd K.okB K.finB shearB K.scB c0 c1).cast K.hcost)
      (shearB_comm (fun _ => 1) (fun q => N0 * Z q) (fun _ => 1))

@[simp] lemma Carrier.inv_cost (K : Carrier H T Sl C) (φ : ℕ → ℝ) :
    K.inv.cost φ = rcost φ K.ranks := rfl
@[simp] lemma Carrier.inv_tv (K : Carrier H T Sl C) : K.inv.tv = K.tv := rfl

end Thm
end
end CR
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.CR.route_erased
#print axioms OAI.PowerSaving.CR.dirty_of_erased
#print axioms OAI.PowerSaving.CR.Carrier.inv
