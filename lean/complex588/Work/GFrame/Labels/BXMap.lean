import Work.GFrame.Labels.StageBFull

/-!
# GFrame labels, part 14 (key: eng-labels): STAGE B frame maps (label space ≠ address space)

In the network a role lives on an address space `α` that is bigger than the label space `H`
of the certificate (`α = H × H`, `H ⊕ (B × H)`, ...).  For stage A this is `GXMap`.  For
stage B (arbitrary subspaces of `H`, exact representatives) it is:

* `BXMap H α`      a base of `H` goes to a base of `α`, a coordinate set to a coordinate set,
                   monotone, preserving the size of differences, and SUBSPACE-FUNCTORIAL: equal
                   subspaces of `H` go to equal subspaces of `α`;
* `BXMap.lab`, `BXMap.Φ`   the lifted label and its exact frame matrix `core (liftG G) (liftS s)`;
* `BXMap.smv`      every stage-B move on `H` (rank bound = number of coordinates of `α`) is a
                   stage-B move on `α` with the same block ranks;
* `HOk`, `HSchedOk`, `hsched_groute`   **stage B route theorem through a frame map**;
* `BXMap.refl`     the identity frame map (`H = α`).

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.GF
open Binary Matrix Finset RAM CB
noncomputable section

/-- **A stage-B frame map** from the label space `H` to the address space `α`. -/
structure BXMap (H α : Type) [Fintype H] [DecidableEq H] [Fintype α] [DecidableEq α] where
  liftG : APerm H → APerm α
  liftS : Finset H → Finset α
  mono : ∀ {s t : Finset H}, s ⊆ t → liftS s ⊆ liftS t
  card : ∀ {s t : Finset H}, s ⊆ t → (liftS t \ liftS s).card = (t \ s).card
  sub : ∀ {G G' : APerm H} {s s' : Finset H}, (∀ x, InSub G s x ↔ InSub G' s' x) →
    ∀ y, InSub (liftG G) (liftS s) y ↔ InSub (liftG G') (liftS s') y

section
variable {H α : Type} [Fintype H] [DecidableEq H] [Fintype α] [DecidableEq α]

namespace BXMap
variable (X : BXMap H α)

/-- the lifted label. -/
def lab (U : SLbl H) : SLbl α := ⟨X.liftG U.G, X.liftS U.s⟩

/-- the exact frame matrix of a role of address space `α` carrying the label `U` of `H`. -/
def Φ (U : SLbl H) : CMat α := (X.lab U).rep

/-- **Moves lift**, with the same block ranks. -/
theorem smv {m : ℕ} {U V : SLbl H} {rs : List ℕ} (h : SMv m U V rs) :
    SMv m (X.lab U) (X.lab V) rs := by
  induction h with
  | stay U => exact SMv.stay _
  | up G hst h1 h2 =>
    have e := X.card hst
    have h := SMv.up (m := m) (X.liftG G) (X.mono hst) (by rw [e]; exact h1)
      (by rw [e]; exact h2)
    rw [e] at h
    exact h
  | down G hst h1 h2 =>
    have e := X.card hst
    have h := SMv.down (m := m) (X.liftG G) (X.mono hst) (by rw [e]; exact h1)
      (by rw [e]; exact h2)
    rw [e] at h
    exact h
  | rebase h => exact SMv.rebase (X.sub h)
  | trans _ _ iha ihb => exact SMv.trans iha ihb

/-- a move on `H` is a one-role move of the generalised engine on `α`. -/
theorem fmv {U V : SLbl H} {rs : List ℕ} (h : SMv (Fintype.card α) U V rs) :
    FMv (gcalc α) (X.Φ U) (X.Φ V) rs := SMv.fmv' (X.smv h)

/-- GATE RULE through a frame map: the lifted representatives are the same matrix iff the
lifted labels satisfy `SLbl.rep_eq_iff`; equal labels always do. -/
theorem Φ_congr {U V : SLbl H} (h : U = V) : X.Φ U = X.Φ V := by rw [h]

end BXMap

/-- the identity frame map. -/
def BXMap.refl (α : Type) [Fintype α] [DecidableEq α] : BXMap α α where
  liftG := id
  liftS := id
  mono := fun h => h
  card := fun _ => rfl
  sub := fun h => h

variable {ρ : Type} [Fintype ρ] [DecidableEq ρ]

/-- legality of one step on labels of `H` for roles of address space `α`. -/
def HOk (X : BXMap H α) (lab : ρ → SLbl H) : GSt (SLbl H) ρ → Prop
  | .gate G => ∀ i j, G i j ≠ 0 → X.Φ (lab i) = X.Φ (lab j)
  | .relab G new => ∀ i j, G i j ≠ 0 → X.Φ (new i) = X.Φ (lab j)
  | .move r V rs => SMv (Fintype.card α) (lab r) V rs

/-- legality of a schedule on labels of `H`. -/
def HSchedOk (X : BXMap H α) : (ρ → SLbl H) → List (GSt (SLbl H) ρ) → Prop
  | _, [] => True
  | lab, s :: l => HOk X lab s ∧ HSchedOk X (s.out lab) l

theorem hsched_ok (X : BXMap H α) (lab : ρ → SLbl H) (l : List (GSt (SLbl H) ρ))
    (h : HSchedOk X lab l) : GSchedOk (gcalc α) X.Φ lab l := by
  induction l generalizing lab with
  | nil => trivial
  | cons s l ih =>
    refine ⟨?_, ih _ h.2⟩
    have h1 := h.1
    cases s with
    | gate G => exact h1
    | relab G new => exact h1
    | move r V rs => exact X.fmv h1

/-- **Stage B route theorem through a frame map.**  Labels are arbitrary subspaces of the
label space `H` with their representatives; the roles live on the address space `α`. -/
theorem hsched_groute (X : BXMap H α) (l : List (GSt (SLbl H) ρ)) (lab : ρ → SLbl H)
    (h : HSchedOk X lab l) :
    GRoute (fun r => X.Φ (lab r)) (fun r => X.Φ (gschedOut lab l r)) (gschedAct l)
      (fun φ => rcost φ (gschedRanks l)) :=
  gsched_groute X.Φ l lab (hsched_ok X lab l h)

end
end
end PowerSaving.GF
end OAI

#print axioms OAI.PowerSaving.GF.BXMap.smv
#print axioms OAI.PowerSaving.GF.BXMap.fmv
#print axioms OAI.PowerSaving.GF.hsched_groute
