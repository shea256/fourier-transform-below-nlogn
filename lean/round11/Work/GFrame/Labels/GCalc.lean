import Work.GFrame.Labels.Sched
import Work.GFrame.Engine.Route

/-!
# GFrame labels, part 4 (key: eng-labels): the generalised engine as a route calculus

* `gcalc α`        ENGINE's language (old letters + the free adapters `perm`, `phase`) as a
                   `Calc α`: `Step := GStep`, `Route := GRoute`, `Free := GF.Free`;
* `FMv.ofX`        every one-role move of the old engine is one of the generalised engine,
                   with the same block ranks (existing certificates keep working);
* `fmv_of_factor`  the frame lemma as a certificate: `N = A * blockMat z * B * M` with `A`, `B`
                   free is ONE block of rank `r`;  `fmv_of_free`: `N = A * M` is free;
* `gsched_groute`  a legal schedule over ANY label system is a `GRoute` of the generalised
                   engine, one block per paid rank.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.GF
open Binary Matrix Finset RAM CB
noncomputable section

/-- **The generalised engine (free adapters) as a route calculus.** -/
def gcalc (α : Type) [Fintype α] [DecidableEq α] : Calc α where
  Step := fun l M N c => GStep l M N c
  Route := fun S T g c => GRoute S T g c
  Free := GF.Free
  step_refl := fun l M => GStep.refl l M
  step_cast := fun a h => a.cast h
  step_trans := fun a b => a.trans b
  route_refl := fun S => GRoute.refl
  route_cast := fun a h => a.cast h
  route_trans := fun a b => a.trans b
  gate := fun g S T h => GRoute.gate g S T h
  on_role := @fun ρ _ _ S l N c h => GRoute.on_role S l N h
  free_one := GF.Free.one
  free_mul := GF.Free.mul
  free_shift := GF.Free.shift
  free := @fun ρ _ _ l M A h => gstep_free h l M
  block := @fun ρ _ _ l M r z ind h1 h2 => gstep_block l M z ind h1 h2

section
variable {α : Type} [Fintype α] [DecidableEq α]

lemma free_of_xfree {A : CMat α} (h : XFree A) : GF.Free A := by
  induction h with
  | one => exact GF.Free.one
  | shift z => exact GF.Free.shift z
  | mul _ _ iha ihb => exact GF.Free.mul iha ihb

/-- every move of the old engine is a move of the generalised engine, same block ranks. -/
theorem FMv.ofX {M N : CMat α} {rs : List ℕ} (h : FMv (xcalc α) M N rs) :
    FMv (gcalc α) M N rs := by
  induction h with
  | free hA => exact FMv.free (K := gcalc α) (free_of_xfree hA)
  | block z ind h1 h2 => exact FMv.block z ind h1 h2
  | trans _ _ iha ihb => exact FMv.trans iha ihb
  | zero _ ih => exact FMv.zero ih

/-- **The frame lemma as a certificate**: a transition `free * block * free` is ONE block. -/
theorem fmv_of_factor {M N A B : CMat α} {r : ℕ} (z : Fin r → Space α)
    (ind : LinearIndependent F z) (h1 : 1 ≤ r) (h2 : r < Fintype.card α)
    (hA : GF.Free A) (hB : GF.Free B) (hN : N = A * blockMat z * B * M) :
    FMv (gcalc α) M N [r] := by
  subst hN
  exact FMv.factor (K := gcalc α) z ind h1 h2 hA hB M

/-- two representatives that differ by a free matrix on the left: a free move. -/
theorem fmv_of_free {M N A : CMat α} (hA : GF.Free A) (hN : N = A * M) :
    FMv (gcalc α) M N [] := by
  subst hN
  exact FMv.free (K := gcalc α) hA

variable {𝓛 ρ : Type} [Fintype ρ] [DecidableEq ρ]

/-- **A legal schedule is an exact route of the generalised engine**, for every label
system `Φ`: one block per paid rank; free adapters and gates cost nothing. -/
theorem gsched_groute (Φ : 𝓛 → CMat α) (l : List (GSt 𝓛 ρ)) (lab : ρ → 𝓛)
    (h : GSchedOk (gcalc α) Φ lab l) :
    GRoute (fun r => Φ (lab r)) (fun r => Φ (gschedOut lab l r)) (gschedAct l)
      (fun φ => rcost φ (gschedRanks l)) :=
  gsched_route (gcalc α) Φ l lab h

/-- a schedule legal for the old engine is legal for the generalised engine. -/
theorem GSchedOk.ofX (Φ : 𝓛 → CMat α) (l : List (GSt 𝓛 ρ)) (lab : ρ → 𝓛)
    (h : GSchedOk (xcalc α) Φ lab l) : GSchedOk (gcalc α) Φ lab l := by
  induction l generalizing lab with
  | nil => trivial
  | cons s l ih =>
    refine ⟨?_, ih _ h.2⟩
    have h1 := h.1
    cases s with
    | gate G => exact h1
    | relab G new => exact h1
    | move r V rs => exact FMv.ofX h1

end
end
end PowerSaving.GF
end OAI

#print axioms OAI.PowerSaving.GF.gcalc
#print axioms OAI.PowerSaving.GF.fmv_of_factor
#print axioms OAI.PowerSaving.GF.gsched_groute
#print axioms OAI.PowerSaving.GF.GSchedOk.ofX
