import Work.GFrame.Labels.GCalc
import Work.GFrame.Labels.Embed
import Work.GFrame.Clifford.AltBlock

/-!
# GFrame labels, part 8 (key: eng-labels): STAGE A, complete

* `altAt_gcalc`     the generalised engine performs an ALTERNATING residual of rank `2p` (no
                    unit vector) as ONE block of rank `2p` between free adapters
                    (CLIFFORD's `alt_block` + ENGINE's free letters);
* `AOk`, `ASchedOk` label-level legality of a schedule (what a certificate checker proves):
                    gates join roles with the same label matrix; a move is a `GMv`
                    (stay / up / down; orthonormal-type or alternating residual);
* `asched_ok`       label-level legality gives matrix-level legality, for every `GXMap` and
                    every engine that knows alternating residuals at the ranks `ar`;
* `asched_groute`   **stage A route theorem**: a label-legal schedule is a `GRoute` of the
                    generalised engine for every `GXMap`; price: ONE block of rank `r` per
                    orthonormal-type step, ONE block of rank `2p` per alternating step;
* `emb_aok`         every old legal schedule (`CR.SchedOk`) is label-legal here.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.GF
open Binary Matrix Finset RAM CB SS
noncomputable section

section
variable {H α ρ : Type} [Fintype H] [DecidableEq H] [Fintype α] [DecidableEq α]
  [Fintype ρ] [DecidableEq ρ]

/-- **One twisted block.**  In the generalised engine an alternating residual of rank `2p`
is ONE block of rank `2p`. -/
theorem altAt_gcalc : AltAt (gcalc α) (fun p => [2 * p]) := by
  intro p w w' ind hp hr M
  obtain ⟨A, B, z, hA, hB, indz, h⟩ := alt_block w w' ind
  refine fmv_of_factor z indz (by omega) hr hA hB ?_
  unfold altMat
  rw [h]

/-- an alternating residual along `w, w'` in the generalised engine, as a step. -/
theorem gstep_alt (l : ρ) (M : CMat α) {p : ℕ} (w w' : Fin p → Space α)
    (ind : LinearIndependent F (Sum.elim w w')) (hp : 1 ≤ p) (hr : 2 * p < Fintype.card α) :
    GStep l M (altMat w w' * M) (fun φ => φ (2 * p)) :=
  GStep.cast (FMv.step (altAt_gcalc w w' ind hp hr M) l)
    (fun φ => by rw [rcost_single, bcost_pos φ (by omega)])

/-- label-level legality of one step (stage A). -/
def AOk (ar : ℕ → List ℕ) (lab : ρ → Lbl H) : GSt (Lbl H) ρ → Prop
  | .gate G => ∀ i j, G i j ≠ 0 → (lab i).P = (lab j).P
  | .relab G new => ∀ i j, G i j ≠ 0 → (new i).P = (lab j).P
  | .move r V rs => GMv ar (lab r) V rs

/-- label-level legality of a schedule (stage A). -/
def ASchedOk (ar : ℕ → List ℕ) : (ρ → Lbl H) → List (GSt (Lbl H) ρ) → Prop
  | _, [] => True
  | lab, s :: l => AOk ar lab s ∧ ASchedOk ar (s.out lab) l

/-- label-level legality gives matrix-level legality. -/
theorem asched_ok (X : GXMap H α) {K : Calc α} {ar : ℕ → List ℕ} (hK : AltAt K ar)
    (lab : ρ → Lbl H) (l : List (GSt (Lbl H) ρ)) (h : ASchedOk ar lab l) :
    GSchedOk K (fun U => X.Φ U.P) lab l := by
  induction l generalizing lab with
  | nil => trivial
  | cons s l ih =>
    refine ⟨?_, ih _ h.2⟩
    have h1 := h.1
    cases s with
    | gate G => exact fun i j hij => congrArg X.Φ (h1 i j hij)
    | relab G new => exact fun i j hij => congrArg X.Φ (h1 i j hij)
    | move r V rs => exact X.mv hK h1

/-- **Stage A route theorem.**  A label-legal schedule (nested steps with ANY nondegenerate
residual: orthonormal-type or alternating) is an exact route of the generalised engine, for
every Walsh-diagonal frame map; one block per step. -/
theorem asched_groute (X : GXMap H α) (l : List (GSt (Lbl H) ρ)) (lab : ρ → Lbl H)
    (h : ASchedOk (fun p => [2 * p]) lab l) :
    GRoute (fun r => X.Φ (lab r).P) (fun r => X.Φ (gschedOut lab l r).P) (gschedAct l)
      (fun φ => rcost φ (gschedRanks l)) :=
  gsched_groute (fun U : Lbl H => X.Φ U.P) l lab
    (asched_ok X (K := gcalc α) (ar := fun p => [2 * p]) altAt_gcalc lab l h)

/-- every old legal schedule is label-legal in the generalised calculus. -/
theorem emb_aok (ar : ℕ → List ℕ) (lab : ρ → Lbl H) (l : List (CR.Step H ρ))
    (h : CR.SchedOk lab l) : ASchedOk ar lab (emb lab l) := by
  induction l generalizing lab with
  | nil => trivial
  | cons s l ih =>
    refine ⟨?_, ?_⟩
    · have h1 := h.1
      cases s with
      | gate G => exact h1
      | relab G new => exact h1
      | move r V => exact Mv.gmv ar h1
    · rw [embSt_out]; exact ih _ h.2

end
end
end PowerSaving.GF
end OAI

#print axioms OAI.PowerSaving.GF.altAt_gcalc
#print axioms OAI.PowerSaving.GF.gstep_alt
#print axioms OAI.PowerSaving.GF.asched_groute
#print axioms OAI.PowerSaving.GF.emb_aok
