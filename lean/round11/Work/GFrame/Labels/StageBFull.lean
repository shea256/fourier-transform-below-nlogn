import Work.GFrame.Labels.StageB
import Work.GFrame.Clifford.Climb

/-!
# GFrame labels, part 12 (key: eng-labels): STAGE B, unconditional

`StageB.lean` proves the stage-B route theorem under the hypothesis `RepChange α` (two
representatives of one subspace differ by a free left adapter).  CLIFFORD's `rep_change`
(`Work/GFrame/Clifford/Climb.lean`) is that statement, so everything is unconditional here.

* `repChange`           `RepChange α` holds;
* `SMv.fmv'`            every stage-B move is a one-role move of the generalised engine;
* `SMv.nested`          ANY nested pair `U ⊂ V`, ANY two representatives: ONE block of rank
                        `|t₀ \ s₀| = dim V - dim U`, given a common base `G₀` (data of the
                        certificate; all its conditions are decidable);
* `SLbl.rep_eq_iff`     GATE RULE, exactly: two labels carry the same matrix iff they name the
                        same subspace AND their bases induce the same pairing on it;
* `SMv.dim`             bookkeeping: a move changes the dimension by the rank it pays;
* `bsched_groute_full`  **stage B route theorem**, no hypothesis.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.GF
open Binary Matrix Finset RAM CB
noncomputable section

section
variable {α : Type} [Fintype α] [DecidableEq α]

/-- two representatives of the same subspace differ by a free left adapter. -/
theorem repChange (α : Type) [Fintype α] [DecidableEq α] : RepChange α :=
  fun G G' s s' h => rep_change G G' s s' h

/-- **Every stage-B move is a one-role move of the generalised engine.** -/
theorem SMv.fmv' {U V : SLbl α} {rs : List ℕ} (h : SMv (Fintype.card α) U V rs) :
    FMv (gcalc α) U.rep V.rep rs := SMv.fmv (repChange α) h

/-- **Any nested pair, any representatives: ONE block**, given a common base `G₀`. -/
theorem SMv.nested {m : ℕ} (U V : SLbl α) (G₀ : APerm α) (s₀ t₀ : Finset α)
    (h1 : ∀ x, U.Mem x ↔ InSub G₀ s₀ x) (h2 : ∀ x, InSub G₀ t₀ x ↔ V.Mem x) (hst : s₀ ⊆ t₀)
    (hr1 : 1 ≤ (t₀ \ s₀).card) (hr2 : (t₀ \ s₀).card < m) :
    SMv m U V [(t₀ \ s₀).card] := by
  have a : SMv m U ⟨G₀, s₀⟩ [] := SMv.rebase h1
  have b : SMv m (⟨G₀, s₀⟩ : SLbl α) ⟨G₀, t₀⟩ [(t₀ \ s₀).card] := SMv.up G₀ hst hr1 hr2
  have c : SMv m (⟨G₀, t₀⟩ : SLbl α) V [] := SMv.rebase h2
  have h := (a.trans b).trans c
  simpa using h

/-- the rank of that block is the difference of the dimensions. -/
theorem SMv.nested_rank (U V : SLbl α) (G₀ : APerm α) (s₀ t₀ : Finset α)
    (h1 : ∀ x, U.Mem x ↔ InSub G₀ s₀ x) (h2 : ∀ x, InSub G₀ t₀ x ↔ V.Mem x) (hst : s₀ ⊆ t₀) :
    (t₀ \ s₀).card = V.dim - U.dim :=
  climb_rank (G := U.G) (G' := V.G) (s := U.s) (t := V.s) h1 h2 hst

/-- **Gate rule, exactly.**  Two labels carry the SAME frame matrix iff they name the same
subspace and their bases induce the same pairing `x, u ↦ (G x)·(G u)` for `u` in it. -/
theorem SLbl.rep_eq_iff (U V : SLbl α) :
    U.rep = V.rep ↔ (∀ x, U.Mem x ↔ V.Mem x) ∧
      ∀ x u, U.Mem u → dot (U.G.π x) (U.G.π u) = dot (V.G.π x) (V.G.π u) :=
  core_eq_iff U.G V.G U.s V.s

variable {ρ : Type} [Fintype ρ] [DecidableEq ρ]

/-- **Stage B route theorem.**  A legal schedule on subspace labels (ARBITRARY subspaces,
degenerate and isotropic ones included; exact representatives; gates only between identical
representatives; free adapters for a change of representative) is an exact route of the
generalised engine: one block per nested step, nothing for adapters and gates. -/
theorem bsched_groute_full (l : List (GSt (SLbl α) ρ)) (lab : ρ → SLbl α)
    (h : BSchedOk lab l) :
    GRoute (fun r => (lab r).rep) (fun r => (gschedOut lab l r).rep) (gschedAct l)
      (fun φ => rcost φ (gschedRanks l)) :=
  bsched_groute (repChange α) l lab h

end
end
end PowerSaving.GF
end OAI

#print axioms OAI.PowerSaving.GF.repChange
#print axioms OAI.PowerSaving.GF.SMv.nested
#print axioms OAI.PowerSaving.GF.SLbl.rep_eq_iff
#print axioms OAI.PowerSaving.GF.bsched_groute_full
