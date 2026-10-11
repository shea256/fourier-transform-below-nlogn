import Work.GFrame.Labels.GCalc

/-!
# GFrame labels, part 17 (key: eng-labels): schedules whose moves are ANY step of the engine

`Sched.lean` asks a move to be an `FMv` (free / block / trans).  Here the most permissive
version: a move from the label `U` to `V` paying the ranks `rs` is legal as soon as the engine
has a one-role step from `Φ U` to `Φ V` of price `rcost φ rs` on every role type (`Reach`).
So every `GStep` theorem (ENGINE's or CLIFFORD's: `gstep_frame`, `gstep_cross`, `gstep_compl`,
`gstep_old_nested`, ...) can be used as a move of a schedule.

* `Reach K M N c`, `FMv.reach`, `reach_of_gstep`;
* `GSt.OkR`, `GSchedOkR`, `GSchedOk.toR`;
* `gsched_route_R`, `gsched_groute_R`   the route theorem for such schedules.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.GF
open Binary Matrix Finset RAM CB
noncomputable section

section
variable {α : Type} [Fintype α] [DecidableEq α] {𝓛 ρ : Type} [Fintype ρ] [DecidableEq ρ]

/-- the engine `K` carries the frame matrix `M` to `N` on any role, at price `c`. -/
def Reach (K : Calc α) (M N : CMat α) (c : (ℕ → ℝ) → ℝ) : Prop :=
  ∀ (ρ : Type) [Fintype ρ] [DecidableEq ρ] (l : ρ), K.Step l M N c

theorem FMv.reach {K : Calc α} {M N : CMat α} {rs : List ℕ} (h : FMv K M N rs) :
    Reach K M N (fun φ => rcost φ rs) := fun ρ _ _ l => FMv.step h l

/-- every `GStep` available on all role types is a `Reach` of the generalised engine. -/
theorem reach_of_gstep {M N : CMat α} {c : (ℕ → ℝ) → ℝ}
    (h : ∀ (ρ : Type) [Fintype ρ] [DecidableEq ρ] (l : ρ), GStep l M N c) :
    Reach (gcalc α) M N c := h

/-- legality of one step, moves being any step of the engine. -/
def GSt.OkR (K : Calc α) (Φ : 𝓛 → CMat α) (lab : ρ → 𝓛) : GSt 𝓛 ρ → Prop
  | .gate G => ∀ i j, G i j ≠ 0 → Φ (lab i) = Φ (lab j)
  | .relab G new => ∀ i j, G i j ≠ 0 → Φ (new i) = Φ (lab j)
  | .move r V rs => Reach K (Φ (lab r)) (Φ V) (fun φ => rcost φ rs)

/-- legality of a schedule, moves being any step of the engine. -/
def GSchedOkR (K : Calc α) (Φ : 𝓛 → CMat α) : (ρ → 𝓛) → List (GSt 𝓛 ρ) → Prop
  | _, [] => True
  | lab, s :: l => s.OkR K Φ lab ∧ GSchedOkR K Φ (s.out lab) l

theorem GSchedOk.toR {K : Calc α} {Φ : 𝓛 → CMat α} (l : List (GSt 𝓛 ρ)) (lab : ρ → 𝓛)
    (h : GSchedOk K Φ lab l) : GSchedOkR K Φ lab l := by
  induction l generalizing lab with
  | nil => trivial
  | cons s l ih =>
    refine ⟨?_, ih _ h.2⟩
    have h1 := h.1
    cases s with
    | gate G => exact h1
    | relab G new => exact h1
    | move r V rs => exact FMv.reach h1

theorem GSt.routeR (K : Calc α) (Φ : 𝓛 → CMat α) (lab : ρ → 𝓛) (s : GSt 𝓛 ρ)
    (h : s.OkR K Φ lab) :
    K.Route (fun r => Φ (lab r)) (fun r => Φ (s.out lab r)) s.act
      (fun φ => rcost φ s.ranks) := by
  cases s with
  | gate G =>
    exact K.route_cast (K.gate G (fun r => Φ (lab r)) (fun r => Φ (lab r)) h)
      (fun φ => (rcost_nil φ).symm)
  | relab G new =>
    exact K.route_cast (K.gate G (fun r => Φ (lab r)) (fun r => Φ (new r)) h)
      (fun φ => (rcost_nil φ).symm)
  | move r V rs =>
    have hr : K.Step r (Φ (lab r)) (Φ V) (fun φ => rcost φ rs) :=
      (show Reach K (Φ (lab r)) (Φ V) (fun φ => rcost φ rs) from h) ρ r
    have b := K.on_role (fun r' => Φ (lab r')) r (Φ V) hr
    have e : Function.update (fun r' => Φ (lab r')) r (Φ V)
        = fun r' => Φ (Function.update lab r V r') := by
      funext r'
      by_cases hr' : r' = r
      · subst hr'; simp
      · simp [Function.update_of_ne hr']
    rw [e] at b
    exact b

/-- **Route theorem, moves being any step of the engine.** -/
theorem gsched_route_R (K : Calc α) (Φ : 𝓛 → CMat α) (l : List (GSt 𝓛 ρ)) (lab : ρ → 𝓛)
    (h : GSchedOkR K Φ lab l) :
    K.Route (fun r => Φ (lab r)) (fun r => Φ (gschedOut lab l r)) (gschedAct l)
      (fun φ => rcost φ (gschedRanks l)) := by
  induction l generalizing lab with
  | nil => exact K.route_cast (K.route_refl _) (fun φ => (rcost_nil φ).symm)
  | cons s l ih =>
    have a := GSt.routeR K Φ lab s h.1
    have b := ih (s.out lab) h.2
    exact K.route_cast (K.route_trans a b) (fun φ => (rcost_append φ _ _).symm)

/-- the same for the generalised engine, as a `GRoute`. -/
theorem gsched_groute_R (Φ : 𝓛 → CMat α) (l : List (GSt 𝓛 ρ)) (lab : ρ → 𝓛)
    (h : GSchedOkR (gcalc α) Φ lab l) :
    GRoute (fun r => Φ (lab r)) (fun r => Φ (gschedOut lab l r)) (gschedAct l)
      (fun φ => rcost φ (gschedRanks l)) :=
  gsched_route_R (gcalc α) Φ l lab h

end
end
end PowerSaving.GF
end OAI

#print axioms OAI.PowerSaving.GF.gsched_route_R
#print axioms OAI.PowerSaving.GF.gsched_groute_R
#print axioms OAI.PowerSaving.GF.GSchedOk.toR
