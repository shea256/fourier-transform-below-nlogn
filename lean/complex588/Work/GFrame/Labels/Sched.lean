import Work.GFrame.Labels.Calc

/-!
# GFrame labels, part 2 (key: eng-labels): schedules over ANY label system

Generalisation of `Work/Carrier/Sched.lean`.  A label system is a type `𝓛` of labels with the
EXACT frame matrix `Φ U : CMat α` of each label (for stage A: `𝓛 = SS.Lbl H`, `Φ U = Xm.Φ U.P`;
for stage B: a subspace with its representative).  A schedule is an ordered list of steps on
an arbitrary role type `ρ`:

* `GSt.gate G`         free gate; legal if every nonzero entry joins two roles with IDENTICAL
                       frame matrices; labels unchanged;
* `GSt.relab G new`    general free gate; role `i` leaves with the label `new i`; legal if
                       `G i j ≠ 0 → Φ (new i) = Φ (lab j)`;
* `GSt.move r V rs`    ONE-role move to the label `V` paying blocks of ranks `rs`; legal if
                       `FMv K (Φ (lab r)) (Φ V) rs`  (`rs = []`: a free adapter;
                       `rs = [q]`: one block of rank `q`).

`gsched_route`: **a legal schedule is an exact route of the engine `K`**, from the frames of
its initial labels to the frames of its final labels, scalar map `gschedAct l`, price
`rcost φ (gschedRanks l)`: one block per paid rank.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.GF
open Binary Matrix Finset RAM CB
noncomputable section

section Sched
variable {α : Type} [Fintype α] [DecidableEq α] {𝓛 ρ : Type} [Fintype ρ] [DecidableEq ρ]

/-- One step of a schedule.  See the file header. -/
inductive GSt (𝓛 ρ : Type) where
  | gate (G : Matrix ρ ρ ℚ) : GSt 𝓛 ρ
  | relab (G : Matrix ρ ρ ℚ) (new : ρ → 𝓛) : GSt 𝓛 ρ
  | move (r : ρ) (V : 𝓛) (rs : List ℕ) : GSt 𝓛 ρ

namespace GSt

/-- labels after the step. -/
def out (lab : ρ → 𝓛) : GSt 𝓛 ρ → (ρ → 𝓛)
  | .gate _ => lab
  | .relab _ new => new
  | .move r V _ => Function.update lab r V

/-- legality of the step at the labels `lab`. -/
def Ok (K : Calc α) (Φ : 𝓛 → CMat α) (lab : ρ → 𝓛) : GSt 𝓛 ρ → Prop
  | .gate G => ∀ i j, G i j ≠ 0 → Φ (lab i) = Φ (lab j)
  | .relab G new => ∀ i j, G i j ≠ 0 → Φ (new i) = Φ (lab j)
  | .move r V rs => FMv K (Φ (lab r)) (Φ V) rs

/-- scalar map of the step. -/
def act : GSt 𝓛 ρ → (ρ → ℂ) → (ρ → ℂ)
  | .gate G => actPoint G
  | .relab G _ => actPoint G
  | .move _ _ _ => id

/-- ranks of the blocks of the step. -/
def ranks : GSt 𝓛 ρ → List ℕ
  | .gate _ => []
  | .relab _ _ => []
  | .move _ _ rs => rs

/-- **One legal step is an exact route of the engine.** -/
theorem route (K : Calc α) (Φ : 𝓛 → CMat α) (lab : ρ → 𝓛) (s : GSt 𝓛 ρ) (h : s.Ok K Φ lab) :
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
      FMv.step (show FMv K (Φ (lab r)) (Φ V) rs from h) r
    have b := K.on_role (fun r' => Φ (lab r')) r (Φ V) hr
    have e : Function.update (fun r' => Φ (lab r')) r (Φ V)
        = fun r' => Φ (Function.update lab r V r') := by
      funext r'
      by_cases hr' : r' = r
      · subst hr'; simp
      · simp [Function.update_of_ne hr']
    rw [e] at b
    exact b

end GSt

/-- labels after the schedule `l` started at `lab`. -/
def gschedOut : (ρ → 𝓛) → List (GSt 𝓛 ρ) → (ρ → 𝓛)
  | lab, [] => lab
  | lab, s :: l => gschedOut (s.out lab) l

/-- legality of the schedule `l` started at `lab`. -/
def GSchedOk (K : Calc α) (Φ : 𝓛 → CMat α) : (ρ → 𝓛) → List (GSt 𝓛 ρ) → Prop
  | _, [] => True
  | lab, s :: l => s.Ok K Φ lab ∧ GSchedOk K Φ (s.out lab) l

/-- scalar map of a schedule (the head of the list acts first). -/
def gschedAct : List (GSt 𝓛 ρ) → (ρ → ℂ) → (ρ → ℂ)
  | [] => id
  | s :: l => gschedAct l ∘ s.act

/-- block ranks of the schedule, in order. -/
def gschedRanks : List (GSt 𝓛 ρ) → List ℕ
  | [] => []
  | s :: l => s.ranks ++ gschedRanks l

lemma gschedOut_append (lab : ρ → 𝓛) (l l' : List (GSt 𝓛 ρ)) :
    gschedOut lab (l ++ l') = gschedOut (gschedOut lab l) l' := by
  induction l generalizing lab with
  | nil => rfl
  | cons s l ih => exact ih (s.out lab)

lemma gschedOk_append (K : Calc α) (Φ : 𝓛 → CMat α) (lab : ρ → 𝓛) (l l' : List (GSt 𝓛 ρ)) :
    GSchedOk K Φ lab (l ++ l') ↔ GSchedOk K Φ lab l ∧ GSchedOk K Φ (gschedOut lab l) l' := by
  induction l generalizing lab with
  | nil => exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | cons s l ih =>
    show (s.Ok K Φ lab ∧ GSchedOk K Φ (s.out lab) (l ++ l'))
      ↔ (s.Ok K Φ lab ∧ GSchedOk K Φ (s.out lab) l) ∧ GSchedOk K Φ (gschedOut (s.out lab) l) l'
    rw [ih (s.out lab), and_assoc]

lemma gschedAct_append (l l' : List (GSt 𝓛 ρ)) :
    gschedAct (l ++ l') = gschedAct l' ∘ gschedAct l := by
  induction l with
  | nil => rfl
  | cons s l ih => exact congrArg (fun f => f ∘ s.act) ih

lemma gschedRanks_append (l l' : List (GSt 𝓛 ρ)) :
    gschedRanks (l ++ l') = gschedRanks l ++ gschedRanks l' := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    show s.ranks ++ gschedRanks (l ++ l') = (s.ranks ++ gschedRanks l) ++ gschedRanks l'
    rw [ih, List.append_assoc]

/-- **A legal schedule is an exact route of the engine `K`**, for every label system `Φ`:
scalar map `gschedAct l`, one block per paid rank, price `rcost φ (gschedRanks l)`. -/
theorem gsched_route (K : Calc α) (Φ : 𝓛 → CMat α) (l : List (GSt 𝓛 ρ)) (lab : ρ → 𝓛)
    (h : GSchedOk K Φ lab l) :
    K.Route (fun r => Φ (lab r)) (fun r => Φ (gschedOut lab l r)) (gschedAct l)
      (fun φ => rcost φ (gschedRanks l)) := by
  induction l generalizing lab with
  | nil => exact K.route_cast (K.route_refl _) (fun φ => (rcost_nil φ).symm)
  | cons s l ih =>
    have a := GSt.route K Φ lab s h.1
    have b := ih (s.out lab) h.2
    exact K.route_cast (K.route_trans a b) (fun φ => (rcost_append φ _ _).symm)

/-- the same, for the OLD engine, as an `XRoute` (what `Work/Carrier` consumes). -/
theorem gsched_xroute (Φ : 𝓛 → CMat α) (l : List (GSt 𝓛 ρ)) (lab : ρ → 𝓛)
    (h : GSchedOk (xcalc α) Φ lab l) :
    XRoute (fun r => Φ (lab r)) (fun r => Φ (gschedOut lab l r)) (gschedAct l)
      (fun φ => rcost φ (gschedRanks l)) :=
  gsched_route (xcalc α) Φ l lab h

end Sched
end
end PowerSaving.GF
end OAI

#print axioms OAI.PowerSaving.GF.GSt.route
#print axioms OAI.PowerSaving.GF.gsched_route
#print axioms OAI.PowerSaving.GF.gsched_xroute
