import Work.Bridge.Inv

/-!
# (key: carrier-thm) Schedules: the label calculus of a general helper circuit, in whole blocks

The present invocation theorem (`Work.Combine.XInvocation`) is written for a `Circuit` whose bank
roles take part only at the entry and at the scatter.  Here the invocation is a general ORDERED
LIST OF STEPS on an arbitrary role type `ρ` (in the application `ρ = Box T Sl C`: both banks,
the helper slots and the scratch copies, all on the same footing):

* `Step.gate G`        a free gate with rational matrix `G`; legal if every nonzero entry
                       joins two roles with the same projector; labels unchanged;
* `Step.relab G new`   the general free gate (`XRoute.gate`): role `i` leaves with the label
                       `new i`; legal if `G i j ≠ 0 → new i` and `lab j` have the same projector
                       (a ZERO row may take any label: erase; a row `e_j`: copy of role `j`);
* `Step.move r V`      ONE block of the single role `r`: its label goes to `V`, where
                       `Mv (lab r) V` (it stays, or climbs, or descends, inside ONE orthonormal
                       basis); the rank of the block is `mvRank (lab r) V = |V.d - (lab r).d|`.

`SchedOk lab l`, `schedOut lab l`, `schedAct l`, `schedRanks lab l`: legality, final labels, scalar
map and list of block ranks of the list `l` started at the labels `lab` (head of the list first).

`sched_route`: **a legal schedule is an exact block route, for EVERY block frame map `Xm`**, from
the frames of its initial labels to the frames of its final labels, with scalar map `schedAct l`
and price `rcost φ (schedRanks lab l)`.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace CR
open Binary Matrix Finset RAM SS CB BR
noncomputable section

section Sched
variable {H ρ : Type} [Fintype H] [DecidableEq H] [Fintype ρ] [DecidableEq ρ]

/-- one role goes from `U` to `V` with ONE block: it stays, or climbs, or descends, inside ONE
orthonormal basis. -/
def Mv (U V : Lbl H) : Prop := U = V ∨ Climb U V ∨ Climb V U

/-- rank of that block: `|V.d - U.d|`. -/
def mvRank (U V : Lbl H) : ℕ := (V.d - U.d) + (U.d - V.d)

lemma mvRank_self (U : Lbl H) : mvRank U U = 0 := by simp [mvRank]

lemma mvRank_climb {U V : Lbl H} (h : Climb U V) : mvRank U V = V.d - U.d := by
  obtain ⟨A, s, t, hst, hU, hV, hd⟩ := h
  unfold mvRank; omega

lemma mvRank_descend {U V : Lbl H} (h : Climb U V) : mvRank V U = V.d - U.d := by
  obtain ⟨A, s, t, hst, hU, hV, hd⟩ := h
  unfold mvRank; omega

/-- **One block move, for every block frame map.** -/
lemma Mv.reach {α : Type} [Fintype α] [DecidableEq α] (Xm : XMap H α) {U V : Lbl H}
    (h : Mv U V) : XReach (Xm.Φ U.P) (Xm.Φ V.P) (fun φ => bcost φ (mvRank U V)) := by
  rcases h with h | h | h
  · subst h
    exact (XReach.refl _).cast (fun φ => by rw [mvRank_self, bcost_zero])
  · exact (Xm.climb h).cast (fun φ => by rw [mvRank_climb h])
  · exact (Xm.descend h).cast (fun φ => by rw [mvRank_descend h])

/-- One step of a schedule.  See the file header. -/
inductive Step (H ρ : Type) where
  | gate (G : Matrix ρ ρ ℚ) : Step H ρ
  | relab (G : Matrix ρ ρ ℚ) (new : ρ → Lbl H) : Step H ρ
  | move (r : ρ) (V : Lbl H) : Step H ρ

namespace Step

/-- labels after the step. -/
def out (lab : ρ → Lbl H) : Step H ρ → (ρ → Lbl H)
  | .gate _ => lab
  | .relab _ new => new
  | .move r V => Function.update lab r V

/-- legality of the step at the labels `lab`. -/
def Ok (lab : ρ → Lbl H) : Step H ρ → Prop
  | .gate G => ∀ i j, G i j ≠ 0 → (lab i).P = (lab j).P
  | .relab G new => ∀ i j, G i j ≠ 0 → (new i).P = (lab j).P
  | .move r V => Mv (lab r) V

/-- scalar map of the step. -/
def act : Step H ρ → (ρ → ℂ) → (ρ → ℂ)
  | .gate G => actPoint G
  | .relab G _ => actPoint G
  | .move _ _ => id

/-- ranks of the blocks of the step. -/
def ranks (lab : ρ → Lbl H) : Step H ρ → List ℕ
  | .gate _ => []
  | .relab _ _ => []
  | .move r V => [mvRank (lab r) V]

/-- **One legal step is an exact block route, for every block frame map.** -/
theorem route {α : Type} [Fintype α] [DecidableEq α] (Xm : XMap H α) (lab : ρ → Lbl H)
    (s : Step H ρ) (h : s.Ok lab) :
    XRoute (fun r => Xm.Φ (lab r).P) (fun r => Xm.Φ (s.out lab r).P) s.act
      (fun φ => rcost φ (s.ranks lab)) := by
  cases s with
  | gate G =>
    have a := XRoute.gate (α := α) G (fun r => Xm.Φ (lab r).P) (fun r => Xm.Φ (lab r).P)
      (fun i j hij => congrArg Xm.Φ (h i j hij))
    exact a.cast (fun φ => (rcost_nil φ).symm)
  | relab G new =>
    have a := XRoute.gate (α := α) G (fun r => Xm.Φ (lab r).P) (fun r => Xm.Φ (new r).P)
      (fun i j hij => congrArg Xm.Φ (h i j hij))
    exact a.cast (fun φ => (rcost_nil φ).symm)
  | move r V =>
    have hr := Mv.reach Xm (show Mv (lab r) V from h)
    have b := XRoute.on_role (fun r' => Xm.Φ (lab r').P) r (Xm.Φ V.P) (hr ρ r)
    have e : Function.update (fun r' => Xm.Φ (lab r').P) r (Xm.Φ V.P)
        = fun r' => Xm.Φ (Function.update lab r V r').P := by
      funext r'
      by_cases hr' : r' = r
      · subst hr'; simp
      · simp [Function.update_of_ne hr']
    rw [e] at b
    exact b.cast (fun φ => (rcost_single φ _).symm)

end Step

/-- labels after the schedule `l` started at `lab`. -/
def schedOut : (ρ → Lbl H) → List (Step H ρ) → (ρ → Lbl H)
  | lab, [] => lab
  | lab, s :: l => schedOut (s.out lab) l

/-- legality of the schedule `l` started at `lab`. -/
def SchedOk : (ρ → Lbl H) → List (Step H ρ) → Prop
  | _, [] => True
  | lab, s :: l => s.Ok lab ∧ SchedOk (s.out lab) l

/-- scalar map of a schedule (the head of the list acts first). -/
def schedAct : List (Step H ρ) → (ρ → ℂ) → (ρ → ℂ)
  | [] => id
  | s :: l => schedAct l ∘ s.act

/-- block ranks of the schedule `l` started at `lab`, in order. -/
def schedRanks : (ρ → Lbl H) → List (Step H ρ) → List ℕ
  | _, [] => []
  | lab, s :: l => s.ranks lab ++ schedRanks (s.out lab) l

lemma schedOut_append (lab : ρ → Lbl H) (l l' : List (Step H ρ)) :
    schedOut lab (l ++ l') = schedOut (schedOut lab l) l' := by
  induction l generalizing lab with
  | nil => rfl
  | cons s l ih => exact ih (s.out lab)

lemma schedOk_append (lab : ρ → Lbl H) (l l' : List (Step H ρ)) :
    SchedOk lab (l ++ l') ↔ SchedOk lab l ∧ SchedOk (schedOut lab l) l' := by
  induction l generalizing lab with
  | nil => exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | cons s l ih =>
    show (s.Ok lab ∧ SchedOk (s.out lab) (l ++ l'))
      ↔ (s.Ok lab ∧ SchedOk (s.out lab) l) ∧ SchedOk (schedOut (s.out lab) l) l'
    rw [ih (s.out lab), and_assoc]

lemma schedAct_append (l l' : List (Step H ρ)) :
    schedAct (l ++ l') = schedAct l' ∘ schedAct l := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    exact congrArg (fun f => f ∘ s.act) ih

lemma schedRanks_append (lab : ρ → Lbl H) (l l' : List (Step H ρ)) :
    schedRanks lab (l ++ l') = schedRanks lab l ++ schedRanks (schedOut lab l) l' := by
  induction l generalizing lab with
  | nil => rfl
  | cons s l ih =>
    show s.ranks lab ++ schedRanks (s.out lab) (l ++ l')
      = (s.ranks lab ++ schedRanks (s.out lab) l) ++ schedRanks (schedOut (s.out lab) l) l'
    rw [ih, List.append_assoc]

/-- **A legal schedule is an exact block route, for EVERY block frame map**: scalar map
`schedAct l`, one block per move, price `rcost φ (schedRanks lab l)`. -/
theorem sched_route {α : Type} [Fintype α] [DecidableEq α] (Xm : XMap H α)
    (l : List (Step H ρ)) (lab : ρ → Lbl H) (h : SchedOk lab l) :
    XRoute (fun r => Xm.Φ (lab r).P) (fun r => Xm.Φ (schedOut lab l r).P) (schedAct l)
      (fun φ => rcost φ (schedRanks lab l)) := by
  induction l generalizing lab with
  | nil => exact XRoute.refl.cast (fun φ => (rcost_nil φ).symm)
  | cons s l ih =>
    have a := Step.route Xm lab s h.1
    have b := ih (s.out lab) h.2
    exact (a.trans b).cast (fun φ => (rcost_append φ _ _).symm)

end Sched
end
end CR
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.CR.Step.route
#print axioms OAI.PowerSaving.CR.sched_route
