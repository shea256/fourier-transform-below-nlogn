import Work.GFrame.Labels.GCalc
import Work.GFrame.Clifford.Core

/-!
# GFrame labels, part 9 (key: eng-labels): STAGE B, labels that are ARBITRARY subspaces

A stage-B label is a subspace of the label space WITH ITS EXACT REPRESENTATIVE: a base `G` (an
additive bijection: coordinates in a basis) and a set `s` of coordinates; the subspace is
`InSub G s` (degenerate and isotropic subspaces included) and the frame matrix of a role
carrying the label is CLIFFORD's `core G s` (the outside `T_U = K_G T_{E_r} K_G⁻¹`; NOT
Walsh-diagonal in general).

* `SLbl α`, `SLbl.rep`, `SLbl.Mem`, `SLbl.dim`;
* `core_down`     the nested step downwards in one base: again ONE block between free adapters;
* `SMv U V rs`    one move: `stay`; `up` / `down` in ONE base (one block of rank `|t \ s|`);
                  `rebase` (same subspace, another representative: a FREE left adapter);
                  `trans` (so: any nested pair with any representatives = rebase, up, rebase);
* `RepChange α`   the hypothesis that two representatives of the same subspace differ by a free
                  left adapter (CLIFFORD's `rep_change`; only `rebase` uses it);
* `SMv.fmv`       every move is a one-role move of the generalised engine;
* GATE RULE: `BOk` asks `(lab i).rep = (lab j).rep` (IDENTICAL matrices; `lab i = lab j`
                  suffices).  Equal subspaces are NOT enough: insert a `rebase` move first;
* `bsched_groute` **stage B route theorem**: a legal schedule is a `GRoute`, one block per
                  nested step, nothing for adapters and gates.

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

/-- **Stage B label**: the subspace `InSub G s` with its exact representative `core G s`. -/
structure SLbl (α : Type) where
  G : APerm α
  s : Finset α

namespace SLbl
/-- exact frame matrix of the label. -/
def rep (U : SLbl α) : CMat α := core U.G U.s
/-- the subspace named by the label. -/
def Mem (U : SLbl α) (x : Space α) : Prop := InSub U.G U.s x
/-- its dimension. -/
def dim (U : SLbl α) : ℕ := U.s.card
end SLbl

/-- the sum of the unit vectors of `d`. -/
def indv (d : Finset α) : Space α := ∑ k ∈ d, eu k

lemma pk_sq (d : Finset α) : pk d * pk d = shift (indv d) := by
  rw [pk, wrap_mul, shift_phase]
  congr 1
  funext x
  rw [← Finset.prod_mul_distrib]
  simp_rw [tint_sq]
  rw [← sign_sum]
  congr 1
  rw [indv, dot_sum_left]
  simp

/-- **Nested step DOWN in one base**: ONE block of rank `|t \ s|` between free adapters. -/
theorem core_down (G : APerm α) {s t : Finset α} (h : s ⊆ t) :
    core G s = (kg G * shift (indv (t \ s))) * blockMat ((OBase.canonical α).fam (t \ s))
      * kg (apInv G) * core G t := by
  rw [core_nested G h, ← pk_eq_blockMat]
  have e : kg G * shift (indv (t \ s)) * pk (t \ s) * kg (apInv G)
        * (kg G * pk (t \ s) * kg (apInv G) * core G s)
      = kg G * (shift (indv (t \ s)) * (pk (t \ s) * ((kg (apInv G) * kg G) * pk (t \ s))))
        * kg (apInv G) * core G s := by
    simp only [Matrix.mul_assoc]
  rw [e, kg_inv_mul, Matrix.one_mul, pk_sq, shift_sq, Matrix.mul_one, kg_mul_inv,
    Matrix.one_mul]

/-- Two representatives of the same subspace differ by a free left adapter. -/
def RepChange (α : Type) [Fintype α] [DecidableEq α] : Prop :=
  ∀ (G G' : APerm α) (s s' : Finset α), (∀ x, InSub G s x ↔ InSub G' s' x) →
    ∃ N : CMat α, GF.Free N ∧ core G' s' = N * core G s

/-- one move of one role (stage B), with the block ranks it pays; `m` bounds the rank of a
block (`m` = number of coordinates of the ADDRESS space the role lives in). -/
inductive SMv (m : ℕ) : SLbl α → SLbl α → List ℕ → Prop
  | stay (U : SLbl α) : SMv m U U []
  | up (G : APerm α) {s t : Finset α} : s ⊆ t → 1 ≤ (t \ s).card →
      (t \ s).card < m → SMv m ⟨G, s⟩ ⟨G, t⟩ [(t \ s).card]
  | down (G : APerm α) {s t : Finset α} : s ⊆ t → 1 ≤ (t \ s).card →
      (t \ s).card < m → SMv m ⟨G, t⟩ ⟨G, s⟩ [(t \ s).card]
  | rebase {U V : SLbl α} : (∀ x, U.Mem x ↔ V.Mem x) → SMv m U V []
  | trans {U V W : SLbl α} {a b : List ℕ} : SMv m U V a → SMv m V W b → SMv m U W (a ++ b)

theorem fmv_core_up (G : APerm α) {s t : Finset α} (h : s ⊆ t) (h1 : 1 ≤ (t \ s).card)
    (h2 : (t \ s).card < Fintype.card α) :
    FMv (gcalc α) (core G s) (core G t) [(t \ s).card] :=
  fmv_of_factor _ ((OBase.canonical α).fam_indep _) h1 h2 (free_kg G) (free_kg _)
    (core_nested G h)

theorem fmv_core_down (G : APerm α) {s t : Finset α} (h : s ⊆ t) (h1 : 1 ≤ (t \ s).card)
    (h2 : (t \ s).card < Fintype.card α) :
    FMv (gcalc α) (core G t) (core G s) [(t \ s).card] :=
  fmv_of_factor _ ((OBase.canonical α).fam_indep _) h1 h2
    (GF.Free.mul (free_kg G) (GF.Free.shift _)) (free_kg _) (core_down G h)

/-- **Every stage-B move is a one-role move of the generalised engine.** -/
theorem SMv.fmv (hR : RepChange α) {U V : SLbl α} {rs : List ℕ}
    (h : SMv (Fintype.card α) U V rs) :
    FMv (gcalc α) U.rep V.rep rs := by
  induction h with
  | stay U => exact FMv.refl _ _
  | up G h h1 h2 => exact fmv_core_up G h h1 h2
  | down G h h1 h2 => exact fmv_core_down G h h1 h2
  | rebase h =>
    obtain ⟨N, hN, e⟩ := hR _ _ _ _ h
    exact fmv_of_free hN e
  | trans _ _ iha ihb => exact FMv.trans iha ihb

variable {ρ : Type} [Fintype ρ] [DecidableEq ρ]

/-- label-level legality of one step (stage B).  GATE RULE: identical representatives. -/
def BOk (lab : ρ → SLbl α) : GSt (SLbl α) ρ → Prop
  | .gate G => ∀ i j, G i j ≠ 0 → (lab i).rep = (lab j).rep
  | .relab G new => ∀ i j, G i j ≠ 0 → (new i).rep = (lab j).rep
  | .move r V rs => SMv (Fintype.card α) (lab r) V rs

/-- label-level legality of a schedule (stage B). -/
def BSchedOk : (ρ → SLbl α) → List (GSt (SLbl α) ρ) → Prop
  | _, [] => True
  | lab, s :: l => BOk lab s ∧ BSchedOk (s.out lab) l

theorem bsched_ok (hR : RepChange α) (lab : ρ → SLbl α) (l : List (GSt (SLbl α) ρ))
    (h : BSchedOk lab l) : GSchedOk (gcalc α) SLbl.rep lab l := by
  induction l generalizing lab with
  | nil => trivial
  | cons s l ih =>
    refine ⟨?_, ih _ h.2⟩
    have h1 := h.1
    cases s with
    | gate G => exact h1
    | relab G new => exact h1
    | move r V rs => exact SMv.fmv hR h1

/-- **Stage B route theorem.**  A legal schedule on subspace labels (arbitrary subspaces,
exact representatives, gates only between identical representatives, free adapters for a change
of representative) is an exact route of the generalised engine: one block per nested step. -/
theorem bsched_groute (hR : RepChange α) (l : List (GSt (SLbl α) ρ)) (lab : ρ → SLbl α)
    (h : BSchedOk lab l) :
    GRoute (fun r => (lab r).rep) (fun r => (gschedOut lab l r).rep) (gschedAct l)
      (fun φ => rcost φ (gschedRanks l)) :=
  gsched_groute (SLbl.rep (α := α)) l lab (bsched_ok hR lab l h)

/-- endpoints: the empty subspace is the identity frame, the full space in the standard base
is the kernel. -/
theorem SLbl.rep_empty (G : APerm α) : (SLbl.mk G ∅).rep = 1 := core_empty G
theorem SLbl.rep_full : (SLbl.mk (apId α) univ).rep = kernel α := core_id_univ

end
end
end PowerSaving.GF
end OAI

#print axioms OAI.PowerSaving.GF.core_down
#print axioms OAI.PowerSaving.GF.SMv.fmv
#print axioms OAI.PowerSaving.GF.bsched_groute
