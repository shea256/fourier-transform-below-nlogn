import Work.GFrame.Labels.BXMap
import Work.GFrame.Clifford.Step

/-!
# GFrame labels, part 16 (key: eng-labels): STAGE B moves from INCLUSIONS only

With CLIFFORD's `exists_common_base` (every nested pair of subspaces has an adapted base) the
legality of a stage-B move needs NO base data: only the inclusion of the two subspaces.

* `SMv.of_sub`       `U ⊆ V` (any two representatives, any subspaces: degenerate, isotropic,
                     alternating residual, ...)  ⇒  ONE block of rank `dim V - dim U`;
* `SMv.of_sup`       the same downwards;
* `SMv.of_same`      same subspace, another representative: free;
* `fmv_sub`, `fmv_sup`  the matrix-level statements `FMv (gcalc α) (core G s) (core G' t) [..]`;
* `fmv_old_to_core`, `fmv_core_to_old`   an OLD frame `frame A s` and the representative
                     `core (coordPerm A) s` of the same subspace differ by a free adapter, so
                     stage-A and stage-B labels can be mixed in one schedule (`gsched_groute`
                     takes any label type);
* `BXMap.fmv_sub`    through a stage-B frame map: an inclusion of subspaces of the label space
                     `H` is ONE block on the address space `α`.

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

/-- **Stage B, upwards, from the inclusion alone**: ONE block of rank `dim V - dim U`. -/
theorem SMv.of_sub {m : ℕ} (U V : SLbl α) (h : ∀ x, U.Mem x → V.Mem x)
    (h1 : U.dim < V.dim) (h2 : V.dim - U.dim < m) : SMv m U V [V.dim - U.dim] := by
  obtain ⟨G₀, s₀, t₀, hst, e1, e2⟩ := exists_common_base U.G V.G U.s V.s h
  have r := SMv.nested_rank U V G₀ s₀ t₀ e1 e2 hst
  have g := SMv.nested (m := m) U V G₀ s₀ t₀ e1 e2 hst (by rw [r]; omega) (by rw [r]; exact h2)
  rw [r] at g
  exact g

/-- **Stage B, downwards, from the inclusion alone.** -/
theorem SMv.of_sup {m : ℕ} (U V : SLbl α) (h : ∀ x, U.Mem x → V.Mem x)
    (h1 : U.dim < V.dim) (h2 : V.dim - U.dim < m) : SMv m V U [V.dim - U.dim] := by
  obtain ⟨G₀, s₀, t₀, hst, e1, e2⟩ := exists_common_base U.G V.G U.s V.s h
  have r := SMv.nested_rank U V G₀ s₀ t₀ e1 e2 hst
  have a : SMv m V ⟨G₀, t₀⟩ [] := SMv.rebase (fun x => (e2 x).symm)
  have b : SMv m (⟨G₀, t₀⟩ : SLbl α) ⟨G₀, s₀⟩ [(t₀ \ s₀).card] :=
    SMv.down G₀ hst (by rw [r]; omega) (by rw [r]; exact h2)
  have c : SMv m (⟨G₀, s₀⟩ : SLbl α) U [] := SMv.rebase (fun x => (e1 x).symm)
  have g := (a.trans b).trans c
  rw [r] at g
  simpa using g

/-- same subspace, another representative: a free move. -/
theorem SMv.of_same {m : ℕ} (U V : SLbl α) (h : ∀ x, U.Mem x ↔ V.Mem x) : SMv m U V [] :=
  SMv.rebase h

/-- matrix level: an inclusion of subspaces is ONE block between their representatives. -/
theorem fmv_sub (G G' : APerm α) (s t : Finset α) (h : ∀ x, InSub G s x → InSub G' t x)
    (h1 : s.card < t.card) (h2 : t.card - s.card < Fintype.card α) :
    FMv (gcalc α) (core G s) (core G' t) [t.card - s.card] := by
  have g : SMv (Fintype.card α) (⟨G, s⟩ : SLbl α) ⟨G', t⟩ [t.card - s.card] :=
    SMv.of_sub ⟨G, s⟩ ⟨G', t⟩ h h1 h2
  show FMv (gcalc α) (SLbl.rep ⟨G, s⟩) (SLbl.rep ⟨G', t⟩) [t.card - s.card]
  exact SMv.fmv' g

theorem fmv_sup (G G' : APerm α) (s t : Finset α) (h : ∀ x, InSub G s x → InSub G' t x)
    (h1 : s.card < t.card) (h2 : t.card - s.card < Fintype.card α) :
    FMv (gcalc α) (core G' t) (core G s) [t.card - s.card] := by
  have g : SMv (Fintype.card α) (⟨G', t⟩ : SLbl α) ⟨G, s⟩ [t.card - s.card] :=
    SMv.of_sup ⟨G, s⟩ ⟨G', t⟩ h h1 h2
  show FMv (gcalc α) (SLbl.rep ⟨G', t⟩) (SLbl.rep ⟨G, s⟩) [t.card - s.card]
  exact SMv.fmv' g

/-- an old frame to the representative of its subspace: free. -/
theorem fmv_old_to_core (A : OBase α) (s : Finset α) :
    FMv (gcalc α) (frame A s) (core (coordPerm A) s) [] := by
  obtain ⟨N, hN, e⟩ := frame_core_free A s
  obtain ⟨N', hN', hl, -⟩ := free_inv hN
  refine fmv_of_free hN' ?_
  rw [e, ← Matrix.mul_assoc, hl, Matrix.one_mul]

/-- the representative of a subspace to the old frame: free. -/
theorem fmv_core_to_old (A : OBase α) (s : Finset α) :
    FMv (gcalc α) (core (coordPerm A) s) (frame A s) [] := by
  obtain ⟨N, hN, e⟩ := frame_core_free A s
  exact fmv_of_free hN e

end

section
variable {H α : Type} [Fintype H] [DecidableEq H] [Fintype α] [DecidableEq α]

/-- **Through a stage-B frame map**: an inclusion of subspaces of the label space is ONE block
on the address space, of rank `dim V - dim U`. -/
theorem BXMap.fmv_sub (X : BXMap H α) (U V : SLbl H) (h : ∀ x, U.Mem x → V.Mem x)
    (h1 : U.dim < V.dim) (h2 : V.dim - U.dim < Fintype.card α) :
    FMv (gcalc α) (X.Φ U) (X.Φ V) [V.dim - U.dim] :=
  X.fmv (SMv.of_sub U V h h1 h2)

theorem BXMap.fmv_sup (X : BXMap H α) (U V : SLbl H) (h : ∀ x, U.Mem x → V.Mem x)
    (h1 : U.dim < V.dim) (h2 : V.dim - U.dim < Fintype.card α) :
    FMv (gcalc α) (X.Φ V) (X.Φ U) [V.dim - U.dim] :=
  X.fmv (SMv.of_sup U V h h1 h2)

end
end
end PowerSaving.GF
end OAI

#print axioms OAI.PowerSaving.GF.SMv.of_sub
#print axioms OAI.PowerSaving.GF.SMv.of_sup
#print axioms OAI.PowerSaving.GF.fmv_old_to_core
#print axioms OAI.PowerSaving.GF.BXMap.fmv_sub
