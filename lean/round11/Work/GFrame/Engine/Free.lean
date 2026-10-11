import Work.GFrame.Engine.Letters
import Work.BlockApply.Exact

/-!
# GFrame engine, part 7: free matrices and one-role steps (agent key: eng-ram)

* `Free A`           the matrices one role gets for free: the closure under products of `1`,
                     address permutations `permMat G`, elementary diagonal phases `phaseMat z c`
                     and translations `shift z` (i.e. affine address maps times `i^Q`);
* `GStep.refl/cast/trans/ofX`   the step calculus (as `XStep`; every old step is a step);
* `gstep_free`       left multiplication by a free matrix costs nothing;
* `gstep_block`      ONE block of rank `rk` along ANY `rk` linearly independent directions;
* `gstep_of_factor`  **the frame lemma as an engine step**: a transition that factors as
                     `A * blockMat z * B` with `A`, `B` free is ONE block of rank `rk`.
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving.GF
open Binary Matrix Finset RAM
noncomputable section
section
variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

/-- Matrices that one role gets for free (one linear pass in the RAM, no recursive call). -/
inductive Free : CMat α → Prop
  | one : Free 1
  | perm (G : APerm α) : Free (permMat G)
  | phase (z : Space α) (c : F) : Free (phaseMat z c)
  | shift (z : Space α) : Free (Binary.shift z)
  | mul {A B : CMat α} : Free A → Free B → Free (A * B)

namespace GStep
variable {l : ρ} {M N K : CMat α} {c c' : (ℕ → ℝ) → ℝ}

theorem refl (l : ρ) (M : CMat α) : GStep l M M (fun _ => 0) := by
  refine ⟨[], 1, GWord.proper_nil _, fun _ => rfl, one_mul _, fun f x => ?_⟩
  funext j
  simp [roleAct]

theorem cast (a : GStep l M N c) (h : ∀ φ, c φ = c' φ) : GStep l M N c' := by
  obtain ⟨w, U, hw, hc, hU, hwalk⟩ := a
  exact ⟨w, U, hw, fun φ => (hc φ).trans (h φ), hU, hwalk⟩

theorem trans (a : GStep l M N c) (b : GStep l N K c') :
    GStep l M K (fun φ => c φ + c' φ) := by
  obtain ⟨w, U, hw, hc, hU, hwalk⟩ := a
  obtain ⟨w', V, hw', hc', hV, hwalk'⟩ := b
  refine ⟨w ++ w', V * U, hw.append hw', fun φ => by rw [GWord.costR_append, hc, hc'],
    by rw [mul_assoc, hU, hV], fun f x => ?_⟩
  rw [gwalk_append, hwalk, hwalk', roleAct_mul]

/-- Every old step is a generalised step. -/
theorem ofX (a : XStep l M N c) : GStep l M N c := by
  obtain ⟨w, U, hw, hc, hU, hwalk⟩ := a
  exact ⟨GWord.ofB w, U, GWord.proper_ofB hw, fun φ => by rw [GWord.costR_ofB, hc], hU,
    fun f x => by rw [gwalk_ofB, hwalk]⟩

end GStep

/-- One letter that acts on role `l` by the matrix `U`. -/
lemma gstep_letter (l : ρ) (M U : CMat α) (mv : GMove α ρ) (hp : mv.Proper (Fintype.card α))
    (hact : ∀ (f : ℕ) (x : Data α ρ f), mv.act f x = roleAct f l U x) :
    GStep l M (U * M) (fun φ => mv.costR φ) := by
  refine ⟨[mv], U, ?_, fun φ => ?_, rfl, fun f x => hact f x⟩
  · intro g hg
    rw [List.mem_singleton] at hg
    subst hg; exact hp
  · simp [GWord.costR]

/-- **Free adapters cost nothing.** -/
theorem gstep_free {A : CMat α} (h : Free A) (l : ρ) (M : CMat α) :
    GStep l M (A * M) (fun _ => 0) := by
  induction h generalizing M with
  | one => rw [one_mul]; exact GStep.refl l M
  | perm G => exact gstep_letter l M _ (.perm l G) trivial (fun f x => rfl)
  | phase z c => exact gstep_letter l M _ (.phase l z c) trivial (fun f x => rfl)
  | shift z => exact gstep_letter l M _ (.old (.shift l z)) trivial (fun f x => rfl)
  | mul hA hB ihA ihB =>
    rw [mul_assoc]
    exact ((ihB M).trans (ihA _)).cast (fun φ => by simp)

/-- **One block of rank `rk` along any `rk` linearly independent directions.** -/
theorem gstep_block (l : ρ) (M : CMat α) {rk : ℕ} (z : Fin rk → Space α)
    (ind : LinearIndependent F z) (h1 : 1 ≤ rk) (h2 : rk < Fintype.card α) :
    GStep l M (blockMat z * M) (fun φ => φ rk) :=
  gstep_letter l M _ (.old (.block l rk z ind)) ⟨h1, h2⟩ (fun f x => rfl)

/-- **The frame lemma as an engine step.**  If the transition between two frame matrices
factors as `free * (block of rank rk) * free`, the step is ONE block of rank `rk`. -/
theorem gstep_of_factor (l : ρ) (M : CMat α) {rk : ℕ} (z : Fin rk → Space α)
    (ind : LinearIndependent F z) {A B : CMat α} (hA : Free A) (hB : Free B)
    (h1 : 1 ≤ rk) (h2 : rk < Fintype.card α) :
    GStep l M (A * blockMat z * B * M) (fun φ => φ rk) := by
  have h := ((gstep_free hB l M).trans (gstep_block l (B * M) z ind h1 h2)).trans
    (gstep_free hA l (blockMat z * (B * M)))
  have e : A * (blockMat z * (B * M)) = A * blockMat z * B * M := by
    simp only [mul_assoc]
  rw [e] at h
  exact h.cast (fun φ => by simp)

/-- The same with the block given as the kernel on the block coordinates of a splitting whose
block directions are `z`. -/
theorem gstep_of_split (l : ρ) (M : CMat α) {β : Type*} [Fintype β] [DecidableEq β] {rk : ℕ}
    (S : Split α β (Fin rk)) (z : Fin rk → Space α) (hz : ∀ i, S.e.symm (0, eu i) = z i)
    (ind : LinearIndependent F z) {A B : CMat α} (hA : Free A) (hB : Free B)
    (h1 : 1 ≤ rk) (h2 : rk < Fintype.card α) :
    GStep l M (A * S.lift (kernel (Fin rk)) * B * M) (fun φ => φ rk) := by
  rw [← blockMat_eq_lift S z hz]
  exact gstep_of_factor l M z ind hA hB h1 h2

end
end
end PowerSaving.GF
end OAI

#print axioms OAI.PowerSaving.GF.gstep_free
#print axioms OAI.PowerSaving.GF.gstep_block
#print axioms OAI.PowerSaving.GF.gstep_of_factor
#print axioms OAI.PowerSaving.GF.gstep_of_split
