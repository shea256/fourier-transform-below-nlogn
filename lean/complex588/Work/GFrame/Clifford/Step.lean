import Work.GFrame.Clifford.Pair
import Work.GFrame.Clifford.AltBlock

/-!
# GFrame / Clifford, part 11: the frame lemma as ENGINE steps (`GStep`)

(agent key: eng-clifford)

* `gstep_rep`          same subspace, another representative: a FREE step;
* `gstep_frame`        nested subspaces `U ⊂ V`, any representatives: ONE block of rank
                       `dim V - dim U` (needs `1 ≤ rank < card α`, as every block does);
* `gstep_old_to_core`, `gstep_core_to_old`   an old frame and its representative: FREE steps;
* `gstep_old_nested`   between the OLD frames of ANY two orthonormal bases whose subspaces are
                       nested: ONE block (the old calculus needed ONE common basis);
* `gstep_frame_down`, `gstep_cross`, `gstep_compl`, `gstep_alt_block`
                       downwards; any two subspaces of one base; complement rule; stage A.
No `sorry`.
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving.GF
open Binary Matrix Finset Complex
noncomputable section
section
variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

theorem gstep_of_free_eq {A M N : CMat α} (l : ρ) (hA : Free A) (h : N = A * M) :
    GStep l M N (fun _ => 0) := by
  rw [h]; exact gstep_free hA l M

/-- **Change of representative is free.** -/
theorem gstep_rep (l : ρ) (G G' : APerm α) (s s' : Finset α)
    (h : ∀ x, InSub G s x ↔ InSub G' s' x) :
    GStep l (core G s) (core G' s') (fun _ => 0) := by
  obtain ⟨N, hN, e⟩ := rep_change G G' s s' h
  exact gstep_of_free_eq l hN e

/-- **One nested step of ANY kind is ONE block of rank `dim V - dim U`.** -/
theorem gstep_frame (l : ρ) (G G' : APerm α) (s t : Finset α)
    (h : ∀ x, InSub G s x → InSub G' t x)
    (h1 : s.card < t.card) (h2 : t.card - s.card < Fintype.card α) :
    GStep l (core G s) (core G' t) (fun φ => φ (t.card - s.card)) := by
  obtain ⟨A, B, z, hA, hB, hz, e⟩ := frame_lemma G G' s t h
  rw [e]
  exact gstep_of_factor l (core G s) z hz hA hB (by omega) h2

theorem gstep_core_to_old (l : ρ) (A : OBase α) (s : Finset α) :
    GStep l (core (coordPerm A) s) (frame A s) (fun _ => 0) := by
  obtain ⟨N, hN, e⟩ := frame_core_free A s
  exact gstep_of_free_eq l hN e

theorem gstep_old_to_core (l : ρ) (A : OBase α) (s : Finset α) :
    GStep l (frame A s) (core (coordPerm A) s) (fun _ => 0) := by
  obtain ⟨N, hN, e⟩ := frame_core_free A s
  obtain ⟨N', hN', hl, -⟩ := free_inv hN
  apply gstep_of_free_eq l hN'
  rw [e, ← Matrix.mul_assoc, hl, Matrix.one_mul]

/-- **Old frames of ANY two orthonormal bases with nested subspaces: ONE block.** -/
theorem gstep_old_nested (l : ρ) (A B : OBase α) (s t : Finset α)
    (h : ∀ x, (∀ k, k ∉ s → dot (A.v k) x = 0) → (∀ k, k ∉ t → dot (B.v k) x = 0))
    (h1 : s.card < t.card) (h2 : t.card - s.card < Fintype.card α) :
    GStep l (frame A s) (frame B t) (fun φ => φ (t.card - s.card)) := by
  have a := gstep_old_to_core l A s
  have b := gstep_frame l (coordPerm A) (coordPerm B) s t h h1 h2
  have c := gstep_core_to_old l B t
  exact ((a.trans b).trans c).cast (fun φ => by simp)

/-- **The nested step downwards is ONE block of rank `dim V - dim U`.** -/
theorem gstep_frame_down (l : ρ) (G G' : APerm α) (s t : Finset α)
    (h : ∀ x, InSub G s x → InSub G' t x)
    (h1 : s.card < t.card) (h2 : t.card - s.card < Fintype.card α) :
    GStep l (core G' t) (core G s) (fun φ => φ (t.card - s.card)) := by
  obtain ⟨A, B, z, hA, hB, hz, e⟩ := frame_lemma_down G G' s t h
  rw [e]
  exact gstep_of_factor l (core G' t) z hz hA hB (by omega) h2

/-- **Any two subspaces named by one base `G₀`** (nested or not): ONE block of rank
`|s₀ Δ t₀| = dim U + dim V - 2 dim (U ∩ V)`. -/
theorem gstep_cross (l : ρ) (G G' G₀ : APerm α) (s t s₀ t₀ : Finset α)
    (h1 : ∀ x, InSub G s x ↔ InSub G₀ s₀ x) (h2 : ∀ x, InSub G₀ t₀ x ↔ InSub G' t x)
    (hr1 : 1 ≤ ((s₀ \ t₀) ∪ (t₀ \ s₀)).card)
    (hr2 : ((s₀ \ t₀) ∪ (t₀ \ s₀)).card < Fintype.card α) :
    GStep l (core G s) (core G' t) (fun φ => φ ((s₀ \ t₀) ∪ (t₀ \ s₀)).card) := by
  obtain ⟨A, B, z, hA, hB, hz, e⟩ := cross_any G G' G₀ s t s₀ t₀ h1 h2
  rw [e]
  exact gstep_of_factor l (core G s) z hz hA hB hr1 hr2

/-- **ANY two subspaces, ANY representatives: ONE block** of rank
`r = dim U + dim V - 2 dim (U ∩ V)` (`2^d` = number of points of `U ∩ V`). -/
theorem gstep_pair (l : ρ) (G G' : APerm α) (s t : Finset α) :
    ∃ d r : ℕ, Fintype.card {x // InSub G s x ∧ InSub G' t x} = 2 ^ d ∧
      r + 2 * d = s.card + t.card ∧
      (1 ≤ r → r < Fintype.card α → GStep l (core G s) (core G' t) (fun φ => φ r)) := by
  obtain ⟨d, r, A, B, z, hd, hr, hA, hB, hz, e⟩ := cross_lemma G G' s t
  refine ⟨d, r, hd, hr, fun h1 h2 => ?_⟩
  rw [e]
  exact gstep_of_factor l (core G s) z hz hA hB h1 h2

/-- the complement rule as free steps. -/
theorem gstep_compl (l : ρ) (G : APerm α) (s : Finset α) :
    GStep l (core G sᶜ) (kernel α * core G s) (fun _ => 0) := by
  obtain ⟨N, hN, e⟩ := kernel_mul_core G s
  exact gstep_of_free_eq l hN e

theorem gstep_compl' (l : ρ) (G : APerm α) (s : Finset α) :
    GStep l (kernel α * core G s) (core G sᶜ) (fun _ => 0) := by
  obtain ⟨N, hN, e⟩ := kernel_mul_core G s
  obtain ⟨N', hN', hl, -⟩ := free_inv hN
  apply gstep_of_free_eq l hN'
  rw [e, ← Matrix.mul_assoc, hl, Matrix.one_mul]

/-- An alternating residual of rank `2p` as ONE block (stage A as an engine step). -/
theorem gstep_alt_block (l : ρ) (M : CMat α) {p : ℕ} (w w' : Fin p → Space α)
    (ind : LinearIndependent F (Sum.elim w w')) (h1 : 1 ≤ p) (h2 : 2 * p < Fintype.card α) :
    GStep l M (wrap (fun x => sign (∑ j, dot (w j) x * dot (w' j) x)) * M)
      (fun φ => φ (2 * p)) := by
  obtain ⟨A, B, z, hA, hB, hz, e⟩ := alt_block w w' ind
  rw [e]
  exact gstep_of_factor l M z hz hA hB (by omega) h2

end
end
end PowerSaving.GF
end OAI

#print axioms OAI.PowerSaving.GF.gstep_rep
#print axioms OAI.PowerSaving.GF.gstep_frame
#print axioms OAI.PowerSaving.GF.gstep_old_nested
#print axioms OAI.PowerSaving.GF.gstep_alt_block
#print axioms OAI.PowerSaving.GF.gstep_frame_down
#print axioms OAI.PowerSaving.GF.gstep_cross
#print axioms OAI.PowerSaving.GF.gstep_pair
#print axioms OAI.PowerSaving.GF.cross_lemma
#print axioms OAI.PowerSaving.GF.gstep_compl'
#print axioms OAI.PowerSaving.GF.kernel_mul_core
#print axioms OAI.PowerSaving.GF.frame_lemma
#print axioms OAI.PowerSaving.GF.rep_change
#print axioms OAI.PowerSaving.GF.core_eq_iff
#print axioms OAI.PowerSaving.GF.frame_core
#print axioms OAI.PowerSaving.GF.alt_block
