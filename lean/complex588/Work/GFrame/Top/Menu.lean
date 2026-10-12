import Work.GFrame.Top.Assemble
import Work.GFrame.Clifford.Step

/-!
# GFrame, top (key: eng-integrate): the menu of legal one-role moves

Every entry is a `Reach (gcalc α) M N (fun φ => rcost φ rs)`: exactly what the `move r V rs`
step of a schedule (`GSt.OkR`, `Labels/SchedR.lean`) asks for.  `rs = [r]`: ONE block of rank
`r` (one family of recursive calls); `rs = []`: a free adapter (linear work, no call).

* `reach_block`, `reach_free`, `reach_factor`     the engine letters and the frame-lemma shape;
* `reach_nested`, `reach_nested_down`             nested subspaces, ANY representatives
                                                  (degenerate, isotropic included): one block of
                                                  rank `dim V - dim U`;
* `reach_rep`                                     same subspace, other representative: free;
* `reach_pair`                                    ANY two subspaces: one block of rank
                                                  `dim U + dim V - 2 dim (U ∩ V)`;
* `reach_compl`, `reach_compl'`                   the complement rule: free;
* `reach_old_nested`, `reach_old_to_core`, `reach_core_to_old`   old orthonormal frames;
* `reach_alt`                                     alternating residual of rank `2p`: one block;
* `Reach.trans`                                   moves compose, ranks concatenate.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.GF
open Binary Matrix Finset RAM CB SS
noncomputable section
section
variable {α : Type} [Fintype α] [DecidableEq α]

/-- a step of the generalised engine paying one block of rank `r ≥ 1` on every role type. -/
theorem reach_rank {M N : CMat α} {r : ℕ} (hr : 1 ≤ r)
    (h : ∀ (ρ : Type) [Fintype ρ] [DecidableEq ρ] (l : ρ), GStep l M N (fun φ => φ r)) :
    Reach (gcalc α) M N (fun φ => rcost φ [r]) :=
  fun ρ _ _ l => (h ρ l).cast (fun φ => by rw [rcost_single, bcost_pos φ (by omega)])

/-- a free step of the generalised engine on every role type. -/
theorem reach_zero {M N : CMat α}
    (h : ∀ (ρ : Type) [Fintype ρ] [DecidableEq ρ] (l : ρ), GStep l M N (fun _ => 0)) :
    Reach (gcalc α) M N (fun φ => rcost φ []) :=
  fun ρ _ _ l => (h ρ l).cast (fun φ => (rcost_nil φ).symm)

/-- moves compose; the paid ranks concatenate. -/
theorem Reach.trans {K : Calc α} {M N L : CMat α} {a b : List ℕ}
    (h1 : Reach K M N (fun φ => rcost φ a)) (h2 : Reach K N L (fun φ => rcost φ b)) :
    Reach K M L (fun φ => rcost φ (a ++ b)) :=
  fun ρ _ _ l => K.step_cast (K.step_trans (h1 ρ l) (h2 ρ l))
    (fun φ => (rcost_append φ a b).symm)

/-- ONE block along any `r` linearly independent directions. -/
theorem reach_block (M : CMat α) {r : ℕ} (z : Fin r → Space α) (ind : LinearIndependent F z)
    (h1 : 1 ≤ r) (h2 : r < Fintype.card α) :
    Reach (gcalc α) M (blockMat z * M) (fun φ => rcost φ [r]) :=
  reach_rank h1 (fun ρ _ _ l => gstep_block l M z ind h1 h2)

/-- a free adapter. -/
theorem reach_free (M : CMat α) {A : CMat α} (hA : GF.Free A) :
    Reach (gcalc α) M (A * M) (fun φ => rcost φ []) :=
  reach_zero (fun ρ _ _ l => gstep_free hA l M)

/-- **The frame-lemma shape**: `free * block * free` is ONE block. -/
theorem reach_factor (M : CMat α) {A B : CMat α} {r : ℕ} (z : Fin r → Space α)
    (ind : LinearIndependent F z) (hA : GF.Free A) (hB : GF.Free B)
    (h1 : 1 ≤ r) (h2 : r < Fintype.card α) :
    Reach (gcalc α) M (A * blockMat z * B * M) (fun φ => rcost φ [r]) :=
  reach_rank h1 (fun ρ _ _ l => gstep_of_factor l M z ind hA hB h1 h2)

/-- **Nested subspaces, any representatives: ONE block of rank `dim V - dim U`.** -/
theorem reach_nested (G G' : APerm α) (s t : Finset α) (h : ∀ x, InSub G s x → InSub G' t x)
    (h1 : s.card < t.card) (h2 : t.card - s.card < Fintype.card α) :
    Reach (gcalc α) (core G s) (core G' t) (fun φ => rcost φ [t.card - s.card]) :=
  reach_rank (by omega) (fun ρ _ _ l => gstep_frame l G G' s t h h1 h2)

/-- the same downwards. -/
theorem reach_nested_down (G G' : APerm α) (s t : Finset α)
    (h : ∀ x, InSub G s x → InSub G' t x)
    (h1 : s.card < t.card) (h2 : t.card - s.card < Fintype.card α) :
    Reach (gcalc α) (core G' t) (core G s) (fun φ => rcost φ [t.card - s.card]) :=
  reach_rank (by omega) (fun ρ _ _ l => gstep_frame_down l G G' s t h h1 h2)

/-- same subspace, another representative: free. -/
theorem reach_rep (G G' : APerm α) (s s' : Finset α) (h : ∀ x, InSub G s x ↔ InSub G' s' x) :
    Reach (gcalc α) (core G s) (core G' s') (fun φ => rcost φ []) :=
  reach_zero (fun ρ _ _ l => gstep_rep l G G' s s' h)

/-- **ANY two subspaces, ANY representatives: ONE block** of rank
`r = dim U + dim V - 2 dim (U ∩ V)` (`2^d` = number of points of `U ∩ V`). -/
theorem reach_pair (G G' : APerm α) (s t : Finset α) :
    ∃ d r : ℕ, Fintype.card {x // InSub G s x ∧ InSub G' t x} = 2 ^ d ∧
      r + 2 * d = s.card + t.card ∧
      (1 ≤ r → r < Fintype.card α →
        Reach (gcalc α) (core G s) (core G' t) (fun φ => rcost φ [r])) := by
  obtain ⟨d, r, A, B, z, hd, hr, hA, hB, hz, e⟩ := cross_lemma G G' s t
  refine ⟨d, r, hd, hr, fun h1 h2 => ?_⟩
  rw [e]
  exact reach_factor (core G s) z hz hA hB h1 h2

/-- the complement rule (`kernel * T_U` is the frame of the complementary coordinates). -/
theorem reach_compl (G : APerm α) (s : Finset α) :
    Reach (gcalc α) (core G sᶜ) (kernel α * core G s) (fun φ => rcost φ []) :=
  reach_zero (fun ρ _ _ l => gstep_compl l G s)

theorem reach_compl' (G : APerm α) (s : Finset α) :
    Reach (gcalc α) (kernel α * core G s) (core G sᶜ) (fun φ => rcost φ []) :=
  reach_zero (fun ρ _ _ l => gstep_compl' l G s)

/-- old frames of any two orthonormal bases with nested subspaces: ONE block. -/
theorem reach_old_nested (A B : OBase α) (s t : Finset α)
    (h : ∀ x, (∀ k, k ∉ s → dot (A.v k) x = 0) → (∀ k, k ∉ t → dot (B.v k) x = 0))
    (h1 : s.card < t.card) (h2 : t.card - s.card < Fintype.card α) :
    Reach (gcalc α) (frame A s) (frame B t) (fun φ => rcost φ [t.card - s.card]) :=
  reach_rank (by omega) (fun ρ _ _ l => gstep_old_nested l A B s t h h1 h2)

theorem reach_old_to_core (A : OBase α) (s : Finset α) :
    Reach (gcalc α) (frame A s) (core (coordPerm A) s) (fun φ => rcost φ []) :=
  reach_zero (fun ρ _ _ l => gstep_old_to_core l A s)

theorem reach_core_to_old (A : OBase α) (s : Finset α) :
    Reach (gcalc α) (core (coordPerm A) s) (frame A s) (fun φ => rcost φ []) :=
  reach_zero (fun ρ _ _ l => gstep_core_to_old l A s)

/-- **Alternating residual of rank `2p`: ONE block** (stage A, on any role matrix). -/
theorem reach_alt (M : CMat α) {p : ℕ} (w w' : Fin p → Space α)
    (ind : LinearIndependent F (Sum.elim w w')) (h1 : 1 ≤ p) (h2 : 2 * p < Fintype.card α) :
    Reach (gcalc α) M (wrap (fun x => sign (∑ j, dot (w j) x * dot (w' j) x)) * M)
      (fun φ => rcost φ [2 * p]) :=
  reach_rank (by omega) (fun ρ _ _ l => gstep_alt_block l M w w' ind h1 h2)

end
end
end PowerSaving.GF
end OAI

#print axioms OAI.PowerSaving.GF.Reach.trans
#print axioms OAI.PowerSaving.GF.reach_factor
#print axioms OAI.PowerSaving.GF.reach_nested
#print axioms OAI.PowerSaving.GF.reach_nested_down
#print axioms OAI.PowerSaving.GF.reach_rep
#print axioms OAI.PowerSaving.GF.reach_pair
#print axioms OAI.PowerSaving.GF.reach_compl
#print axioms OAI.PowerSaving.GF.reach_old_nested
#print axioms OAI.PowerSaving.GF.reach_alt
