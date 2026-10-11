import Work.GFrame.Clifford.Fibre
import Work.GFrame.Clifford.FreeLift

/-!
# GFrame / Clifford, part 3 (STAGE A): an alternating residual of rank `2p` is ONE block

(agent key: eng-clifford)

* `alt_block_split`  for a splitting `S` whose block directions are the symplectic basis:
                     `wrap (∏_j (-1)^((w_j·x)(w'_j·x))) = A * S.lift (kernel γ) * B`, `A`, `B` free;
* `alt_block`        the form the label layer consumes: for `w w' : Fin p → Space α` with
                     `Sum.elim w w'` linearly independent,
                     `wrap (x ↦ (-1)^(∑_j (w_j·x)(w'_j·x))) = A * blockMat z * B`
                     with `z : Fin (2p) → Space α` linearly independent, `A`, `B` free.
No `sorry`.
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving.GF
open Binary Matrix Finset Complex
noncomputable section
section
variable {α β γ ι : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ] [Fintype ι] [DecidableEq ι]

/-- an alternating plane is three unit moves and a shift (all Walsh-diagonal). -/
lemma cz_three (w w' : Space α) :
    wrap (fun x => sign (dot w x * dot w' x))
      = shift (w + w') * (dir w * dir w' * dir (w + w')) := by
  rw [shift_phase, dir_phase w, dir_phase w', dir_phase (w + w'), wrap_mul, wrap_mul, wrap_mul]
  apply congrArg wrap
  funext x
  rw [dot_add_left, sign_mul_bits]
  ring

/-- the plane of two fibre coordinates, lifted. -/
lemma lift_cz (S : Split α β γ) (c c' : γ) :
    S.lift (wrap fun y : Space γ => sign (y c * y c'))
      = wrap (fun x => sign (dot (S.e.symm (0, eu c)) x * dot (S.e.symm (0, eu c')) x)) := by
  have h := cz_three (eu c) (eu c')
  simp only [dot_eu_left] at h
  have h01 : S.e.symm (0, eu c + eu c') = S.e.symm (0, eu c) + S.e.symm (0, eu c') := by
    rw [← S.symm_add, Prod.mk_add_mk, add_zero]
  rw [h, cz_three, S.lift_mul, S.lift_mul, S.lift_mul, S.lift_shift, S.lift_dir, S.lift_dir,
    S.lift_dir, h01]

lemma lift_alt (S : Split α β γ) (e : ι ⊕ ι ≃ γ) (A : Finset ι) :
    S.lift (wrap fun y : Space γ => ∏ j ∈ A, sign (y (e (.inl j)) * y (e (.inr j))))
      = wrap (fun x => ∏ j ∈ A, sign (dot (S.e.symm (0, eu (e (.inl j)))) x
          * dot (S.e.symm (0, eu (e (.inr j)))) x)) := by
  induction A using Finset.induction_on with
  | empty => simp [wrap_one, S.lift_one]
  | insert j A hj ih =>
    simp only [Finset.prod_insert hj]
    have e1 := wrap_mul (fun y : Space γ => sign (y (e (.inl j)) * y (e (.inr j))))
      (fun y => ∏ k ∈ A, sign (y (e (.inl k)) * y (e (.inr k))))
    rw [← e1, S.lift_mul, ih, lift_cz, wrap_mul]

lemma free_pairPhase (e : ι ⊕ ι ≃ γ) : Free (diagonal (pairPhase e)) := by
  have h : pairPhase e = fun y => ∏ j ∈ univ, tint (dot (pairDir e j) y + 0) := by
    funext y
    simp [pairPhase, dot_pairDir]
  rw [h]
  exact free_diag_prod univ _ (fun j _ => free_diag_tint _ _)

/-- **STAGE A, splitting form.**  The transition of an alternating residual whose symplectic
basis is the family of block directions of `S` (paired by `e`) is ONE kernel of order `|γ|` on
the block coordinates, between free adapters. -/
theorem alt_block_split (S : Split α β γ) (e : ι ⊕ ι ≃ γ) :
    ∃ A B : CMat α, Free A ∧ Free B ∧
      wrap (fun x => ∏ j : ι, sign (dot (S.e.symm (0, eu (e (.inl j)))) x
          * dot (S.e.symm (0, eu (e (.inr j)))) x))
        = A * S.lift (kernel γ) * B := by
  refine ⟨S.lift (diagonal fun y => (-I) ^ Fintype.card ι * pairPhase e y),
    S.lift (permMat (pairSwap e) * diagonal (pairPhase e)), free_lift S ?_, free_lift S ?_, ?_⟩
  · exact free_diag_mul (free_diag_negI _) (free_pairPhase e)
  · exact Free.mul (Free.perm _) (free_pairPhase e)
  · rw [← lift_alt S e univ, alt_fibre e, S.lift_mul, S.lift_mul]

/-- **STAGE A, the form the label layer consumes.** -/
theorem alt_block {p : ℕ} (w w' : Fin p → Space α)
    (ind : LinearIndependent F (Sum.elim w w')) :
    ∃ (A B : CMat α) (z : Fin (2 * p) → Space α), Free A ∧ Free B ∧ LinearIndependent F z ∧
      wrap (fun x => sign (∑ j, dot (w j) x * dot (w' j) x)) = A * blockMat z * B := by
  let e : Fin p ⊕ Fin p ≃ Fin (2 * p) := finSumFinEquiv.trans (finCongr (two_mul p).symm)
  let z : Fin (2 * p) → Space α := Sum.elim w w' ∘ e.symm
  have indz : LinearIndependent F z := ind.comp e.symm e.symm.injective
  obtain ⟨S, hS⟩ := exists_split z indz
  obtain ⟨A, B, hA, hB, h⟩ := alt_block_split S e
  refine ⟨A, B, z, hA, hB, indz, ?_⟩
  rw [blockMat_eq_lift S z hS, ← h]
  congr 1
  funext x
  rw [sign_sum]
  apply Finset.prod_congr rfl
  intro j _
  rw [hS, hS]
  simp [z]

/-- the block directions of `alt_block`, explicitly: `w` then `w'`. -/
theorem alt_block_dirs {p : ℕ} (w w' : Fin p → Space α)
    (ind : LinearIndependent F (Sum.elim w w')) :
    ∃ (A B : CMat α), Free A ∧ Free B ∧
      wrap (fun x => sign (∑ j, dot (w j) x * dot (w' j) x))
        = A * blockMat (Sum.elim w w' ∘
            (finSumFinEquiv.trans (finCongr (two_mul p).symm)).symm) * B := by
  let e : Fin p ⊕ Fin p ≃ Fin (2 * p) := finSumFinEquiv.trans (finCongr (two_mul p).symm)
  have indz : LinearIndependent F (Sum.elim w w' ∘ e.symm) := ind.comp e.symm e.symm.injective
  obtain ⟨S, hS⟩ := exists_split _ indz
  obtain ⟨A, B, hA, hB, h⟩ := alt_block_split S e
  refine ⟨A, B, hA, hB, ?_⟩
  rw [blockMat_eq_lift S _ hS, ← h]
  congr 1
  funext x
  rw [sign_sum]
  apply Finset.prod_congr rfl
  intro j _
  rw [hS, hS]
  simp

end
end
end PowerSaving.GF
end OAI

#print axioms OAI.PowerSaving.GF.alt_block_split
#print axioms OAI.PowerSaving.GF.alt_block
#print axioms OAI.PowerSaving.GF.alt_block_dirs
