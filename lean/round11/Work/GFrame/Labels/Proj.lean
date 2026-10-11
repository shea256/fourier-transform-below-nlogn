import Work.GFrame.Labels.Embed

/-!
# GFrame labels, part 13 (key: eng-labels): what a certificate checker calls (stage A)

The checker (`Work/SharedSumChecker/Proj.lean`) keeps, for every role, a label matrix `P`
(`pmat`) that is the sum of the forms of the blocks the role has made, and proves `Climb`
between an earlier and a later label from a COMPLETE history.  The generalised statements:

* `IsProj P`             `Pᵀ = P ∧ P * P = P`; then `gram P = P` (`IsProj.gram_eq`);
* `gclimbO_of_proj`      labels projectors, `V.P = U.P + ∑ z_i z_iᵀ`, `z` independent
                         ⇒ `GClimbO U V r`;
* `gclimbA_of_proj`      the same with `V.P = U.P + ∑ (w_j w'_jᵀ + w'_j w_jᵀ)` ⇒ `GClimbA U V p`;
* `gclimbO_of_list`      the block given as a LIST of directions (the checker's `psum`);
* `complete_gram`        COMPLETE HISTORY: if the directions of all moves of a role (columns
                         of `M`) with their block form `N` (a symmetric involution: identity on
                         orthonormal-type blocks, hyperbolic planes on alternating blocks) reach
                         the full projector, `M N Mᵀ = 1`, and there are as many directions as
                         coordinates, then `Mᵀ M = N`: the Gram matrix of the directions is the
                         block form itself;
* `complete_indep`       and the directions are linearly independent (no rank computation);
* `complete_proj`        hence EVERY partial sum `M D N D Mᵀ` over a set of whole blocks (`D`
                         a diagonal 0/1 matrix commuting with `N`) is a projector.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.GF
open Binary Matrix Finset RAM CB SS
noncomputable section

section
variable {H : Type} [Fintype H] [DecidableEq H]

/-- a symmetric idempotent matrix over `F_2`: the orthogonal projector of a nondegenerate
subspace. -/
def IsProj (P : Matrix H H F) : Prop := Pᵀ = P ∧ P * P = P

lemma IsProj.gram_eq {P : Matrix H H F} (h : IsProj P) : gram P = P := by
  show Pᵀ * P = P
  rw [h.1, h.2]

lemma mat_symm (A : OBase H) (s : Finset H) : (A.mat s)ᵀ = A.mat s := by
  ext i j
  simp only [Matrix.transpose_apply, OBase.mat]
  apply Finset.sum_congr rfl; intro k _; ring

lemma isProj_mat (A : OBase H) (s : Finset H) : IsProj (A.mat s) := by
  refine ⟨mat_symm A s, ?_⟩
  have h := gram_mat A s
  rwa [gram, mat_symm] at h

/-- orthonormal-type block between two projector labels. -/
theorem gclimbO_of_proj {U V : Lbl H} (hU : IsProj U.P) (hV : IsProj V.P) {r : ℕ}
    (z : Fin r → Space H) (ind : LinearIndependent F z) (h : V.P = U.P + ∑ i, tt (z i))
    (hd : V.d = U.d + r) : GClimbO U V r :=
  ⟨z, ind, by rw [hU.gram_eq, hV.gram_eq]; exact h, hd⟩

/-- alternating block between two projector labels. -/
theorem gclimbA_of_proj {U V : Lbl H} (hU : IsProj U.P) (hV : IsProj V.P) {p : ℕ}
    (w w' : Fin p → Space H) (ind : LinearIndependent F (Sum.elim w w')) (hp : 1 ≤ p)
    (h : V.P = U.P + ∑ j, (vv (w j) (w' j) + vv (w' j) (w j)))
    (hd : V.d = U.d + 2 * p) : GClimbA U V p :=
  ⟨w, w', ind, hp, by rw [hU.gram_eq, hV.gram_eq]; exact h, hd⟩

/-- the block given as a list of directions (the checker's `psum`). -/
theorem gclimbO_of_list {U V : Lbl H} (hU : IsProj U.P) (hV : IsProj V.P)
    (l : List (Space H)) (ind : LinearIndependent F (fun i : Fin l.length => l[i]))
    (h : V.P = U.P + (l.map tt).sum) (hd : V.d = U.d + l.length) : GClimbO U V l.length :=
  gclimbO_of_proj hU hV (fun i : Fin l.length => l[i]) ind
    (by rw [h]; congr 1; exact (Fin.sum_univ_fun_getElem l tt).symm) hd

/-- **Complete history.**  `M N Mᵀ = 1` with as many directions as coordinates and `N` an
involution gives `Mᵀ M = N`. -/
theorem complete_gram {ι : Type} [Fintype ι] [DecidableEq ι] (e : H ≃ ι) (M : Matrix H ι F)
    (N : Matrix ι ι F) (hN : N * N = 1) (h : M * N * Mᵀ = 1) : Mᵀ * M = N := by
  have h1 : M * (N * Mᵀ) = 1 := by rw [← Matrix.mul_assoc]; exact h
  have h2 : (N * Mᵀ) * M = 1 := (Matrix.mul_eq_one_comm_of_equiv e).mp h1
  calc Mᵀ * M = (N * N) * (Mᵀ * M) := by rw [hN, Matrix.one_mul]
    _ = N * ((N * Mᵀ) * M) := by simp only [Matrix.mul_assoc]
    _ = N := by rw [h2, Matrix.mul_one]

/-- **The directions of a complete history are linearly independent** (so is every block of
them: `LinearIndependent.comp`).  No rank computation is needed in the checker. -/
theorem complete_indep {ι : Type} [Fintype ι] [DecidableEq ι] (e : H ≃ ι) (M : Matrix H ι F)
    (N : Matrix ι ι F) (hN : N * N = 1) (h : M * N * Mᵀ = 1) :
    LinearIndependent F (fun j : ι => (fun i => M i j : Space H)) := by
  have h1 : M * (N * Mᵀ) = 1 := by rw [← Matrix.mul_assoc]; exact h
  have h2 : (N * Mᵀ) * M = 1 := (Matrix.mul_eq_one_comm_of_equiv e).mp h1
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have e1 : M *ᵥ g = 0 := by
    rw [← hg]; funext i
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl; intro k _; ring
  have e2 : g = (N * Mᵀ) *ᵥ (M *ᵥ g) := by
    rw [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  rw [e2, e1, Matrix.mulVec_zero]; rfl

/-- **Every partial sum over whole blocks of a complete history is a projector.**  `D` selects
the directions of the blocks made so far (`D * D = D`, `Dᵀ = D`, `D * N = N * D`). -/
theorem complete_proj {ι : Type} [Fintype ι] [DecidableEq ι] (e : H ≃ ι) (M : Matrix H ι F)
    (N D : Matrix ι ι F) (hN : N * N = 1) (hNs : Nᵀ = N) (h : M * N * Mᵀ = 1)
    (hD : D * D = D) (hDs : Dᵀ = D) (hDN : D * N = N * D) :
    IsProj (M * (D * N) * Mᵀ) := by
  have hg := complete_gram e M N hN h
  refine ⟨?_, ?_⟩
  · rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_mul, hNs, hDs, ← hDN]
    simp only [Matrix.mul_assoc]
  · have e1 : M * (D * N) * Mᵀ * (M * (D * N) * Mᵀ)
        = M * (D * (N * ((Mᵀ * M) * (D * N)))) * Mᵀ := by
      simp only [Matrix.mul_assoc]
    rw [e1, hg]
    have e2 : D * (N * (N * (D * N))) = D * N := by
      rw [← Matrix.mul_assoc N N, hN, Matrix.one_mul, ← Matrix.mul_assoc, hD]
    rw [e2]

end
end
end PowerSaving.GF
end OAI

#print axioms OAI.PowerSaving.GF.gclimbO_of_list
#print axioms OAI.PowerSaving.GF.complete_gram
#print axioms OAI.PowerSaving.GF.complete_indep
#print axioms OAI.PowerSaving.GF.complete_proj
