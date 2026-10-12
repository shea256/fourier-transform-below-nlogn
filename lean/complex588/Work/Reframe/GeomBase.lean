import Work.Reframe.FrameAlg

/-!
# (key: reframe) Orthogonal matrices over `F_2` as orthonormal bases (generic tools)

* `diagI S`             the 0/1 diagonal matrix of an index set;
* `mul_diagI_mul`       `(M * diagI S * Mᵀ) a b = ∑ k ∈ S, M a k * M b k` for ANY square `M`;
* `cmat A`, `mat_eq_cmat`   an orthonormal basis as the matrix of its columns;
                        `A.mat s = cmat A * diagI s * (cmat A)ᵀ`;
* `ofCols M hM`         the orthonormal basis of the columns of an orthogonal matrix;
                        `frame_ofCols : frame (ofCols M hM) S = frameM (M * diagI S * Mᵀ)`;
* `submatrix_diagI`     permuting the columns of `M` by `π` moves the index set by `π`;
* `frameM_conj_add`     `frameM (g (P + Q) gᵀ) = frameM (g P gᵀ) * frameM (g Q gᵀ)` for `P ⟂ Q`;
* `Orth n`              the finite type of orthogonal matrices; `Orth.colPerm π` (permute the
                        columns) and `Orth.conjPerm B π` (`g ↦ ((g B) with columns permuted) Bᵀ`,
                        i.e. right multiplication by the isometry that permutes the basis `B`).

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace RF
open Binary Matrix Finset RAM SS CB
noncomputable section

section Gen
variable {n : Type} [Fintype n] [DecidableEq n]

/-- the 0/1 diagonal matrix of an index set. -/
def diagI (S : Finset n) : Matrix n n F := Matrix.diagonal fun i => if i ∈ S then 1 else 0

lemma diagI_apply (S : Finset n) (a b : n) :
    diagI S a b = if a = b then (if a ∈ S then 1 else 0) else 0 :=
  Matrix.diagonal_apply _ _ _

lemma diagI_empty : diagI (∅ : Finset n) = 0 := by
  ext a b
  rw [diagI_apply]
  by_cases h : a = b <;> simp [h]

lemma diagI_univ : diagI (univ : Finset n) = 1 := by
  ext a b
  rw [diagI_apply, Matrix.one_apply]
  by_cases h : a = b <;> simp [h]

lemma diagI_transpose (S : Finset n) : (diagI S)ᵀ = diagI S := Matrix.diagonal_transpose _

lemma diagI_union (S S' : Finset n) (h : Disjoint S S') :
    diagI (S ∪ S') = diagI S + diagI S' := by
  ext a b
  rw [Matrix.add_apply, diagI_apply, diagI_apply, diagI_apply]
  by_cases hab : a = b
  · subst hab
    by_cases h1 : a ∈ S
    · have h2 : a ∉ S' := fun h2 => Finset.disjoint_left.mp h h1 h2
      simp [h1, h2]
    · by_cases h2 : a ∈ S' <;> simp [h1, h2]
  · simp [hab]

/-- `M * diagI S * Mᵀ` is the sum of the outer squares of the columns in `S`. -/
lemma mul_diagI_mul (M : Matrix n n F) (S : Finset n) (a b : n) :
    (M * diagI S * Mᵀ) a b = ∑ k ∈ S, M a k * M b k := by
  have h1 : (M * diagI S * Mᵀ) a b = ∑ k, M a k * (if k ∈ S then 1 else 0) * M b k := by
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k _
    unfold diagI
    rw [Matrix.mul_diagonal]
    rfl
  calc (M * diagI S * Mᵀ) a b = ∑ k, M a k * (if k ∈ S then 1 else 0) * M b k := h1
    _ = ∑ k ∈ S, M a k * (if k ∈ S then 1 else 0) * M b k :=
        (Finset.sum_subset (Finset.subset_univ S) (fun k _ hk => by simp [hk])).symm
    _ = ∑ k ∈ S, M a k * M b k := Finset.sum_congr rfl (fun k hk => by simp [hk])

/-- projectors on disjoint index sets, transported by the same matrix, are orthogonal. -/
lemma diagI_orth (S S' : Finset n) (h : Disjoint S S') : (diagI S)ᵀ * diagI S' = 0 := by
  rw [diagI_transpose]
  unfold diagI
  rw [Matrix.diagonal_mul_diagonal]
  ext a b
  rw [Matrix.diagonal_apply, Matrix.zero_apply]
  by_cases hab : a = b
  · rw [if_pos hab]
    by_cases h1 : a ∈ S
    · have h2 : a ∉ S' := fun h2 => Finset.disjoint_left.mp h h1 h2
      rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]
  · rw [if_neg hab]

/-- the matrix whose COLUMNS are the vectors of the basis. -/
def cmat (A : OBase n) : Matrix n n F := fun a k => A.v k a

lemma cmat_orth (A : OBase n) : (cmat A)ᵀ * cmat A = 1 := by
  ext i j
  have h := A.rows i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  exact h

lemma cmat_orth' (A : OBase n) : cmat A * (cmat A)ᵀ = 1 :=
  mul_eq_one_comm.mp (cmat_orth A)

lemma mat_eq_cmat (A : OBase n) (s : Finset n) : A.mat s = cmat A * diagI s * (cmat A)ᵀ := by
  ext a b
  rw [mul_diagI_mul]
  rfl

/-- the orthonormal basis of the columns of an orthogonal matrix. -/
def ofCols (M : Matrix n n F) (hM : Mᵀ * M = 1) : OBase n where
  v := fun k a => M a k
  rows := fun i j => by
    have h := congrFun (congrFun hM i) j
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    exact h

lemma ofCols_mat (M : Matrix n n F) (hM : Mᵀ * M = 1) (S : Finset n) :
    (ofCols M hM).mat S = M * diagI S * Mᵀ :=
  mat_eq_cmat (ofCols M hM) S

lemma frame_ofCols (M : Matrix n n F) (hM : Mᵀ * M = 1) (S : Finset n) :
    frame (ofCols M hM) S = frameM (M * diagI S * Mᵀ) := by
  rw [frame_eq, ofCols_mat]

/-- permuting the columns by `π` moves the index set by `π`. -/
lemma submatrix_diagI (M : Matrix n n F) (π : Equiv.Perm n) (S : Finset n) :
    M.submatrix id π * diagI S * (M.submatrix id π)ᵀ
      = M * diagI (S.map π.toEmbedding) * Mᵀ := by
  ext a b
  have h1 := mul_diagI_mul (M.submatrix id π) S a b
  have h2 := mul_diagI_mul M (S.map π.toEmbedding) a b
  rw [Finset.sum_map] at h2
  exact h1.trans h2.symm

lemma submatrix_orth (M : Matrix n n F) (hM : Mᵀ * M = 1) (π : Equiv.Perm n) :
    (M.submatrix id π)ᵀ * M.submatrix id π = 1 := by
  ext i j
  have h := congrFun (congrFun hM (π i)) (π j)
  rw [Matrix.mul_apply, Matrix.one_apply] at h ⊢
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl] at h ⊢
    exact h
  · have hne : π i ≠ π j := fun e => hij (π.injective e)
    rw [if_neg hne] at h
    rw [if_neg hij]
    exact h

lemma mul_orth {M N : Matrix n n F} (hM : Mᵀ * M = 1) (hN : Nᵀ * N = 1) :
    (M * N)ᵀ * (M * N) = 1 := by
  rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Mᵀ, hM, Matrix.one_mul, hN]

lemma transpose_orth {M : Matrix n n F} (hM : Mᵀ * M = 1) : Mᵀᵀ * Mᵀ = 1 := by
  rw [Matrix.transpose_transpose]
  exact mul_eq_one_comm.mp hM

/-- frame of an orthogonal sum, transported by an orthogonal matrix. -/
lemma frameM_conj_add (g : Matrix n n F) (hg : gᵀ * g = 1) (P Q : Matrix n n F)
    (h : Pᵀ * Q = 0) :
    frameM (g * (P + Q) * gᵀ) = frameM (g * P * gᵀ) * frameM (g * Q * gᵀ) := by
  have e : g * (P + Q) * gᵀ = g * P * gᵀ + g * Q * gᵀ := by
    rw [Matrix.mul_add, Matrix.add_mul]
  rw [e]
  apply frameM_add
  have e2 : (g * P * gᵀ)ᵀ * (g * Q * gᵀ) = g * (Pᵀ * ((gᵀ * g) * Q)) * gᵀ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [e2, hg, Matrix.one_mul, h, Matrix.mul_zero, Matrix.zero_mul]


/-- the orthogonal matrices of the label space. -/
abbrev Orth (n : Type) [Fintype n] [DecidableEq n] := {g : Matrix n n F // gᵀ * g = 1}

namespace Orth

lemma orth' (g : Orth n) : g.1 * g.1ᵀ = 1 := mul_eq_one_comm.mp g.2

/-- the identity matrix. -/
def one : Orth n := ⟨1, by rw [Matrix.transpose_one, Matrix.one_mul]⟩

lemma card_pos : 1 ≤ Fintype.card (Orth n) := Fintype.card_pos_iff.mpr ⟨one⟩

/-- permute the columns by `π`. -/
def colPerm (π : Equiv.Perm n) : Orth n ≃ Orth n where
  toFun g := ⟨g.1.submatrix id π, submatrix_orth g.1 g.2 π⟩
  invFun g := ⟨g.1.submatrix id π.symm, submatrix_orth g.1 g.2 π.symm⟩
  left_inv g := by
    apply Subtype.ext
    ext a b
    show g.1 a (π (π.symm b)) = g.1 a b
    rw [Equiv.apply_symm_apply]
  right_inv g := by
    apply Subtype.ext
    ext a b
    show g.1 a (π.symm (π b)) = g.1 a b
    rw [Equiv.symm_apply_apply]

lemma colPerm_val (π : Equiv.Perm n) (g : Orth n) : (colPerm π g).1 = g.1.submatrix id π := rfl

lemma submatrix_symm (M : Matrix n n F) (π : Equiv.Perm n) :
    (M.submatrix id π).submatrix id π.symm = M := by
  ext a b
  show M a (π (π.symm b)) = M a b
  rw [Equiv.apply_symm_apply]

lemma submatrix_symm' (M : Matrix n n F) (π : Equiv.Perm n) :
    (M.submatrix id π.symm).submatrix id π = M := by
  ext a b
  show M a (π.symm (π b)) = M a b
  rw [Equiv.symm_apply_apply]

/-- right multiplication by the isometry that permutes the columns of the orthogonal matrix
`B` by `π`:  `g ↦ ((g B) with columns permuted by π) Bᵀ`. -/
def conjPerm (B : Matrix n n F) (hB : Bᵀ * B = 1) (π : Equiv.Perm n) : Orth n ≃ Orth n where
  toFun g := ⟨(g.1 * B).submatrix id π * Bᵀ,
    mul_orth (submatrix_orth _ (mul_orth g.2 hB) π) (transpose_orth hB)⟩
  invFun g := ⟨(g.1 * B).submatrix id π.symm * Bᵀ,
    mul_orth (submatrix_orth _ (mul_orth g.2 hB) π.symm) (transpose_orth hB)⟩
  left_inv g := by
    apply Subtype.ext
    show ((g.1 * B).submatrix id π * Bᵀ * B).submatrix id π.symm * Bᵀ = g.1
    rw [Matrix.mul_assoc ((g.1 * B).submatrix id π), hB, Matrix.mul_one, submatrix_symm,
      Matrix.mul_assoc, mul_eq_one_comm.mp hB, Matrix.mul_one]
  right_inv g := by
    apply Subtype.ext
    show ((g.1 * B).submatrix id π.symm * Bᵀ * B).submatrix id π * Bᵀ = g.1
    rw [Matrix.mul_assoc ((g.1 * B).submatrix id π.symm), hB, Matrix.mul_one, submatrix_symm',
      Matrix.mul_assoc, mul_eq_one_comm.mp hB, Matrix.mul_one]

/-- after `conjPerm B π` the columns of `g B` are permuted by `π`. -/
lemma conjPerm_mul (B : Matrix n n F) (hB : Bᵀ * B = 1) (π : Equiv.Perm n) (g : Orth n) :
    (conjPerm B hB π g).1 * B = (g.1 * B).submatrix id π := by
  show (g.1 * B).submatrix id π * Bᵀ * B = _
  rw [Matrix.mul_assoc, hB, Matrix.mul_one]

end Orth

end Gen
end
end RF
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.RF.frame_ofCols
#print axioms OAI.PowerSaving.RF.submatrix_diagI
#print axioms OAI.PowerSaving.RF.frameM_conj_add
#print axioms OAI.PowerSaving.RF.Orth.conjPerm_mul
