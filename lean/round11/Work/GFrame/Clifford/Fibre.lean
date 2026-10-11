import Work.GFrame.Clifford.Basic

/-!
# GFrame / Clifford, part 1 (STAGE A on the fibre): an alternating form of rank `2p` is ONE
order-`2p` kernel between free adapters  (agent key: eng-clifford)

The fibre index type `γ` is cut into pairs by `e : ι ⊕ ι ≃ γ`.  The Walsh-diagonal matrix
`wrap (y ↦ ∏_j (-1)^(y_{l j} y_{r j}))` (the transition of an alternating residual in a
symplectic basis) equals

    diag ((-i)^p ∏_j i^[y_l + y_r])  *  kernel γ  *  (swap inside each pair) * diag (∏_j i^[y_l + y_r]).

`alt_fibre` is the general-rank form of `FLEngine.cz2_one_child` (which is the case `p = 1`).
No `sorry`.
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving.GF
open Binary Matrix Finset Complex
noncomputable section

/-- the 16-case identity behind one plane. -/
lemma pair_identity (a b c d : F) :
    cb * (littleC a c * littleC b d) + ca * (littleC (a + 1) c * littleC (b + 1) d)
      = -I * tint (a + b) * (littleC a d * littleC b c) * tint (c + d) := by
  rcases bit_cases a with rfl|rfl <;> rcases bit_cases b with rfl|rfl <;>
    rcases bit_cases c with rfl|rfl <;> rcases bit_cases d with rfl|rfl <;>
    simp only [littleC, tint, one_add_one_F, zero_add, add_zero, if_true, if_false,
      zero_ne_one, one_ne_zero, mul_one, one_mul, ↓reduceIte, ca, cb] <;>
    first
      | (norm_num [Complex.ext_iff]; done)
      | (ring_nf; simp only [Complex.I_sq, Complex.I_pow_four]; ring_nf; done)
      | (apply Complex.ext <;> simp <;> norm_num; done)

section
variable {ι γ : Type*} [Fintype ι] [DecidableEq ι] [Fintype γ] [DecidableEq γ]

/-- the coordinate swap inside each pair, as an additive bijection of the fibre. -/
def pairSwap (e : ι ⊕ ι ≃ γ) : APerm γ where
  π := { toFun := fun y c => y (e (e.symm c).swap)
         invFun := fun y c => y (e (e.symm c).swap)
         left_inv := by intro y; funext c; simp
         right_inv := by intro y; funext c; simp }
  add := by intro x y; funext c; rfl

variable (e : ι ⊕ ι ≃ γ)

/-- diagonal direction of the pair `j`. -/
def pairDir (j : ι) : Space γ := eu (e (.inl j)) + eu (e (.inr j))

/-- the quarter phase of the pairs: `∏_j i^[y_l + y_r]`. -/
def pairPhase (y : Space γ) : ℂ := ∏ j : ι, tint (y (e (.inl j)) + y (e (.inr j)))

/-- factor of an untouched pair in the kernel. -/
def pairK (j : ι) (x y : Space γ) : ℂ :=
  littleC (x (e (.inl j))) (y (e (.inl j))) * littleC (x (e (.inr j))) (y (e (.inr j)))

/-- factor of a twisted pair. -/
def pairG (j : ι) (x y : Space γ) : ℂ :=
  -I * tint (x (e (.inl j)) + x (e (.inr j)))
    * (littleC (x (e (.inl j))) (y (e (.inr j))) * littleC (x (e (.inr j))) (y (e (.inl j))))
    * tint (y (e (.inl j)) + y (e (.inr j)))

lemma kernel_pairs (x y : Space γ) : kernel γ x y = ∏ j, pairK e j x y := by
  rw [kernel, digitProd_apply, ← Equiv.prod_comp e, Fintype.prod_sum_type,
    ← Finset.prod_mul_distrib]
  rfl

lemma lum_pairs (s : Space γ) :
    lum s = ∏ j : ι, (tint (s (e (.inl j))) * tint (s (e (.inr j)))) := by
  rw [lum, ← Equiv.prod_comp e, Fintype.prod_sum_type, ← Finset.prod_mul_distrib]

lemma dot_pairDir (j : ι) (s : Space γ) :
    dot (pairDir e j) s = s (e (.inl j)) + s (e (.inr j)) := by
  simp [pairDir]

/-- product of the inverse unit moves along the pair diagonals in `A`. -/
def EA (A : Finset ι) : CMat γ :=
  wrap (fun s => ∏ j ∈ A, (tint (dot (pairDir e j) s) * sign (dot (pairDir e j) s)))

lemma EA_insert (j : ι) (A : Finset ι) (hj : j ∉ A) :
    EA e (insert j A) = (cb • (1 : CMat γ) + ca • shift (pairDir e j)) * EA e A := by
  rw [← wrap_conj_tint, EA, EA, wrap_mul]
  congr 1
  funext s
  rw [Finset.prod_insert hj]

lemma pairDir_other_l (j k : ι) (h : k ≠ j) (x : Space γ) :
    (x + pairDir e j) (e (.inl k)) = x (e (.inl k)) := by
  have h' : ¬ j = k := fun h' => h h'.symm
  simp [pairDir, eu, h']

lemma pairDir_other_r (j k : ι) (h : k ≠ j) (x : Space γ) :
    (x + pairDir e j) (e (.inr k)) = x (e (.inr k)) := by
  have h' : ¬ j = k := fun h' => h h'.symm
  simp [pairDir, eu, h']

lemma pairDir_self_l (j : ι) (x : Space γ) :
    (x + pairDir e j) (e (.inl j)) = x (e (.inl j)) + 1 := by
  simp [pairDir, eu]

lemma pairDir_self_r (j : ι) (x : Space γ) :
    (x + pairDir e j) (e (.inr j)) = x (e (.inr j)) + 1 := by
  simp [pairDir, eu]

/-- **Entry formula**: twisting the pairs in `A`. -/
theorem EA_kernel_apply (A : Finset ι) (x y : Space γ) :
    (EA e A * kernel γ) x y = ∏ j, (if j ∈ A then pairG e j x y else pairK e j x y) := by
  induction A using Finset.induction_on generalizing x with
  | empty => simp [EA, wrap_one, kernel_pairs e]
  | insert j A hj ih =>
    rw [EA_insert e j A hj, Matrix.mul_assoc, invdir_mul_apply, ih, ih,
      ← Finset.mul_prod_erase univ _ (mem_univ j), ← Finset.mul_prod_erase univ _ (mem_univ j),
      ← Finset.mul_prod_erase univ _ (mem_univ j)]
    have hrest : ∏ k ∈ univ.erase j,
        (if k ∈ A then pairG e k (x + pairDir e j) y else pairK e k (x + pairDir e j) y)
        = ∏ k ∈ univ.erase j, (if k ∈ A then pairG e k x y else pairK e k x y) := by
      apply Finset.prod_congr rfl
      intro k hk
      have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
      simp only [pairG, pairK, pairDir_other_l e j k hkj, pairDir_other_r e j k hkj]
    have hrest2 : ∏ k ∈ univ.erase j,
        (if k ∈ insert j A then pairG e k x y else pairK e k x y)
        = ∏ k ∈ univ.erase j, (if k ∈ A then pairG e k x y else pairK e k x y) := by
      apply Finset.prod_congr rfl
      intro k hk
      have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
      simp [Finset.mem_insert, hkj]
    rw [hrest, hrest2, if_neg hj, if_neg hj, if_pos (Finset.mem_insert_self j A)]
    generalize (∏ k ∈ univ.erase j, (if k ∈ A then pairG e k x y else pairK e k x y)) = P
    simp only [pairK, pairG, pairDir_self_l, pairDir_self_r]
    linear_combination P * pair_identity (x (e (.inl j))) (x (e (.inr j))) (y (e (.inl j)))
      (y (e (.inr j)))

/-- **STAGE A on the fibre**: an alternating form in a symplectic basis is ONE kernel of the
full order between a diagonal quarter phase (left) and the pair swap with a diagonal quarter
phase (right). -/
theorem alt_fibre :
    wrap (fun y : Space γ => ∏ j : ι, sign (y (e (.inl j)) * y (e (.inr j))))
      = diagonal (fun y => (-I) ^ Fintype.card ι * pairPhase e y) * kernel γ
          * (permMat (pairSwap e) * diagonal (pairPhase e)) := by
  have h1 : wrap (fun y : Space γ => ∏ j : ι, sign (y (e (.inl j)) * y (e (.inr j))))
      = EA e univ * kernel γ := by
    rw [← wrap_lum, EA, wrap_mul]
    congr 1
    funext s
    rw [lum_pairs e, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    rw [dot_pairDir, sign_mul_bits]
    ring
  rw [h1]
  ext x y
  rw [EA_kernel_apply, Matrix.mul_assoc, Matrix.diagonal_mul, ← Matrix.mul_assoc,
    Matrix.mul_diagonal, mul_permMat_apply, kernel_pairs e]
  simp only [mem_univ, ↓reduceIte, pairPhase]
  rw [show ((-I) ^ Fintype.card ι : ℂ) = ∏ _j : ι, (-I) by simp, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  simp only [pairG, pairK, pairSwap, Equiv.coe_fn_symm_mk, Equiv.symm_apply_apply, Sum.swap_inl,
    Sum.swap_inr]
  ring

end
end
end PowerSaving.GF
end OAI

#print axioms OAI.PowerSaving.GF.alt_fibre
