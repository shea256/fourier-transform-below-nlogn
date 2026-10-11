import Work.GFrame.Clifford.Basic

/-!
# GFrame / Clifford, part 2: closure properties of the free matrices (agent key: eng-clifford)

* `free_diag_tint`, `free_diag_sign`, `free_diag_mul`, `free_diag_prod`, `free_diag_pow`,
  `free_scalar`      diagonal quarter phases built from affine functionals are free;
* `free_lift`        a free matrix of the fibre of a splitting lifts to a free matrix;
* `free_inv`         free matrices have free inverses.
No `sorry`.
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving.GF
open Binary Matrix Finset Complex
noncomputable section
section
variable {α β γ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ]

lemma tint_four (t : F) : tint t * (tint t * tint t) * tint t = 1 := by
  rcases bit_cases t with rfl|rfl <;> simp [tint]

lemma tint_four' (t : F) : tint t * (tint t * (tint t * tint t)) = 1 := by
  rcases bit_cases t with rfl|rfl <;> simp [tint]

lemma free_diag_tint (z : Space α) (c : F) :
    Free (diagonal fun x : Space α => tint (dot z x + c)) := Free.phase z c

lemma free_diag_mul {f g : Space α → ℂ} (hf : Free (diagonal f)) (hg : Free (diagonal g)) :
    Free (diagonal fun x => f x * g x) := by
  have h := Free.mul hf hg
  rwa [Matrix.diagonal_mul_diagonal] at h

lemma free_diag_one : Free (diagonal fun _ : Space α => (1 : ℂ)) := by
  rw [Matrix.diagonal_one]; exact Free.one

lemma free_diag_prod {κ : Type*} (s : Finset κ) (f : κ → Space α → ℂ)
    (h : ∀ j ∈ s, Free (diagonal (f j))) : Free (diagonal fun x => ∏ j ∈ s, f j x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using free_diag_one (α := α)
  | insert i s hi ih =>
    have h1 := free_diag_mul (h i (mem_insert_self i s))
      (ih fun j hj => h j (mem_insert_of_mem hj))
    simpa [Finset.prod_insert hi] using h1

lemma free_diag_sign (z : Space α) (c : F) :
    Free (diagonal fun x : Space α => sign (dot z x + c)) := by
  have h := free_diag_mul (free_diag_tint z c) (free_diag_tint z c)
  simpa [tint_sq] using h

lemma free_diag_I : Free (diagonal fun _ : Space α => I) := by
  have h := free_diag_tint (0 : Space α) 1
  simpa [tint] using h

lemma free_diag_pow {f : Space α → ℂ} (hf : Free (diagonal f)) (n : ℕ) :
    Free (diagonal fun x => f x ^ n) := by
  induction n with
  | zero => simpa using free_diag_one (α := α)
  | succ n ih =>
    have h := free_diag_mul ih hf
    simpa [pow_succ] using h

lemma free_diag_const (n : ℕ) : Free (diagonal fun _ : Space α => I ^ n) :=
  free_diag_pow free_diag_I n

lemma free_diag_negI (n : ℕ) : Free (diagonal fun _ : Space α => (-I) ^ n) := by
  have h := free_diag_pow (free_diag_const (α := α) 3) n
  have e : (I : ℂ) ^ 3 = -I := by
    rw [pow_succ, pow_two, Complex.I_mul_I]; ring
  simpa [e] using h

theorem free_scalar (n : ℕ) : Free ((I ^ n) • (1 : CMat α)) := by
  have e : (I ^ n) • (1 : CMat α) = diagonal fun _ => I ^ n := by
    ext x y
    by_cases h : x = y
    · subst h; simp
    · simp [Matrix.one_apply, h]
  rw [e]; exact free_diag_const n

/-! ### lifting along a splitting -/

lemma split_map_sum (S : Split α β γ) {κ : Type*} (s : Finset κ) (f : κ → Space α) :
    S.e (∑ j ∈ s, f j) = ∑ j ∈ s, S.e (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [S.map_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, S.add, ih]

lemma split_map_smul (S : Split α β γ) (a : F) (x : Space α) : S.e (a • x) = a • S.e x := by
  rcases bit_cases a with rfl|rfl
  · simp [S.map_zero]
  · simp

lemma space_eq_sum (x : Space α) : x = ∑ i, x i • eu i := by
  funext k
  simp [eu]

/-- a functional of the fibre, pulled back to the label space. -/
def pullVec (S : Split α β γ) (z : Space γ) : Space α := fun i => dot z (S.e (eu i)).2

lemma dot_pullVec (S : Split α β γ) (z : Space γ) (x : Space α) :
    dot (pullVec S z) x = dot z (S.e x).2 := by
  conv_rhs => rw [space_eq_sum x, split_map_sum, Prod.snd_sum, dot_sum]
  simp only [split_map_smul, Prod.smul_snd, dot_smul_right]
  simp only [dot, pullVec]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma lift_diagonal (S : Split α β γ) (d : Space γ → ℂ) :
    S.lift (diagonal d) = diagonal (fun x => d (S.e x).2) := by
  ext x y
  simp only [Split.lift, Matrix.diagonal_apply]
  by_cases h : x = y
  · subst h; simp
  · by_cases h1 : (S.e x).1 = (S.e y).1
    · have h2 : (S.e x).2 ≠ (S.e y).2 := fun h2 => h (S.e.injective (Prod.ext h1 h2))
      rw [if_pos h1, if_neg h2, if_neg h]
    · rw [if_neg h1, if_neg h]

/-- an additive bijection of the fibre, acting on the label space. -/
def liftPerm (S : Split α β γ) (G : APerm γ) : APerm α where
  π := { toFun := fun x => S.e.symm ((S.e x).1, G.π (S.e x).2)
         invFun := fun x => S.e.symm ((S.e x).1, G.π.symm (S.e x).2)
         left_inv := by intro x; simp
         right_inv := by intro x; simp }
  add := by
    intro x y
    change S.e.symm ((S.e (x + y)).1, G.π (S.e (x + y)).2)
      = S.e.symm ((S.e x).1, G.π (S.e x).2) + S.e.symm ((S.e y).1, G.π (S.e y).2)
    rw [← S.symm_add, S.add]
    simp [G.add]

lemma lift_permMat (S : Split α β γ) (G : APerm γ) :
    S.lift (permMat G) = permMat (liftPerm S G) := by
  ext x y
  have hπ : (liftPerm S G).π x = S.e.symm ((S.e x).1, G.π (S.e x).2) := rfl
  simp only [Split.lift, permMat, hπ]
  have key : S.e.symm ((S.e x).1, G.π (S.e x).2) = y ↔
      (S.e x).1 = (S.e y).1 ∧ G.π (S.e x).2 = (S.e y).2 := by
    rw [Equiv.symm_apply_eq, Prod.ext_iff]
  by_cases h1 : (S.e x).1 = (S.e y).1
  · by_cases h2 : G.π (S.e x).2 = (S.e y).2
    · rw [if_pos h1, if_pos h2, if_pos (key.2 ⟨h1, h2⟩)]
    · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 (key.1 h).2)]
  · rw [if_neg h1, if_neg (fun h => h1 (key.1 h).1)]

/-- **Free matrices of the fibre lift to free matrices.** -/
theorem free_lift (S : Split α β γ) {A : CMat γ} (h : Free A) : Free (S.lift A) := by
  induction h with
  | one => rw [S.lift_one]; exact Free.one
  | perm G => rw [lift_permMat]; exact Free.perm _
  | phase z c =>
    have e : S.lift (phaseMat z c) = phaseMat (pullVec S z) c := by
      unfold phaseMat
      rw [lift_diagonal]
      congr 1
      funext x
      rw [dot_pullVec]
    rw [e]; exact Free.phase _ _
  | shift z => rw [S.lift_shift]; exact Free.shift _
  | mul _ _ ihA ihB => rw [S.lift_mul]; exact Free.mul ihA ihB

/-- **Free matrices have free inverses.** -/
theorem free_inv {A : CMat α} (h : Free A) : ∃ A', Free A' ∧ A' * A = 1 ∧ A * A' = 1 := by
  induction h with
  | one => exact ⟨1, Free.one, by simp, by simp⟩
  | perm G => exact ⟨permMat (apInv G), Free.perm _, permMat_inv_mul G, permMat_mul_inv G⟩
  | phase z c =>
    refine ⟨phaseMat z c * (phaseMat z c * phaseMat z c),
      Free.mul (Free.phase z c) (Free.mul (Free.phase z c) (Free.phase z c)), ?_, ?_⟩
    · unfold phaseMat
      simp only [Matrix.diagonal_mul_diagonal, tint_four, Matrix.diagonal_one]
    · unfold phaseMat
      simp only [Matrix.diagonal_mul_diagonal, tint_four', Matrix.diagonal_one]
  | shift z => exact ⟨shift z, Free.shift z, shift_sq z, shift_sq z⟩
  | mul _ _ ihA ihB =>
    obtain ⟨A', fA, lA, rA⟩ := ihA
    obtain ⟨B', fB, lB, rB⟩ := ihB
    refine ⟨B' * A', Free.mul fB fA, ?_, ?_⟩
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc A', lA, Matrix.one_mul, lB]
    · rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ B', rB, Matrix.one_mul, rA]

end
end
end PowerSaving.GF
end OAI

#print axioms OAI.PowerSaving.GF.free_lift
#print axioms OAI.PowerSaving.GF.free_inv
#print axioms OAI.PowerSaving.GF.free_scalar
