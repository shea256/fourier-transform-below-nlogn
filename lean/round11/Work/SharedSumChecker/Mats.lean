import Work.SharedSumChecker.Proj

/-!
# Shared-sum checker: gate matrices of a micro-program, their inverse and transposed inverse
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace SSC
open OAI.PowerSaving.Binary OAI.PowerSaving.RAM OAI.PowerSaving.SS Finset Matrix

section
variable {ρ : Type} [Fintype ρ] [DecidableEq ρ]

/-- the matrix unit -/
def eMat (a b : ρ) : Matrix ρ ρ ℚ := fun i j => if i = a ∧ j = b then 1 else 0

theorem addMat_eq (a b : ρ) (c : ℚ) : addMat a b c = 1 + c • eMat a b := by
  ext i j
  simp only [addMat, eMat, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]
  split <;> split <;> simp

theorem eMat_sq (a b : ρ) (hab : a ≠ b) : eMat a b * eMat a b = 0 := by
  ext i j
  simp only [Matrix.mul_apply, eMat, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases h1 : i = a ∧ k = b
  · have h2 : ¬ (k = a ∧ j = b) := fun h => hab (h.1.symm.trans h1.2)
    rw [if_pos h1, if_neg h2, mul_zero]
  · rw [if_neg h1, zero_mul]

omit [Fintype ρ] [DecidableEq ρ] in
theorem one_add_mul_one_sub {A : Type*} [Ring A] (X : A) : (1 + X) * (1 - X) = 1 - X * X := by
  noncomm_ring

theorem addMat_mul_neg (a b : ρ) (c : ℚ) (hab : a ≠ b) : addMat a b c * addMat a b (-c) = 1 := by
  have h2 : addMat a b (-c) = 1 - c • eMat a b := by
    rw [addMat_eq, neg_smul, sub_eq_add_neg]
  have hX : (c • eMat a b) * (c • eMat a b) = 0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, eMat_sq a b hab, smul_zero, smul_zero]
  have h3 := one_add_mul_one_sub (c • eMat a b)
  rw [addMat_eq, h2, h3, hX, sub_zero]

theorem addMat_transpose (a b : ρ) (c : ℚ) : (addMat a b c)ᵀ = addMat b a c := by
  ext i j
  simp only [addMat, Matrix.transpose_apply]
  congr 1
  · by_cases h : i = j
    · simp [h]
    · have h' : ¬ j = i := fun e => h e.symm
      simp [h, h']
  · by_cases h : j = a ∧ i = b
    · have h' : i = b ∧ j = a := ⟨h.2, h.1⟩
      simp [h, h']
    · have h' : ¬ (i = b ∧ j = a) := fun e => h ⟨e.2, e.1⟩
      simp [h, h']

/-- product of the inverse gate matrices, in reverse order -/
noncomputable def matPinv (unemb : Nat → ρ) : List Micro → Matrix ρ ρ ℚ
  | [] => 1
  | .add t s c :: ms => addMat (unemb t) (unemb s) (-c.val) * matPinv unemb ms
  | .dir _ _ :: ms => matPinv unemb ms
  | .shift _ _ :: ms => matPinv unemb ms
  | .copy _ _ :: ms => matPinv unemb ms
  | .erase _ :: ms => matPinv unemb ms
  | .expect _ _ :: ms => matPinv unemb ms

/-- every gate joins two different embedded roles -/
def gatesDistinct (unemb : Nat → ρ) : List Micro → Prop
  | [] => True
  | .add t s _ :: ms => unemb t ≠ unemb s ∧ gatesDistinct unemb ms
  | _ :: ms => gatesDistinct unemb ms

theorem matP_inv (unemb : Nat → ρ) (ms : List Micro) (h : gatesDistinct unemb ms) :
    matP unemb ms * matPinv unemb ms = 1 := by
  induction ms with
  | nil => simp [matP, matPinv]
  | cons m ms ih =>
    cases m with
    | add t s c =>
      obtain ⟨h1, h2⟩ := h
      show matP unemb ms * addMat (unemb t) (unemb s) c.val
        * (addMat (unemb t) (unemb s) (-c.val) * matPinv unemb ms) = 1
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (addMat _ _ c.val), addMat_mul_neg _ _ _ h1,
        Matrix.one_mul, ih h2]
    | dir _ _ => exact ih h
    | shift _ _ => exact ih h
    | copy _ _ => exact ih h
    | erase _ => exact ih h
    | expect _ _ => exact ih h

/-- negated coefficient -/
def Coef.negate (c : Coef) : Coef := ⟨!c.neg, c.num, c.den⟩

theorem Coef.negate_val (c : Coef) : c.negate.val = -c.val := by
  unfold Coef.negate Coef.val
  cases c.neg <;> simp [neg_div]

/-- the transposed inverse gate -/
def swapNeg : Micro → Micro
  | .add t s c => .add s t c.negate
  | m => m

theorem matP_swap (unemb : Nat → ρ) (ms : List Micro) :
    matP unemb (ms.map swapNeg) = (matPinv unemb ms)ᵀ := by
  induction ms with
  | nil => simp [matP, matPinv]
  | cons m ms ih =>
    cases m with
    | add t s c =>
      show matP unemb (ms.map swapNeg) * addMat (unemb s) (unemb t) c.negate.val
        = (addMat (unemb t) (unemb s) (-c.val) * matPinv unemb ms)ᵀ
      rw [Matrix.transpose_mul, addMat_transpose, ih, Coef.negate_val]
    | dir _ _ => exact ih
    | shift _ _ => exact ih
    | copy _ _ => exact ih
    | erase _ => exact ih
    | expect _ _ => exact ih

end

/-! ## the transposed inverse program has the same labels -/

theorem stepLab_swap (p : Par) (m : Micro) (lab : Nat → Nat) :
    stepLab p (swapNeg m) lab = stepLab p m lab := by
  cases m <;> rfl

theorem runLab_swap (p : Par) (lab : Nat → Nat) (ms : List Micro) :
    runLab p lab (ms.map swapNeg) = runLab p lab ms := by
  induction ms generalizing lab with
  | nil => rfl
  | cons m ms ih => rw [List.map_cons, runLab_cons, runLab_cons, stepLab_swap, ih]

theorem ok_swap (p : Par) (lab : Nat → Nat) (ms : List Micro) (h : Ok p lab ms) :
    Ok p lab (ms.map swapNeg) := by
  induction ms generalizing lab with
  | nil => exact trivial
  | cons m ms ih =>
    obtain ⟨h1, h2⟩ := h
    rw [List.map_cons]
    refine ⟨?_, ?_⟩
    · cases m with
      | add t s c => exact ⟨h1.2.1, h1.1, h1.2.2.symm⟩
      | dir _ _ => exact h1
      | shift _ _ => exact h1
      | copy _ _ => exact h1
      | erase _ => exact h1
      | expect _ _ => exact h1
    · rw [stepLab_swap]; exact ih _ h2

theorem isCopy_swap (m : Micro) : isCopy (swapNeg m) = isCopy m := by
  cases m <;> rfl

theorem histStep_swap (m : Micro) (H : Nat → List Nat) : histStep (swapNeg m) H = histStep m H := by
  cases m <;> rfl

section
variable {ρ : Type}

theorem segOK_swap (emb : ρ → Nat) (unemb : Nat → ρ) (m : Micro) (h : segOK emb unemb m) :
    segOK emb unemb (swapNeg m) := by
  cases m with
  | add t s c => exact ⟨h.2, h.1⟩
  | dir _ _ => exact h
  | shift _ _ => exact h
  | copy _ _ => exact h
  | erase _ => exact h
  | expect _ _ => exact h

/-- a complete certificate stays complete when a contiguous part is replaced by its transposed
inverse -/
theorem Complete.swap {p : Par} {lab0 : Nat → Nat} {H0 : Nat → List Nat} {a seg c : List Micro}
    {emb : ρ → Nat} (C : Complete p lab0 H0 (a ++ seg ++ c) emb) :
    Complete p lab0 H0 (a ++ seg.map swapNeg ++ c) emb := by
  have hrun : ∀ lab, runLab p lab (a ++ seg.map swapNeg ++ c) = runLab p lab (a ++ seg ++ c) := by
    intro lab
    simp only [runLab_append, runLab_swap]
  refine ⟨C.hh, C.hw, C.hc, C.hinv, ?_, ?_, ?_⟩
  · have h := C.hok
    rw [Ok_append, Ok_append] at h ⊢
    rw [runLab_append, runLab_swap, ← runLab_append]
    exact ⟨⟨h.1.1, ok_swap p _ _ h.1.2⟩, h.2⟩
  · intro m hm
    rcases List.mem_append.mp hm with h | h
    · rcases List.mem_append.mp h with h | h
      · exact C.hnc m (by simp [h])
      · obtain ⟨m', hm', rfl⟩ := List.mem_map.mp h
        rw [isCopy_swap]
        exact C.hnc m' (by simp [hm'])
    · exact C.hnc m (by simp [h])
  · intro q
    rw [hrun]
    exact C.hfull q

end

/-! ## rows given by lists of terms -/

section
variable {n : Nat}

/-- the row vector with entry `∑ coef` over the terms `(index, coef)` of the list -/
noncomputable def rowOf (l : List (Nat × Coef)) (q : Fin n) : ℚ :=
  (l.map fun x => if x.1 = q.val then x.2.val else 0).sum

theorem rowOf_nil (q : Fin n) : rowOf ([] : List (Nat × Coef)) q = 0 := rfl

theorem rowOf_cons (x : Nat × Coef) (l : List (Nat × Coef)) (q : Fin n) :
    rowOf (x :: l) q = (if x.1 = q.val then x.2.val else 0) + rowOf l q := by
  simp [rowOf]

theorem rowOf_ne_zero (l : List (Nat × Coef)) (q : Fin n) (h : rowOf l q ≠ 0) :
    ∃ x ∈ l, x.1 = q.val := by
  induction l with
  | nil => exact absurd rfl h
  | cons x l ih =>
    by_cases e : x.1 = q.val
    · exact ⟨x, List.mem_cons_self .., e⟩
    · rw [rowOf_cons, if_neg e, zero_add] at h
      obtain ⟨y, hy, hq⟩ := ih h
      exact ⟨y, List.mem_cons_of_mem _ hy, hq⟩

/-- pairing a row with a vector is a sum over the terms -/
theorem rowOf_sum (l : List (Nat × Coef)) (hl : ∀ x ∈ l, x.1 < n) (f : Fin n → ℚ) (g : Nat → ℚ)
    (hg : ∀ q : Fin n, f q = g q.val) :
    ∑ q : Fin n, rowOf l q * f q = (l.map fun x => x.2.val * g x.1).sum := by
  induction l with
  | nil => simp [rowOf]
  | cons x l ih =>
    have hx : x.1 < n := hl x (List.mem_cons_self ..)
    have ih' := ih (fun y hy => hl y (List.mem_cons_of_mem _ hy))
    simp only [rowOf_cons, add_mul, Finset.sum_add_distrib, List.map_cons, List.sum_cons, ih']
    congr 1
    rw [Finset.sum_eq_single (⟨x.1, hx⟩ : Fin n)]
    · simp [hg]
    · intro q _ hq
      have : ¬ x.1 = q.val := fun e => hq (Fin.ext e.symm)
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h

end

end SSC
