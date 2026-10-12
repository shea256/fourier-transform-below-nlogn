import Work.CarrierCheck.Roles
import Work.SharedSumChecker.Scalar

/-!
# (key: carrier-check) Unit rows and unit columns of the gate product of a micro-program

* `matP_row`   no gate INTO the role `i`  →  row `i` of `matP unemb ms` is a unit row;
* `matP_col`   no gate READS the role `j` →  column `j` of `matP unemb ms` is a unit column;
* `unitRow_mul`, `unitCol_mul`   these properties pass to products;
* `matP_append`, `gatesDistinct_of`, `mul_unitCol`.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace SSC
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM OAI.PowerSaving.SS Finset Matrix

section
variable {ρ : Type} [Fintype ρ] [DecidableEq ρ]

theorem mul_eMat_apply (M : Matrix ρ ρ ℚ) (a b i j : ρ) :
    (M * eMat a b) i j = if j = b then M i a else 0 := by
  rw [Matrix.mul_apply]
  by_cases h : j = b
  · rw [if_pos h, Finset.sum_eq_single a]
    · simp [eMat, h]
    · intro k _ hk; simp [eMat, hk]
    · intro hb; exact absurd (Finset.mem_univ _) hb
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro k _
    simp [eMat, h]

theorem mul_addMat_apply (M : Matrix ρ ρ ℚ) (a b : ρ) (cf : ℚ) (i j : ρ) :
    (M * addMat a b cf) i j = M i j + (if j = b then cf * M i a else 0) := by
  rw [addMat_eq, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_smul,
    Matrix.smul_apply, mul_eMat_apply]
  split <;> simp

/-- no gate INTO the role `i`: its row of the gate product is a unit row -/
theorem matP_row (unemb : Nat → ρ) (i : ρ) : ∀ (ms : List Micro),
    (∀ t s cf, Micro.add t s cf ∈ ms → unemb t ≠ i) →
    ∀ j, matP unemb ms i j = if i = j then 1 else 0 := by
  intro ms
  induction ms with
  | nil =>
    intro _ j
    exact Matrix.one_apply
  | cons m ms ih =>
    intro h j
    have ih' := ih (fun t s cf hm => h t s cf (List.mem_cons_of_mem _ hm))
    cases m with
    | add t s cf =>
      have hne : unemb t ≠ i := h t s cf (List.mem_cons_self ..)
      show (matP unemb ms * addMat (unemb t) (unemb s) cf.val) i j = _
      rw [mul_addMat_apply, ih' j, ih' (unemb t), if_neg (Ne.symm hne), mul_zero]
      simp
    | dir _ _ => exact ih' j
    | shift _ _ => exact ih' j
    | copy _ _ => exact ih' j
    | erase _ => exact ih' j
    | expect _ _ => exact ih' j

/-- no gate READS the role `j`: its column of the gate product is a unit column -/
theorem matP_col (unemb : Nat → ρ) (j : ρ) : ∀ (ms : List Micro),
    (∀ t s cf, Micro.add t s cf ∈ ms → unemb s ≠ j) →
    ∀ i, matP unemb ms i j = if i = j then 1 else 0 := by
  intro ms
  induction ms with
  | nil =>
    intro _ i
    exact Matrix.one_apply
  | cons m ms ih =>
    intro h i
    have ih' := ih (fun t s cf hm => h t s cf (List.mem_cons_of_mem _ hm))
    cases m with
    | add t s cf =>
      have hne : unemb s ≠ j := h t s cf (List.mem_cons_self ..)
      show (matP unemb ms * addMat (unemb t) (unemb s) cf.val) i j = _
      rw [mul_addMat_apply, if_neg (Ne.symm hne), add_zero]
      exact ih' i
    | dir _ _ => exact ih' i
    | shift _ _ => exact ih' i
    | copy _ _ => exact ih' i
    | erase _ => exact ih' i
    | expect _ _ => exact ih' i

theorem unitRow_mul (A B : Matrix ρ ρ ℚ) (i : ρ) (hA : ∀ j, A i j = if i = j then 1 else 0)
    (hB : ∀ j, B i j = if i = j then 1 else 0) : ∀ j, (A * B) i j = if i = j then 1 else 0 := by
  intro j
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [hA i, if_pos rfl, one_mul, hB j]
  · intro k _ hk
    rw [hA k, if_neg (Ne.symm hk), zero_mul]
  · intro hb
    exact absurd (Finset.mem_univ _) hb

theorem unitCol_mul (A B : Matrix ρ ρ ℚ) (j : ρ) (hA : ∀ i, A i j = if i = j then 1 else 0)
    (hB : ∀ i, B i j = if i = j then 1 else 0) : ∀ i, (A * B) i j = if i = j then 1 else 0 := by
  intro i
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [hB j, if_pos rfl, mul_one, hA i]
  · intro k _ hk
    rw [hB k, if_neg hk, mul_zero]
  · intro hb
    exact absurd (Finset.mem_univ _) hb

/-- multiplying by a matrix whose column `T` is the unit column at `j0` picks the column `j0` -/
theorem mul_unitCol {m : Type} (M : Matrix ρ ρ ℚ) (X : Matrix ρ m ℚ) (j0 : ρ) (T : m)
    (hX : ∀ j, X j T = if j = j0 then 1 else 0) (i : ρ) : (M * X) i T = M i j0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j0]
  · rw [hX j0, if_pos rfl, mul_one]
  · intro k _ hk
    rw [hX k, if_neg hk, mul_zero]
  · intro hb
    exact absurd (Finset.mem_univ _) hb

theorem matP_append (unemb : Nat → ρ) (a b : List Micro) :
    matP unemb (a ++ b) = matP unemb b * matP unemb a := by
  induction a with
  | nil =>
    show matP unemb b = matP unemb b * 1
    rw [Matrix.mul_one]
  | cons m a ih =>
    cases m with
    | add t s cf =>
      show matP unemb (a ++ b) * addMat (unemb t) (unemb s) cf.val
        = matP unemb b * (matP unemb a * addMat (unemb t) (unemb s) cf.val)
      rw [ih, Matrix.mul_assoc]
    | dir _ _ => exact ih
    | shift _ _ => exact ih
    | copy _ _ => exact ih
    | erase _ => exact ih
    | expect _ _ => exact ih

/-- gates between different roles -/
theorem gatesDistinct_of (unemb : Nat → ρ) : ∀ (ms : List Micro),
    (∀ t s cf, Micro.add t s cf ∈ ms → unemb t ≠ unemb s) → gatesDistinct unemb ms := by
  intro ms
  induction ms with
  | nil => intro _; exact trivial
  | cons m ms ih =>
    intro h
    have ih' := ih (fun t s cf hm => h t s cf (List.mem_cons_of_mem _ hm))
    cases m with
    | add t s cf => exact ⟨h t s cf (List.mem_cons_self ..), ih'⟩
    | dir _ _ => exact ih'
    | shift _ _ => exact ih'
    | copy _ _ => exact ih'
    | erase _ => exact ih'
    | expect _ _ => exact ih'

end

end SSC
