import Mathlib

namespace OAI
/-! Elementary tensor of local matrices in Pi indexing. -/

namespace PowerSaving
open Matrix Finset

variable {J : Type*} [Fintype J]
variable {κ : J → Type*} {μ : J → Type*} {ν : J → Type*}
variable {R : Type*} [CommSemiring R]

/-- Matrix tensor product indexed by digit tuples. -/
def digitProd (M : ∀ j, Matrix (κ j) (μ j) R) :
    Matrix ((j:J) → κ j) ((j:J) → μ j) R :=
  fun x y => ∏ j, M j (x j) (y j)

@[simp] theorem digitProd_apply (M : ∀ j, Matrix (κ j) (μ j) R) x y :
    digitProd M x y = ∏ j, M j (x j) (y j) := rfl

/-- Product of Kronecker deltas. -/
theorem prod_delta [∀ j, DecidableEq (κ j)] [DecidableEq ((j:J) → κ j)]
    (x y : (j:J) → κ j) :
    ∏ j:J, (if x j = y j then (1:R) else 0)
    = if x=y then 1 else 0 := by
  classical
  by_cases h : x = y
  · simp [h]
  · rw [ite_eq_right h]
    replace h : ∃ j, x j ≠ y j := Classical.byContradiction (by
      intro nh
      apply h
      push Not at nh
      exact funext nh)
    rcases h with ⟨j,hj⟩
    exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)

theorem digitProd_one [∀ j, DecidableEq (κ j)] [DecidableEq ((j:J) → κ j)] :
    digitProd (fun j:J => (1:Matrix (κ j) (κ j) R)) = 1 := by
  ext x y
  simp only [digitProd_apply, one_apply]
  apply prod_delta

theorem digitProd_diagonal [∀ j, DecidableEq (κ j)] [DecidableEq ((j:J) → κ j)]
    (d : ∀ j, κ j → R) :
    digitProd (fun j => Matrix.diagonal (d j))
      = Matrix.diagonal (fun x => ∏ j, d j (x j)) := by
  classical
  ext x y
  by_cases h : x = y
  · subst y; simp
  · simp only [digitProd_apply, diagonal_apply]
    -- diagonal if i=j then ... else 0
    rw [ite_eq_right h]
    replace h : ∃ j, x j ≠ y j := Classical.byContradiction (by
      intro nh
      apply h
      push Not at nh
      exact funext nh)
    obtain ⟨j,hj⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)

theorem digitProd_mul [∀ j, Fintype (μ j)] [DecidableEq J]
    (M : ∀ j, Matrix (κ j) (μ j) R) (N : ∀ j, Matrix (μ j) (ν j) R) :
    digitProd M * digitProd N = digitProd (fun j => M j * N j) := by
  classical
  ext x z
  simp only [digitProd_apply, Matrix.mul_apply, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun j y => M j (x j) y * N j y (z j))).symm

end PowerSaving

end OAI
