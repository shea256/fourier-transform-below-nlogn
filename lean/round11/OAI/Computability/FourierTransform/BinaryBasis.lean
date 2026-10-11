import OAI.Computability.FourierTransform.ProductMatrix

namespace OAI

/-! Binary orthonormal bases and masks for the fixed saving. -/

namespace PowerSaving.Binary
open Finset Matrix

abbrev F := ZMod 2
abbrev Space (α : Type*) := α → F

lemma bit_cases (x : F) : x=0 ∨ x=1 := by
  fin_cases x
  · left; rfl
  · right; rfl

@[simp] theorem cancel (x : F) : x+x=0 := by
  rcases bit_cases x with rfl | rfl <;> decide

@[simp] theorem binary_cancel {α : Type*} (x : Space α) : x+x=0 := by ext; exact cancel _

section Dot
variable {α : Type*} [Fintype α]

def dot (x y : Space α) := ∑ i : α, x i * y i

theorem dot_symm (x y : Space α) : dot x y = dot y x := by simp [dot, mul_comm]

@[simp] theorem dot_add_left (x y z : Space α) :
    dot (x+y) z = dot x z + dot y z := by simp [dot, add_mul, sum_add_distrib]

@[simp] theorem dot_add_right (x y z : Space α) :
    dot x (y+z) = dot x y + dot x z := by simp [dot, mul_add, sum_add_distrib]

@[simp] theorem dot_smul_left (a : F) (x y : Space α) :
    dot (a • x) y = a * dot x y := by simp [dot, mul_sum, mul_assoc]
@[simp] theorem dot_smul_right (a : F) (x y : Space α) :
    dot x (a • y) = a * dot x y := by rw [dot_symm, dot_smul_left, dot_symm]

@[simp] theorem dot_zero_left (x : Space α) : dot 0 x=0 := by simp [dot]

@[simp] theorem dot_zero_right (x : Space α) : dot x 0=0 := by simp [dot]

theorem dot_sum {β : Type*} (x : Space α) (s : Finset β) (f : β → Space α) :
    dot x (∑ j ∈ s, f j) = ∑ j ∈ s, dot x (f j) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s h ih => simp [h, ih]

variable [DecidableEq α]

def eu (i : α) : Space α := fun j => if i=j then 1 else 0

@[simp] theorem dot_eu_left (x : Space α) (i : α) : dot (eu i) x = x i := by
  simp [dot, eu, ite_mul]
@[simp] theorem dot_eu_right (x : Space α) (i : α) : dot x (eu i) = x i := by
  rw [dot_symm]; simp

end Dot

/-- Represent an orthonormal basis with full index set α. -/
structure OBase (α : Type*) [Fintype α] [DecidableEq α] where
  v : α → Space α
  rows : ∀ i j, dot (v i) (v j) = if i=j then 1 else 0

namespace OBase
variable {α : Type*} [Fintype α] [DecidableEq α]

@[simp] theorem self (A : OBase α) (i : α) : dot (A.v i) (A.v i)=1 := by
  simp [A.rows]

theorem nz (A : OBase α) (i : α) : A.v i ≠ 0 := by
  intro h
  have := A.self i
  simp [h] at this

/-- Orthonormality of columns follows from the square matrix identity. -/
theorem cols (A : OBase α) (i j : α) :
    ∑ k, A.v k i * A.v k j = if i=j then 1 else 0 := by
  let M : Matrix α α F := Matrix.of A.v
  have h : M * Mᵀ = 1 := by
    ext i j
    simpa [M, Matrix.mul_apply, one_apply, dot] using A.rows i j
  have g : Mᵀ * M = 1 := mul_eq_one_comm.mp h
  simpa [M, Matrix.mul_apply, one_apply] using congr_fun (congr_fun g i) j

def canonical (α : Type*) [Fintype α] [DecidableEq α] : OBase α :=
  ⟨eu, fun i j => by simp [eu]⟩

def mat (A : OBase α) (s : Finset α) : Matrix α α F :=
  fun i j => ∑ k ∈ s, A.v k i * A.v k j

@[simp] theorem mat_univ (A : OBase α) : A.mat univ = 1 := by
  ext i j
  simpa only [mat, one_apply] using A.cols i j

theorem mat_sub (A : OBase α) (s t : Finset α) (h : t ⊆ s) :
    A.mat (s \ t) = A.mat s - A.mat t := by
  ext i j
  simpa [mat, eq_sub_iff_add_eq] using
    Finset.sum_sdiff h (f:=fun k => A.v k i * A.v k j)

/-- Projection action. -/
def proj (A : OBase α) (s : Finset α) (x : Space α) : Space α :=
  ∑ k ∈ s, dot (A.v k) x • A.v k

theorem proj_apply (A : OBase α) (s : Finset α) (x : Space α) (i : α) :
    A.proj s x i = ∑ j, A.mat s i j*x j := by
  simp only [mat, proj, Finset.sum_apply, dot, sum_mul, Pi.smul_apply, smul_eq_mul]
  rw [sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ac_rfl

theorem proj_congr (A B : OBase α) (s t : Finset α) (h : A.mat s = B.mat t) :
    A.proj s = B.proj t := by
  funext x i; rw [proj_apply, h, ← proj_apply]

@[simp] theorem proj_univ (A : OBase α) (x : Space α) : A.proj univ x = x := by
  ext i; simp [proj_apply, one_apply, ite_mul]

theorem dot_proj_omit (A : OBase α) {s : Finset α} {i : α} (x : Space α) (hi : i ∉ s) :
    dot (A.v i) (A.proj s x) = 0 := by
  rw [proj, dot_sum]
  apply sum_eq_zero
  intro j hj
  have h : i ≠ j := by intro hh; exact hi (hh ▸ hj)
  simp [A.rows, h]

section Adapt

/-- Transvection carrying a chosen coordinate vector to a given norm-one t on disjoint support. -/
def tv (w x : Space α) := x + dot w x • w

omit [DecidableEq α] in
theorem tv_isom (w x y : Space α) (h : dot w w = 0) :
    dot (tv w x) (tv w y) = dot x y := by
  simp only [tv, dot_add_right, dot_add_left, dot_smul_right, dot_smul_left, h,
    mul_zero, add_zero]
  rw [dot_symm x w, mul_comm (dot w y), add_assoc, cancel, add_zero]

def acted (A : OBase α) (w : Space α) (h : dot w w=0) : OBase α :=
  ⟨fun i => tv w (A.v i), fun i j => by rw [tv_isom _ _ _ h]; apply A.rows⟩

def adapt (A : OBase α) (i : α) (t : Space α) (h1 : dot t t=1)
    (h2 : dot t (A.v i) = 0) : OBase α :=
  acted A (t + A.v i) (by simp [h1, h2, dot_symm (A.v i) t])

theorem adapt_pivot (A : OBase α) (i : α) (t : Space α)
    (h1 : dot t t=1) (h2 : dot t (A.v i) = 0) :
    (adapt A i t h1 h2).v i = t := by
  simp only [adapt, acted, tv, dot_add_left, h2, A.self, zero_add, one_smul]
  rw [add_comm t, ← add_assoc, binary_cancel, zero_add]

theorem adapt_other (A : OBase α) (i j : α) (t : Space α) (hi : i≠j)
    (h1 : dot t t=1) (h2 : dot t (A.v i)=0) (h3 : dot t (A.v j)=0) :
    (adapt A i t h1 h2).v j = A.v j := by simp [adapt, acted, tv, A.rows, hi, h3]

end Adapt

section Tensor
variable {J H : Type*} [Fintype J] [DecidableEq J] [Fintype H] [DecidableEq H]

def pure (A : J → OBase H) (k : J → H) : Space (J → H) :=
  fun l => ∏ j, (A j).v (k j) (l j)

def tensor (A : J → OBase H) : OBase (J → H) where
  v := pure A
  rows := fun x y => by
    classical
    simp only [pure, dot, ← prod_mul_distrib]
    rw [← Fintype.prod_sum (fun j l => (A j).v (x j) l * (A j).v (y j) l)]
    have hh (j : J) : ∑ l, ((A j).v (x j) l * (A j).v (y j) l) =
        if x j=y j then 1 else 0 := (A j).rows (x j) (y j)
    simpa only [hh] using
      (show ∏ j, (∑ l, ((A j).v (x j) l * (A j).v (y j) l)) = _ by
        simp only [hh]
        apply prod_delta)

theorem mat_rect (A : J → OBase H) (s : J → Finset H) :
    (tensor A).mat (Fintype.piFinset s) = digitProd (fun j => (A j).mat (s j)) := by
  ext x y
  simp only [digitProd_apply, mat, tensor, pure, ← prod_mul_distrib]
  exact (prod_univ_sum s (fun j l => (A j).v l (x j) * (A j).v l (y j))).symm

end Tensor
end OBase

end PowerSaving.Binary

end OAI
