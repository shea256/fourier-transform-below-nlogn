import Work.GFrame.Engine.Free

/-!
# GFrame / Clifford, part 0: entry calculus for the free matrices (agent key: eng-clifford)

Entry formulas for products with `permMat`, `shift`, diagonal matrices, the combination
`cb • 1 + ca • shift u` (the inverse of the unit move `dir u`), and the helpers `apId`,
`apInv`, `apComp` on ENGINE's additive bijections `APerm`.  No `sorry`.
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving.GF
open Binary Matrix Finset Complex
noncomputable section

lemma one_add_one_F : (1 : F) + 1 = 0 := by decide

/-- `(-1)^(ab) = i^a i^b * conj (i^(a+b))`. -/
lemma sign_mul_bits (a b : F) :
    sign (a * b) = tint a * tint b * (tint (a + b) * sign (a + b)) := by
  rcases bit_cases a with rfl|rfl <;> rcases bit_cases b with rfl|rfl <;>
    simp [sign, tint]

section
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- identity as an additive bijection. -/
def apId (α : Type*) : APerm α := ⟨Equiv.refl _, fun _ _ => rfl⟩

/-- inverse of an additive bijection. -/
def apInv (G : APerm α) : APerm α where
  π := G.π.symm
  add := by
    intro x y
    apply G.π.injective
    rw [G.add]; simp

/-- composition: first `G`, then `H`. -/
def apComp (G H : APerm α) : APerm α where
  π := G.π.trans H.π
  add := by intro x y; simp [G.add, H.add]

@[simp] lemma apInv_apply (G : APerm α) (x : Space α) : (apInv G).π (G.π x) = x := by
  simp [apInv]
@[simp] lemma apply_apInv (G : APerm α) (x : Space α) : G.π ((apInv G).π x) = x := by
  simp [apInv]

lemma APerm.map_zero' (G : APerm α) : G.π 0 = 0 := by
  have h := G.add 0 0
  rw [add_zero] at h
  have h2 : G.π 0 + G.π 0 = 0 := binary_cancel _
  rw [← h] at h2
  exact h2

lemma APerm.map_sum' {κ : Type*} (G : APerm α) (s : Finset κ) (f : κ → Space α) :
    G.π (∑ j ∈ s, f j) = ∑ j ∈ s, G.π (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [G.map_zero']
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, G.add, ih]

lemma APerm.map_smul' (G : APerm α) (a : F) (x : Space α) : G.π (a • x) = a • G.π x := by
  rcases bit_cases a with rfl|rfl
  · simp [G.map_zero']
  · simp

lemma permMat_mul_apply (G : APerm α) (M : CMat α) (x y : Space α) :
    (permMat G * M) x y = M (G.π x) y := by
  rw [Matrix.mul_apply]
  simp [permMat]

lemma mul_permMat_apply (M : CMat α) (G : APerm α) (x y : Space α) :
    (M * permMat G) x y = M x (G.π.symm y) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (G.π.symm y)]
  · simp [permMat]
  · intro b _ hb
    have : ¬ G.π b = y := fun h => hb (by rw [← h]; simp)
    simp [permMat, this]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma permMat_apId : permMat (apId α) = 1 := by
  ext x y
  by_cases h : x = y
  · subst h; simp [permMat, apId]
  · simp [permMat, apId, Matrix.one_apply, h]

lemma permMat_comp (G H : APerm α) : permMat (apComp G H) = permMat G * permMat H := by
  ext x y
  rw [permMat_mul_apply]
  by_cases h : H.π (G.π x) = y <;> simp [permMat, apComp, h]

lemma permMat_inv_mul (G : APerm α) : permMat (apInv G) * permMat G = 1 := by
  ext x y
  rw [permMat_mul_apply]
  simp [permMat, apInv, Matrix.one_apply]

lemma permMat_mul_inv (G : APerm α) : permMat G * permMat (apInv G) = 1 := by
  ext x y
  rw [permMat_mul_apply]
  simp [permMat, apInv, Matrix.one_apply]

lemma shift_mul_apply (u : Space α) (M : CMat α) (x y : Space α) :
    (shift u * M) x y = M (x + u) y := by
  rw [Matrix.mul_apply]
  simp [shift]

lemma mul_shift_apply (u : Space α) (M : CMat α) (x y : Space α) :
    (M * shift u) x y = M x (y + u) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (y + u)]
  · simp [shift, add_assoc]
  · intro b _ hb
    have : ¬ b + u = y := fun h => hb (by rw [← h, add_assoc, binary_cancel, add_zero])
    simp [shift, this]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `wrap` of the conjugate unit phase is the inverse unit move `cb • 1 + ca • shift u`. -/
lemma wrap_conj_tint (u : Space α) :
    wrap (fun s => tint (dot u s) * sign (dot u s)) = cb • (1 : CMat α) + ca • shift u := by
  rw [← wrap_mul, ← dir_phase, ← shift_phase]
  unfold dir
  rw [add_mul, Matrix.smul_mul, Matrix.smul_mul, one_mul, shift_sq, add_comm]

lemma invdir_mul_apply (u : Space α) (M : CMat α) (x y : Space α) :
    ((cb • (1 : CMat α) + ca • shift u) * M) x y = cb * M x y + ca * M (x + u) y := by
  rw [add_mul, Matrix.smul_mul, Matrix.smul_mul, one_mul, Matrix.add_apply, Matrix.smul_apply,
    Matrix.smul_apply, shift_mul_apply]
  rfl

end
end
end PowerSaving.GF
end OAI

#print axioms OAI.PowerSaving.GF.mul_permMat_apply
#print axioms OAI.PowerSaving.GF.wrap_conj_tint
#print axioms OAI.PowerSaving.GF.invdir_mul_apply
