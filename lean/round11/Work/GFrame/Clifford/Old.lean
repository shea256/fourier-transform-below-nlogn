import Work.GFrame.Clifford.Climb

/-!
# GFrame / Clifford, part 9: the OLD frames are representatives (up to a free scalar)

(agent key: eng-clifford)

For an orthonormal basis `A` (`OBase α`) put `coordPerm A x = (A.v k · x)_k`.  Then

    frame A s = I^n • core (coordPerm A) s        (`frame_core`)

and `InSub (coordPerm A) s x ↔ ∀ k ∉ s, A.v k · x = 0` holds by definition.  So every frame of
the old label calculus is a representative of the new one, up to the free scalar `I^n`.
No `sorry`.
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving.GF
open Binary Matrix Finset Complex
noncomputable section
section
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- coordinates in an orthonormal basis, as an additive bijection. -/
def coordPerm (A : OBase α) : APerm α where
  π := { toFun := fun x k => dot (A.v k) x
         invFun := fun c => ∑ k, c k • A.v k
         left_inv := by
           intro x
           show ∑ k, dot (A.v k) x • A.v k = x
           exact A.proj_univ x
         right_inv := by
           intro c
           funext j
           show dot (A.v j) (∑ k, c k • A.v k) = c j
           rw [dot_sum]
           simp [A.rows] }
  add := by
    intro x y
    funext k
    show dot (A.v k) (x + y) = dot (A.v k) x + dot (A.v k) y
    exact dot_add_right _ _ _

lemma coordPerm_v (A : OBase α) (i : α) : (coordPerm A).π (A.v i) = eu i := by
  funext k
  show dot (A.v k) (A.v i) = eu i k
  rw [A.rows]
  by_cases h : k = i
  · subst h; simp [eu]
  · have h' : ¬ i = k := fun h' => h h'.symm
    simp [eu, h, h']

lemma lum_eu (i : α) : lum (eu i : Space α) = I := by
  have h : ∀ k, tint (eu i k) = if i = k then I else 1 := by
    intro k
    by_cases hk : i = k <;> simp [eu, tint, hk]
  simp only [lum, h, Finset.prod_ite_eq, mem_univ, if_true]

lemma kg_shift_kg (A : OBase α) (i : α) :
    kg (coordPerm A) * shift (eu i) * kg (apInv (coordPerm A))
      = (I / lum (A.v i)) • shift (A.v i) := by
  ext x y
  rw [mul_kg_inv_apply, kg_mul_apply]
  simp only [shift, Matrix.smul_apply, smul_eq_mul]
  have hG := coordPerm_v A i
  have hiff : (coordPerm A).π x + eu i = (coordPerm A).π y ↔ x + A.v i = y := by
    rw [← hG, ← (coordPerm A).add]
    exact (coordPerm A).π.injective.eq_iff
  by_cases h : x + A.v i = y
  · rw [if_pos (hiff.2 h), if_pos h]
    subst h
    have h2 : dot ((coordPerm A).π x) (eu i) = dot x (A.v i) := by
      rw [dot_eu_right]; exact dot_symm _ _
    rw [(coordPerm A).add, hG, lum_add, lum_add, lum_eu, h2]
    have hx := lum_nonzero x
    have hgx := lum_nonzero ((coordPerm A).π x)
    have hv := lum_nonzero (A.v i)
    have hs := sign_ne_zero (dot x (A.v i))
    field_simp
  · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]
    simp

lemma kg_dir_kg (A : OBase α) (i : α) :
    kg (coordPerm A) * dir (eu i) * kg (apInv (coordPerm A))
      = ca • (1 : CMat α) + cb • ((I / lum (A.v i)) • shift (A.v i)) := by
  unfold dir
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    kg_mul_inv, Matrix.mul_smul, Matrix.smul_mul, kg_shift_kg]

lemma negI_ca : -I * ca = cb := by
  unfold ca cb
  linear_combination (-1 / 2 : ℂ) * Complex.I_sq

lemma I_cb : I * cb = ca := by
  unfold ca cb
  linear_combination (-1 / 2 : ℂ) * Complex.I_sq

/-- one line: the old one-line change is the new one up to a power of `I`. -/
lemma step_scalar (A : OBase α) (i : α) :
    ∃ n : ℕ, delta (A.v i)
      = (I ^ n) • (kg (coordPerm A) * dir (eu i) * kg (apInv (coordPerm A))) := by
  rcases lum_of_unit (A.v i) (A.self i) with h|h
  · refine ⟨0, ?_⟩
    rw [kg_dir_kg, h, delta_pos _ h, div_self Complex.I_ne_zero, pow_zero, one_smul, one_smul]
    rfl
  · refine ⟨3, ?_⟩
    have hI3 : (I : ℂ) ^ 3 = -I := by
      rw [pow_succ, pow_two, Complex.I_mul_I]; ring
    have hdiv : I / -I = (-1 : ℂ) := by
      rw [div_neg, div_self Complex.I_ne_zero]
    rw [kg_dir_kg, h, delta_neg _ h, hI3, hdiv]
    unfold dir
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one, shift_sq, smul_add,
      smul_smul, smul_smul, smul_smul, negI_ca]
    have e : -I * cb * -1 = ca := by rw [mul_neg_one, neg_mul, neg_neg, I_cb]
    rw [e, add_comm]

lemma core_insert (G : APerm α) {i : α} {s : Finset α} (hi : i ∉ s) :
    core G (insert i s) = kg G * dir (eu i) * kg (apInv G) * core G s := by
  have h1 : pk ({i} : Finset α) = dir (eu i) := by
    rw [dir_phase, pk]
    congr 1
    funext x
    simp
  have h2 : pk (insert i s) = pk {i} * pk s := by
    rw [← pk_union _ _ (Finset.disjoint_singleton_left.mpr hi), Finset.insert_eq]
  rw [core, core, h2, h1]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (kg (apInv G)) (kg G), kg_inv_mul, Matrix.one_mul]

/-- **Every old frame is a representative, up to a power of `I`.** -/
theorem frame_core (A : OBase α) (s : Finset α) :
    ∃ n : ℕ, frame A s = (I ^ n) • core (coordPerm A) s := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by rw [frame_zero, core_empty, pow_zero, one_smul]⟩
  | insert i s hi ih =>
    obtain ⟨n, hn⟩ := ih
    obtain ⟨m, hm⟩ := step_scalar A i
    refine ⟨m + n, ?_⟩
    rw [frame_ins A s i hi, hn, hm, core_insert _ hi, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, ← pow_add]

theorem frame_core_free (A : OBase α) (s : Finset α) :
    ∃ N, Free N ∧ frame A s = N * core (coordPerm A) s := by
  obtain ⟨n, hn⟩ := frame_core A s
  exact ⟨(I ^ n) • (1 : CMat α), free_scalar n, by rw [Matrix.smul_mul, Matrix.one_mul]; exact hn⟩

/-- membership in the subspace of an old frame, spelled out. -/
lemma insub_coordPerm (A : OBase α) (s : Finset α) (x : Space α) :
    InSub (coordPerm A) s x ↔ ∀ k, k ∉ s → dot (A.v k) x = 0 := Iff.rfl

end
end
end PowerSaving.GF
end OAI

#print axioms OAI.PowerSaving.GF.frame_core
#print axioms OAI.PowerSaving.GF.frame_core_free
