import Work.GFrame.Clifford.Core

/-!
# GFrame / Clifford, part 5 (STAGE B): the entry formula of a representative

(agent key: eng-clifford)

* `pk_apply`     `pk s a b = [a = b off s] ca^|s| / lum (a + b)`;
* `core_apply`   `core G s x y = [x + y ∈ U] ca^|s| (lum x / lum y) (-1)^(G x · G (x + y))`.
No `sorry`.
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving.GF
open Binary Matrix Finset Complex
noncomputable section

lemma ca_div_I : ca / I = cb := by
  rw [div_eq_iff Complex.I_ne_zero]
  unfold ca cb
  linear_combination (1 / 2 : ℂ) * Complex.I_sq

lemma cb_eq : cb = -(ca * I) := by
  unfold ca cb
  linear_combination (1 / 2 : ℂ) * Complex.I_sq

lemma littleC_eq (a b : F) : littleC a b = ca / tint (a + b) := by
  rcases bit_cases a with rfl|rfl <;> rcases bit_cases b with rfl|rfl <;>
    simp [littleC, tint] <;> exact cb_eq

section
variable {α : Type*} [Fintype α] [DecidableEq α]

lemma pk_eq_digit (s : Finset α) :
    pk s = digitProd fun k => if k ∈ s then littleC else (1 : Matrix F F ℂ) := by
  unfold pk
  apply wrap_of
  have hd : diagonal (fun x : Space α => ∏ k ∈ s, tint (x k))
      = digitProd (fun k => diagonal (if k ∈ s then tint else fun _ => (1 : ℂ))) := by
    rw [digitProd_diagonal]
    congr 1
    funext x
    symm
    simp only [ite_apply]
    rw [Finset.prod_ite_mem, Finset.univ_inter]
  rw [hd]
  unfold wal
  rw [digitProd_mul, digitProd_mul]
  congr 1
  funext k
  split_ifs
  · exact little_phase
  · rw [Matrix.one_mul, Matrix.diagonal_one, Matrix.mul_one]

/-- **Entries of the kernel on the coordinates in `s`.** -/
lemma pk_apply (s : Finset α) (a b : Space α) :
    pk s a b = if (∀ k, k ∉ s → a k = b k) then ca ^ s.card / lum (a + b) else 0 := by
  rw [pk_eq_digit, digitProd_apply]
  by_cases h : ∀ k, k ∉ s → a k = b k
  · rw [if_pos h]
    have h1 : ∀ k, (if k ∈ s then littleC else (1 : Matrix F F ℂ)) (a k) (b k)
        = (if k ∈ s then ca else 1) / tint ((a + b) k) := by
      intro k
      by_cases hk : k ∈ s
      · simp only [if_pos hk, littleC_eq, Pi.add_apply]
      · have hab := h k hk
        simp [if_neg hk, hab, tint]
    simp only [h1]
    rw [Finset.prod_div_distrib, Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
    rfl
  · rw [if_neg h]
    push_neg at h
    obtain ⟨k, hk, hne⟩ := h
    apply Finset.prod_eq_zero (mem_univ k)
    simp [if_neg hk, Matrix.one_apply, hne]

lemma insub_add (G : APerm α) (s : Finset α) {a b : Space α} (ha : InSub G s a)
    (hb : InSub G s b) : InSub G s (a + b) := by
  intro k hk
  rw [G.add, Pi.add_apply, ha k hk, hb k hk, add_zero]

lemma insub_iff (G : APerm α) (s : Finset α) (x y : Space α) :
    (∀ k, k ∉ s → G.π x k = G.π y k) ↔ InSub G s (x + y) := by
  unfold InSub
  constructor
  · intro h k hk
    rw [G.add, Pi.add_apply, h k hk, cancel]
  · intro h k hk
    have h1 := h k hk
    rw [G.add, Pi.add_apply] at h1
    calc G.π x k = G.π x k + (G.π y k + G.π y k) := by rw [cancel, add_zero]
      _ = (G.π x k + G.π y k) + G.π y k := by ring
      _ = G.π y k := by rw [h1, zero_add]

/-- **Entry formula of a representative.** -/
theorem core_apply (G : APerm α) (s : Finset α) (x y : Space α) :
    core G s x y = if InSub G s (x + y) then
      ca ^ s.card * (lum x / lum y) * sign (dot (G.π x) (G.π (x + y))) else 0 := by
  rw [core, mul_kg_inv_apply, kg_mul_apply, pk_apply]
  by_cases h : InSub G s (x + y)
  · rw [if_pos ((insub_iff G s x y).2 h), if_pos h, G.add, lum_add, dot_add_right, sign_add]
    have hb := lum_nonzero (G.π y)
    have hA := lum_inv_sq (G.π x)
    have hs := inv_sign (dot (G.π x) (G.π y))
    calc lum x / lum (G.π x) * (ca ^ s.card /
            (lum (G.π x) * lum (G.π y) * sign (dot (G.π x) (G.π y)))) * (lum (G.π y) / lum y)
        = ca ^ s.card * (lum x / lum y) * (((lum (G.π x))⁻¹ * (lum (G.π x))⁻¹)
            * (sign (dot (G.π x) (G.π y)))⁻¹) * ((lum (G.π y))⁻¹ * lum (G.π y)) := by ring
      _ = ca ^ s.card * (lum x / lum y)
            * (sign (dot (G.π x) (G.π x)) * sign (dot (G.π x) (G.π y))) := by
          rw [hA, hs, inv_mul_cancel₀ hb, mul_one]
  · rw [if_neg (fun h' => h ((insub_iff G s x y).1 h')), if_neg h]
    simp

end
end
end PowerSaving.GF
end OAI

#print axioms OAI.PowerSaving.GF.pk_apply
#print axioms OAI.PowerSaving.GF.core_apply
