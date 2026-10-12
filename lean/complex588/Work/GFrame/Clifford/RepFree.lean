import Work.GFrame.Clifford.Rep

/-!
# GFrame / Clifford, part 7 (STAGE B): the adapter between two representatives is FREE

(agent key: eng-clifford)

* `free_tint_fun`, `free_sign_mul_fun`, `free_sign_dot`, `free_lum_comp`
                   diagonal phases built from additive maps are free;
* `repP_add`, `repP_inj`, `repPerm`   `x ↦ x + p(x)` is an additive bijection;
* `free_repMat`    `repMat G G' s` is free;
* `rep_change`     **same subspace ⇒ the two representatives differ by a free left adapter.**
No `sorry`.
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving.GF
open Binary Matrix Finset Complex
noncomputable section
section
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- additive functionals of the label space. -/
def IsAddF (f : Space α → F) : Prop := ∀ x y, f (x + y) = f x + f y
/-- additive maps of the label space. -/
def IsAddM (P : Space α → Space α) : Prop := ∀ x y, P (x + y) = P x + P y

lemma F_cancel_left (a b : F) (h : a = a + b) : b = 0 := by
  revert a b; decide

lemma eq_of_add_eq_zero' (a b : Space α) (h : a + b = 0) : a = b := by
  calc a = a + (b + b) := by rw [binary_cancel, add_zero]
    _ = (a + b) + b := by abel
    _ = b := by rw [h, zero_add]

namespace IsAddF
variable {f g : Space α → F}

lemma zero (hf : IsAddF f) : f 0 = 0 := by
  have h := hf 0 0
  rw [add_zero] at h
  exact F_cancel_left _ _ h

lemma sum {κ : Type*} (hf : IsAddF f) (s : Finset κ) (v : κ → Space α) :
    f (∑ j ∈ s, v j) = ∑ j ∈ s, f (v j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hf.zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hf, ih]

lemma smul (hf : IsAddF f) (a : F) (x : Space α) : f (a • x) = a * f x := by
  rcases bit_cases a with rfl|rfl <;> simp [hf.zero]

lemma eq_dot (hf : IsAddF f) (x : Space α) : f x = dot (fun j => f (eu j)) x := by
  conv_lhs => rw [space_eq_sum x, hf.sum]
  simp only [hf.smul, dot]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma add (hf : IsAddF f) (hg : IsAddF g) : IsAddF (fun x => f x + g x) := by
  intro x y
  simp only [hf x y, hg x y]
  ring

end IsAddF

lemma IsAddM.coord {P : Space α → Space α} (hP : IsAddM P) (i : α) :
    IsAddF (fun x => P x i) := fun x y => by
  show P (x + y) i = P x i + P y i
  rw [hP]; rfl

lemma IsAddM.comp {P Q : Space α → Space α} (hP : IsAddM P) (hQ : IsAddM Q) :
    IsAddM (fun x => P (Q x)) := fun x y => by
  show P (Q (x + y)) = P (Q x) + P (Q y)
  rw [hQ, hP]

lemma free_tint_fun {f : Space α → F} (hf : IsAddF f) :
    Free (diagonal fun x => tint (f x)) := by
  have e : (fun x => tint (f x)) = fun x => tint (dot (fun j => f (eu j)) x + 0) := by
    funext x; rw [add_zero, ← hf.eq_dot]
  rw [e]; exact free_diag_tint _ _

lemma free_sign_fun {f : Space α → F} (hf : IsAddF f) :
    Free (diagonal fun x => sign (f x)) := by
  have h := free_diag_mul (free_tint_fun hf) (free_tint_fun hf)
  simpa [tint_sq] using h

lemma free_sign_mul_fun {f g : Space α → F} (hf : IsAddF f) (hg : IsAddF g) :
    Free (diagonal fun x => sign (f x * g x)) := by
  have h := free_diag_mul (free_diag_mul (free_tint_fun hf) (free_tint_fun hg))
    (free_diag_mul (free_tint_fun (hf.add hg)) (free_sign_fun (hf.add hg)))
  have e : (fun x => sign (f x * g x))
      = fun x => tint (f x) * tint (g x) * (tint (f x + g x) * sign (f x + g x)) := by
    funext x; exact sign_mul_bits _ _
  rw [e]; exact h

lemma free_sign_dot {P Q : Space α → Space α} (hP : IsAddM P) (hQ : IsAddM Q) :
    Free (diagonal fun x => sign (dot (P x) (Q x))) := by
  have e : (fun x => sign (dot (P x) (Q x))) = fun x => ∏ i ∈ univ, sign (P x i * Q x i) := by
    funext x; rw [dot, sign_sum]
  rw [e]
  exact free_diag_prod univ _ (fun i _ => free_sign_mul_fun (hP.coord i) (hQ.coord i))

lemma free_lum_comp {P : Space α → Space α} (hP : IsAddM P) :
    Free (diagonal fun x => lum (P x)) := by
  have e : (fun x => lum (P x)) = fun x => ∏ i ∈ univ, tint (P x i) := by
    funext x; rfl
  rw [e]
  exact free_diag_prod univ _ (fun i _ => free_tint_fun (hP.coord i))

lemma free_lum_inv_comp {P : Space α → Space α} (hP : IsAddM P) :
    Free (diagonal fun x => (lum (P x))⁻¹) := by
  rw [show (fun x => (lum (P x))⁻¹) = fun x => lum (P x) ^ 3 from funext fun x => lum_inv _]
  exact free_diag_pow (free_lum_comp hP) 3

lemma repP_add (G G' : APerm α) (s : Finset α) : IsAddM (repP G G' s) := by
  intro x y
  unfold repP
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [G.add, G'.add, Pi.add_apply, dot_add_left, ← add_smul]
  congr 1
  ring

lemma free_repN (G G' : APerm α) (s : Finset α) : Free (diagonal (repN G G' s)) := by
  have hp := repP_add G G' s
  have hid : IsAddM (fun x : Space α => x) := fun _ _ => rfl
  have hG' : IsAddM G'.π := G'.add
  have h := free_diag_mul (free_lum_inv_comp hp)
    (free_diag_mul (free_sign_dot hid hp) (free_sign_dot hG' (hG'.comp hp)))
  have e : repN G G' s = fun x => (lum (repP G G' s x))⁻¹ *
      (sign (dot x (repP G G' s x)) * sign (dot (G'.π x) (G'.π (repP G G' s x)))) := by
    funext x; rw [repN, sign_add]
  rw [e]; exact h

lemma insub_bvec (G : APerm α) (s : Finset α) {j : α} (hj : j ∈ s) : InSub G s (bvec G j) := by
  intro k hk
  rw [G_bvec]
  have : ¬ j = k := fun h => hk (h ▸ hj)
  simp [eu, this]

lemma repP_inj (G G' : APerm α) (s s' : Finset α) (h : ∀ x, InSub G s x ↔ InSub G' s' x) :
    Function.Injective (fun x => x + repP G G' s x) := by
  intro x x' hxx
  have hxx' : x + repP G G' s x = x' + repP G G' s x' := hxx
  obtain ⟨w, hw⟩ : ∃ w, w = x + x' := ⟨_, rfl⟩
  have hw0 : w + repP G G' s w = 0 := by
    rw [hw, repP_add G G' s x x']
    have e : x + x' + (repP G G' s x + repP G G' s x')
        = (x + repP G G' s x) + (x' + repP G G' s x') := by abel
    rw [e, hxx']
    exact binary_cancel _
  have hwp : w = repP G G' s w := eq_of_add_eq_zero' _ _ hw0
  have hwU : InSub G s w := by rw [hwp]; exact insub_repP G G' s w
  have hwU' : InSub G' s' w := (h w).1 hwU
  have horth : ∀ u, InSub G s u → dot (G'.π w) (G'.π u) = 0 := by
    intro u hu
    have k := repP_key G G' s w u hu
    rw [← hwp] at k
    exact F_cancel_left _ _ k
  have hz : G'.π w = 0 := by
    funext j
    by_cases hj : j ∈ s'
    · have hb := horth (bvec G' j) ((h _).2 (insub_bvec G' s' hj))
      rw [G_bvec, dot_eu_right] at hb
      exact hb
    · exact hwU' j hj
  have hw00 : w = 0 := G'.π.injective (by rw [hz, G'.map_zero'])
  rw [hw00] at hw
  exact eq_of_add_eq_zero' _ _ hw.symm

/-- the address map of the change of representative. -/
def repPerm (G G' : APerm α) (s s' : Finset α) (h : ∀ x, InSub G s x ↔ InSub G' s' x) :
    APerm α where
  π := Equiv.ofBijective (fun x => x + repP G G' s x)
    (Finite.injective_iff_bijective.mp (repP_inj G G' s s' h))
  add := by
    intro x y
    change (x + y) + repP G G' s (x + y) = (x + repP G G' s x) + (y + repP G G' s y)
    rw [repP_add G G' s x y]
    abel

lemma repMat_eq (G G' : APerm α) (s s' : Finset α) (h : ∀ x, InSub G s x ↔ InSub G' s' x) :
    repMat G G' s = diagonal (repN G G' s) * permMat (repPerm G G' s s' h) := by
  ext x y
  rw [Matrix.diagonal_mul]
  have e : (repPerm G G' s s' h).π x = x + repP G G' s x := rfl
  simp only [repMat, permMat, e]
  split_ifs <;> simp

theorem free_repMat (G G' : APerm α) (s s' : Finset α)
    (h : ∀ x, InSub G s x ↔ InSub G' s' x) : Free (repMat G G' s) := by
  rw [repMat_eq G G' s s' h]
  exact Free.mul (free_repN G G' s) (Free.perm _)

end
end
end PowerSaving.GF
end OAI

#print axioms OAI.PowerSaving.GF.free_repMat
