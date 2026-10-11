import Work.GFrame.Clifford.RepFree

/-!
# GFrame / Clifford, part 8 (STAGE B): the frame lemma for representatives; the gate rule

(agent key: eng-clifford)

* `same_card`     two names of one subspace have the same number of coordinates (dimension);
* `rep_change`    same subspace ⇒ `core G' s' = N * core G s` with `N` free;
* `climb_any`     **nested step between ARBITRARY representatives**: if `(G₀, s₀ ⊆ t₀)` is a base
                  adapted to both subspaces, then `core G' t = A * blockMat z * B * core G s`
                  with `A`, `B` free and `z` of rank `|t₀ \ s₀| = dim V - dim U` (`climb_rank`);
* `core_eq_iff`   **gate rule**: two representatives are the SAME matrix iff they name the same
                  subspace `U` and the forms `(x, u) ↦ G x · G u` agree on `Space α × U`.
No `sorry`.
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving.GF
open Binary Matrix Finset Complex
noncomputable section
section
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- coordinate vectors supported on `s` are the functions on `s`. -/
def supEquiv (s : Finset α) : {c : Space α // ∀ k, k ∉ s → c k = 0} ≃ (s → F) where
  toFun c := fun k => c.1 k.1
  invFun d := ⟨fun k => if hk : k ∈ s then d ⟨k, hk⟩ else 0, fun k hk => by simp [hk]⟩
  left_inv c := by
    apply Subtype.ext
    funext k
    by_cases hk : k ∈ s
    · simp [hk]
    · simp [hk, c.2 k hk]
  right_inv d := by
    funext k
    simp

lemma insub_card (G : APerm α) (s : Finset α) :
    Fintype.card {x // InSub G s x} = 2 ^ s.card := by
  have e1 : {x // InSub G s x} ≃ {c : Space α // ∀ k, k ∉ s → c k = 0} :=
    Equiv.subtypeEquiv G.π (fun x => Iff.rfl)
  rw [Fintype.card_congr (e1.trans (supEquiv s))]
  simp [ZMod.card]

/-- two names of one subspace have the same dimension. -/
theorem same_card {G G' : APerm α} {s s' : Finset α}
    (h : ∀ x, InSub G s x ↔ InSub G' s' x) : s.card = s'.card := by
  have e := Fintype.card_congr (Equiv.subtypeEquivRight h)
  rw [insub_card, insub_card] at e
  exact Nat.pow_right_injective (le_refl 2) e

/-- **Change of representative**: same subspace ⇒ a free left adapter. -/
theorem rep_change (G G' : APerm α) (s s' : Finset α)
    (h : ∀ x, InSub G s x ↔ InSub G' s' x) :
    ∃ N, Free N ∧ core G' s' = N * core G s :=
  ⟨repMat G G' s, free_repMat G G' s s' h, rep_change_eq G G' s s' h (same_card h)⟩

/-- **The frame lemma for arbitrary representatives of nested subspaces.** -/
theorem climb_any (G G' G₀ : APerm α) (s t s₀ t₀ : Finset α)
    (h1 : ∀ x, InSub G s x ↔ InSub G₀ s₀ x) (h2 : ∀ x, InSub G₀ t₀ x ↔ InSub G' t x)
    (hst : s₀ ⊆ t₀) :
    ∃ (A B : CMat α) (z : Fin (t₀ \ s₀).card → Space α), Free A ∧ Free B ∧
      LinearIndependent F z ∧ core G' t = A * blockMat z * B * core G s := by
  have r1 := rep_change_eq G G₀ s s₀ h1 (same_card h1)
  have r2 := rep_change_eq G₀ G' t₀ t h2 (same_card h2)
  refine ⟨repMat G₀ G' t₀ * kg G₀, kg (apInv G₀) * repMat G G₀ s, _,
    Free.mul (free_repMat _ _ _ _ h2) (free_kg _), Free.mul (free_kg _) (free_repMat _ _ _ _ h1),
    (OBase.canonical α).fam_indep _, ?_⟩
  rw [r2, core_nested G₀ hst, r1]
  simp only [Matrix.mul_assoc]

/-- the rank of the block of `climb_any` is the difference of the dimensions. -/
theorem climb_rank {G G' G₀ : APerm α} {s t s₀ t₀ : Finset α}
    (h1 : ∀ x, InSub G s x ↔ InSub G₀ s₀ x) (h2 : ∀ x, InSub G₀ t₀ x ↔ InSub G' t x)
    (hst : s₀ ⊆ t₀) : (t₀ \ s₀).card = t.card - s.card := by
  rw [Finset.card_sdiff_of_subset hst, same_card h1, same_card h2]

lemma sign_ne_zero (t : F) : sign t ≠ 0 := by
  rcases bit_cases t with rfl|rfl <;> simp [sign]

lemma sign_inj {a b : F} (h : sign a = sign b) : a = b := by
  rcases bit_cases a with rfl|rfl <;> rcases bit_cases b with rfl|rfl <;>
    simp [sign] at h ⊢
  all_goals
    have h' := congrArg Complex.re h
    norm_num at h'

lemma ca_ne_zero : ca ≠ 0 := by
  intro h
  have h' := congrArg Complex.re h
  simp [ca] at h'

lemma core_ne_zero_iff (G : APerm α) (s : Finset α) (x y : Space α) :
    core G s x y ≠ 0 ↔ InSub G s (x + y) := by
  rw [core_apply]
  by_cases h : InSub G s (x + y)
  · rw [if_pos h]
    simp only [h, iff_true]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ ca_ne_zero)
      (div_ne_zero (lum_nonzero x) (lum_nonzero y))) (sign_ne_zero _)
  · rw [if_neg h]
    simp [h]

/-- **Gate rule**: when two representatives are IDENTICAL matrices. -/
theorem core_eq_iff (G G' : APerm α) (s s' : Finset α) :
    core G s = core G' s' ↔
      (∀ x, InSub G s x ↔ InSub G' s' x) ∧
      ∀ x u, InSub G s u → dot (G.π x) (G.π u) = dot (G'.π x) (G'.π u) := by
  constructor
  · intro h
    have hsub : ∀ x, InSub G s x ↔ InSub G' s' x := by
      intro x
      have e : (0 : Space α) + x = x := zero_add x
      rw [← e, ← core_ne_zero_iff, ← core_ne_zero_iff, h]
    refine ⟨hsub, fun x u hu => ?_⟩
    have hu' : InSub G' s' u := (hsub u).1 hu
    have e := congrFun (congrFun h x) (x + u)
    have exu : x + (x + u) = u := by rw [← add_assoc, binary_cancel, zero_add]
    rw [core_apply, core_apply, exu, if_pos hu, if_pos hu', same_card hsub] at e
    have hne : ca ^ s'.card * (lum x / lum (x + u)) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ ca_ne_zero)
        (div_ne_zero (lum_nonzero x) (lum_nonzero (x + u)))
    exact sign_inj (mul_left_cancel₀ hne e)
  · rintro ⟨hsub, hb⟩
    ext x y
    rw [core_apply, core_apply]
    by_cases hu : InSub G s (x + y)
    · rw [if_pos hu, if_pos ((hsub _).1 hu), hb x (x + y) hu, same_card hsub]
    · rw [if_neg hu, if_neg (fun h' => hu ((hsub _).2 h'))]

end
end
end PowerSaving.GF
end OAI

#print axioms OAI.PowerSaving.GF.rep_change
#print axioms OAI.PowerSaving.GF.climb_any
#print axioms OAI.PowerSaving.GF.climb_rank
#print axioms OAI.PowerSaving.GF.core_eq_iff
