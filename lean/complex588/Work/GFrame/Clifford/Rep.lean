import Work.GFrame.Clifford.Entry

/-!
# GFrame / Clifford, part 6 (STAGE B): two representatives of the SAME subspace

(agent key: eng-clifford)

If `(G, s)` and `(G', s')` name the same subspace `U`, then

    core G' s' = repMat G G' s * core G s,

where `repMat` is MONOMIAL: `(repMat *ᵥ v) x = n(x) v(x + p(x))` with

    p(x) = ∑_{k ∈ s} ((G x)_k + G'x · G'v_k) v_k        (v_k = G⁻¹ e_k, the basis of `U`),
    n(x) = (lum (p x))⁻¹ (-1)^(x · p x + G'x · G'(p x)).

This is the "Clifford elimination" step of the outside note, with the adapter written down.
`RepFree.lean` shows that `repMat` is free.  No `sorry`.
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving.GF
open Binary Matrix Finset Complex
noncomputable section
section
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- the `k`-th basis vector of the base `G`. -/
def bvec (G : APerm α) (k : α) : Space α := (apInv G).π (eu k)

@[simp] lemma G_bvec (G : APerm α) (k : α) : G.π (bvec G k) = eu k := by simp [bvec]

/-- the address correction of the change of representative. -/
def repP (G G' : APerm α) (s : Finset α) (x : Space α) : Space α :=
  ∑ k ∈ s, (G.π x k + dot (G'.π x) (G'.π (bvec G k))) • bvec G k

/-- the phase of the change of representative. -/
def repN (G G' : APerm α) (s : Finset α) (x : Space α) : ℂ :=
  (lum (repP G G' s x))⁻¹
    * sign (dot x (repP G G' s x) + dot (G'.π x) (G'.π (repP G G' s x)))

/-- the adapter between two representatives of one subspace. -/
def repMat (G G' : APerm α) (s : Finset α) : CMat α :=
  fun x y => if x + repP G G' s x = y then repN G G' s x else 0

lemma G_sum_bvec (G : APerm α) (s : Finset α) (c : α → F) (k : α) :
    G.π (∑ j ∈ s, c j • bvec G j) k = if k ∈ s then c k else 0 := by
  rw [G.map_sum']
  simp only [G.map_smul', G_bvec, Finset.sum_apply, Pi.smul_apply, eu, smul_eq_mul, mul_ite,
    mul_one, mul_zero]
  rw [Finset.sum_ite_eq']

lemma G_repP (G G' : APerm α) (s : Finset α) (x : Space α) (k : α) :
    G.π (repP G G' s x) k
      = if k ∈ s then G.π x k + dot (G'.π x) (G'.π (bvec G k)) else 0 :=
  G_sum_bvec G s _ k

lemma insub_repP (G G' : APerm α) (s : Finset α) (x : Space α) :
    InSub G s (repP G G' s x) := by
  intro k hk
  rw [G_repP, if_neg hk]

/-- a vector of the subspace, expanded in the base. -/
lemma insub_expand (G : APerm α) (s : Finset α) (u : Space α) (hu : InSub G s u) :
    u = ∑ k ∈ s, G.π u k • bvec G k := by
  apply G.π.injective
  funext j
  rw [G_sum_bvec]
  by_cases hj : j ∈ s
  · rw [if_pos hj]
  · rw [if_neg hj, hu j hj]

/-- **Key relation**: on the subspace, `G p(x) · G u = G x · G u + G' x · G' u`. -/
lemma repP_key (G G' : APerm α) (s : Finset α) (x u : Space α) (hu : InSub G s u) :
    dot (G.π (repP G G' s x)) (G.π u) = dot (G.π x) (G.π u) + dot (G'.π x) (G'.π u) := by
  have h1 : dot (G.π (repP G G' s x)) (G.π u)
      = ∑ k ∈ s, (G.π x k + dot (G'.π x) (G'.π (bvec G k))) * G.π u k := by
    change ∑ k, G.π (repP G G' s x) k * G.π u k = _
    simp only [G_repP, ite_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have h2 : dot (G.π x) (G.π u) = ∑ k ∈ s, G.π x k * G.π u k := by
    unfold dot
    symm
    apply Finset.sum_subset (Finset.subset_univ s)
    intro k _ hk
    rw [hu k hk, mul_zero]
  have h3 : dot (G'.π x) (G'.π u)
      = ∑ k ∈ s, dot (G'.π x) (G'.π (bvec G k)) * G.π u k := by
    have e := insub_expand G s u hu
    calc dot (G'.π x) (G'.π u)
        = dot (G'.π x) (G'.π (∑ k ∈ s, G.π u k • bvec G k)) := by rw [← e]
      _ = ∑ k ∈ s, dot (G'.π x) (G'.π (bvec G k)) * G.π u k := by
          rw [G'.map_sum', dot_sum]
          apply Finset.sum_congr rfl
          intro k _
          rw [G'.map_smul', dot_smul_right, mul_comm]
  rw [h1, h2, h3, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma repMat_mul_apply (G G' : APerm α) (s : Finset α) (M : CMat α) (x y : Space α) :
    (repMat G G' s * M) x y = repN G G' s x * M (x + repP G G' s x) y := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (x + repP G G' s x)]
  · simp [repMat]
  · intro b _ hb
    simp [repMat, Ne.symm hb]
  · intro h; exact absurd (mem_univ _) h

lemma F_four (a b c d : F) : a + b + (a + c + (b + d)) = c + d := by
  revert a b c d; decide

lemma F_three (a b c : F) : a + c = b + (a + b + c) := by
  revert a b c; decide

/-- **Change of representative** (matrix identity). -/
theorem rep_change_eq (G G' : APerm α) (s s' : Finset α)
    (h : ∀ x, InSub G s x ↔ InSub G' s' x) (hc : s.card = s'.card) :
    core G' s' = repMat G G' s * core G s := by
  ext x y
  rw [repMat_mul_apply, core_apply, core_apply]
  have hpU := insub_repP G G' s x
  have key := fun u hu => repP_key G G' s x u hu
  simp only [repN]
  generalize repP G G' s x = p at hpU key ⊢
  have e1 : x + p + y = p + (x + y) := by abel
  have e2 : x + y = p + (x + p + y) := by
    funext k
    simp only [Pi.add_apply]
    exact F_three _ _ _
  by_cases hu : InSub G' s' (x + y)
  · have hu' : InSub G s (x + y) := (h _).2 hu
    have hin : InSub G s (x + p + y) := by rw [e1]; exact insub_add G s hpU hu'
    rw [if_pos hu, if_pos hin]
    have k1 := key (x + y) hu'
    have k2 := key p hpU
    have hdot : dot (G.π (x + p)) (G.π (x + p + y))
        = dot (G'.π x) (G'.π p) + dot (G'.π x) (G'.π (x + y)) := by
      rw [e1, G.add x p, G.add p (x + y), dot_add_left, dot_add_right, dot_add_right, k1, k2]
      exact F_four _ _ _ _
    rw [hdot, sign_add, sign_add, lum_add, ← hc]
    have hp := lum_nonzero p
    calc ca ^ s.card * (lum x / lum y) * sign (dot (G'.π x) (G'.π (x + y)))
        = ca ^ s.card * (lum x / lum y) * sign (dot (G'.π x) (G'.π (x + y)))
            * ((lum p)⁻¹ * lum p) * (sign (dot x p) * sign (dot x p))
            * (sign (dot (G'.π x) (G'.π p)) * sign (dot (G'.π x) (G'.π p))) := by
          rw [inv_mul_cancel₀ hp, sign_sq, sign_sq]; ring
      _ = _ := by ring
  · have hu' : ¬ InSub G s (x + y) := fun h' => hu ((h _).1 h')
    have hin : ¬ InSub G s (x + p + y) := by
      intro h'
      apply hu'
      rw [e2]
      exact insub_add G s hpU h'
    rw [if_neg hu, if_neg hin, mul_zero]

end
end
end PowerSaving.GF
end OAI

#print axioms OAI.PowerSaving.GF.rep_change_eq
