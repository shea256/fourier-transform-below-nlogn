import Work.GFrame.Clifford.Base

/-!
# GFrame / Clifford, part 12 (STAGE B): any two subspaces of one base; the complement rule

(agent key: eng-clifford)

* `core_cross`      in ONE base, for ANY two coordinate sets `s`, `t` (nested or not, up or down):
                    `core G t = kg G * shift _ * pk (s Δ t) * kg G⁻¹ * core G s`:
                    ONE block of rank `|s Δ t| = dim U + dim V - 2 dim (U ∩ V)`;
* `cross_any`       the same between ARBITRARY representatives, given a base naming both;
* `frame_lemma_down` the nested step DOWNWARDS, arbitrary representatives, unconditional;
* `kernel_mul_core` the complement rule: `kernel α * core G s = N * core G sᶜ`, `N` free
                    (the outside note's "F T_U has the label of the complement V_U").
No `sorry`.
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving.GF
open Binary Matrix Finset Complex
noncomputable section
section
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- indicator vector of a set of coordinates. -/
def ones (d : Finset α) : Space α := fun k => if k ∈ d then 1 else 0

lemma dot_ones (d : Finset α) (x : Space α) : dot (ones d) x = ∑ k ∈ d, x k := by
  simp only [dot, ones, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

lemma shift_pk_comm (z : Space α) (d : Finset α) : shift z * pk d = pk d * shift z := by
  rw [shift_phase, pk]; exact wrap_comm _ _

lemma pk_mul_self (d : Finset α) : pk d * pk d = shift (ones d) := by
  rw [pk, wrap_mul, shift_phase]
  congr 1
  funext x
  rw [dot_ones, sign_sum, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k _
  rw [tint_sq]

/-- the kernels of two coordinate sets differ by the kernel of the symmetric difference. -/
lemma pk_cross (s t : Finset α) :
    pk t = shift (ones (s \ t)) * pk ((s \ t) ∪ (t \ s)) * pk s := by
  unfold pk
  rw [shift_phase, wrap_mul, wrap_mul]
  congr 1
  funext x
  have h1 : sign (dot (ones (s \ t)) x)
      * ((∏ k ∈ s \ t, tint (x k)) * (∏ k ∈ s \ t, tint (x k))) = 1 := by
    rw [dot_ones, sign_sum, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro k _
    rw [tint_sq, sign_sq]
  have hd : Disjoint (s \ t) (t \ s) := disjoint_sdiff_sdiff
  have ht : ∏ k ∈ t, tint (x k) = (∏ k ∈ t \ s, tint (x k)) * ∏ k ∈ s ∩ t, tint (x k) := by
    rw [Finset.inter_comm, ← Finset.prod_union (Finset.disjoint_sdiff_inter t s),
      Finset.sdiff_union_inter]
  have hs : ∏ k ∈ s, tint (x k) = (∏ k ∈ s \ t, tint (x k)) * ∏ k ∈ s ∩ t, tint (x k) := by
    rw [← Finset.prod_union (Finset.disjoint_sdiff_inter s t), Finset.sdiff_union_inter]
  rw [Finset.prod_union hd, ht, hs]
  linear_combination (-((∏ k ∈ t \ s, tint (x k)) * ∏ k ∈ s ∩ t, tint (x k))) * h1

/-- **Any two subspaces named in ONE base**: one block on the symmetric difference. -/
theorem core_cross (G : APerm α) (s t : Finset α) :
    core G t = (kg G * shift (ones (s \ t)))
      * blockMat ((OBase.canonical α).fam ((s \ t) ∪ (t \ s))) * kg (apInv G) * core G s := by
  rw [← pk_eq_blockMat, core, core, pk_cross s t]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (kg (apInv G)) (kg G), kg_inv_mul, Matrix.one_mul]

/-- **Any two subspaces, any representatives**, given a base naming both: ONE block of rank
`|s₀ Δ t₀|`. -/
theorem cross_any (G G' G₀ : APerm α) (s t s₀ t₀ : Finset α)
    (h1 : ∀ x, InSub G s x ↔ InSub G₀ s₀ x) (h2 : ∀ x, InSub G₀ t₀ x ↔ InSub G' t x) :
    ∃ (A B : CMat α) (z : Fin ((s₀ \ t₀) ∪ (t₀ \ s₀)).card → Space α), Free A ∧ Free B ∧
      LinearIndependent F z ∧ core G' t = A * blockMat z * B * core G s := by
  have r1 := rep_change_eq G G₀ s s₀ h1 (same_card h1)
  have r2 := rep_change_eq G₀ G' t₀ t h2 (same_card h2)
  refine ⟨repMat G₀ G' t₀ * (kg G₀ * shift (ones (s₀ \ t₀))), kg (apInv G₀) * repMat G G₀ s, _,
    Free.mul (free_repMat _ _ _ _ h2) (Free.mul (free_kg _) (Free.shift _)),
    Free.mul (free_kg _) (free_repMat _ _ _ _ h1), (OBase.canonical α).fam_indep _, ?_⟩
  rw [r2, core_cross G₀ s₀ t₀, r1]
  simp only [Matrix.mul_assoc]

/-- **The frame lemma, downwards**: for nested subspaces `U ⊆ V` and arbitrary representatives,
the step from `V` to `U` is ONE block of rank `dim V - dim U` between free adapters. -/
theorem frame_lemma_down (G G' : APerm α) (s t : Finset α)
    (h : ∀ x, InSub G s x → InSub G' t x) :
    ∃ (A B : CMat α) (z : Fin (t.card - s.card) → Space α), Free A ∧ Free B ∧
      LinearIndependent F z ∧ core G s = A * blockMat z * B * core G' t := by
  obtain ⟨G₀, s₀, t₀, hst, h1, h2⟩ := exists_common_base G G' s t h
  have hset : (t₀ \ s₀) ∪ (s₀ \ t₀) = t₀ \ s₀ := by
    rw [Finset.sdiff_eq_empty_iff_subset.mpr hst, Finset.union_empty]
  have key : ∀ r, ((t₀ \ s₀) ∪ (s₀ \ t₀)).card = r → ∃ (A B : CMat α) (z : Fin r → Space α),
      Free A ∧ Free B ∧ LinearIndependent F z ∧ core G s = A * blockMat z * B * core G' t := by
    intro r hr
    subst hr
    exact cross_any G' G G₀ t s t₀ s₀ (fun x => (h2 x).symm) (fun x => (h1 x).symm)
  exact key _ (by rw [hset]; exact climb_rank h1 h2 hst)

/-- **The complement rule**: the kernel times a representative of `U` is a representative of
the complement named by the other coordinates of the same base, up to a free left factor. -/
theorem kernel_mul_core (G : APerm α) (s : Finset α) :
    ∃ N, Free N ∧ kernel α * core G s = N * core G sᶜ := by
  have htriv : ∀ x, InSub (apId α) univ x ↔ InSub G univ x := by
    intro x
    constructor <;> intro _ k hk <;> exact absurd (mem_univ k) hk
  obtain ⟨N₁, hN₁, e₁⟩ := rep_change (apId α) G univ univ htriv
  obtain ⟨N₁', hN₁', hl, -⟩ := free_inv hN₁
  have hk : kernel α = N₁' * core G univ := by
    rw [e₁, core_id_univ, ← Matrix.mul_assoc, hl, Matrix.one_mul]
  have hu : pk (univ : Finset α) = pk sᶜ * pk s := by
    rw [← pk_union _ _ disjoint_compl_left, Finset.union_comm, Finset.union_compl]
  have h2 : core G univ * core G s
      = kg G * shift (ones s) * kg (apInv G) * core G sᶜ := by
    rw [core, core, core, hu]
    have e : kg G * (pk sᶜ * pk s) * kg (apInv G) * (kg G * pk s * kg (apInv G))
        = kg G * (pk sᶜ * (pk s * ((kg (apInv G) * kg G) * pk s))) * kg (apInv G) := by
      simp only [Matrix.mul_assoc]
    rw [e, kg_inv_mul, Matrix.one_mul, pk_mul_self, ← shift_pk_comm]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (kg (apInv G)) (kg G), kg_inv_mul, Matrix.one_mul]
  refine ⟨N₁' * (kg G * shift (ones s) * kg (apInv G)),
    Free.mul hN₁' (Free.mul (Free.mul (free_kg G) (Free.shift _)) (free_kg _)), ?_⟩
  rw [hk, Matrix.mul_assoc, h2]
  simp only [Matrix.mul_assoc]

end
end
end PowerSaving.GF
end OAI

#print axioms OAI.PowerSaving.GF.core_cross
#print axioms OAI.PowerSaving.GF.cross_any
#print axioms OAI.PowerSaving.GF.frame_lemma_down
#print axioms OAI.PowerSaving.GF.kernel_mul_core
