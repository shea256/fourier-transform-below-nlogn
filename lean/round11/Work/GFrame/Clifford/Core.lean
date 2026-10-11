import Work.GFrame.Clifford.FreeLift
import Work.Block.Frames

/-!
# GFrame / Clifford, part 4 (STAGE B): exact representatives of ARBITRARY subspaces

(agent key: eng-clifford)

A base is an additive bijection `G` of the label space (`G x` = coordinates of `x` in a basis);
a set `s` of coordinates names the subspace `U = {x | (G x)_k = 0 for k ∉ s}` (`InSub G s`).
ANY subspace is of this form, degenerate and isotropic ones included.

* `pk s`       the kernel on the coordinates in `s` (`pk ∅ = 1`, `pk univ = kernel α`);
* `kg G`       the free adapter `diag(lum) * permMat G * diag(lum)⁻¹` (`free_kg`);
* `core G s = kg G * pk s * kg G⁻¹`   the representative (the outside note's `T_U = K_G T_{E_r} K_G⁻¹`);
* `core_empty`, `core_id_univ`        `core G ∅ = 1`, `core id univ = kernel α`;
* `core_nested`  in ONE base: `core G t = kg G * blockMat z * kg G⁻¹ * core G s` for `s ⊆ t`,
                 `z` = the `|t \ s|` unit vectors: ONE block between free adapters;
* `core_apply`   the entry formula
                 `core G s x y = [x + y ∈ U] ca^|s| (lum x / lum y) (-1)^(G x · G (x + y))`.
No `sorry`.
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving.GF
open Binary Matrix Finset Complex
noncomputable section
section
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- kernel on the coordinates in `s`. -/
def pk (s : Finset α) : CMat α := wrap fun x => ∏ k ∈ s, tint (x k)

/-- the adapter of a base: address map `G` with the phase `lum x / lum (G x)`. -/
def kg (G : APerm α) : CMat α := fun x y => if G.π x = y then lum x / lum y else 0

/-- exact representative of the subspace `InSub G s`. -/
def core (G : APerm α) (s : Finset α) : CMat α := kg G * pk s * kg (apInv G)

/-- membership in the subspace named by `(G, s)`. -/
def InSub (G : APerm α) (s : Finset α) (x : Space α) : Prop := ∀ k, k ∉ s → G.π x k = 0

instance (G : APerm α) (s : Finset α) (x : Space α) : Decidable (InSub G s x) := by
  unfold InSub; infer_instance

lemma inv_sign (t : F) : (sign t)⁻¹ = sign t :=
  (eq_inv_of_mul_eq_one_left (sign_sq t)).symm

lemma lum_inv (x : Space α) : (lum x)⁻¹ = lum x ^ 3 := by
  have h4 : lum x ^ 3 * lum x = 1 := by
    rw [← pow_succ, show (3 + 1 : ℕ) = 2 + 2 by rfl, pow_add, pow_two, lum_sq, sign_sq]
  exact (eq_inv_of_mul_eq_one_left h4).symm

lemma lum_inv_sq (x : Space α) : (lum x)⁻¹ * (lum x)⁻¹ = sign (dot x x) := by
  rw [← mul_inv, lum_sq, inv_sign]

lemma free_diag_lum : Free (diagonal (lum : Space α → ℂ)) := by
  have h : (lum : Space α → ℂ) = fun x => ∏ k ∈ univ, tint (dot (eu k) x + 0) := by
    funext x; simp [lum]
  rw [h]
  exact free_diag_prod univ _ (fun k _ => free_diag_tint _ _)

lemma free_diag_lum_inv : Free (diagonal fun x : Space α => (lum x)⁻¹) := by
  rw [show (fun x : Space α => (lum x)⁻¹) = fun x => lum x ^ 3 from funext lum_inv]
  exact free_diag_pow free_diag_lum 3

lemma kg_eq (G : APerm α) :
    kg G = diagonal lum * permMat G * diagonal (fun y => (lum y)⁻¹) := by
  ext x y
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [kg, permMat]
  split_ifs <;> simp [div_eq_mul_inv]

theorem free_kg (G : APerm α) : Free (kg G) := by
  rw [kg_eq]
  exact Free.mul (Free.mul free_diag_lum (Free.perm G)) free_diag_lum_inv

lemma kg_mul_apply (G : APerm α) (M : CMat α) (x y : Space α) :
    (kg G * M) x y = lum x / lum (G.π x) * M (G.π x) y := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (G.π x)]
  · simp [kg]
  · intro b _ hb
    simp [kg, Ne.symm hb]
  · intro h; exact absurd (mem_univ _) h

lemma mul_kg_inv_apply (G : APerm α) (M : CMat α) (x y : Space α) :
    (M * kg (apInv G)) x y = M x (G.π y) * (lum (G.π y) / lum y) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (G.π y)]
  · simp [kg, apInv]
  · intro b _ hb
    have : ¬ G.π.symm b = y := fun h => hb (by rw [← h]; simp)
    simp [kg, apInv, this]
  · intro h; exact absurd (mem_univ _) h

lemma kg_mul_inv (G : APerm α) : kg G * kg (apInv G) = 1 := by
  ext x y
  rw [mul_kg_inv_apply]
  have hx := lum_nonzero x
  have hy := lum_nonzero y
  have hg := lum_nonzero (G.π y)
  by_cases h : x = y
  · subst h
    simp only [kg, if_true, Matrix.one_apply_eq]
    field_simp
  · have h' : ¬ G.π x = G.π y := fun h' => h (G.π.injective h')
    simp [kg, h', Matrix.one_apply, h]

lemma kg_inv_mul (G : APerm α) : kg (apInv G) * kg G = 1 :=
  mul_eq_one_comm.mp (kg_mul_inv G)

lemma pk_empty : pk (∅ : Finset α) = 1 := by simp [pk, wrap_one]

lemma pk_univ : pk (univ : Finset α) = kernel α := by
  rw [pk, ← wrap_lum]; rfl

lemma pk_union (s t : Finset α) (h : Disjoint s t) : pk (s ∪ t) = pk s * pk t := by
  rw [pk, pk, pk, wrap_mul]
  congr 1
  funext x
  rw [Finset.prod_union h]

lemma pk_sdiff {s t : Finset α} (h : s ⊆ t) : pk t = pk (t \ s) * pk s := by
  rw [← pk_union _ _ Finset.sdiff_disjoint, Finset.sdiff_union_of_subset h]

lemma pk_eq_blockMat (d : Finset α) : pk d = blockMat ((OBase.canonical α).fam d) := by
  rw [OBase.blockMat_fam]
  simp [pk, OBase.canonical]

theorem core_empty (G : APerm α) : core G ∅ = 1 := by
  rw [core, pk_empty, Matrix.mul_one, kg_mul_inv]

theorem core_id_univ : core (apId α) univ = kernel α := by
  have h : kg (apId α) = 1 := by
    ext x y
    by_cases hxy : x = y
    · subst hxy; simp [kg, apId, lum_nonzero]
    · simp [kg, apId, Matrix.one_apply, hxy]
  have h2 : apInv (apId α) = apId α := rfl
  rw [core, h2, h, pk_univ, Matrix.one_mul, Matrix.mul_one]

/-- **Nested step in one base**: ONE block of rank `|t \ s|` between the free adapters
`kg G` and `kg G⁻¹`. -/
theorem core_nested (G : APerm α) {s t : Finset α} (h : s ⊆ t) :
    core G t = kg G * blockMat ((OBase.canonical α).fam (t \ s)) * kg (apInv G) * core G s := by
  rw [← pk_eq_blockMat, core, core, pk_sdiff h]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (kg (apInv G)) (kg G), kg_inv_mul, Matrix.one_mul]

/-- the same, in the form the label layer consumes. -/
theorem core_nested_ex (G : APerm α) {s t : Finset α} (h : s ⊆ t) :
    ∃ (A B : CMat α) (z : Fin (t \ s).card → Space α), Free A ∧ Free B ∧
      LinearIndependent F z ∧ core G t = A * blockMat z * B * core G s :=
  ⟨kg G, kg (apInv G), _, free_kg G, free_kg _, (OBase.canonical α).fam_indep _,
    core_nested G h⟩

end
end
end PowerSaving.GF
end OAI

#print axioms OAI.PowerSaving.GF.free_kg
#print axioms OAI.PowerSaving.GF.core_id_univ
#print axioms OAI.PowerSaving.GF.core_nested_ex
