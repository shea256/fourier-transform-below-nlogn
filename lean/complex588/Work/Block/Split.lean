import Work.Scratch.Engine

/-!
# Block moves, part 1: block matrices and splittings of the label space

(agent key: block-engine).  Nothing upstream is modified.  No `sorry`.

A *unit move* multiplies one role by `dir z` (`BinaryFrames.lean:152`).  A *block* is a family
`z : Fin r → Space α` of directions; its matrix is the product of the `dir (z i)`
(`blockMat`).  This file proves the linear-algebra fact that makes a block ONE recursive call:

* `Split α β γ`         an additive bijection `Space α ≃ Space β × Space γ`;
* `Split.lift M`        the matrix "identity on `Space β`, `M` on `Space γ`" in those coordinates;
* `blockMat_eq_lift`    if the splitting sends the `i`-th block direction to the `i`-th unit
                        vector of `Space (Fin r)`, then `blockMat z = S.lift (kernel (Fin r))`;
* `exists_split`        such a splitting exists as soon as the directions are LINEARLY
                        INDEPENDENT over `ZMod 2` (no orthogonality, no norm condition);
* `linearIndependent_of_orthonormal`  pairwise-orthogonal unit directions are independent.
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving.Binary
open Matrix Finset
noncomputable section

/-- A splitting of the label space: an additive bijection onto `rest × block coordinates`. -/
structure Split (α β γ : Type*) where
  e : Space α ≃ Space β × Space γ
  add : ∀ x y, e (x + y) = e x + e y

section
variable {α β γ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ]

namespace Split
variable (S : Split α β γ)

lemma symm_add (p q : Space β × Space γ) :
    S.e.symm (p + q) = S.e.symm p + S.e.symm q := by
  apply S.e.injective
  rw [S.add]; simp

lemma map_zero : S.e 0 = 0 := by
  have h := S.add 0 0
  rw [add_zero] at h
  have h2 : S.e 0 + S.e 0 = 0 := Prod.ext (binary_cancel _) (binary_cancel _)
  rw [h2] at h
  exact h

lemma symm_zero : S.e.symm 0 = 0 := by
  apply S.e.injective
  rw [S.map_zero]; simp

/-- A matrix on the block coordinates, acting as the identity on the remaining ones. -/
def lift (M : CMat γ) : CMat α :=
  fun x y => if (S.e x).1 = (S.e y).1 then M (S.e x).2 (S.e y).2 else 0

lemma lift_one : S.lift (1 : CMat γ) = 1 := by
  ext x y
  simp only [lift, one_apply]
  by_cases h : x = y
  · subst h; simp
  · by_cases h1 : (S.e x).1 = (S.e y).1
    · have h2 : (S.e x).2 ≠ (S.e y).2 := fun h2 => h (S.e.injective (Prod.ext h1 h2))
      rw [if_pos h1, if_neg h2, if_neg h]
    · rw [if_neg h1, if_neg h]

lemma lift_mul (M N : CMat γ) : S.lift (M * N) = S.lift M * S.lift N := by
  ext x y
  rw [Matrix.mul_apply, ← Equiv.sum_comp S.e.symm, Fintype.sum_prod_type]
  simp only [lift, Equiv.apply_symm_apply]
  by_cases h : (S.e x).1 = (S.e y).1
  · rw [if_pos h, Finset.sum_eq_single (S.e x).1]
    · simp only [↓reduceIte, h, Matrix.mul_apply]
    · intro b _ hb
      apply Finset.sum_eq_zero
      intro c _
      rw [if_neg (Ne.symm hb), zero_mul]
    · intro h'; exact absurd (Finset.mem_univ _) h'
  · rw [if_neg h]
    symm
    apply Finset.sum_eq_zero; intro b _
    apply Finset.sum_eq_zero; intro c _
    by_cases h1 : (S.e x).1 = b
    · have h2 : ¬ b = (S.e y).1 := fun h2 => h (h1.trans h2)
      rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]

lemma lift_add (M N : CMat γ) : S.lift (M + N) = S.lift M + S.lift N := by
  ext x y
  simp only [lift, Matrix.add_apply]
  split <;> simp

lemma lift_smul (c : ℂ) (M : CMat γ) : S.lift (c • M) = c • S.lift M := by
  ext x y
  simp only [lift, Matrix.smul_apply]
  split <;> simp

lemma lift_shift (c : Space γ) : S.lift (shift c) = shift (S.e.symm (0,c)) := by
  ext x y
  simp only [lift, shift]
  have key : x + S.e.symm (0,c) = y ↔ (S.e x).1 = (S.e y).1 ∧ (S.e x).2 + c = (S.e y).2 := by
    rw [← S.e.injective.eq_iff, S.add, Equiv.apply_symm_apply, Prod.ext_iff]
    simp
  by_cases h1 : (S.e x).1 = (S.e y).1
  · by_cases h2 : (S.e x).2 + c = (S.e y).2
    · rw [if_pos h1, if_pos h2, if_pos (key.2 ⟨h1,h2⟩)]
    · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 (key.1 h).2)]
  · rw [if_neg h1, if_neg (fun h => h1 (key.1 h).1)]

lemma lift_dir (c : Space γ) : S.lift (dir c) = dir (S.e.symm (0,c)) := by
  unfold dir
  rw [lift_add, lift_smul, lift_smul, lift_one, lift_shift]

lemma lift_list_prod (L : List (CMat γ)) : S.lift L.prod = (L.map S.lift).prod := by
  induction L with
  | nil => simp [lift_one]
  | cons a L ih => rw [List.prod_cons, lift_mul, ih, List.map_cons, List.prod_cons]

end Split

/-- The matrix of a block: the product of the unit-move matrices of its directions. -/
def blockMat {r : ℕ} (z : Fin r → Space α) : CMat α := (List.ofFn fun i => dir (z i)).prod

lemma blockMat_zero (z : Fin 0 → Space α) : blockMat z = 1 := by
  simp [blockMat]

lemma blockMat_one (z : Fin 1 → Space α) : blockMat z = dir (z 0) := by
  simp [blockMat]

lemma prod_dir_wrap (L : List (Space γ)) :
    (L.map dir).prod = wrap (fun x => (L.map (fun z => tint (dot z x))).prod) := by
  induction L with
  | nil => simp [wrap_one]
  | cons z L ih =>
    rw [List.map_cons, List.prod_cons, ih, dir_phase, wrap_mul]
    simp only [List.map_cons, List.prod_cons]

/-- The kernel on `r` coordinates is the block of the `r` unit vectors. -/
lemma kernel_eq_blockMat (r : ℕ) : blockMat (fun i : Fin r => eu i) = kernel (Fin r) := by
  unfold blockMat
  have h1 : (List.ofFn fun i : Fin r => dir (eu i)) = ((List.finRange r).map eu).map dir := by
    rw [List.ofFn_eq_map, List.map_map]; rfl
  rw [h1, prod_dir_wrap, ← wrap_lum]
  congr 1
  funext x
  rw [List.map_map]
  have h2 : (tint ∘ fun z : Space (Fin r) => dot z x) ∘ eu = fun i : Fin r => tint (x i) := by
    funext i; simp
  have h3 : (fun z : Space (Fin r) => tint (dot z x)) ∘ eu = fun i : Fin r => tint (x i) := h2
  rw [h3, ← List.ofFn_eq_map, List.prod_ofFn]
  rfl

/-- **A block is the kernel on the block coordinates of a suitable splitting.** -/
theorem blockMat_eq_lift {r : ℕ} (S : Split α β (Fin r)) (z : Fin r → Space α)
    (hz : ∀ i, S.e.symm (0, eu i) = z i) : blockMat z = S.lift (kernel (Fin r)) := by
  rw [← kernel_eq_blockMat]
  unfold blockMat
  rw [Split.lift_list_prod, List.map_ofFn]
  congr 2
  funext i
  simp only [Function.comp_apply]
  rw [Split.lift_dir, hz]

/-- Pairwise-orthogonal unit directions are linearly independent. -/
lemma linearIndependent_of_orthonormal {r : ℕ} (z : Fin r → Space α)
    (h : ∀ i j, dot (z i) (z j) = if i = j then 1 else 0) : LinearIndependent F z := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h1 := congrArg (dot (z i)) hg
  rw [dot_sum] at h1
  simpa [h] using h1

/-- A single nonzero direction is a legal block of rank one. -/
lemma linearIndependent_single (z : Space α) (hz : z ≠ 0) :
    LinearIndependent F (fun _ : Fin 1 => z) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h1 : g 0 • z = 0 := by simpa using hg
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  rcases bit_cases (g 0) with h0|h0
  · exact h0
  · rw [h0, one_smul] at h1; exact absurd h1 hz

/-- **Existence of the splitting.**  For linearly independent directions `z` there is an
additive bijection `Space α ≃ Space (Fin (m - r)) × Space (Fin r)` under which adding `z i`
is adding the `i`-th unit vector of the second factor. -/
theorem exists_split {r : ℕ} (z : Fin r → Space α) (hz : LinearIndependent F z) :
    ∃ S : Split α (Fin (Fintype.card α - r)) (Fin r), ∀ i, S.e.symm (0, eu i) = z i := by
  classical
  let Zm : (Fin r → F) →ₗ[F] (α → F) := Fintype.linearCombination F z
  have hinj : Function.Injective Zm := hz.fintypeLinearCombination_injective
  obtain ⟨W, hW⟩ := Zm.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hinj)
  have hWZ (a : Fin r → F) : W (Zm a) = a := LinearMap.congr_fun hW a
  have hsurj : Function.Surjective W := fun a => ⟨Zm a, hWZ a⟩
  have hdim : Module.finrank F (LinearMap.ker W) = Fintype.card α - r := by
    have h := W.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fin_fun,
      Module.finrank_fintype_fun_eq_card] at h
    omega
  let κ : LinearMap.ker W ≃ₗ[F] (Fin (Fintype.card α - r) → F) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [hdim, Module.finrank_fin_fun])
  have hmem (x : α → F) : x - Zm (W x) ∈ LinearMap.ker W := by
    rw [LinearMap.mem_ker, map_sub, hWZ, sub_self]
  let toF (x : Space α) : Space (Fin (Fintype.card α - r)) × Space (Fin r) :=
    (κ ⟨x - Zm (W x), hmem x⟩, W x)
  let invF (p : Space (Fin (Fintype.card α - r)) × Space (Fin r)) : Space α :=
    ((κ.symm p.1 : LinearMap.ker W) : α → F) + Zm p.2
  have hleft : Function.LeftInverse invF toF := by
    intro x
    simp only [invF, toF, LinearEquiv.symm_apply_apply]
    exact sub_add_cancel _ _
  have hright : Function.RightInverse invF toF := by
    rintro ⟨y, a⟩
    have hk : W ((κ.symm y : LinearMap.ker W) : α → F) = 0 := LinearMap.mem_ker.mp (κ.symm y).2
    have hWx : W (invF (y,a)) = a := by
      simp only [invF, map_add, hk, hWZ, zero_add]
    apply Prod.ext
    · change κ ⟨invF (y,a) - Zm (W (invF (y,a))), _⟩ = y
      have hs : (⟨invF (y,a) - Zm (W (invF (y,a))), hmem _⟩ : LinearMap.ker W) = κ.symm y := by
        apply Subtype.ext
        change invF (y,a) - Zm (W (invF (y,a))) = _
        rw [hWx]
        simp only [invF, add_sub_cancel_right]
      rw [hs, LinearEquiv.apply_symm_apply]
    · exact hWx
  refine ⟨⟨⟨toF, invF, hleft, hright⟩, ?_⟩, ?_⟩
  · intro x y
    apply Prod.ext
    · change κ ⟨(x+y) - Zm (W (x+y)), _⟩ = κ ⟨x - Zm (W x), _⟩ + κ ⟨y - Zm (W y), _⟩
      rw [← map_add]
      congr 1
      apply Subtype.ext
      change (x+y) - Zm (W (x+y)) = (x - Zm (W x)) + (y - Zm (W y))
      rw [map_add, map_add]; abel
    · change W (x+y) = W x + W y
      exact map_add _ _ _
  · intro i
    change ((κ.symm (0 : Fin (Fintype.card α - r) → F) : LinearMap.ker W) : α → F) + Zm (eu i)
      = z i
    rw [map_zero]
    have hz' : Zm (eu i) = z i := by
      change Fintype.linearCombination F z (eu i) = z i
      rw [Fintype.linearCombination_apply]
      simp [eu]
    rw [hz']
    simp

end
end
end PowerSaving.Binary
end OAI

#print axioms OAI.PowerSaving.Binary.blockMat_eq_lift
#print axioms OAI.PowerSaving.Binary.exists_split
#print axioms OAI.PowerSaving.Binary.linearIndependent_of_orthonormal
