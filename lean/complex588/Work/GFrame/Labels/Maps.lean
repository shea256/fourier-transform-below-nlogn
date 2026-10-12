import Work.GFrame.Labels.Embed

/-!
# GFrame labels, part 7 (key: eng-labels): the two frame maps of the network are `GXMap`s

The frame maps `SS.Phi1 t`, `SS.Phi2 t` of the two-stage network (the `Φ` of `CB.xmap1`,
`CB.xmap2`) are Walsh-diagonal frame maps in the sense of `GXMap`: their phase is a quadratic
phase whose polar form is `gram P ⊗ t tᵀ` (stage 1), `t tᵀ ⊗ gram P + const` (stage 2).
Hence EVERY generalised climb (any independent residual vectors; alternating residuals) is a
one-role move for them, not only climbs inside one orthonormal basis.

* `gxmap1`, `gxmap2`      the two `GXMap H (H × H)`, for ANY unit vector `t`;
* `gxmap1_Φ`, `gxmap2_Φ`  they have the same `Φ` as `CB.xmap1`, `CB.xmap2`.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.GF
open Binary Matrix Finset RAM CB SS
noncomputable section

section
variable {H : Type} [Fintype H] [DecidableEq H]

lemma kron_transpose (M N : Matrix H H F) : (kron M N)ᵀ = kron Mᵀ Nᵀ := by
  ext p q; rfl

lemma kron_mul (M N M' N' : Matrix H H F) : kron M N * kron M' N' = kron (M * M') (N * N') := by
  ext ⟨i, j⟩ ⟨i', j'⟩
  simp only [Matrix.mul_apply, kron, Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  ring

lemma kron_add_left (B B' N : Matrix H H F) : kron (B + B') N = kron B N + kron B' N := by
  ext p q; simp [kron, add_mul]

lemma kron_add_right (N B B' : Matrix H H F) : kron N (B + B') = kron N B + kron N B' := by
  ext p q; simp [kron, mul_add]

lemma tt_gram (t : Space H) (ht : dot t t = 1) : (tt t)ᵀ * tt t = tt t := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, tt]
  have e : ∀ l, t l * t i * (t l * t j) = (t l * t l) * (t i * t j) := fun l => by ring
  simp_rw [e, ← Finset.sum_mul]
  have h : ∑ l, t l * t l = 1 := ht
  rw [h, one_mul]

lemma gram_kron_left (P : Matrix H H F) (t : Space H) (ht : dot t t = 1) :
    (kron P (tt t))ᵀ * kron P (tt t) = kron (gram P) (tt t) := by
  rw [kron_transpose, kron_mul, tt_gram t ht]; rfl

lemma gram_kron_right (P : Matrix H H F) (t : Space H) (ht : dot t t = 1) :
    (kron (tt t) P)ᵀ * kron (tt t) P = kron (tt t) (gram P) := by
  rw [kron_transpose, kron_mul, tt_gram t ht]; rfl

lemma exists_one (t : Space H) (ht : dot t t = 1) : ∃ k, t k = 1 := by
  by_contra hne
  have h0 : ∀ k, t k = 0 := fun k => by
    rcases bit_cases (t k) with h|h
    · exact h
    · exact absurd ⟨k, h⟩ hne
  have : dot t t = 0 := by simp [dot, h0]
  rw [this] at ht; exact zero_ne_one ht

/-- `a ↦ a ⊗ t`, linear. -/
def tensL (t : Space H) : Space H →ₗ[F] Space (H × H) where
  toFun := fun a => tens a t
  map_add' := fun a b => by funext p; simp [tens, add_mul]
  map_smul' := fun c a => by funext p; simp [tens, mul_assoc]

/-- `a ↦ t ⊗ a`, linear. -/
def tensR (t : Space H) : Space H →ₗ[F] Space (H × H) where
  toFun := fun a => tens t a
  map_add' := fun a b => by funext p; simp [tens, mul_add]
  map_smul' := fun c a => by funext p; simp [tens, mul_left_comm]

lemma tensL_inj (t : Space H) (ht : dot t t = 1) : Function.Injective (tensL t) := by
  obtain ⟨k, hk⟩ := exists_one t ht
  intro a b h
  funext i
  have h1 := congrFun h (i, k)
  simpa [tensL, tens, hk] using h1

lemma tensR_inj (t : Space H) (ht : dot t t = 1) : Function.Injective (tensR t) := by
  obtain ⟨k, hk⟩ := exists_one t ht
  intro a b h
  funext i
  have h1 := congrFun h (k, i)
  simpa [tensR, tens, hk] using h1

lemma card_lt_prod (hH : 2 ≤ Fintype.card H) : Fintype.card H < Fintype.card (H × H) := by
  rw [Fintype.card_prod]; nlinarith

/-- **Stage 1 frame map** (`Φ = SS.Phi1 t`, label on the first factor, the line of the unit
vector `t` on the second) **as a `GXMap`**. -/
def gxmap1 (hH : 2 ≤ Fintype.card H) (t : Space H) (ht : dot t t = 1) : GXMap H (H × H) where
  Φ := Phi1 t
  ph := fun P x => lum (kron P (tt t) *ᵥ x)
  hΦ := fun P => rfl
  L := fun B => kron B (tt t)
  B0 := 0
  quad := fun P => by
    have h := QPh.of_lum (kron P (tt t))
    rw [gram_kron_left P t ht] at h
    rw [add_zero]; exact h
  ι := tensL t
  inj := tensL_inj t ht
  L_add := fun B B' => kron_add_left B B' _
  L_vv := fun a b => by
    ext ⟨i, j⟩ ⟨i', j'⟩
    simp only [kron, vv, tt, tensL, tens, LinearMap.coe_mk, AddHom.coe_mk]
    ring
  card := card_lt_prod hH

/-- **Stage 2 frame map** (`Φ = SS.Phi2 t`) **as a `GXMap`**. -/
def gxmap2 (hH : 2 ≤ Fintype.card H) (t : Space H) (ht : dot t t = 1) : GXMap H (H × H) where
  Φ := Phi2 t
  ph := fun P x => lum (kron (tt t) P *ᵥ x) * lum (kron (1 + tt t) 1 *ᵥ x)
  hΦ := fun P => by
    unfold Phi2 Kmat frameM
    rw [wrap_mul]
  L := fun B => kron (tt t) B
  B0 := (kron (1 + tt t) (1 : Matrix H H F))ᵀ * kron (1 + tt t) 1
  quad := fun P => by
    have h := (QPh.of_lum (kron (tt t) P)).mul (QPh.of_lum (kron (1 + tt t) (1 : Matrix H H F)))
    rw [gram_kron_right P t ht] at h
    exact h
  ι := tensR t
  inj := tensR_inj t ht
  L_add := fun B B' => kron_add_right _ B B'
  L_vv := fun a b => by
    ext ⟨i, j⟩ ⟨i', j'⟩
    simp only [kron, vv, tt, tensR, tens, LinearMap.coe_mk, AddHom.coe_mk]
    ring
  card := card_lt_prod hH

/-- same `Φ` as the old stage-1 block frame map. -/
theorem gxmap1_Φ (hH : 2 ≤ Fintype.card H) (B : OBase H) (k : H) :
    (gxmap1 hH (B.v k) (B.self k)).Φ = (xmap1 hH B k).Φ := rfl

/-- same `Φ` as the old stage-2 block frame map. -/
theorem gxmap2_Φ (hH : 2 ≤ Fintype.card H) (B : OBase H) (k : H) :
    (gxmap2 hH (B.v k) (B.self k)).Φ = (xmap2 hH B k).Φ := rfl

end
end
end PowerSaving.GF
end OAI

#print axioms OAI.PowerSaving.GF.gxmap1
#print axioms OAI.PowerSaving.GF.gxmap2
#print axioms OAI.PowerSaving.GF.gxmap1_Φ
