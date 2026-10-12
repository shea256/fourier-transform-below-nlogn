import Work.Carrier.Live

/-!
# (key: carrier-thm) Live roles: the scatter without copies, and the two shears

* `g8_facts`, `h8_facts`   unit rows / columns of the top gates;
* `embYS K`                the block `y ← slots` of a rectangular matrix `K : T × Sl`;
  `scatM K = 1 + embYS K`  the scatter with the copies eliminated (`y += K s`, `K = Jr * Cc`),
  `scatMi K = 1 - embYS K` its inverse (`scat_inv`);
* `act_scat`, `act_scatT`  scalar maps of `scatM K` and of the transpose of `scatMi K`;
* `act_shear`, `act_shearT` scalar maps of `1 + PY * M * PX` (`y += x`) and of the transpose of
  `1 - PY * M * PX` (`x -= y`) when the block `y ← x` of `M` is the identity.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace CR
open Binary Matrix Finset RAM SS CB BR
noncomputable section

section Scat
variable {T Sl : Type} [Fintype T] [DecidableEq T] [Fintype Sl] [DecidableEq Sl]

lemma g8_facts {Mi : Matrix (L3 T Sl) (L3 T Sl) ℚ} (hiy : Mi * PY = PY) :
    PX * g8 Mi = PX ∧ PY * g8 Mi = PY ∧ g8 Mi * PY = PY := by
  unfold g8
  exact ⟨side_g_x PX_sq PX_PY Mi, side_g_y PY_sq PY_PX Mi, side_g_ycol PY_sq PX_PY hiy⟩

lemma h8_facts {M : Matrix (L3 T Sl) (L3 T Sl) ℚ} (hmy : M * PY = PY) :
    PX * h8 M = PX ∧ PY * h8 M = PY ∧ h8 M * PY = PY := by
  unfold h8
  exact ⟨side_g_x PX_sq PX_PY M, side_g_y PY_sq PY_PX M, side_g_ycol PY_sq PX_PY hmy⟩

/-- the block `y ← slots` of a rectangular matrix, as a matrix on the live roles. -/
def embYS (K : Matrix T Sl ℚ) : Matrix (L3 T Sl) (L3 T Sl) ℚ := fun i j =>
  Sum.elim (Sum.elim (fun _ => 0) (fun S => Sum.elim (fun _ => 0) (fun q => K S q) j))
    (fun _ => 0) i

/-- the scatter with the copies eliminated: `y += K s`. -/
def scatM (K : Matrix T Sl ℚ) : Matrix (L3 T Sl) (L3 T Sl) ℚ := 1 + embYS K
/-- its inverse: `y -= K s`. -/
def scatMi (K : Matrix T Sl ℚ) : Matrix (L3 T Sl) (L3 T Sl) ℚ := 1 - embYS K

lemma embYS_mul (A B : Matrix T Sl ℚ) : embYS A * embYS B = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro k _
  rcases k with ((t|S)|q)
  · simp [embYS]
  · rcases i with ((t'|S')|q') <;> simp [embYS]
  · simp [embYS]

lemma scat_inv (K : Matrix T Sl ℚ) : scatMi K * scatM K = 1 := by
  unfold scatMi scatM
  rw [sub_mul, one_mul, mul_add, mul_one, embYS_mul, add_zero]
  abel

/-- scalar map of the scatter: `y_S += ∑_q K S q * s_q`. -/
lemma act_scat (K : Matrix T Sl ℚ) (u : L3 T Sl → ℂ) :
    actPoint (1 + embYS K) u = fun i => u i +
      Sum.elim (Sum.elim (fun _ => 0) (fun S => ap K (fun q => u (Sum.inr q)) S)) (fun _ => 0) i := by
  have h : actPoint (1 + embYS K) u = u + ap (embYS K) u := by
    have e := ap_madd (1 : Matrix (L3 T Sl) (L3 T Sl) ℚ) (embYS K) u
    rw [ap_one] at e
    exact e
  funext i
  have e2 : actPoint (1 + embYS K) u i = u i + ap (embYS K) u i := congrFun h i
  rw [e2]
  congr 1
  rcases i with ((t|S)|q)
  · show ∑ j, ((embYS K (Sum.inl (Sum.inl t)) j : ℚ) : ℂ) * u j = 0
    apply Finset.sum_eq_zero
    intro j _
    simp [embYS]
  · show ∑ j, ((embYS K (Sum.inl (Sum.inr S)) j : ℚ) : ℂ) * u j
      = ∑ q, ((K S q : ℚ) : ℂ) * u (Sum.inr q)
    rw [Fintype.sum_sum_type]
    simp [embYS]
  · show ∑ j, ((embYS K (Sum.inr q) j : ℚ) : ℂ) * u j = 0
    apply Finset.sum_eq_zero
    intro j _
    simp [embYS]

/-- scalar map of the transposed inverse scatter: `s_q -= ∑_S K S q * y_S`. -/
lemma act_scatT (K : Matrix T Sl ℚ) (u : L3 T Sl → ℂ) :
    actPoint ((1 - embYS K)ᵀ) u = fun i => u i -
      Sum.elim (fun _ => 0) (fun q => ap Kᵀ (fun S => u (Sum.inl (Sum.inr S))) q) i := by
  have e' : (1 - embYS K)ᵀ = 1 + -(embYS K)ᵀ := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, sub_eq_add_neg]
  have h : actPoint (1 + -(embYS K)ᵀ) u = u + -(ap (embYS K)ᵀ u) := by
    have e := ap_madd (1 : Matrix (L3 T Sl) (L3 T Sl) ℚ) (-(embYS K)ᵀ) u
    rw [ap_one, ap_mneg] at e
    exact e
  funext i
  have e2 : actPoint (1 + -(embYS K)ᵀ) u i = u i + -(ap (embYS K)ᵀ u i) := congrFun h i
  rw [e', e2, ← sub_eq_add_neg]
  congr 1
  rcases i with (b|q)
  · show ∑ j, (((embYS K)ᵀ (Sum.inl b) j : ℚ) : ℂ) * u j = 0
    apply Finset.sum_eq_zero
    intro j _
    rcases j with ((t|S)|q') <;> simp [embYS, Matrix.transpose_apply]
  · show ∑ j, (((embYS K)ᵀ (Sum.inr q) j : ℚ) : ℂ) * u j
      = ∑ S, ((Kᵀ q S : ℚ) : ℂ) * u (Sum.inl (Sum.inr S))
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp [embYS, Matrix.transpose_apply]

/-- what the y roles receive from the x roles when the block `y ← x` of `M` is the identity. -/
lemma act_yx (M : Matrix (L3 T Sl) (L3 T Sl) ℚ)
    (hid : ∀ S t, M (Sum.inl (Sum.inr S)) (Sum.inl (Sum.inl t)) = if S = t then 1 else 0)
    (u : L3 T Sl → ℂ) :
    actPoint (PY * M * PX) u
      = Sum.elim (Sum.elim (fun _ => 0) (fun S => u (Sum.inl (Sum.inl S)))) (fun _ => 0) := by
  rw [actPoint_mul, actPoint_mul]
  unfold PX PY
  rw [act_diag, act_diag]
  funext i
  rcases i with ((t|S)|q)
  · simp [iY]
  · show ((iY (Sum.inl (Sum.inr S)) : ℚ) : ℂ) *
        (∑ j, ((M (Sum.inl (Sum.inr S)) j : ℚ) : ℂ) * (((iX j : ℚ) : ℂ) * u j))
      = u (Sum.inl (Sum.inl S))
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [iX, iY, Sum.elim_inl, Sum.elim_inr, Rat.cast_one, Rat.cast_zero, one_mul,
      zero_mul, mul_zero, Finset.sum_const_zero, add_zero, zero_add, hid]
    exact sum_ind_right S (fun t => u (Sum.inl (Sum.inl t)))
  · simp [iY]

/-- the transpose: what the x roles receive from the y roles. -/
lemma act_yxT (M : Matrix (L3 T Sl) (L3 T Sl) ℚ)
    (hid : ∀ S t, M (Sum.inl (Sum.inr S)) (Sum.inl (Sum.inl t)) = if S = t then 1 else 0)
    (u : L3 T Sl → ℂ) :
    actPoint ((PY * M * PX)ᵀ) u
      = Sum.elim (Sum.elim (fun t => u (Sum.inl (Sum.inr t))) (fun _ => 0)) (fun _ => 0) := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, PX_T, PY_T, actPoint_mul, actPoint_mul]
  unfold PX PY
  rw [act_diag, act_diag]
  funext i
  rcases i with ((t|S)|q)
  · show ((iX (Sum.inl (Sum.inl t)) : ℚ) : ℂ) *
        (∑ j, ((Mᵀ (Sum.inl (Sum.inl t)) j : ℚ) : ℂ) * (((iY j : ℚ) : ℂ) * u j))
      = u (Sum.inl (Sum.inr t))
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [iX, iY, Sum.elim_inl, Sum.elim_inr, Rat.cast_one, Rat.cast_zero, one_mul,
      zero_mul, mul_zero, Finset.sum_const_zero, add_zero, zero_add, Matrix.transpose_apply, hid]
    exact sum_ind_left t (fun S => u (Sum.inl (Sum.inr S)))
  · simp [iX]
  · simp [iX]

/-- **the forward shear** `y += x` on the live roles. -/
lemma act_shear (M : Matrix (L3 T Sl) (L3 T Sl) ℚ)
    (hid : ∀ S t, M (Sum.inl (Sum.inr S)) (Sum.inl (Sum.inl t)) = if S = t then 1 else 0)
    (u : L3 T Sl → ℂ) :
    actPoint (1 + PY * M * PX) u = fun i => u i +
      Sum.elim (Sum.elim (fun _ => 0) (fun S => u (Sum.inl (Sum.inl S)))) (fun _ => 0) i := by
  have h : actPoint (1 + PY * M * PX) u = u + ap (PY * M * PX) u := by
    have e := ap_madd (1 : Matrix (L3 T Sl) (L3 T Sl) ℚ) (PY * M * PX) u
    rw [ap_one] at e
    exact e
  funext i
  have e2 : actPoint (1 + PY * M * PX) u i = u i + actPoint (PY * M * PX) u i := congrFun h i
  have e3 := congrFun (act_yx M hid u) i
  rw [e2, e3]

/-- **the backward shear** `x -= y` on the live roles. -/
lemma act_shearT (M : Matrix (L3 T Sl) (L3 T Sl) ℚ)
    (hid : ∀ S t, M (Sum.inl (Sum.inr S)) (Sum.inl (Sum.inl t)) = if S = t then 1 else 0)
    (u : L3 T Sl → ℂ) :
    actPoint ((1 - PY * M * PX)ᵀ) u = fun i => u i -
      Sum.elim (Sum.elim (fun t => u (Sum.inl (Sum.inr t))) (fun _ => 0)) (fun _ => 0) i := by
  have e' : (1 - PY * M * PX)ᵀ = 1 + -(PY * M * PX)ᵀ := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, sub_eq_add_neg]
  have h : actPoint (1 + -(PY * M * PX)ᵀ) u = u + -(ap (PY * M * PX)ᵀ u) := by
    have e := ap_madd (1 : Matrix (L3 T Sl) (L3 T Sl) ℚ) (-(PY * M * PX)ᵀ) u
    rw [ap_one, ap_mneg] at e
    exact e
  funext i
  have e2 : actPoint (1 + -(PY * M * PX)ᵀ) u i = u i + -(actPoint (PY * M * PX)ᵀ u i) :=
    congrFun h i
  have e3 := congrFun (act_yxT M hid u) i
  rw [e', e2, e3, ← sub_eq_add_neg]

end Scat
end
end CR
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.CR.scat_inv
#print axioms OAI.PowerSaving.CR.act_shear
#print axioms OAI.PowerSaving.CR.act_shearT
