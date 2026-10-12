import Work.GFrame.Labels.Calc

/-!
# GFrame labels, part 3 (key: eng-labels): quadratic phases (STAGE A mathematics)

Every frame of stage A is `wrap f` with `f` a QUADRATIC PHASE: `f (x+y) = f x * f y * (-1)^(xᵀ B y)`
for a matrix `B` over `F_2` (its polar form).  The whole stage-A calculus rests on one fact:

* `QPh.unique`   two quadratic phases with the SAME polar form differ by a sign character,
                 i.e. their frames differ by a FREE SHIFT.

Polar forms: `lum (P x)` has `Pᵀ P` (`QPh.of_lum`), `tint (z·x)` has `z zᵀ` (`QPh.of_tint`),
a block along `z₁..z_r` has `∑ z_i z_iᵀ` (`QPh.of_block`), the alternating phase
`(-1)^(∑ (w_j·x)(w'_j·x))` has `∑ (w_j w'_jᵀ + w'_j w_jᵀ)` (`QPh.of_alt`); products add.

* `wrap_step`    polar forms differing by `∑ z_i z_iᵀ`  ⇒  `wrap g = shift c * blockMat z * wrap f`
                 (NO orthogonality, NO unit vector: any family `z`);
* `wrap_astep`   polar forms differing by an alternating form with symplectic data `w, w'`
                 ⇒  `wrap g = shift c * altMat w w' * wrap f`.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.GF
open Binary Matrix Finset SS
noncomputable section

section
variable {α : Type} [Fintype α] [DecidableEq α]

/-- outer product `a bᵀ` over `F_2` (`SS.tt z = vv z z`). -/
def vv (a b : Space α) : Matrix α α F := fun i j => a i * b j

lemma tt_eq_vv (z : Space α) : tt z = vv z z := rfl

lemma dot_vv (a b x y : Space α) : dot x (vv a b *ᵥ y) = dot a x * dot b y := by
  have h : vv a b *ᵥ y = dot b y • a := by
    funext i
    show ∑ j, a i * b j * y j = (∑ j, b j * y j) * a i
    rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro j _; ring
  rw [h, dot_smul_right, dot_symm x a]; ring

lemma sign_ne (a : F) : sign a ≠ 0 := by
  rcases bit_cases a with rfl|rfl <;> simp [sign]

lemma sign_zero' : sign (0 : F) = 1 := by simp [sign]

/-- `f` is a quadratic phase with polar form `B`. -/
def QPh (f : Space α → ℂ) (B : Matrix α α F) : Prop :=
  f 0 = 1 ∧ ∀ x y, f (x + y) = f x * f y * sign (dot x (B *ᵥ y))

/-- a multiplicative function on a binary space is a sign character. -/
lemma char_of_mul (h : Space α → ℂ) (h0 : h 0 = 1) (hm : ∀ x y, h (x + y) = h x * h y) :
    ∃ c : Space α, ∀ x, h x = sign (dot c x) := by
  classical
  have hsq : ∀ x, h x * h x = 1 := fun x => by rw [← hm, binary_cancel, h0]
  have hpm : ∀ x, h x = 1 ∨ h x = -1 := fun x => mul_self_eq_one_iff.mp (hsq x)
  have hc : ∀ i (b : F), h (b • eu i) = sign ((if h (eu i) = 1 then (0:F) else 1) * b) := by
    intro i b
    rcases bit_cases b with rfl|rfl
    · simp [h0, sign]
    · rw [one_smul, mul_one]
      by_cases hh : h (eu i) = 1
      · rw [ite_eq_left hh, hh]; simp [sign]
      · rw [ite_eq_right hh, (hpm (eu i)).resolve_left hh]; simp [sign]
  have hsum : ∀ (s : Finset α) (v : α → Space α), h (∑ i ∈ s, v i) = ∏ i ∈ s, h (v i) := by
    intro s v
    induction s using Finset.induction_on with
    | empty => simp [h0]
    | insert i s hi ih => rw [Finset.sum_insert hi, hm, ih, Finset.prod_insert hi]
  refine ⟨fun i => if h (eu i) = 1 then 0 else 1, fun x => ?_⟩
  have hx : x = ∑ i, x i • eu i := by
    funext j
    simp [eu, Finset.sum_apply]
  conv_lhs => rw [hx]
  rw [hsum]
  simp_rw [hc]
  rw [← sign_sum]
  rfl

namespace QPh
variable {f g : Space α → ℂ} {B B' : Matrix α α F}

lemma sq (h : QPh f B) (x : Space α) : f x * f x * sign (dot x (B *ᵥ x)) = 1 := by
  rw [← h.2, binary_cancel, h.1]

lemma ne_zero (h : QPh f B) (x : Space α) : f x ≠ 0 := by
  intro h0
  have := h.sq x
  rw [h0] at this; simp at this

lemma congr (h : QPh f B) (e : B = B') : QPh f B' := e ▸ h

lemma mul (hf : QPh f B) (hg : QPh g B') : QPh (fun x => f x * g x) (B + B') := by
  refine ⟨by simp [hf.1, hg.1], fun x y => ?_⟩
  simp only [hf.2 x y, hg.2 x y, Matrix.add_mulVec, dot_add_right, sign_add]
  ring

lemma one : QPh (fun _ : Space α => (1:ℂ)) 0 := by
  refine ⟨rfl, fun x y => ?_⟩
  rw [Matrix.zero_mulVec, dot_zero_right, sign_zero']; ring

lemma of_char (c : Space α) : QPh (fun x => sign (dot c x)) 0 := by
  refine ⟨by beta_reduce; rw [dot_zero_right, sign_zero'], fun x y => ?_⟩
  beta_reduce
  rw [dot_add_right, sign_add, Matrix.zero_mulVec, dot_zero_right, sign_zero', mul_one]

lemma of_tint (z : Space α) : QPh (fun x => tint (dot z x)) (tt z) := by
  refine ⟨by simp [tint], fun x y => ?_⟩
  beta_reduce
  rw [dot_add_right, tint_add, tt_eq_vv, dot_vv]

/-- the frame phase of a label matrix `P`: polar form `Pᵀ P`. -/
lemma of_lum (P : Matrix α α F) : QPh (fun x => lum (P *ᵥ x)) (Pᵀ * P) := by
  refine ⟨by simp, fun x y => ?_⟩
  beta_reduce
  rw [Matrix.mulVec_add, lum_add]
  congr 2
  show (P *ᵥ x) ⬝ᵥ (P *ᵥ y) = x ⬝ᵥ ((Pᵀ * P) *ᵥ y)
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x Pᵀ (P *ᵥ y), Matrix.vecMul_transpose]

lemma prod {ι : Type*} (s : Finset ι) (f : ι → Space α → ℂ) (B : ι → Matrix α α F)
    (h : ∀ i ∈ s, QPh (f i) (B i)) : QPh (fun x => ∏ i ∈ s, f i x) (∑ i ∈ s, B i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (one : QPh (fun _ : Space α => (1:ℂ)) 0)
  | insert i s hi ih =>
    have h1 := (h i (Finset.mem_insert_self i s)).mul
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))
    simp only [Finset.prod_insert hi, Finset.sum_insert hi]
    exact h1

/-- a block along ANY family `z`: polar form `∑ z_i z_iᵀ`. -/
lemma of_block {r : ℕ} (z : Fin r → Space α) :
    QPh (fun x => ∏ i, tint (dot (z i) x)) (∑ i, tt (z i)) :=
  prod Finset.univ _ _ (fun i _ => of_tint (z i))

lemma of_pair (w w' : Space α) :
    QPh (fun x => sign (dot w x * dot w' x)) (vv w w' + vv w' w) := by
  refine ⟨by beta_reduce; rw [dot_zero_right, zero_mul, sign_zero'], fun x y => ?_⟩
  beta_reduce
  have e : dot x ((vv w w' + vv w' w) *ᵥ y) = dot w x * dot w' y + dot w' x * dot w y := by
    rw [Matrix.add_mulVec, dot_add_right, dot_vv, dot_vv]
  rw [e, dot_add_right, dot_add_right, ← sign_add, ← sign_add]
  congr 1; ring

/-- the alternating phase with symplectic data `w, w'`. -/
lemma of_alt {p : ℕ} (w w' : Fin p → Space α) :
    QPh (fun x => sign (∑ j, dot (w j) x * dot (w' j) x))
      (∑ j, (vv (w j) (w' j) + vv (w' j) (w j))) := by
  have h := prod Finset.univ (fun j x => sign (dot (w j) x * dot (w' j) x)) _
    (fun j _ => of_pair (w j) (w' j))
  simpa only [← sign_sum] using h

/-- **Same polar form ⇒ a sign character apart.** -/
theorem unique (hf : QPh f B) (hg : QPh g B) :
    ∃ c : Space α, ∀ x, g x = sign (dot c x) * f x := by
  obtain ⟨c, hc⟩ := char_of_mul (fun x => g x * (f x)⁻¹) (by simp [hf.1, hg.1]) (fun x y => by
    have h1 := hf.ne_zero x
    have h2 := hf.ne_zero y
    have h3 := sign_ne (dot x (B *ᵥ y))
    simp only [hf.2 x y, hg.2 x y]
    field_simp)
  refine ⟨c, fun x => ?_⟩
  have h1 := hf.ne_zero x
  have h2 : g x * (f x)⁻¹ = sign (dot c x) := hc x
  rw [← h2]; field_simp

end QPh

lemma blockMat_wrap' {r : ℕ} (z : Fin r → Space α) :
    blockMat z = wrap (fun x => ∏ i, tint (dot (z i) x)) := by
  rw [blockMat_wrap]
  congr 1
  funext x
  rw [List.map_ofFn, List.prod_ofFn]
  rfl

/-- transition matrix of an alternating residual with symplectic data `w, w'`
(`= ∏ czMat (w j) (w' j)`, Walsh-diagonal with phases `±1`). -/
def altMat {p : ℕ} (w w' : Fin p → Space α) : CMat α :=
  wrap fun x => sign (∑ j, dot (w j) x * dot (w' j) x)

/-- **Same polar form ⇒ a free shift apart.** -/
theorem wrap_same {f g : Space α → ℂ} {B : Matrix α α F} (hf : QPh f B) (hg : QPh g B) :
    ∃ c : Space α, wrap g = shift c * wrap f := by
  obtain ⟨c, hc⟩ := hf.unique hg
  refine ⟨c, ?_⟩
  rw [shift_phase, wrap_mul]
  congr 1; funext x; exact hc x

/-- **One block, any directions**: polar forms differing by `∑ z_i z_iᵀ`. -/
theorem wrap_step {f g : Space α → ℂ} {B : Matrix α α F} {r : ℕ} (z : Fin r → Space α)
    (hf : QPh f B) (hg : QPh g (B + ∑ i, tt (z i))) :
    ∃ c : Space α, wrap g = shift c * blockMat z * wrap f := by
  obtain ⟨c, hc⟩ := (hf.mul (QPh.of_block z)).unique hg
  refine ⟨c, ?_⟩
  rw [shift_phase, blockMat_wrap', wrap_mul, wrap_mul]
  congr 1
  funext x
  rw [hc x]; ring

/-- **Alternating residual**: polar forms differing by `∑ (w_j w'_jᵀ + w'_j w_jᵀ)`. -/
theorem wrap_astep {f g : Space α → ℂ} {B : Matrix α α F} {p : ℕ} (w w' : Fin p → Space α)
    (hf : QPh f B) (hg : QPh g (B + ∑ j, (vv (w j) (w' j) + vv (w' j) (w j)))) :
    ∃ c : Space α, wrap g = shift c * altMat w w' * wrap f := by
  obtain ⟨c, hc⟩ := (hf.mul (QPh.of_alt w w')).unique hg
  refine ⟨c, ?_⟩
  unfold altMat
  rw [shift_phase, wrap_mul, wrap_mul]
  congr 1
  funext x
  rw [hc x]; ring

end
end
end PowerSaving.GF
end OAI

#print axioms OAI.PowerSaving.GF.QPh.unique
#print axioms OAI.PowerSaving.GF.wrap_step
#print axioms OAI.PowerSaving.GF.wrap_astep
