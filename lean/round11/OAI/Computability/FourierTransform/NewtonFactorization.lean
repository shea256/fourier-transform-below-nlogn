import OAI.Computability.FourierTransform.FourierIdentities

namespace OAI

/-! Newton-factorization input to the Fourier compiler. -/
namespace PowerSaving.Spectral
open Matrix Polynomial Finset Complex
noncomputable section

/-- Toeplitz entries with lower triangular convention. -/
def rise (h : Line) (i j : ℕ) : ℂ := if j ≤ i then h (i-j) else 0

def stairs (n : ℕ) (h : Line) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => rise h i.val j.val

def gap (u : ℂ) : Line := fun i => ∏ j ∈ range i, (1-u^(j+1))

def roof (u : ℂ) : Line := fun i => ∏ j ∈ range i, (-(u^j))

def floorH (u : ℂ) : Line := fun i => (gap u i)⁻¹

def cog (u : ℂ) : Line := fun i => gap u i * roof u i

abbrev RootMat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

def fade (n : ℕ) (d : Line) : RootMat n := Matrix.diagonal (front n d)

/-- Matrix of Newton polynomial values, by its product formula. -/
def steps (n : ℕ) (u : ℂ) : RootMat n :=
    fade n (gap u) * stairs n (floorH u) * fade n (roof u)

lemma steps_apply (n : ℕ) (u : ℂ) (i j : Fin n) :
    steps n u i j = gap u i.val * rise (floorH u) i.val j.val * roof u j.val := by
  unfold steps fade
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rfl

lemma steps_diag (n : ℕ) (u : ℂ) (i : Fin n) :
    steps n u i i = cog u i.val := by simp [steps_apply,cog,rise,floorH,gap]

lemma steps_zero (n : ℕ) (u : ℂ) (i j : Fin n) (h : i<j) :
    steps n u i j=0 := by
  have hx : ¬ (j.val ≤ i.val) := by omega
  simp [steps_apply,rise,hx]

lemma roof_ne_zero {n : ℕ} (u : ℂ) (h : IsPrimitiveRoot u n) (j : ℕ) (hj : j<n) :
    roof u j ≠ 0 := by
  have hz := h.ne_zero (by omega)
  unfold roof
  exact prod_ne_zero_iff.mpr fun i _ => by simp [hz]

lemma gap_ne_zero {n : ℕ} (u : ℂ) (h : IsPrimitiveRoot u n) (j : ℕ) (hj : j<n) :
    gap u j ≠ 0 := by
  apply prod_ne_zero_iff.mpr
  intro i hi
  exact sub_ne_zero.mpr (Ne.symm (h.pow_ne_one_of_pos_of_lt (by omega)
    (Nat.lt_of_le_of_lt (mem_range.mp hi) hj)))

lemma cog_ne_zero {n : ℕ} (u : ℂ) (h : IsPrimitiveRoot u n) (j : ℕ) (hj : j<n) :
    cog u j ≠ 0 := mul_ne_zero (gap_ne_zero _ h j hj) (roof_ne_zero _ h j hj)

-- P upper from monic Newton basis
def newton (u : ℂ) : ℕ → Polynomial ℂ
  | 0 => 1
  | i+1 => newton u i * (X-C (u^i))

def bridge (n : ℕ) (u : ℂ) : RootMat n :=
  fun i j => (newton u j.val).coeff i.val

lemma newton_monic (u : ℂ) (i : ℕ) : (newton u i).Monic := by
  induction i with
  | zero => exact monic_one
  | succ i ih => exact ih.mul (monic_X_sub_C _)

lemma newton_natDegree (u : ℂ) (i : ℕ) : (newton u i).natDegree = i := by
  induction i with
  | zero => simp [newton]
  | succ i ih =>
    rw [newton,(newton_monic u i).natDegree_mul (monic_X_sub_C _),
      ih, natDegree_X_sub_C]

lemma bridge_zero (n : ℕ) (u : ℂ) (i j : Fin n) (h : j < i) :
    bridge n u i j=0 := by
  unfold bridge
  apply coeff_eq_zero_of_natDegree_lt
  rw [newton_natDegree]; exact h

lemma bridge_diag (n : ℕ) (u : ℂ) (i : Fin n) :
    bridge n u i i=1 := by
  simpa only [bridge,newton_natDegree] using (newton_monic u i.val).coeff_natDegree

lemma bridge_unit (n : ℕ) (u : ℂ) : IsUnit (bridge n u) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have hh : (bridge n u).BlockTriangular id := by
    intro i j hij
    exact bridge_zero _ _ _ _ hij
  rw [Matrix.det_of_isUpperTriangular hh]
  simp [bridge_diag]

lemma newton_zero (u : ℂ) (k i : ℕ) (hi : i<k) :
    (newton u k).eval (u^i) = 0 := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [newton,eval_mul,eval_sub,eval_X,eval_C]
    rcases eq_or_ne i k with rfl|h
    · ring
    · rw [ih (by omega), zero_mul]

lemma newton_eval {n : ℕ} (u : ℂ) (h : IsPrimitiveRoot u n) (i j : ℕ)
    (hi : i<n) (hj : j ≤ i) :
    (newton u j).eval (u^i) = gap u i * (gap u (i-j))⁻¹ * roof u j := by
  induction j with
  | zero =>
    rw [newton, eval_one, roof,prod_range_zero, Nat.sub_zero,
      mul_inv_cancel₀ (gap_ne_zero u h i hi),mul_one]
  | succ j ih =>
    let s := i-(j+1)
    have hs : i-j=s+1 := by dsimp [s]; omega
    rw [newton, eval_mul, eval_sub, eval_X, eval_C, ih (by omega),hs]
    have gh (i : ℕ) : gap u (i+1)=gap u i*(1-u^(i+1)) := prod_range_succ ..
    have rh (i : ℕ) : roof u (i+1)=roof u i * (-u^i) := prod_range_succ ..
    have up : u^i-u^j=(1-u^(s+1))*(-u^j) := by
      conv_lhs => lhs; rw [show i=s+1+j by dsimp [s]; omega, pow_add]
      ring
    change gap u i * _ * _ * _ = gap u i * (gap u s)⁻¹ * _
    have hh := gap_ne_zero u h (s+1) (by omega)
    rw [gh] at hh ⊢
    have hx := left_ne_zero_of_mul hh
    have hz := right_ne_zero_of_mul hh
    rw [up,rh]
    field_simp

lemma winds_bridge (n : ℕ) (u : ℂ) (h : IsPrimitiveRoot u n) :
    winds n u * bridge n u = steps n u := by
  ext i j
  rw [Matrix.mul_apply]
  have hf : (∑ k : Fin n, winds n u i k * bridge n u k j) =
      (newton u j.val).eval (u ^ i.val) := by
    rw [eval_eq_sum_range' (by rw [newton_natDegree]; exact j.isLt : (newton u j.val).natDegree < n),
      ← Fin.sum_univ_eq_sum_range]
    refine sum_congr rfl ?_
    intro k _
    simp [winds,bridge,pow_mul,mul_comm]
  rw [hf]
  rcases lt_or_ge i j with g|g
  · rw [newton_zero u _ _ g, steps_zero n u i j g]
  · have hh : j.val ≤ i.val := g
    rw [steps_apply, newton_eval u h _ _ i.isLt hh, rise, ite_eq_left hh, floorH]

lemma winds_symm (n : ℕ) (u : ℂ) :
    (winds n u)ᵀ = winds n u := by ext i j; simp [winds,mul_comm]

lemma cog_products (n : ℕ) (u : ℂ) (h : IsPrimitiveRoot u n) :
    (steps n u)ᵀ * bridge n u = fade n (cog u) := by
  let M := (bridge n u)ᵀ * steps n u
  have ht : (steps n u)ᵀ * bridge n u = M := by
    unfold M
    rw [← winds_bridge n u h, transpose_mul, winds_symm, Matrix.mul_assoc]
  have sym : Mᵀ=M := by
    change ((bridge n u)ᵀ * steps n u)ᵀ = _
    rw [transpose_mul,transpose_transpose,ht]
  have hz (i j : Fin n) (hij : i<j) : M i j = 0 := by
    simp only [M,Matrix.mul_apply,transpose_apply]
    refine sum_eq_zero ?_
    intro l hl
    rcases lt_or_ge i l with g|g
    · rw [bridge_zero n u l i g,zero_mul]
    · rw [steps_zero n u l j (by omega),mul_zero]
  have hd (i : Fin n) : M i i = cog u i.val := by
    simp only [M,Matrix.mul_apply,transpose_apply]
    rw [sum_eq_single i,bridge_diag,one_mul,steps_diag]
    · intro l _ hl
      rcases lt_or_ge i l with g|g
      · rw [bridge_zero n u l i g,zero_mul]
      · rw [steps_zero n u l i (by omega),mul_zero]
    · simp
  rw [ht]
  ext i j
  rcases lt_trichotomy i j with g|g|g
  · rw [hz i j g,fade,diagonal_apply,ite_eq_right (by omega)]
  · subst j; rw [hd,fade,diagonal_apply,ite_eq_left rfl]; rfl
  · rw [← sym,transpose_apply,hz j i g,fade,diagonal_apply,ite_eq_right (by omega)]

/-- Newton reduction into diagonal and Toeplitz factors (and transpose). -/
theorem winds_reduction (n : ℕ) (u : ℂ) (h : IsPrimitiveRoot u n) :
    winds n u =
      steps n u * fade n (fun i => (cog u i)⁻¹) * (steps n u)ᵀ := by
  have hh :
      fade n (fun i => (cog u i)⁻¹) * fade n (cog u)=1 := by
    unfold fade
    rw [diagonal_mul_diagonal, show (1 : RootMat n) = diagonal (fun _ => 1) from rfl]
    congr 1
    funext i
    exact inv_mul_cancel₀ (cog_ne_zero u h i.val i.isLt)
  apply (bridge_unit n u).mul_right_cancel
  rw [winds_bridge _ _ h, Matrix.mul_assoc, cog_products _ _ h, Matrix.mul_assoc, hh, mul_one]

end
end PowerSaving.Spectral

end OAI
