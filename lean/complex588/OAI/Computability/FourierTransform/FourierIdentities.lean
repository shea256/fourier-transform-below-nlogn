import OAI.Computability.FourierTransform.Goal

namespace OAI

/- Elementary finite Fourier formulas.
Values beyond a given length are irrelevant. Using natural ranges eases index arithmetic. -/
namespace PowerSaving
open Complex Matrix Finset
noncomputable section

abbrev Line := ℕ → ℂ

namespace Spectral

def freq (n : ℕ) (u : ℂ) (x : Line) : Line :=
  fun i => ∑ j ∈ range n, u ^ (i*j) * x j

def winds (n : ℕ) (u : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => u ^ (i.val*j.val)

def front (n : ℕ) (x : Line) : Vec n := fun i => x i.val

lemma front_freq (n : ℕ) (u : ℂ) (x : Line) :
    front n (freq n u x) = winds n u *ᵥ front n x := by
  funext i
  exact (Fin.sum_univ_eq_sum_range (fun j => u^(i.val*j)*x j) n).symm

lemma root_primitive (n : ℕ) (hn : 0 < n) : IsPrimitiveRoot (root n) n :=
  Complex.isPrimitiveRoot_exp n (by omega)

lemma root_four : root 4 = I := by
  unfold root ExactFourier.zeta
  convert! Complex.exp_pi_div_two_mul_I using 2
  push_cast
  ring

lemma root_mul_pow (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    (root (m*n))^m = root n := by
  unfold root ExactFourier.zeta
  rw [← exp_nat_mul]
  have hm' : (m:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn' : (n:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  congr 1
  push_cast
  field_simp

lemma root_factor {n m : ℕ} (hn : 0<n) (hm : m ∣ n) :
    (root n)^(n/m)=root m := by
  have h := Nat.div_mul_cancel hm
  have h1 : m ≠ 0 := by
    intro g; simp [g] at h; omega
  have h2 : n/m ≠ 0 := by
    intro g; simp [g] at h; omega
  exact ((congrArg (fun a : ℕ => root a ^ (n/m)) h).symm).trans
    (root_mul_pow (n/m) m (Nat.pos_of_ne_zero h2) (Nat.pos_of_ne_zero h1))

lemma power_mod {u : ℂ} {n : ℕ} (hu : u^n=1) (i : ℕ) :
    u^(i%n)=u^i := by
  have h := congrArg (fun a : ℕ => u^a) (Nat.mod_add_div i n)
  simpa [pow_add, pow_mul, hu] using h

lemma norm_of_root {n : ℕ} {u : ℂ} (hn : 0<n) (hu : u^n=1) :
    ‖u‖=1 :=
  (pow_left_inj₀ (norm_nonneg _) (by norm_num) (by omega : n ≠ 0)).mp (by rw [← norm_pow,
    hu, norm_one, one_pow])

lemma conj_of_root {n : ℕ} {u : ℂ} (hn : 0<n) (hu : u^n=1) :
    (starRingEnd ℂ) u = u⁻¹ := by
  have h := norm_of_root hn hu
  have g : normSq u = 1 := by rw [← Complex.sq_norm, h, one_pow]
  exact (inv_eq_of_mul_eq_one_right (by rw [Complex.mul_conj,g,Complex.ofReal_one])).symm

lemma freq_congr {n : ℕ} {x y : Line} (h : ∀ i < n, x i=y i) (u : ℂ) :
    freq n u x = freq n u y := by
  funext j
  exact sum_congr rfl fun i hi => by rw [h i (mem_range.mp hi)]

lemma freq_add (n : ℕ) (u : ℂ) (x y : Line) :
    freq n u (x+y) = freq n u x + freq n u y := by
  ext i; simp [freq, mul_add, sum_add_distrib]

lemma freq_scale (n : ℕ) (u a : ℂ) (x : Line) :
    freq n u (fun j => a*x j) = fun i => a*freq n u x i := by
  ext i; simp [freq, mul_left_comm, mul_sum]

lemma freq_period {n : ℕ} {u : ℂ} (hu : u^n=1) (x : Line) (i : ℕ) :
    freq n u x (n+i) = freq n u x i := by
  simp only [freq, add_mul,pow_add,pow_mul,hu,one_pow,one_mul]

-- Orthogonality in inverse formula
lemma orth {n : ℕ} {u : ℂ} (hu : IsPrimitiveRoot u n) (i j : ℕ)
    (hi : i<n) (hj : j<n) :
    (∑ l ∈ range n, u⁻¹ ^ (i*l) * u ^ (l*j)) =
    if i=j then (n:ℂ) else 0 := by
  have hz : u ≠ 0 := hu.ne_zero (by omega)
  have form (l : ℕ) :
      u⁻¹ ^ (i*l) * u ^ (l*j)=(u^j/u^i)^l := by
    rw [Nat.mul_comm l j]
    simp only [pow_mul, div_pow, inv_pow]
    ring
  simp_rw [form]
  by_cases h : i=j
  · simp [h, hz]
  · rw [ite_eq_right h, geom_sum_eq]
    · have a (j : ℕ) : (u^j)^n=1 := by rw [← pow_mul, Nat.mul_comm,pow_mul,hu.pow_eq_one,one_pow]
      rw [div_pow,a,a]
      norm_num
    · intro hh
      exact h (hu.pow_inj hi hj ((div_eq_one_iff_eq (pow_ne_zero _ hz)).mp hh).symm)

lemma freq_back {n : ℕ} {u : ℂ} (hu : IsPrimitiveRoot u n) (x : Line)
    (i : ℕ) (hi : i<n) :
    freq n u⁻¹ (freq n u x) i = n * x i := by
  simp only [freq,mul_sum]
  rw [sum_comm]
  simp only [← mul_assoc,← sum_mul]
  refine Eq.trans (b := ∑ j ∈ range n, (if i=j then (n:ℂ) else 0) * x j) ?_ ?_
  · exact sum_congr rfl fun j hj => by rw [orth hu i j hi (mem_range.mp hj)]
  · simp [ite_mul, hi]

lemma freq_inv {n : ℕ} {u : ℂ} (hu : IsPrimitiveRoot u n) (x : Line)
    (i : ℕ) (hi : i<n) :
    (n:ℂ)⁻¹ * freq n u⁻¹ (freq n u x) i = x i := by
  rw [freq_back hu x i hi, ← mul_assoc, inv_mul_cancel₀,one_mul]
  exact Nat.cast_ne_zero.mpr (by omega)

-- Circulant acts by difference of row & column
def predAt (n i j : ℕ) := if j ≤ i then i-j else i+n-j

lemma pred_lt {n i j : ℕ} (hi : i<n) (hj : j<n) :
    predAt n i j < n := by unfold predAt; split <;> omega

lemma sum_pred (f : ℕ → ℂ) (n j : ℕ) (hj : j<n) :
    ∑ i ∈ range n, f (predAt n i j) = ∑ i ∈ range n, f i := by
  refine sum_bij (fun a _ => predAt n a j) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro a ha; exact mem_range.mpr (pred_lt (mem_range.mp ha) hj)
  · simp only [mem_range]; intro a ha b hb h
    unfold predAt at h
    split_ifs at h <;> omega
  · simp only [mem_range]; intro i hi
    by_cases h : i+j<n
    · refine ⟨i+j,h,?_⟩
      unfold predAt; split <;> omega
    · refine ⟨i+j-n,by omega,?_⟩
      unfold predAt; split <;> omega

lemma pow_pred {n : ℕ} {u : ℂ} (hu : u^n=1) {i j : ℕ} (hj : j<n) (k : ℕ) :
    u^(k*i)=u^(k*(predAt n i j))*u^(k*j) := by
  rw [← pow_add,← mul_add]
  unfold predAt; split
  case isTrue h => rw [Nat.sub_add_cancel h]
  case isFalse h =>
    rw [Nat.sub_add_cancel (by omega),mul_add,pow_add,Nat.mul_comm k n, pow_mul u n, hu, one_pow,mul_one]

def cyclic (n : ℕ) (h x : Line) : Line :=
  fun i => ∑ j ∈ range n, h (predAt n i j) * x j

lemma freq_cyclic {n : ℕ} {u : ℂ} (hu : u^n=1) (h x : Line) (k : ℕ) :
    freq n u (cyclic n h x) k = freq n u h k * freq n u x k := by
  have form (j : ℕ) (hj : j ∈ range n) :
      ∑ i ∈ range n, u^(k*i)*(h (predAt n i j) * x j) = freq n u h k * (u^(k*j)*x j) := by
    unfold freq
    rw [← sum_pred (fun i => u^(k*i)*h i) n j (mem_range.mp hj),sum_mul]
    refine sum_congr rfl ?_
    intro i hi
    rw [pow_pred hu (mem_range.mp hj) k]
    ring
  unfold freq
  simp only [cyclic,mul_sum]
  rw [sum_comm]
  exact sum_congr rfl form

-- Binary recursion
lemma sum_eo (n : ℕ) (f : ℕ→ℂ) :
    ∑ i ∈ range (n+n), f i =
    ∑ i ∈ range n, f (2*i) + ∑ i ∈ range n, f (2*i+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show n+1+(n+1)=n+n+1+1 by omega]
    rw [sum_range_succ, sum_range_succ, ih, sum_range_succ, sum_range_succ]
    rw [show n+n=2*n by omega]; ring

lemma freq_eo (n : ℕ) (u : ℂ) (i : ℕ) (x : Line) :
    freq (n+n) u x i =
    freq n (u^2) (fun j => x (2*j)) i +
    u^i * freq n (u^2) (fun j => x (2*j+1)) i := by
  simp only [freq,sum_eo,mul_sum]
  have A (j : ℕ) : i*(2*j)=2*(i*j) := by ring
  simp_rw [mul_add,A,pow_add,mul_one,← pow_mul]
  simp [mul_comm, mul_assoc,mul_left_comm]

lemma even_prim {n : ℕ} {u : ℂ} (hu : IsPrimitiveRoot u (n+n)) :
    IsPrimitiveRoot (u^2) n := by
  have h := hu.pow_of_dvd (p:=2) (by omega) (by exact ⟨n,by omega⟩)
  rwa [show (n+n)/2=n by omega] at h

lemma half_power {n : ℕ} {u : ℂ} (hn : 0<n) (hu : IsPrimitiveRoot u (n+n)) :
    u^n = -1 := by
  have h : (u^n)^2=(1:ℂ)^2 := by rw [pow_two,← pow_add, hu.pow_eq_one, one_pow]
  exact (sq_eq_sq_iff_eq_or_eq_neg.mp h).resolve_left (hu.pow_ne_one_of_pos_of_lt
    (by omega) (by omega))

lemma freq_eo' {n : ℕ} {u : ℂ} (hn : 0<n) (hu : IsPrimitiveRoot u (n+n))
    (i : ℕ) (x : Line) :
    freq (n+n) u x (n+i) =
    freq n (u^2) (fun j => x (2*j)) i -
    u^i * freq n (u^2) (fun j => x (2*j+1)) i := by
  rw [freq_eo, freq_period (even_prim hu).pow_eq_one,
    freq_period (even_prim hu).pow_eq_one, pow_add, half_power hn hu]
  ring

end Spectral
end
end PowerSaving

end OAI
