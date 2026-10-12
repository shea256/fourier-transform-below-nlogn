import OAI.Computability.FourierTransform.FourierIdentities

namespace OAI

/- Positive/negative chirps and consequence for linear convolution. -/
namespace PowerSaving
open Finset Complex Matrix
noncomputable section

namespace Spectral

-- ret true for inverse signs
def pr : Bool→ℕ→ℂ
  | false => root
  | true => fun n => (root n)⁻¹

lemma primitive_pr (n : ℕ) (hn : 0<n) (r : Bool) :
    IsPrimitiveRoot (pr r n) n := by
  cases r
  · exact root_primitive n hn
  · exact (root_primitive n hn).inv
lemma twice_pr (n : ℕ) (hn : 0<n) (r : Bool) :
    (pr r (2*n))^2 = pr r n := by
  cases r with
  | false => exact root_mul_pow 2 n (by norm_num) hn
  | true => simp [pr,inv_pow,root_mul_pow 2 n (by norm_num) hn]
lemma cyc_formula {u : ℂ} {n : ℕ} (hu : IsPrimitiveRoot u n) (x h : Line) {i} (hi : i<n) :
    (n:ℂ)⁻¹ * freq n u⁻¹ (fun j => freq n u h j * freq n u x j) i =
    cyclic n h x i := by
  simp_rw [← freq_cyclic hu.pow_eq_one]
  exact freq_inv hu (cyclic n h x) i hi

lemma range_pad (n N : ℕ) (h : n ≤ N) (x : Line) :
    ∑ i ∈ range N, (if i < n then x i else 0) = ∑ i ∈ range n,x i := by
  induction N, h using Nat.le_induction with
  | base =>
    exact sum_congr rfl fun i hi => ite_eq_left (mem_range.mp hi)
  | succ m hm ih => rw [sum_range_succ,ih,ite_eq_right (not_lt.mpr hm),add_zero]

def epschirp (z : ℂ) : Line := fun i => z ^ (i*i)

lemma eps_eq_sq (z : ℂ) (h : z≠0) (i j k : ℕ)
    (hk : i=j+k ∨ j=i+k) :
    epschirp z i * (epschirp z k)⁻¹ * epschirp z j = (z^2)^(i*j) := by
  have hh : i*i+j*j=2*(i*j)+k*k := by rcases hk with rfl|rfl <;> ring
  unfold epschirp
  rw [show z^(i*i) * (z^(k*k))⁻¹ * z^(j*j)=z^(i*i+j*j)*(z^(k*k))⁻¹ by
    rw [pow_add]; ring, hh,pow_add,mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ h),mul_one,
    pow_mul]

def chirp_seed (n : ℕ) (z : ℂ) (x : Line) : Line :=
  fun i => if i<n then epschirp z i * x i else 0

def legdist (n N : ℕ) (i : ℕ) := if i < n then i else N-i

def fall (n N : ℕ) (z : ℂ) : Line :=
  fun i => (epschirp z (legdist n N i))⁻¹

lemma chirp (z : ℂ) (h : z≠0) (x : Line) {n N : ℕ} (hn : 2*n≤N) (i : ℕ) (hi : i<n) :
    epschirp z i * (cyclic N (fall n N z) (chirp_seed n z x) i) =
    freq n (z^2) x i := by
  have hh (j : ℕ) (hj : j<n) :
      epschirp z i * (fall n N z (predAt N i j) * (epschirp z j * x j)) =
      (z^2)^(i*j)*x j := by
    unfold fall; rw [← mul_assoc,← mul_assoc]
    rw [eps_eq_sq z h i j _ ?_]
    unfold legdist predAt; split_ifs <;> omega
  simp only [cyclic,chirp_seed,mul_sum,mul_ite,mul_zero,freq]
  rw [range_pad n N (by omega)]
  exact sum_congr rfl fun j hj => hh j (mem_range.mp hj)

def pointC (n : ℕ) (u : ℂ) (h x : Line) : Line :=
  fun i => freq n u h i * freq n u x i

def fetchC (n : ℕ) (u : ℂ) (h x : Line) : Line :=
  freq n u⁻¹ (pointC n u h x)

lemma chirps (n N : ℕ) (hn : 0<n) (hh : 2*n ≤ N) (ret : Bool) (x : Line)
    (i : ℕ) (hi : i<n) :
    let z := pr ret (2*n)
    epschirp z i * ((N:ℂ)⁻¹ * fetchC N (pr false N) (fall n N z) (chirp_seed n z x) i)
      = freq n (pr ret n) x i := by
  have hk := primitive_pr N (by omega) false
  have ht := (primitive_pr (2*n) (by omega) ret).ne_zero (by omega)
  dsimp only [fetchC,pointC]
  unfold pointC
  rw [cyc_formula hk _ _ (by omega),chirp _ ht _ hh _ hi,twice_pr _ hn ret]

def padline (n : ℕ) (x : Line) : Line := fun i => if i<n then x i else 0

lemma conv_pad_row (n : ℕ) (x y : Line) {i : ℕ} (hi : i < 2*n-1) (r : ℕ) (hr : r<n) :
    padline n y (predAt (2*n-1) i r) * x r =
    ∑ j ∈ range n, if r+j=i then x r*y j else 0 := by
  unfold padline predAt
  by_cases h : r ≤ i ∧ i-r<n
  · obtain ⟨h,g⟩ := h
    rw [ite_eq_left h,ite_eq_left g]
    rw [sum_eq_single (i-r)]
    · rw [ite_eq_left (by omega),mul_comm]
    · intro b _ h; rw [ite_eq_right (by omega)]
    · intro k; have := k (mem_range.mpr g); contradiction
  · have hh (j : ℕ) (hj : j ∈ range n) : r+j≠i := by have := mem_range.mp hj; omega
    rw [sum_eq_zero (fun j hj => ite_eq_right (hh j hj))]
    split_ifs <;> first | rw [zero_mul] | omega

lemma cyclic_pad (n : ℕ) (x y : Line) (i : ℕ) (hi : i < 2*n-1) :
    cyclic (2*n-1) (padline n y) (padline n x) i =
    ∑ r ∈ range n, ∑ j ∈ range n, if r+j=i then x r*y j else 0 := by
  unfold cyclic padline
  simp_rw [mul_ite,mul_zero]
  rw [range_pad n (2*n-1) (by omega)]
  exact sum_congr rfl fun j hj => conv_pad_row n x y hi j (mem_range.mp hj)

lemma cyclic_pad_front (n : ℕ) (x y : Line) :
    front (2*n-1) (cyclic (2*n-1) (padline n y) (padline n x)) =
    conv n (front n x) (front n y) := by
  funext i
  simp only [front,cyclic_pad n x y _ i.isLt,conv]
  have hh (r : ℕ) : ∑ j : Fin n,(if r+j.val=i.val then x r*y j.val else 0) =
      ∑ j ∈ range n, if r+j=i.val then x r*y j else 0 :=
    Fin.sum_univ_eq_sum_range (fun j => if r+j=i.val then x r*y j else 0) n
  simp_rw [hh]
  exact (Fin.sum_univ_eq_sum_range (fun r => ∑ j ∈ range n, if r+j=i.val then x r*y j else 0) n).symm

lemma freq_pad_row (n : ℕ) (x y : Line) (i : ℕ) (hi : i < 2*n-1) :
    let N := 2*n-1
    (N:ℂ)⁻¹*freq N (pr true N)
      (pointC N (pr false N) (padline n x) (padline n y)) i
      = cyclic N (padline n y) (padline n x) i := by
  let N := 2*n-1
  have H := cyc_formula (primitive_pr N (by dsimp [N]; omega) false)
    (padline n x) (padline n y) hi
  have h (j : ℕ) : pointC N (pr false N) (padline n x) (padline n y) j =
      freq N (pr false N) (padline n y) j * freq N (pr false N) (padline n x) j :=
    mul_comm _ _
  change (N:ℂ)⁻¹* freq N (pr false N)⁻¹ (pointC _ _ _ _) i = _
  rw [show pointC N (pr false N) (padline n x) (padline n y) =
    (fun j => freq N (pr false N) (padline n y) j * freq N (pr false N) (padline n x) j) from
    funext h]; exact H

lemma dft_front (n : ℕ) (x : Line) :
    dft n (front n x) = front n (freq n (pr false n) x) :=
  funext fun i => Fin.sum_univ_eq_sum_range (fun j => (root n)^(i.val*j)*x j) n

def extendLine {n : ℕ} (x : Vec n) : Line := fun i => if h : i<n then x ⟨i,h⟩ else 0
lemma front_exact {n : ℕ} (x : Vec n) : front n (extendLine x) = x := by
  funext i; simp [front,extendLine,i.isLt]

end Spectral
end
end PowerSaving

end OAI
