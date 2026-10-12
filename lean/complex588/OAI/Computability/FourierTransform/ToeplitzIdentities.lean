import OAI.Computability.FourierTransform.NewtonFactorization

namespace OAI

/-! Finite Toeplitz formulas needed by exact-width construction. -/
namespace PowerSaving.Spectral
open Matrix Polynomial Finset Complex
noncomputable section

def stencil (v : ℕ) (h x : Line) : Line :=
  fun i => ∑ j ∈ range v, rise h i j * x j

def creep (v : ℕ) (h x : Line) : Line :=
  fun i => ∑ j ∈ range v, rise h j i * x j

lemma front_stencil (v : ℕ) (h x : Line) :
    front v (stencil v h x)= stairs v h *ᵥ front v x := by
  ext i
  exact (Fin.sum_univ_eq_sum_range (fun j => rise h i.val j*x j) v).symm

lemma front_creep (v : ℕ) (h x : Line) :
    front v (creep v h x)=(stairs v h)ᵀ *ᵥ front v x := by
  ext i
  exact (Fin.sum_univ_eq_sum_range (fun j => rise h j i.val*x j) v).symm

lemma stencil_reversed (v : ℕ) (h x : Line) (i : ℕ) (hi : i<v) :
    stencil v h (fun j => x (v-1-j)) (v-1-i) = creep v h x i := by
  unfold stencil creep
  rw [← sum_range_reflect (fun j => rise h j i*x j) v]
  refine sum_congr rfl ?_
  intro j hj
  replace hj := mem_range.mp hj
  simp only [rise]
  split_ifs with h1 h2 <;> first | omega | congr 2 <;> omega

lemma rise_both (h : Line) (s i j : ℕ) :
    rise h (s+i) (s+j)=rise h i j := by
  simp [rise, show s+i-(s+j)=i-j by omega]

lemma stencil_left (v w : ℕ) (h x : Line) (i : ℕ) (hi : i<v) :
    stencil (v+w) h x i=stencil v h x i := by
  unfold stencil
  rw [sum_range_add]
  have hz (j : ℕ) : rise h i (v+j) = 0 := by
    rw [rise,ite_eq_right (by omega)]
  simp_rw [hz]; simp

lemma stencil_right (v w : ℕ) (h x : Line) (i : ℕ) :
    stencil (v+w) h x (v+i)=stencil v h x (v+i)+stencil w h (fun j => x (v+j)) i := by
  unfold stencil
  rw [sum_range_add]; simp_rw [rise_both]

lemma stencil_congr (v : ℕ) (h : Line) {x y : Line} (H : ∀ i<v, x i=y i) :
    stencil v h x = stencil v h y := funext fun _ => sum_congr rfl
      fun _ hj => congr_arg (_*·) (H _ (mem_range.mp hj))

/-- Reciprocal sequence, with finite truncated calls. -/
def recoil (h : Line) (j : ℕ) : ℂ :=
  match j with
  | 0 => (h 0)⁻¹
  | k+1 => -(∑ l : Fin (k+1), recoil h (k-l.val)*h (l.val+1))/(h 0)
termination_by j
decreasing_by all_goals omega

lemma recoil_zero (h : Line) : recoil h 0=(h 0)⁻¹ := by rw [recoil]

lemma recoil_next (h : Line) (j : ℕ) :
    recoil h (j+1)=-(∑ i ∈ range (j+1), recoil h (j-i)*h (i+1))/(h 0) := by
  rw [← Fin.sum_univ_eq_sum_range]
  rw [recoil]

lemma recoil_conv (h : Line) (hh : h 0≠0) (j : ℕ) :
    (∑ i ∈ range (j+1), recoil h (j-i) * h i) =
      if j=0 then 1 else 0 := by
  cases j with
  | zero => simp [recoil_zero,hh]
  | succ j =>
    rw [sum_range_succ']
    simp only [Nat.add_sub_add_right,
      Nat.sub_zero, Nat.succ_ne_zero, ↓reduceIte]
    rw [recoil_next]
    field_simp
    ring

lemma recoil_orth (v : ℕ) (h : Line) (hh : h 0≠0) (i j : ℕ) (hi : i<v) :
    (∑ k ∈ range v, rise (recoil h) i k * rise h k j) =
    if i=j then 1 else 0 := by
  let f (k : ℕ) := rise (recoil h) i k * rise h k j
  have hz (k : ℕ) : i<k ∨ k<j → f k=0 := by
    unfold f rise
    rintro h1
    split_ifs <;> first | omega | ring
  change (∑ k ∈ range v, f k) = _
  rcases lt_or_ge i j with g|g
  · rw [sum_eq_zero (fun k _ => hz k (by omega)),ite_eq_right (by omega)]
  · let p := i-j
    have hp : j+(p+1)=i+1 := by unfold p; omega
    have hs : (∑ k ∈ range v, f k) =
        ∑ k ∈ range (p+1), recoil h (p-k)*h k := by
      conv_lhs =>
        rw [show v=j+(p+1)+(v-(i+1)) by omega,sum_range_add,sum_range_add]
      have H (k : ℕ) : f (j+(p+1)+k)=0 := hz _ (by omega)
      simp_rw [H]
      rw [sum_const_zero,add_zero,sum_eq_zero (fun k (hk : k∈range j) => hz k (.inr
        (mem_range.mp hk))),zero_add]
      refine sum_congr rfl ?_
      intro k hk
      replace hk := mem_range.mp hk
      simp only [f,rise, ite_eq_left (show j+k ≤ i by omega),ite_eq_left (show j ≤ j+k by omega),
        show i-(j+k)=p-k by omega, show j+k-j=k by omega]
    rw [hs,recoil_conv h hh]
    split_ifs <;> first | rfl | (unfold p at *; omega)

lemma recoil_back (v : ℕ) (h x : Line) (hh : h 0≠0) (i : ℕ) (hi : i<v) :
    stencil v (recoil h) (stencil v h x) i = x i := by
  simp only [stencil,mul_sum,← mul_assoc]
  rw [sum_comm]
  simp only [← sum_mul]
  simp [recoil_orth v h hh i _ hi, ite_mul, hi]

end
end PowerSaving.Spectral

end OAI
