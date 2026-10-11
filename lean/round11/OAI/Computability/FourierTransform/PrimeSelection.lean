import OAI.Computability.FourierTransform.ChineseRemainder

namespace OAI

/- Prime supply and bounded parameters -/
namespace PowerSaving.Selection
open Finset Real
noncomputable section

def stackN (n : ℕ) := Nat.log 2 (2*n)+1

lemma stack_pos (n : ℕ) : 0< stackN n := Nat.succ_pos _

lemma stack_above (n : ℕ) :
    2*n < 2^stackN n :=
  Nat.lt_pow_succ_log_self Nat.one_lt_two _

lemma stack_pow (n : ℕ) (hn : 0<n) :
    2^stackN n ≤ 4*n := by
  have hh : 2^(Nat.log 2 (2*n)) ≤ 2*n := Nat.pow_log_le_self _ (by omega)
  rw [stackN,pow_succ]; omega

lemma stack_le (n : ℕ) (hn : 0<n) :
    stackN n ≤ 4*n := Nat.lt_two_pow_self.le.trans (stack_pow n hn)

def silo (k : ℕ) := (16*(k+4))^2

lemma silo_big (k : ℕ) : 2 < silo k := by
  have hh : 2 < 16*(k+4) := by omega
  unfold silo; nlinarith [hh]

lemma harvest (k : ℕ) :
    k+2 ≤ Nat.primeCounting (silo k) := by
  let q := silo k
  let t : ℝ := k+4
  let s : ℝ := 16*t
  have hq : (q:ℝ)=s^2 := by dsimp [q,silo,s,t]; push_cast; ring
  have ht : 4≤t := by simp [t]
  have hs : 64≤ s := by unfold s; linarith
  have he : 0< s := by linarith
  have hh : 1 < (q:ℝ) := by rw [hq]; nlinarith
  have HL : log (q:ℝ) ≤ 2*s := by
    rw [hq, Real.log_pow]
    norm_num
    have := Real.log_le_sub_one_of_pos he
    linarith
  have hk : log (2:ℝ) ≥ 2/3 := by
    have hh := Real.le_log_one_add_of_nonneg (show (0:ℝ)≤1 by norm_num)
    norm_num at hh ⊢
    exact hh
  have hu : log ((q:ℝ)+1) ≤ 1+2*s := by
    have h1 : (q:ℝ)+1 ≤ 2*q := by linarith
    have hy := Real.log_le_log (by linarith : 0<(q:ℝ)+1) h1
    rw [Real.log_mul (by norm_num) (by linarith)] at hy
    have h2 := Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num)
    linarith
  have h3 := Chebyshev.pi_ge q
  have HG : (k:ℝ)+2 ≤ Nat.primeCounting q := by
    refine le_trans ?_ h3
    rw [le_div_iff₀ (Real.log_pos hh)]
    calc
      _ ≤ t * (2*s) := by
        have hg : (k:ℝ)+2 ≤ t := by unfold t; linarith
        gcongr
      _ ≤ s^2*(2/3)-(1+2*s) := by
        have g : s=16*t := rfl
        nlinarith
      _ ≤ _ := by rw [hq] at hu ⊢; gcongr
  exact_mod_cast HG

-- odd primes up to and excluding limit
def Bar (i : ℕ) := Nat.Prime i ∧ i>2
instance (i) : Decidable (Bar i) := inferInstanceAs (Decidable (_ ∧ _))
def bars (p : ℕ) : ℕ := ∑ i ∈ range p, if Bar i then 1 else 0
lemma bars_step (i : ℕ) : bars (i+1)=bars i+(if Bar i then 1 else 0) := sum_range_succ ..
lemma bars_zero : bars 0=0 := by simp [bars]

lemma bars_count (p : ℕ) (hp : 2 ≤ p) :
    bars (p+1)+1 = Nat.primeCounting p := by
  let Q := range (p+1)
  have h (i : ℕ) : (if Bar i then 1 else 0)+(if i=2 then 1 else 0)=
      (if i.Prime then 1 else 0) := by
    by_cases g : i.Prime
    · have ht := g.two_le; simp only [Bar,g,true_and,ite_true]; split_ifs <;> omega
    · have hh : i≠2 := by intro H; rw [H] at g; exact g Nat.prime_two
      simp [g,hh,Bar]
  have hh1 : ∑ i ∈ Q, (if i=2 then 1 else 0)=1 := by
    have hg : 2<p+1 := by omega
    simp [Q,hg]
  conv_lhs => rhs; rw [← hh1]
  rw [bars]
  dsimp only [Q]
  rw [← sum_add_distrib]
  simp_rw [h]
  rw [← Nat.primesLE_card_eq_primeCounting]
  -- filter
  rw [← sum_filter]
  simp [Nat.primesLE,Nat.primesBelow]

lemma bar_bounds (k : ℕ) :
    k < bars (silo k+1) := by
  have H := bars_count _ (silo_big k).le
  have G := harvest k
  omega

end
end PowerSaving.Selection

end OAI
