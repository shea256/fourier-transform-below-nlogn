import OAI.Computability.FourierTransform.UniformBounds

namespace OAI

/- asymptotic analysis, one n for both length functions -/
namespace PowerSaving
open RAM Bench Selection Slant Filter Asymptotics Real
noncomputable section

namespace Skies

abbrev Tm (n : ℕ) : ℝ := log (n:ℝ)
abbrev Qm (n : ℕ) : ℝ := log (Tm n)

lemma Ttop : Tendsto Tm atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
lemma Qtop : Tendsto Qm atTop atTop := Real.tendsto_log_atTop.comp Ttop
lemma log2_min : 2/3 ≤ log (2:ℝ) := by
  have hh := le_log_one_add_of_nonneg (show (0:ℝ)≤1 by norm_num)
  norm_num at *
  exact hh

-- n is problem size, N allowed between n and 2n
lemma stack_lim (n N : ℕ) (hn : 0<n) (h : n≤N) (hk : N ≤ 2*n) (ht : 1≤Tm n) :
    (stackN N:ℝ) ≤ 10 * Tm n := by
  let k := Nat.log 2 (2*N)
  have H : 2^k ≤ 2*N := Nat.pow_log_le_self _ (by omega)
  have H0 : 2^k ≤ 4*n := by omega
  have he : 0<(n:ℝ) := by exact_mod_cast hn
  have HH := log_le_log (by positivity : 0<(2:ℝ)^k)
    (show (2:ℝ)^k ≤ 4*n by exact_mod_cast H0)
  rw [log_pow,log_mul (by norm_num) he.ne'] at HH
  have H4 := log_le_sub_one_of_pos (show (0:ℝ)<4 by norm_num)
  change (((k+1:ℕ):ℝ)) ≤ _
  push_cast
  unfold Tm at *
  nlinarith [log2_min,show 0≤(k:ℝ) by positivity]

lemma order_pow_lim (n N : ℕ) (hn : 0<n) (h : n≤N) (hk : N ≤ 2*n) (ht : 1 ≤ Tm n) :
    (2:ℝ)^orderE N ≤ 10^6*Tm n^2 := by
  have hh : (2:ℝ)^orderE N ≤ 8*harvestN N := by exact_mod_cast orderE_small N
  refine hh.trans ?_
  unfold harvestN silo; push_cast
  have hg := stack_lim n N hn h hk ht
  calc
    _ ≤ 8*(16*(14*Tm n))^2 := by gcongr; linarith
    _ ≤ _ := by nlinarith [sq_nonneg (Tm n)]

lemma order_lim (n N : ℕ) (hn : 0<n) (h : n≤N) (hk : N ≤ 2*n) (ht : 1 ≤ Tm n) (hu : 1 ≤ Qm n) :
    (orderE N:ℝ) ≤ 3*10^6 * Qm n := by
  have H := log_le_log (by positivity : 0<(2:ℝ)^orderE N) (order_pow_lim n N hn h hk ht)
  have he : 0<Tm n := by linarith
  rw [log_pow,log_mul (by norm_num) (by positivity),log_pow,log_pow] at H
  have H4 := log_le_sub_one_of_pos (show 0 < (10:ℝ) by norm_num)
  unfold Qm at *
  have h0 : 0 ≤ (orderE N:ℝ) := by positivity
  push_cast at H
  nlinarith [log2_min]

lemma score_lim (n N : ℕ) (hn : 0<n) (h : n≤N) (hk : N ≤ 2*n) (ht : 1 ≤ Tm n) (hu : 1 ≤ Qm n) :
    (score (orderE N):ℝ)+1 ≤ 10^32*Qm n^2 := by
  have H := order_lim n N hn h hk ht hu
  have hk : (score (orderE N):ℝ) ≤ 20000000*((orderE N:ℝ)+1)^2+7 := by
    exact_mod_cast score_le (orderE N)
  calc
    _ ≤ (20000000*((orderE N:ℝ)+1)^2+7)+1 := by gcongr
    _ ≤ (20000000*(4*10^6*Qm n)^2+7)+1 := by gcongr; linarith
    _ ≤ _ := by nlinarith

lemma hills_lim (n N : ℕ) (hn : 0<n) (h : n≤N) (hk : N ≤ 2*n) (ht : 1 ≤ Tm n) :
    (hills (barge N).l:ℝ) ≤ 100*Tm n^alpha := by
  have he : 0<Tm n := by linarith
  have H := stack_lim n N hn h hk ht
  have G : ((barge N).l:ℝ) ≤ stackN N := by
    exact_mod_cast (barge_spec N (lt_of_lt_of_le hn h)).count
  have hg := alpha_pos
  refine (hills_real _).trans ?_
  calc
    _ ≤ 2*(11*Tm n)^alpha := by gcongr; linarith
    _ = 2*(11^alpha*Tm n^alpha) := by rw [mul_rpow (by norm_num) he.le]
    _ ≤ 2*(11^(1:ℝ)*Tm n^alpha) := by gcongr <;> first | exact alpha_lt.le | norm_num
    _ ≤ _ := by
      rw [rpow_one]
      have hTT : 0 < Tm n^alpha := by positivity
      linarith

def flight (n : ℕ) := (n:ℝ)*(Tm n)^alpha*Qm n^2

lemma leg_lim (n N : ℕ) (hn : 0<n) (h : n≤N) (hk : N ≤ 2*n) (ht : 1 ≤ Tm n) (hu : 1 ≤ Qm n) :
    (leg N:ℝ) ≤ 10^40*flight n := by
  have hg : (barge N).vol ≤ 8*n := by
    have hh := (barge_spec N (by omega)).upper
    omega
  have hh : ((barge N).vol:ℝ) ≤ 8*n := by exact_mod_cast hg
  have hT : 0 < Tm n := by linarith
  unfold leg; push_cast
  calc
    _ ≤ (10^32 * Qm n^2)*((8*n)*(100*Tm n^alpha)) :=
      mul_le_mul (score_lim n N hn h hk ht hu)
        (mul_le_mul hh (hills_lim n N hn h hk ht) (by positivity) (by positivity))
        (by positivity) (by positivity)
    _ = 8*100*10^32*flight n := by unfold flight; ring
    _ ≤ _ := by
      have hh : 0 ≤ flight n := by unfold flight; positivity
      gcongr; norm_num

lemma flight_big (n : ℕ) (ht : 1 ≤ Tm n) (hu : 1 ≤ Qm n) :
    (n:ℝ) ≤ flight n := by
  have H := Real.one_le_rpow ht alpha_pos.le
  unfold flight
  calc
    (n:ℝ) = n*1*1 := by ring
    _ ≤ _ := by gcongr; nlinarith

-- little o fournishes eventual caps.
lemma dwarf {v : ℕ→ℝ} (h : Tendsto v atTop atTop) (d : ℕ) {p c : ℝ} (hp : 0<p) (hc : 0<c) :
    ∀ᶠ n in atTop, log (v n)^d ≤ c*v n^p := by
  have H := (isLittleO_log_rpow_rpow_atTop (d:ℝ) hp).comp_tendsto h
  have hg := H.def hc
  filter_upwards [hg,h.eventually_ge_atTop 1] with n hn he
  have he' : 0<v n := by linarith
  change ‖log (v n)^(d:ℝ)‖ ≤ c*‖v n^p‖ at hn
  rw [rpow_natCast,Real.norm_of_nonneg (pow_nonneg (Real.log_nonneg he) _),
    Real.norm_of_nonneg (by positivity)] at hn
  exact hn

variable {N : ℕ→ℕ}
-- initial branch disappears
lemma docks_ev (h : ∀ n:ℕ,n ≤ N n ∧ N n ≤ 2*n) :
    ∀ᶠ n in atTop, Ports (N n) := by
  have H := dwarf (v:=fun n => (n:ℝ)) tendsto_natCast_atTop_atTop 2
    (c:=1/10^6) (p:=1) (by norm_num) (by norm_num)
  filter_upwards [H,eventually_gt_atTop 0,Ttop.eventually_ge_atTop 1] with n hh hn ht
  rw [rpow_one] at hh
  have hh' : (Tm n)^2 ≤ 1/10^6*n := hh
  have hh1 := order_pow_lim n (N n) hn (h n).1 (h n).2 ht
  have hh2 : (2:ℝ)^(orderE (N n)) ≤ n := by linarith
  exact (show 2^orderE (N n) ≤ n by exact_mod_cast hh2).trans (h n).1

lemma polylog_ev (h : ∀ n:ℕ,n ≤ N n ∧ N n ≤ 2*n) (d : ℕ) :
    ∀ᶠ n in atTop, ((stackN (N n):ℝ)+2)^d ≤ n := by
  have h0 : 0< (12:ℝ)^d := by positivity
  have H := dwarf (v:=fun n => (n:ℝ)) tendsto_natCast_atTop_atTop d
    (c:=((12:ℝ)^d)⁻¹) (p:=1) (by norm_num) (by positivity)
  filter_upwards [H,eventually_gt_atTop 0,Ttop.eventually_ge_atTop 1] with n hh hn ht
  rw [rpow_one] at hh
  have hh' : (Tm n)^d ≤ ((12:ℝ)^d)⁻¹*n := hh
  have hh1 := stack_lim n (N n) hn (h n).1 (h n).2 ht
  calc
    _ ≤ (12*Tm n)^d := by gcongr; linarith
    _ ≤ _ := by
      rw [mul_pow]
      calc
        _ ≤ _ := mul_le_mul_of_nonneg_left hh' h0.le
        _ = _ := by rw [← mul_assoc,mul_inv_cancel₀ h0.ne',one_mul]

lemma wind_ev (h : ∀ n:ℕ,n ≤ N n ∧ N n ≤ 2*n) (d : ℕ) :
    ∀ᶠ n in atTop,(fairwind d (N n):ℝ)+1 ≤ 10^41*flight n := by
  filter_upwards [docks_ev h,polylog_ev h d,eventually_gt_atTop 0,Ttop.eventually_ge_atTop 1,
    Qtop.eventually_ge_atTop 1] with n hh hk hn ht hu
  unfold fairwind Bench.surf
  rw [ite_eq_left hh,Nat.add_zero]
  push_cast
  have hp := leg_lim n (N n) hn (h n).1 (h n).2 ht hu
  have he := flight_big n ht hu
  have he' : 1≤(n:ℝ) := by exact_mod_cast hn
  have hx : (N n:ℝ) ≤ 2*n := by exact_mod_cast (h n).2
  linarith

lemma lunch_big (a b : Ration) (h : ∀ n:ℕ,n ≤ N n ∧ N n ≤ 2*n) :
    (fun n : ℕ => (lunch a b N n:ℝ)) =O[atTop] flight := by
  let W := lunch a b N
  refine isBigO_iff.mpr ⟨(a.c:ℝ)*10^41+1+(b.c:ℝ)*10^41,?_⟩
  filter_upwards [wind_ev h a.d,wind_ev h b.d,eventually_gt_atTop 0,Ttop.eventually_ge_atTop 1,
    Qtop.eventually_ge_atTop 1] with n hh hk hn ht hu
  have he := flight_big n ht hu
  have h1 : 1≤(n:ℝ) := by exact_mod_cast hn
  rw [Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg (by linarith)]
  unfold lunch calorie
  push_cast; simp only [add_mul,one_mul,mul_assoc]
  gcongr
  exact h1.trans he

end Skies
end
end PowerSaving

end OAI
