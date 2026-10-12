import OAI.Computability.FourierTransform.Asymptotics
import OAI.Computability.FourierTransform.RegisterBounds

namespace OAI

/-!
Exact uniform Fourier transforms and convolution.

The construction formalizes the exact arithmetic algorithms of
*An explicit power saving for the exact discrete Fourier transform* (OpenAI).
The finite phase network originates in the complex construction of
*Integer multiplication below n log n*.

`transform_main` and `convolution_main` give fixed finite RAM programs, including
preparation and index work, polynomial storage bounds, and a canonical root whose
order is computed from the input length. Each includes the paper exponent, decimal
power saving, and little-o bound. The `_order` variants also specify the root order.

The implementation uses a smaller concrete tensor network (32 binary coordinates
per factor, 4060 triples, and a `2^50` role envelope) with a stronger saving that
implies the stated paper constants. The general rational-algebra extraction,
symbolic certificate search, circuit printer, and bounded-printer uniformization
from the synthesis appendix are outside this formalization.
-/
namespace PowerSaving
open RAM Bench Selection Filter Asymptotics Real
noncomputable section
namespace Skies

lemma multiplier_range : 1 < paperMultiplier ∧ paperMultiplier < paperM := by
  norm_num [paperMultiplier,paperM,paperDelta,paperW]

lemma theta_lt : theta < 1 := by
  have h := multiplier_range
  have hg : 0<log paperM := Real.log_pos (lt_trans h.1 h.2)
  rw [theta,div_lt_iff₀ hg,one_mul]
  exact Real.log_lt_log (by linarith) h.2

lemma alpha_theta : alpha < theta := by
  let d : ℝ := 2/(10:ℝ)^11
  have hp : 0<d := by dsimp [d]; norm_num
  have hm : 2 ≤ paperM := by norm_num [paperM]
  have hx : 0<paperMultiplier := lt_trans zero_lt_one multiplier_range.1
  have hu : 0<paperM := by linarith
  have h2 := (Real.log_le_log (by norm_num : 0 < (2:ℝ)) hm)
  have he := log2_min
  have hh : 0<log paperM := by linarith
  have hk := Real.log_le_sub_one_of_pos (show 0<paperM/paperMultiplier by positivity)
  rw [log_div hu.ne' hx.ne'] at hk
  have H : paperM/paperMultiplier-1 < d*(2/3) := by
    norm_num [d,paperM,paperMultiplier,paperW,paperDelta]
  rw [theta,lt_div_iff₀ hh]
  change (1-d)*log paperM < log paperMultiplier
  have H' := mul_le_mul_of_nonneg_left (he.trans h2) hp.le
  have hy := hk.trans_lt (lt_of_lt_of_le H H')
  rw [sub_mul,one_mul]
  linarith only [hy]

lemma decimal_range : alpha < decimalExponent ∧ decimalExponent < 1 := by
  norm_num [decimalExponent,alpha]

def speed (v : ℝ) (n : ℕ) := (n:ℝ)*(Tm n)^v

lemma flight_little {v : ℝ} (h : alpha < v) :
    flight =o[atTop] speed v := by
  rw [isLittleO_iff]
  intro c hc
  filter_upwards [Ttop.eventually_ge_atTop 1,dwarf Ttop 2
    (p:=v-alpha) (sub_pos.mpr h) hc] with n hn hh
  have he : 0<Tm n := by linarith
  change ‖(n:ℝ)*Tm n^alpha*Qm n^2‖ ≤ c*‖(n:ℝ)*Tm n^v‖
  rw [Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ ((n:ℝ)*Tm n^alpha)*(c*Tm n^(v-alpha)) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = c*((n:ℝ)*(Tm n^alpha*Tm n^(v-alpha))) := by ring
    _ = _ := by rw [← rpow_add he, show alpha + (v-alpha)=v by ring] -- a+(v-a)

lemma speed_little {u v : ℝ} (h : u < v) :
    speed u =o[atTop] speed v := by
  rw [isLittleO_iff]
  intro c hc
  filter_upwards [Ttop.eventually_ge_atTop 1,dwarf Ttop 0
    (p:=v-u) (sub_pos.mpr h) hc] with n hn hh
  have he : 0<Tm n := by linarith
  change ‖(n:ℝ)*Tm n^u‖ ≤ c*‖(n:ℝ)*Tm n^v‖
  rw [Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg (by positivity)]
  have hh' : 1 ≤ c * Tm n^(v-u) := by simpa only [pow_zero] using hh
  calc
    _ = ((n:ℝ)*Tm n^u)*1 := by ring
    _ ≤ ((n:ℝ)*Tm n^u)*(c*Tm n^(v-u)) := mul_le_mul_of_nonneg_left hh' (by positivity)
    _ = c*((n:ℝ)*(Tm n^u*Tm n^(v-u))) := by ring
    _ = _ := by rw [← rpow_add he, show u+(v-u)=v by ring]

theorem decimal_little : decimalTime =o[atTop] nlogn := by
  have H := speed_little decimal_range.2
  have h : speed 1 = nlogn := funext fun n => by rw [speed,Real.rpow_one]; rfl
  rw [h] at H; exact H

lemma speed_paper : speed theta =O[atTop] paperTime := by
  rw [isBigO_iff]
  refine ⟨1,?_⟩
  filter_upwards [Ttop.eventually_ge_atTop 1,Qtop.eventually_ge_atTop 1] with n hn hh
  have he : 0<Tm n := by linarith
  have he' : 0<Qm n := by linarith
  change ‖(n:ℝ)*Tm n^theta‖ ≤ 1*‖(n:ℝ)*Tm n^theta*Qm n^(4-theta)‖
  rw [Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg (by positivity),one_mul]
  have hb := Real.one_le_rpow hh (show 0 ≤ 4-theta by linarith [theta_lt])
  exact le_mul_of_one_le_right (by positivity) hb

lemma time_bound {N} (h : ∀ n:ℕ,n ≤ N n ∧ N n ≤ 2*n) (a b : Ration) :
    TimeBounds (lunch a b N) := by
  have H := lunch_big a b h
  have hp := H.trans_isLittleO (flight_little alpha_theta)
  have hd := H.trans_isLittleO (flight_little decimal_range.1)
  have ht : (fun n => (lunch a b N n:ℝ)) =O[atTop] decimalTime := hd.isBigO
  exact ⟨hp.isBigO.trans speed_paper,ht,ht.trans_isLittleO decimal_little⟩

end Skies

/-! Main results. Provide formula for the order besides the existential specification. -/
theorem transform_main_order : ∃ order solve W,
    DFTProgram order solve W ∧ TimeBounds W ∧
    ∀ n, 0<n → (run order n).val = receipt n ∧ (run order n).val < 8*n^3 := by
  obtain ⟨o,s,a,b,hp,ho⟩ := flagshipOne
  exact ⟨o,s,lunch a b id,hp,Skies.time_bound (N:=id) (fun n => ⟨le_rfl,by dsimp; omega⟩)
    a b,fun n hn => ⟨ho n hn,(ho n hn).symm ▸ (receipt_bound n hn).2⟩⟩

theorem convolution_main_order : ∃ order solve W,
    ConvProgram order solve W ∧ TimeBounds W ∧
    ∀ n, 0<n → (run order n).val = receipt (2*n-1) ∧ (run order n).val < 8*(2*n-1)^3 := by
  obtain ⟨o,s,a,b,hp,ho⟩ := flagshipBoth
  have h (n : ℕ) : n ≤ stretch n ∧ stretch n ≤ 2*n := by unfold stretch; omega
  exact ⟨o,s,lunch a b stretch,hp,Skies.time_bound h a b,fun n hn =>
    ⟨ho n hn,(ho n hn).symm ▸ (receipt_bound _ (stretch_pos hn)).2⟩⟩

theorem transform_main : DFTGoal :=
  let ⟨o,s,W,h,g,_⟩ := transform_main_order
  ⟨o,s,W,h,g⟩

theorem convolution_main : ConvGoal :=
  let ⟨o,s,W,h,g,_⟩ := convolution_main_order
  ⟨o,s,W,h,g⟩

lemma matrix_definition (n : ℕ) (x : Vec n) : dft n x = Matrix.mulVec (dftMatrix n) x :=
  rfl

end
end PowerSaving

end OAI
