import OAI.Computability.FourierTransform.RecursionBounds
import OAI.Computability.FourierTransform.TensorCertificate

namespace OAI
namespace PowerSaving
open Real Filter Asymptotics
noncomputable section
namespace RAM

/-- Work bound for the flat recursion. k=0 treated with k+1 in the conclusion. -/
theorem allot_bound (u a D : ℕ) (hu : 3≤u) (z : ℝ) (hz : 0≤z)
    (hD : (D:ℝ)/(2:ℝ)^a < (u:ℝ)^z) :
    ∃ C : ℝ, 1≤C ∧ ∀ k : ℕ,
      (allot u a D k : ℝ) ≤ C*(2:ℝ)^k*((k:ℝ)+1)^z := by
  let Q := (2:ℝ)^a
  let s := (D:ℝ)/Q
  let t := (u:ℝ)^z
  have ht : 0<t-s := sub_pos.mpr hD
  let C := 1+(t-s)⁻¹
  have hc : 1≤C := by unfold C; simp [ht.le]
  have hg : 1 ≤ C*(t-s) := by unfold C; rw [add_mul, inv_mul_cancel₀ ht.ne']; linarith
  have hQ : 0<Q := by positivity
  have H (k : ℕ) (hk : 0<k) :
      (allot u a D k : ℝ) ≤ C*(2:ℝ)^k*(k:ℝ)^z := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      have hk' : 1 ≤ (k:ℝ) := Nat.one_le_cast.mpr hk
      have hgk : 1≤(k:ℝ)^z := Real.one_le_rpow hk' hz
      rw [allot]
      split
      next h =>
        let f : ℕ := k/u
        have hf : 1 ≤ f := by
          have h := h.2
          unfold threshold at h
          apply (Nat.le_div_iff_mul_le (by omega)).2
          calc
            _ ≤ u*(a+1) := by simp [mul_add]
            _ ≤ _ := h
        let b := (batches u a k:ℝ)
        let x := (2:ℝ)^k
        let y := (2:ℝ)^f
        have he : x=b*(Q*y) := by
          dsimp only [x,b,y,Q,f]
          exact_mod_cast (rounds_eq u a k hu h.2).symm
        have hf' : 1 ≤ (f:ℝ) := Nat.one_le_cast.mpr hf
        have hy : 1 ≤ (f:ℝ)^z := Real.one_le_rpow hf' hz
        have hw : t*(f:ℝ)^z ≤ (k:ℝ)^z := by
          unfold t
          rw [← Real.mul_rpow (by positivity) (by positivity)]
          apply Real.rpow_le_rpow (by positivity) _ hz
          exact_mod_cast Nat.mul_div_le k u
        have hs : 1+C*s*(f:ℝ)^z ≤ C*(k:ℝ)^z := calc
          _ ≤ C*(t-s)*(f:ℝ)^z + C*s*(f:ℝ)^z := by gcongr; nlinarith [hg,hy]
          _ = C*(t*(f:ℝ)^z) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hw (by positivity)
        push_cast
        change x + D*b* (allot u a D f:ℝ) ≤ C*x*(k:ℝ)^z
        calc
          _ ≤ x + D*b*(C*y*(f:ℝ)^z) := by
            apply add_le_add_right
            apply mul_le_mul_of_nonneg_left (ih f h.1 hf)
            positivity
          _ = x*(1+C*s*(f:ℝ)^z) := by rw [he]; unfold s; field
          _ ≤ x*(C*(k:ℝ)^z) := mul_le_mul_of_nonneg_left hs (by positivity)
          _ = _ := by ring
      next =>
        push_cast
        calc
          _ = 1*(2:ℝ)^k*1 := by simp
          _ ≤ _ := by gcongr
  refine ⟨C,hc,fun k => ?_⟩
  by_cases he : k=0
  · subst k; simpa [allot]
  · apply (H k (Nat.pos_of_ne_zero he)).trans
    gcongr
    first | exact hz | simp

end RAM

def alpha : ℝ := 1-2/(10:ℝ)^11

theorem alpha_pos : 0<alpha := by norm_num [alpha]
theorem alpha_lt : alpha < 1 := by norm_num [alpha]

open Cluster

lemma network_rate : (nMoves:ℝ)/(2:ℝ)^50 < (mcol:ℝ)^alpha := by
  let h : ℝ := 2/(10:ℝ)^11
  let M : ℝ := (mcol:ℝ)
  change _ < M^alpha
  have hm : 0<M := by norm_num [M,mcol]
  have he : Real.log M ≤ 16 := by
    rw [show M = (2:ℝ)^(15:ℕ) from (by norm_num [M,mcol]), Real.log_pow]
    have hh := Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num)
    norm_num at *
    linarith
  have ht : M^alpha = M*Real.exp (-(Real.log M)*h) := by
    rw [Real.rpow_def_of_pos hm]
    unfold alpha
    change Real.exp (Real.log M * (1-h))=_
    rw [show Real.log M*(1-h)=Real.log M + -(Real.log M)*h from by ring, Real.exp_add,Real.exp_log hm]
  rw [ht]
  calc
    _ < M*(1-16*h) := by
      norm_num [nMoves, tower, bankSave, mcol, M, h]
    _ ≤ M*((-(Real.log M)*h)+1) := by
      apply mul_le_mul_of_nonneg_left _ hm.le
      dsimp only [h]
      linarith
    _ ≤ _ := by gcongr; apply Real.add_one_le_exp

/-- Natural envelopes using a ceiling for real powers. -/
def hills (k : ℕ) := Nat.ceil (((k:ℝ)+1)^alpha)

lemma hills_pos (k : ℕ) : 1≤hills k := by
  exact Nat.one_le_ceil_iff.mpr (by positivity)

lemma hills_mono {a b : ℕ} (h : a≤b) : hills a ≤ hills b := by
  unfold hills
  have := alpha_pos
  gcongr

lemma hills_le (k : ℕ) : hills k ≤ k+1 := by
  have hk : 1≤(k:ℝ)+1 := by simp
  apply Nat.ceil_le.mpr
  simpa using Real.rpow_le_rpow_of_exponent_le hk alpha_lt.le

lemma hills_real (k : ℕ) : (hills k:ℝ) ≤ 2*((k:ℝ)+1)^alpha := by
  have h := Real.one_le_rpow (show 1≤(k:ℝ)+1 by simp) alpha_pos.le
  have hh : (hills k:ℝ) < ((k:ℝ)+1)^alpha+1 :=
    Nat.ceil_lt_add_one (by positivity)
  linarith

lemma total_hills : ∃ c : ℕ, ∀ k : ℕ,
    RAM.allot mcol 50 nMoves k + 1 ≤ c*(2^k*hills k + 1) := by
  obtain ⟨C,hC,h⟩ := RAM.allot_bound mcol 50 nMoves (by norm_num [mcol]) alpha alpha_pos.le network_rate
  obtain ⟨c,hc⟩ := exists_nat_ge C
  have ht : 1≤c := Nat.one_le_cast.mp (hC.trans hc)
  refine ⟨c,fun k => ?_⟩
  specialize h k
  have hg : (RAM.allot mcol 50 nMoves k : ℝ) ≤ c*((2:ℝ)^k*(hills k:ℝ)) := by
    rw [← mul_assoc]
    refine h.trans ?_
    have hh : ((k:ℝ)+1)^alpha ≤ (hills k:ℝ) := Nat.le_ceil _
    gcongr
  have he : RAM.allot mcol 50 nMoves k ≤ c*(2^k*hills k) := by exact_mod_cast hg
  rw [mul_add,mul_one]
  omega
end
end PowerSaving

end OAI
