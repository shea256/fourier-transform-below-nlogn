import Work.BlockAccounting.Moment

/-!
# Lower bounds for the moment (sharpness of the rate lemmas) (agent key: block-accounting)

Importable module `Work.BlockAccounting.Sharp`.  Imports only Mathlib (through `Moment`).  No `sorry`.

`term_ge` is the lower-bound companion of `term_le`: with a rational LOWER bound `L` of
`log (m/r)` it gives `n (r/m) (1 + x + x²/2 + x³/6) ≤ n (r/m)^(1-ε)`, `x = ε L`.
`le_log_of_expbound` proves `L ≤ log x` by rational arithmetic: `exp L = exp (L/2^s)^(2^s)`
and `exp (L/2^s)` is bounded above by a partial sum of the series plus Mathlib's remainder
(`Real.exp_bound'`).
-/

namespace OAI.PowerSaving.BlockAccounting
open Finset

/-- `L ≤ log x` from an upper bound of `exp (L / 2^s)`, raised to the power `2^s`. -/
lemma le_log_of_expbound (x L : ℝ) (s n : ℕ) (hn : 0 < n) (hL : 0 ≤ L) (hy : L / 2^s ≤ 1)
    (h : ((∑ i ∈ range n, (L/2^s)^i / (i.factorial:ℝ))
        + (L/2^s)^n * ((n:ℝ)+1) / ((n.factorial:ℝ) * (n:ℝ)))^(2^s) ≤ x) :
    L ≤ Real.log x := by
  have hy0 : 0 ≤ L / 2^s := div_nonneg hL (by positivity)
  have hb := Real.exp_bound' hy0 hy hn
  have h2 : ((2^s : ℕ) : ℝ) * (L / 2^s) = L := by
    push_cast
    field_simp
  have he : Real.exp L = (Real.exp (L / 2^s))^(2^s) := by
    rw [← Real.exp_nat_mul, h2]
  have h1 : Real.exp L ≤ x := by
    rw [he]
    exact (pow_le_pow_left₀ (Real.exp_pos _).le hb _).trans h
  calc L = Real.log (Real.exp L) := (Real.log_exp L).symm
    _ ≤ Real.log x := Real.log_le_log (Real.exp_pos L) h1

/-- Third-order lower bound of `exp` on `[0, ∞)`. -/
lemma cubic_le_exp (x : ℝ) (h0 : 0 ≤ x) : 1 + x + x^2/2 + x^3/6 ≤ Real.exp x := by
  have h := Real.sum_le_exp_of_nonneg h0 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

/-- `(r/m) (1 + x + x²/2 + x³/6) ≤ (r/m)^(1-ε)` with `x = ε L`, when `L ≤ log (m/r)`. -/
lemma rpow_ratio_ge3 (r m L ε : ℝ) (hr : 0 < r) (hm : 0 < m) (hε : 0 ≤ ε) (hL0 : 0 ≤ L)
    (hL : L ≤ Real.log (m/r)) :
    r/m * (1 + ε*L + (ε*L)^2/2 + (ε*L)^3/6) ≤ (r/m)^(1-ε) := by
  have hx0 : (0:ℝ) < r/m := div_pos hr hm
  have hlog : Real.log (r/m) = - Real.log (m/r) := by
    rw [← Real.log_inv, inv_div]
  have h1 : (r/m)^(1-ε) = r/m * Real.exp (ε * Real.log (m/r)) := by
    rw [Real.rpow_def_of_pos hx0, hlog,
      show -Real.log (m/r) * (1-ε) = -Real.log (m/r) + ε * Real.log (m/r) by ring,
      Real.exp_add, ← hlog, Real.exp_log hx0]
  rw [h1]
  apply mul_le_mul_of_nonneg_left _ hx0.le
  have h2 : Real.exp (ε * L) ≤ Real.exp (ε * Real.log (m/r)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hL hε)
  exact (cubic_le_exp (ε*L) (mul_nonneg hε hL0)).trans h2

/-- Lower bound for one term of the moment at `z = 1 - ε`. -/
lemma term_ge (m r n : ℕ) (ε L q : ℝ) (hr : 0 < r) (hm : 0 < m) (hε : 0 ≤ ε) (hL0 : 0 ≤ L)
    (hL : L ≤ Real.log ((m:ℝ)/(r:ℝ)))
    (hq : q ≤ (n:ℝ) * ((r:ℝ)/(m:ℝ) * (1 + ε*L + (ε*L)^2/2 + (ε*L)^3/6))) :
    q ≤ T m (1-ε) r n := by
  have hr' : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr
  have hm' : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have h := rpow_ratio_ge3 (r:ℝ) (m:ℝ) L ε hr' hm' hε hL0 hL
  have h' : (n:ℝ) * ((r:ℝ)/(m:ℝ) * (1 + ε*L + (ε*L)^2/2 + (ε*L)^3/6))
      ≤ T m (1-ε) r n :=
    mul_le_mul_of_nonneg_left h (by positivity)
  exact hq.trans h'

end OAI.PowerSaving.BlockAccounting

#print axioms OAI.PowerSaving.BlockAccounting.term_ge
#print axioms OAI.PowerSaving.BlockAccounting.le_log_of_expbound
