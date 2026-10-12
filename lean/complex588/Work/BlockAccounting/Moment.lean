import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Moment inequalities for the whole-block recurrence: generic tools (agent key: block-accounting)

Importable module `Work.BlockAccounting.Moment`.  Imports only Mathlib.  No `sorry`.

The whole-block recurrence `t k ≤ A + (∑ over blocks n * t (r * (k / m))) / 2^a` gives
`t k = O(k^z)` as soon as the *moment* `∑ n * (r/m)^z` is below `2^a`
(`OAI.PowerSaving.BlockRecursion.block_bound`, checks/wht3/saving/BlockRecurrence.lean).

This file provides

* `moment m z blocks` for a list of `(rank, count)` pairs, and the same sum over a `Finset`
  of ranks with a histogram function (`histFn`, `keys`, `moment_finset`,
  `mem_keys_of_histFn_ne_zero`): the form used by `engine_program_block`
  (checks/wht5/shared/block-engine-interface.md);
* `term_le`: a third-order upper bound for one term `n * (r/m)^(1-ε)`,
  from a rational upper bound `L` of `log (m/r)`;
* `log_le_of_le_expsum`: `log x ≤ L` from a partial sum of the exponential series
  (pure rational arithmetic, no table of logarithms).
-/

namespace OAI.PowerSaving.BlockAccounting
open Finset

/-- One term of the moment: `n` blocks of rank `r`, label space of dimension `m`. -/
noncomputable def T (m : ℕ) (z : ℝ) (r n : ℕ) : ℝ := (n:ℝ) * ((r:ℝ)/(m:ℝ))^z

/-- Moment of a block list `(rank, count)`. -/
noncomputable def moment (m : ℕ) (z : ℝ) (blocks : List (ℕ × ℕ)) : ℝ :=
  (blocks.map fun b => (b.2:ℝ) * ((b.1:ℝ)/(m:ℝ))^z).sum

lemma moment_nil (m : ℕ) (z : ℝ) : moment m z [] = 0 := rfl
lemma moment_cons (m : ℕ) (z : ℝ) (r n : ℕ) (l : List (ℕ × ℕ)) :
    moment m z ((r,n)::l) = T m z r n + moment m z l := rfl

/-- `log x ≤ L` from a partial sum of the exponential series. -/
lemma log_le_of_le_expsum (x L : ℝ) (N : ℕ) (hx : 0 < x) (hL : 0 ≤ L)
    (h : x ≤ ∑ i ∈ range N, L^i / (i.factorial:ℝ)) : Real.log x ≤ L := by
  have h2 : x ≤ Real.exp L := h.trans (Real.sum_le_exp_of_nonneg hL N)
  calc Real.log x ≤ Real.log (Real.exp L) := Real.log_le_log hx h2
    _ = L := Real.log_exp L

/-- Third-order upper bound of `exp` on `[0,1]`. -/
lemma exp_le_cubic (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Real.exp x ≤ 1 + x + x^2/2 + x^3*(2/9) := by
  have h := Real.exp_bound' h0 h1 (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

/-- `(r/m)^(1-ε) ≤ (r/m) (1 + x + x²/2 + (2/9) x³)` with `x = ε L`, when `log (m/r) ≤ L`. -/
lemma rpow_ratio_le3 (r m L ε : ℝ) (hr : 0 < r) (hm : 0 < m) (hε : 0 ≤ ε) (hL0 : 0 ≤ L)
    (hL : Real.log (m/r) ≤ L) (hx : ε * L ≤ 1) :
    (r/m)^(1-ε) ≤ r/m * (1 + ε*L + (ε*L)^2/2 + (ε*L)^3*(2/9)) := by
  have hx0 : (0:ℝ) < r/m := div_pos hr hm
  have hlog : Real.log (r/m) = - Real.log (m/r) := by
    rw [← Real.log_inv, inv_div]
  have h1 : (r/m)^(1-ε) = r/m * Real.exp (ε * Real.log (m/r)) := by
    rw [Real.rpow_def_of_pos hx0, hlog,
      show -Real.log (m/r) * (1-ε) = -Real.log (m/r) + ε * Real.log (m/r) by ring,
      Real.exp_add, ← hlog, Real.exp_log hx0]
  rw [h1]
  apply mul_le_mul_of_nonneg_left _ hx0.le
  have h2 : Real.exp (ε * Real.log (m/r)) ≤ Real.exp (ε * L) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hL hε)
  exact h2.trans (exp_le_cubic (ε*L) (mul_nonneg hε hL0) hx)

/-- Upper bound for one term of the moment at `z = 1 - ε`. -/
lemma term_le (m r n : ℕ) (ε L q : ℝ) (hr : 0 < r) (hm : 0 < m) (hε : 0 ≤ ε) (hL0 : 0 ≤ L)
    (hL : Real.log ((m:ℝ)/(r:ℝ)) ≤ L) (hx : ε * L ≤ 1)
    (hq : (n:ℝ) * ((r:ℝ)/(m:ℝ) * (1 + ε*L + (ε*L)^2/2 + (ε*L)^3*(2/9))) ≤ q) :
    T m (1-ε) r n ≤ q := by
  have hr' : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr
  have hm' : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have h := rpow_ratio_le3 (r:ℝ) (m:ℝ) L ε hr' hm' hε hL0 hL hx
  have h' : T m (1-ε) r n
      ≤ (n:ℝ) * ((r:ℝ)/(m:ℝ) * (1 + ε*L + (ε*L)^2/2 + (ε*L)^3*(2/9))) :=
    mul_le_mul_of_nonneg_left h (by positivity)
  exact h'.trans hq

/-! ### the same sum over a finite set of ranks -/

/-- Number of blocks of rank `r` in a list of `(rank, count)` pairs. -/
def histFn (l : List (ℕ × ℕ)) (r : ℕ) : ℕ := ((l.filter fun b => b.1 = r).map Prod.snd).sum

/-- The ranks that occur. -/
def keys (l : List (ℕ × ℕ)) : Finset ℕ := (l.map Prod.fst).toFinset

lemma histFn_nil (r : ℕ) : histFn [] r = 0 := rfl

lemma histFn_cons (b : ℕ × ℕ) (l : List (ℕ × ℕ)) (r : ℕ) :
    histFn (b::l) r = (if b.1 = r then b.2 else 0) + histFn l r := by
  unfold histFn
  by_cases h : b.1 = r
  · simp [h]
  · simp [h]

lemma mem_keys_of_histFn_ne_zero (l : List (ℕ × ℕ)) (r : ℕ) (h : histFn l r ≠ 0) :
    r ∈ keys l := by
  induction l with
  | nil => exact absurd (histFn_nil r) h
  | cons b l ih =>
    rw [histFn_cons] at h
    unfold keys
    simp only [List.map_cons, List.toFinset_cons, Finset.mem_insert]
    by_cases hb : b.1 = r
    · exact Or.inl hb.symm
    · right
      rw [ite_eq_right hb, zero_add] at h
      exact ih h

lemma sum_histFn (l : List (ℕ × ℕ)) (g : ℕ → ℝ) (s : Finset ℕ) (hs : ∀ b ∈ l, b.1 ∈ s) :
    ∑ r ∈ s, (histFn l r : ℝ) * g r = (l.map fun b => (b.2:ℝ) * g b.1).sum := by
  induction l with
  | nil => simp [histFn_nil]
  | cons b l ih =>
    have hb : b.1 ∈ s := hs b (by simp)
    have hl : ∀ c ∈ l, c.1 ∈ s := fun c hc => hs c (by simp [hc])
    simp only [histFn_cons, Nat.cast_add, add_mul, Finset.sum_add_distrib, List.map_cons,
      List.sum_cons, ih hl]
    congr 1
    rw [Finset.sum_eq_single b.1]
    · simp
    · intro r _ hr
      simp [Ne.symm hr]
    · intro h
      exact absurd hb h

/-- The list moment equals the sum over the ranks that occur, with the histogram function. -/
theorem moment_finset (m : ℕ) (z : ℝ) (l : List (ℕ × ℕ)) :
    ∑ r ∈ keys l, (histFn l r : ℝ) * ((r:ℝ)/(m:ℝ))^z = moment m z l :=
  sum_histFn l (fun r => ((r:ℝ)/(m:ℝ))^z) (keys l)
    (fun b hb => List.mem_toFinset.mpr (List.mem_map.mpr ⟨b, hb, rfl⟩))

end OAI.PowerSaving.BlockAccounting

#print axioms OAI.PowerSaving.BlockAccounting.term_le
#print axioms OAI.PowerSaving.BlockAccounting.log_le_of_le_expsum
#print axioms OAI.PowerSaving.BlockAccounting.moment_finset
#print axioms OAI.PowerSaving.BlockAccounting.mem_keys_of_histFn_ne_zero
