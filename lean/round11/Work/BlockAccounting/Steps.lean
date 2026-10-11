import Work.BlockAccounting.Moment

/-!
# Block lists given step by step (agent key: block-accounting)

Importable module `Work.BlockAccounting.Steps`.  Imports only Mathlib (through `Moment`).  No `sorry`.

A block word built with a path calculus has a cost that is a SUM OVER THE LABEL STEPS of the word
(one summand `count * (rank/m)^z` per step and role class).  The rate lemmas
(`Work.BlockAccounting.Rate*`) are stated for the merged histogram.  This file connects the two:

* `moment_congr`       : two block lists with the same histogram function have the same moment;
* `histFn_eq_of_list`  : equality of two histogram functions, reduced to the finitely many
                         ranks of an explicit list (then `decide`).
-/

namespace OAI.PowerSaving.BlockAccounting
open Finset

lemma histFn_eq_zero (l : List (ℕ × ℕ)) (r : ℕ) (h : ∀ b ∈ l, b.1 ≠ r) : histFn l r = 0 := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [histFn_cons, ite_eq_right (h b (by simp)), zero_add]
    exact ih (fun c hc => h c (by simp [hc]))

lemma histFn_append (l l' : List (ℕ × ℕ)) (r : ℕ) :
    histFn (l ++ l') r = histFn l r + histFn l' r := by
  induction l with
  | nil => simp [histFn_nil]
  | cons b l ih => rw [List.cons_append, histFn_cons, histFn_cons, ih, add_assoc]

/-- Two histogram functions agree everywhere as soon as they agree on a list `ks` of ranks that
contains every rank occurring in either list. -/
theorem histFn_eq_of_list (l l' : List (ℕ × ℕ)) (ks : List ℕ)
    (hk : ∀ b ∈ l, b.1 ∈ ks) (hk' : ∀ b ∈ l', b.1 ∈ ks)
    (h : ∀ r ∈ ks, histFn l r = histFn l' r) : ∀ r, histFn l r = histFn l' r := by
  intro r
  by_cases hr : r ∈ ks
  · exact h r hr
  · have h1 : histFn l r = 0 :=
      histFn_eq_zero l r (fun b hb e => hr (e ▸ hk b hb))
    have h2 : histFn l' r = 0 :=
      histFn_eq_zero l' r (fun b hb e => hr (e ▸ hk' b hb))
    rw [h1, h2]

/-- The moment depends only on the histogram function. -/
theorem moment_congr (m : ℕ) (z : ℝ) (l l' : List (ℕ × ℕ))
    (h : ∀ r, histFn l r = histFn l' r) : moment m z l = moment m z l' := by
  have h1 := sum_histFn l (fun r => ((r:ℝ)/(m:ℝ))^z) (keys l ∪ keys l')
    (fun b hb => Finset.mem_union_left _
      (List.mem_toFinset.mpr (List.mem_map.mpr ⟨b, hb, rfl⟩)))
  have h2 := sum_histFn l' (fun r => ((r:ℝ)/(m:ℝ))^z) (keys l ∪ keys l')
    (fun b hb => Finset.mem_union_right _
      (List.mem_toFinset.mpr (List.mem_map.mpr ⟨b, hb, rfl⟩)))
  unfold moment
  rw [← h1, ← h2]
  exact Finset.sum_congr rfl (fun r _ => by rw [h r])

end OAI.PowerSaving.BlockAccounting

#print axioms OAI.PowerSaving.BlockAccounting.moment_congr
#print axioms OAI.PowerSaving.BlockAccounting.histFn_eq_of_list
