import Work.SharedSumChecker.Impl
import Work.GCert.Labels.Bits
import Work.GCert.Labels.Canon

/-!
# (key: gx-labels) Soundness of the packed elimination and of the frame-table check

* `elimT_sound`   if `elimT` succeeds, every digit of `A` lies in every additively closed set
                  that contains the digits of `Pb` (so: in the subspace coded by `Pb`);
* `goodK_sound`   `goodK h c = true → Good h c`;
* `tabK_good`     a checked table has only good leaves; `tabK_node` (composition of parts).

No `sorry`.
-/

set_option linter.unusedVariables false
set_option linter.deprecated false

namespace GLab
open SSC OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.GF Finset

theorem bF_xor (a b : Bool) : bF (a ^^ b) = bF a + bF b := by cases a <;> cases b <;> decide

theorem bF_eq_zero (b : Bool) : bF b = 0 ↔ b = false := by cases b <;> decide

theorem dv_xor (h A B j : Nat) : dv h (A ^^^ B) j = dv h A j + dv h B j := by
  funext q
  simp only [dv, Pi.add_apply, Nat.testBit_xor, bF_xor]

theorem dv_zero (h j : Nat) : dv h 0 j = 0 := by
  funext q
  simp [dv, bF]

theorem dv_dig (h P p : Nat) (q : Fin h) : dv h P p q = bF ((dig h P p).testBit q.val) := by
  rw [dig_bit]; simp [dv, q.isLt]

theorem dv_eq_zero_iff (h P p : Nat) : dv h P p = 0 ↔ dig h P p = 0 := by
  constructor
  · intro e
    apply Nat.eq_of_testBit_eq
    intro i
    rw [dig_bit, Nat.zero_testBit]
    by_cases hi : i < h
    · have := congrFun e ⟨i, hi⟩
      have h2 : P.testBit (h * p + i) = false := (bF_eq_zero _).mp this
      rw [h2, Bool.and_false]
    · simp [hi]
  · intro e
    funext q
    rw [dv_dig, e, Nat.zero_testBit]; rfl

/-- digit `j` of `(X &&& rep h K) * w` is `w` or `0` -/
theorem dv_sel (h : Nat) (hh : 0 < h) (K X w j : Nat) (hw : w < 2 ^ h) (v : Space (Fin h))
    (hv : ∀ q : Fin h, v q = bF (w.testBit q.val)) :
    dv h ((X &&& rep h K) * w) j = v ∨ dv h ((X &&& rep h K) * w) j = 0 := by
  cases hc : (decide (j < K) && X.testBit (h * j))
  · right
    funext q
    simp only [dv]
    rw [sel_mul_bit h hh w hw K X j q.val q.isLt, hc, Bool.false_and]; rfl
  · left
    funext q
    simp only [dv]
    rw [sel_mul_bit h hh w hw K X j q.val q.isLt, hc, Bool.true_and, hv]

theorem elimK_succ (h hm O Pb p A : Nat) : elimK h hm O Pb (p + 1) A =
    Nat.rec (motive := fun _ => Bool) (elimK h hm O Pb p A)
      (fun m _ => forceN (Nat.xor A (Nat.mul (Nat.land (Nat.shiftRight A p) O) (Nat.succ m)))
        (elimK h hm O Pb p)) (digK h hm Pb p) := rfl

theorem elimK_sound (h : Nat) (hh : 0 < h) (K Pb : Nat) (Sp : Space (Fin h) → Prop)
    (h0 : Sp 0) (hadd : ∀ x y, Sp x → Sp y → Sp (x + y)) (hb : ∀ p, p < h → Sp (dv h Pb p)) :
    ∀ n, n ≤ h → ∀ A, elimK h (2 ^ h - 1) (rep h K) Pb n A = true → ∀ j, Sp (dv h A j) := by
  intro n
  induction n with
  | zero =>
    intro _ A H j
    have e : A = 0 := beq_true H
    rw [e, dv_zero]; exact h0
  | succ p ih =>
    intro hp A H j
    rw [elimK_succ, digK_eq] at H
    rcases hw : dig h Pb p with _ | m
    · rw [hw] at H; exact ih (by omega) A H j
    · rw [hw] at H
      have H2 : forceN (Nat.xor A (Nat.mul (Nat.land (Nat.shiftRight A p) (rep h K)) (Nat.succ m)))
          (elimK h (2 ^ h - 1) (rep h K) Pb p) = true := H
      rw [forceN_eq] at H2
      have H3 : elimK h (2 ^ h - 1) (rep h K) Pb p (A ^^^ ((A >>> p) &&& rep h K) * (m + 1))
          = true := H2
      have h1 := ih (by omega) _ H3 j
      have hw' : m + 1 < 2 ^ h := hw ▸ dig_lt h Pb p
      have e : dv h A j = dv h (A ^^^ ((A >>> p) &&& rep h K) * (m + 1)) j
          + dv h (((A >>> p) &&& rep h K) * (m + 1)) j := by
        rw [← dv_xor, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      rw [e]
      refine hadd _ _ h1 ?_
      rcases dv_sel h hh K (A >>> p) (m + 1) j hw' (dv h Pb p)
        (fun q => by rw [dv_dig, hw]) with e2 | e2
      · rw [e2]; exact hb p (by omega)
      · rw [e2]; exact h0

/-- **the elimination is sound** -/
theorem elimT_sound (h : Nat) (hh : 0 < h) (K Pb A : Nat) (Sp : Space (Fin h) → Prop)
    (h0 : Sp 0) (hadd : ∀ x y, Sp x → Sp y → Sp (x + y)) (hb : ∀ p, p < h → Sp (dv h Pb p))
    (H : elimT h (2 ^ h - 1) (rep h K) Pb A = true) : ∀ j, Sp (dv h A j) := by
  cases A with
  | zero => intro j; rw [dv_zero]; exact h0
  | succ a => exact elimK_sound h hh K Pb Sp h0 hadd hb h (le_refl _) _ H

/-! ## the frame table -/

theorem goodLoop_succ (h hm P M dm p cnt : Nat) : goodLoop h hm P M dm (p + 1) cnt =
    Nat.rec (motive := fun _ => Bool) (goodLoop h hm P M dm p cnt)
      (fun m _ => guard (Nat.beq (Nat.land (Nat.succ m) M) (Nat.pow 2 p))
        (goodLoop h hm P M dm p (Nat.succ cnt))) (digK h hm P p) := rfl

theorem goodLoop_sound (h P M dm : Nat) : ∀ n cnt, goodLoop h (2 ^ h - 1) P M dm n cnt = true →
    (∀ p, p < n → dig h P p ≠ 0 → dig h P p &&& M = 2 ^ p) ∧
    cnt + ∑ p ∈ range n, (if dig h P p ≠ 0 then 1 else 0) = dm := by
  intro n
  induction n with
  | zero =>
    intro cnt H
    exact ⟨fun p hp => absurd hp (Nat.not_lt_zero p), by simpa using beq_true H⟩
  | succ p ih =>
    intro cnt H
    rw [goodLoop_succ, digK_eq] at H
    rcases hw : dig h P p with _ | m
    · rw [hw] at H
      obtain ⟨a, b⟩ := ih cnt H
      refine ⟨fun p' hp' hne => ?_, ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hp' with h1 | h1
        · exact a p' h1 hne
        · rw [h1] at hne; exact absurd hw hne
      · rw [Finset.sum_range_succ, hw]; simpa using b
    · rw [hw] at H
      obtain ⟨g1, g2⟩ := guard_true H
      obtain ⟨a, b⟩ := ih _ g2
      refine ⟨fun p' hp' hne => ?_, ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hp' with h1 | h1
        · exact a p' h1 hne
        · rw [h1, hw]; exact beq_true g1
      · rw [Finset.sum_range_succ, hw, if_pos (Nat.succ_ne_zero m)]
        have b' : cnt + 1 + ∑ p ∈ range p, (if dig h P p ≠ 0 then 1 else 0) = dm := b
        omega

/-- **a checked code is good** -/
theorem goodK_sound (h c : Nat) (H : goodK h c = true) : Good h c := by
  unfold goodK at H
  rw [forceN_eq, forceN_eq] at H
  obtain ⟨g1, g2⟩ := guard_true H
  obtain ⟨a, b⟩ := goodLoop_sound h (cP h c) _ _ h 0 g2
  generalize Nat.land (Nat.shiftRight c 8) (Nat.sub (Nat.pow 2 h) 1) = M at a
  have piv : ∀ p : Fin h, p ∈ pivs h (cP h c) → dig h (cP h c) p.val ≠ 0 := by
    intro p hp hz
    exact (mem_filter.mp hp).2 ((dv_eq_zero_iff h _ _).mpr hz)
  refine ⟨?_, ?_, ble_true g1⟩
  · intro p hp q hq
    have ep := a p.val p.isLt (piv p hp)
    have eq := a q.val q.isLt (piv q hq)
    have mq : M.testBit q.val = true := by
      have := congrArg (fun x => x.testBit q.val) eq
      simp only [Nat.testBit_and, Nat.testBit_two_pow_self] at this
      exact (Bool.and_eq_true_iff.mp this).2
    have bp : (dig h (cP h c) p.val).testBit q.val = decide (p.val = q.val) := by
      have := congrArg (fun x => x.testBit q.val) ep
      simp only [Nat.testBit_and, Nat.testBit_two_pow] at this
      rw [mq, Bool.and_true] at this
      exact this
    show dv h (cP h c) p.val q = _
    rw [dv_dig, bp]
    by_cases e : p = q
    · rw [if_pos e]; simp [e, bF]
    · rw [if_neg e]
      have : ¬ p.val = q.val := fun e' => e (Fin.ext e')
      simp [this, bF]
  · have e1 : (pivs h (cP h c)).card
        = ∑ p : Fin h, (fun i => if dig h (cP h c) i ≠ 0 then 1 else 0) p.val := by
      unfold pivs
      rw [Finset.card_filter]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      have : (bas h (cP h c) p ≠ 0) ↔ (dig h (cP h c) p.val ≠ 0) :=
        not_congr (dv_eq_zero_iff h _ _)
      simp only [this]
    rw [e1, Fin.sum_univ_eq_sum_range (fun i => if dig h (cP h c) i ≠ 0 then 1 else 0) h]
    have b' : 0 + ∑ p ∈ range h, (if dig h (cP h c) p ≠ 0 then 1 else 0) = cdim c := b
    omega

theorem tabK_node (h : Nat) (l r : Trie) (hl : tabK h l = true) (hr : tabK h r = true) :
    tabK h (.node l r) = true := by
  show guard (tabK h l) (tabK h r) = true
  rw [hl, hr]; rfl

/-- **every leaf of a checked table is good** (for every key) -/
theorem tabK_good (h : Nat) : ∀ (t : Trie), tabK h t = true → ∀ key, Good h (t.get key) := by
  intro t
  induction t with
  | leaf v => intro H key; exact goodK_sound h v H
  | node l r il ir =>
    intro H key
    obtain ⟨g1, g2⟩ := guard_true (show guard (tabK h l) (tabK h r) = true from H)
    show Good h (if key % 2 = 0 then l.get (key / 2) else r.get (key / 2))
    split
    · exact il g1 _
    · exact ir g2 _

end GLab

#print axioms GLab.elimT_sound
#print axioms GLab.goodK_sound
#print axioms GLab.tabK_good
