import Work.GCert.Labels.EndDef
import Work.GCert.Labels.Sound

/-!
# (key: gx-labels) Facts behind the end check: parities, ports, shape of a trie

* `tvec h u`        the vector of a mask;
* `pars_bit`        bits of the packed parity fold `parsK`;
* `unit_of_pars`    odd weight: `dot (tvec h u) (tvec h u) = 1`;
* `gap_of_lt`       `u < 2^h - 1`: some coordinate of `tvec h u` is zero;
* `dots_zero`       ONE fold gives `dot (tvec h u) (digit p of P) = 0` for every `p < h`;
* `mem_of_elim`     `u` lies in a coded subspace (the elimination on one digit);
* `perp_of_dots`    hence `u` is orthogonal to the whole coded subspace;
* `wfK_sound`.

No `sorry`.
-/

set_option linter.unusedVariables false
set_option linter.deprecated false

namespace GLab
open SSC GXD OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.GF Finset

/-- the vector of a mask -/
def tvec (h u : Nat) : Space (Fin h) := fun q => bF (u.testBit q.val)

theorem bF_and (a b : Bool) : bF (a && b) = bF a * bF b := by cases a <;> cases b <;> decide

theorem parsK_succ (n O Y : Nat) :
    parsK (n + 1) O Y = Nat.xor (parsK n O Y) (Nat.land (Nat.shiftRight Y n) O) := rfl

theorem pars_bit (O Y i : Nat) : ∀ n, bF ((parsK n O Y).testBit i)
    = ∑ q ∈ range n, bF (Y.testBit (q + i) && O.testBit i) := by
  intro n
  induction n with
  | zero =>
    show bF ((0 : Nat).testBit i) = _
    simp [bF]
  | succ n ih =>
    rw [parsK_succ, Finset.sum_range_succ, ← ih]
    show bF ((parsK n O Y ^^^ ((Y >>> n) &&& O)).testBit i) = _
    rw [Nat.testBit_xor, bF_xor, Nat.testBit_and, Nat.testBit_shiftRight]

theorem unit_of_pars (h u : Nat) (H : parsK h 1 u = 1) : dot (tvec h u) (tvec h u) = 1 := by
  have e := pars_bit 1 u 0 h
  rw [H] at e
  unfold dot
  calc ∑ q : Fin h, tvec h u q * tvec h u q
      = ∑ q : Fin h, (fun q => bF (u.testBit (q + 0) && (1 : Nat).testBit 0)) q.val :=
        Finset.sum_congr rfl (fun q _ => by
          show bF (u.testBit q.val) * bF (u.testBit q.val)
            = bF (u.testBit (q.val + 0) && (1 : Nat).testBit 0)
          rw [Nat.add_zero]
          cases u.testBit q.val <;> decide)
    _ = ∑ q ∈ range h, (fun q => bF (u.testBit (q + 0) && (1 : Nat).testBit 0)) q :=
        Fin.sum_univ_eq_sum_range (fun q => bF (u.testBit (q + 0) && (1 : Nat).testBit 0)) h
    _ = 1 := e.symm.trans (by decide)

theorem gap_of_lt (h u : Nat) (hu : u < 2 ^ h - 1) : ∃ q : Fin h, tvec h u q = 0 := by
  by_contra hne
  have hall : ∀ i, i < h → u.testBit i = true := by
    intro i hi
    cases hb : u.testBit i
    · exact absurd ⟨⟨i, hi⟩, by simp [tvec, bF, hb]⟩ hne
    · rfl
  have e : u = 2 ^ h - 1 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_two_pow_sub_one]
    by_cases hi : i < h
    · simp [hi, hall i hi]
    · have h1 : u < 2 ^ i :=
        lt_of_lt_of_le (by omega) (Nat.pow_le_pow_right (by norm_num) (not_lt.mp hi))
      simp [hi, Nat.testBit_lt_two_pow h1]
  omega

/-- ONE parity fold: every digit of `P` is orthogonal to `u`. -/
theorem dots_zero (h : Nat) (hh : 0 < h) (P u : Nat) (hu : u < 2 ^ h)
    (H : parsK h (rep h h) (Nat.land P (Nat.mul u (rep h h))) = 0) (p : Nat) (hp : p < h) :
    dot (tvec h u) (dv h P p) = 0 := by
  have h1 : (rep h h).testBit (h * p) = true := by
    have := rep_bit h hh h p 0 hh
    simpa [hp] using this
  have e := pars_bit (rep h h) (P &&& (u * rep h h)) (h * p) h
  have H' : parsK h (rep h h) (P &&& (u * rep h h)) = 0 := H
  rw [H', Nat.zero_testBit] at e
  have hd : decide (p < h) = true := by simp [hp]
  unfold dot
  calc ∑ q : Fin h, tvec h u q * dv h P p q
      = ∑ q : Fin h, (fun q => bF ((P &&& (u * rep h h)).testBit (q + h * p)
          && (rep h h).testBit (h * p))) q.val :=
        Finset.sum_congr rfl (fun q _ => by
          show tvec h u q * dv h P p q = bF ((P &&& (u * rep h h)).testBit (q.val + h * p)
            && (rep h h).testBit (h * p))
          rw [h1, Bool.and_true, Nat.add_comm, Nat.testBit_and,
            mul_rep_bit h hh u hu h p q.val q.isLt, hd, Bool.true_and, bF_and, mul_comm]
          rfl)
    _ = ∑ q ∈ range h, (fun q => bF ((P &&& (u * rep h h)).testBit (q + h * p)
          && (rep h h).testBit (h * p))) q :=
        Fin.sum_univ_eq_sum_range (fun q => bF ((P &&& (u * rep h h)).testBit (q + h * p)
          && (rep h h).testBit (h * p))) h
    _ = 0 := e.symm

theorem rep_one (h : Nat) : rep h 1 = 1 := by
  show 2 ^ h * rep h 0 + 1 = 1
  rw [rep_zero]; simp

/-- the elimination on ONE digit: the mask `u` lies in the coded subspace. -/
theorem mem_of_elim (h : Nat) (hh : 0 < h) (c u : Nat) (hg : Good h c)
    (H : elimT h (2 ^ h - 1) 1 (cP h c) u = true) : (lab h c).Mem (tvec h u) := by
  have H' : elimT h (2 ^ h - 1) (rep h 1) (cP h c) u = true := by rw [rep_one]; exact H
  have a := elimT_sound h hh 1 (cP h c) u (fun y => (lab h c).Mem y) (mem_zero _)
    (fun x y hx hy => mem_add _ hx hy) (fun q hq => lab_bas hg ⟨q, hq⟩) H' 0
  have e : dv h u 0 = tvec h u := by
    funext q; simp [dv, tvec]
  rw [e] at a
  exact a

theorem dot_smul_right {α : Type} [Fintype α] (x y : Space α) (a : F) :
    dot x (a • y) = a * dot x y := by
  unfold dot
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring)

/-- orthogonal to every digit, hence to the whole coded subspace. -/
theorem perp_of_dots (h c : Nat) (hg : Good h c) (w : Space (Fin h))
    (H : ∀ p, p < h → dot w (dv h (cP h c) p) = 0) :
    ∀ x, (lab h c).Mem x → dot w x = 0 := by
  intro x hx
  rw [(lab_mem hg x).mp hx, dot_sum]
  refine Finset.sum_eq_zero (fun q _ => ?_)
  rw [dot_smul_right]
  have : dot w (bas h (cP h c) q) = 0 := H q.val q.isLt
  rw [this, mul_zero]

theorem wfK_sound : ∀ (t : Trie) (d : Nat), wfK t d = true → t.wf d := by
  intro t
  induction t with
  | leaf v =>
    intro d H
    have e : d = 0 := beq_true H
    rw [e]; exact trivial
  | node l r il ir =>
    intro d H
    cases d with
    | zero => exact absurd H Bool.false_ne_true
    | succ m =>
      obtain ⟨g1, g2⟩ := guard_true (show guard (wfK l m) (wfK r m) = true from H)
      exact ⟨il m g1, ir m g2⟩

end GLab

#print axioms GLab.unit_of_pars
#print axioms GLab.gap_of_lt
#print axioms GLab.dots_zero
#print axioms GLab.mem_of_elim
#print axioms GLab.perp_of_dots
#print axioms GLab.wfK_sound
