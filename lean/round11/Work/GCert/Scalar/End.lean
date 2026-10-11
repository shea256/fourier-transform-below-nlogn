import Work.GCert.Scalar.Fin

/-!
# (key: gx-scalar) Final test, contents at the start and at the end, equality of tries

* `gFin_sound`    the final test: `P = N + unit at digit S - lo` (or `+ 0`);
* `cont_start`, `cont_end`   first contents and final test as contents (`gcont`);
* `beqK_eq`       the kernel's equality test of tries.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace GS
open SSC GXD

theorem finE_eq (sw u lo hi S : Nat) :
    Bool.rec (motive := fun _ => Nat) 0 (Bool.rec (motive := fun _ => Nat) 0
      (Nat.shiftLeft u (Nat.mul sw (Nat.sub S lo))) (Nat.ble (Nat.succ S) hi)) (Nat.ble lo S)
      = if lo ≤ S ∧ S < hi then u * 2^(sw * (S - lo)) else 0 := by
  by_cases h1 : lo ≤ S
  · have e1 : Nat.ble lo S = true := Nat.ble_eq_true_of_le h1
    rw [e1]
    by_cases h2 : S < hi
    · have e2 : Nat.ble (Nat.succ S) hi = true := Nat.ble_eq_true_of_le h2
      rw [e2, if_pos ⟨h1, h2⟩]
      exact Nat.shiftLeft_eq _ _
    · have e2 : Nat.ble (Nat.succ S) hi = false :=
        Bool.eq_false_iff.mpr (fun h => h2 (ble_true h))
      rw [e2, if_neg (fun h => h2 h.2)]
  · have e1 : Nat.ble lo S = false := Bool.eq_false_iff.mpr (fun h => h1 (ble_true h))
    rw [e1, if_neg (fun h => h1 h.1)]

theorem gFin_succ (sw K m2 u base lo hi : Nat) (tr : Trie) (cnt S : Nat) :
    gFin sw K m2 u base lo hi tr (cnt+1) S = tr.getK (Nat.add base S) fun x =>
      guard (Nat.beq (Nat.shiftRight (Nat.mod x m2) 64)
          (Nat.add (Nat.shiftRight (Nat.shiftRight x K) 64) (Bool.rec (motive := fun _ => Nat) 0
            (Bool.rec (motive := fun _ => Nat) 0 (Nat.shiftLeft u (Nat.mul sw (Nat.sub S lo)))
              (Nat.ble (Nat.succ S) hi)) (Nat.ble lo S))))
        (forceN (Nat.succ S) (gFin sw K m2 u base lo hi tr cnt)) := rfl

theorem gFin_sound (d sw K u base lo hi : Nat) (tr : Trie) (hwf : tr.wf d) :
    ∀ (cnt S : Nat), gFin sw K (2^K) u base lo hi tr cnt S = true → ∀ j, j < cnt →
      (absG d K tr).P (base + (S + j)) = (absG d K tr).N (base + (S + j))
        + (if lo ≤ S + j ∧ S + j < hi then u * 2^(sw * (S + j - lo)) else 0) := by
  intro cnt
  induction cnt with
  | zero =>
    intro S _ j hj
    exact absurd hj (Nat.not_lt_zero _)
  | succ cnt ih =>
    intro S h j hj
    rw [gFin_succ, Trie.getK_eq d tr hwf] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hr, h2⟩ := h
    obtain ⟨hb, h4⟩ := guard_true h2
    rw [forceN_eq] at h4
    have hr' : base + S < 2^d := hr
    cases j with
    | zero =>
      have hv := beq_true hb
      rw [finE_eq] at hv
      show (absS (2^d) tr (base + (S + 0)) % 2^K) >>> 64
        = (absS (2^d) tr (base + (S + 0)) >>> K) >>> 64 + _
      rw [Nat.add_zero, absS_apply d tr _ hr']
      exact hv
    | succ j =>
      have h5 := ih (S+1) h4 j (by omega)
      have e : S + (j + 1) = S + 1 + j := by omega
      rw [e]
      exact h5

/-- at the start the register `off + T` holds source `T`, all others nothing -/
theorem cont_start (sw n : Nat) (U : Nat → Nat) (a0 : SSt) (off u : Nat) (hu1 : 1 ≤ u)
    (hus : u < 2^sw)
    (h0 : ∀ r, a0.N r = 0 ∧ a0.P r = if off ≤ r ∧ r < off + n then u * 2^(sw * (r - off)) else 0)
    (r T : Nat) (hT : T < n) (hU : (off ≤ r ∧ r < off + n) → U r = u) :
    gcont sw U a0 r T = if r = off + T then 1 else 0 := by
  unfold gcont
  rw [(h0 r).1, (h0 r).2, dg_zero_left]
  by_cases hr : off ≤ r ∧ r < off + n
  · rw [if_pos hr, dg_mul_pow sw u hus, hU hr]
    have u0 : (u:ℚ) ≠ 0 := by positivity
    by_cases e : r = off + T
    · have e' : T = r - off := by omega
      rw [if_pos e', if_pos e]
      field_simp
      simp
    · have e' : ¬ T = r - off := by omega
      rw [if_neg e', if_neg e]
      simp
  · have e : ¬ r = off + T := by omega
    rw [if_neg hr, if_neg e, dg_zero_left]
    simp

/-- at the end: `P = N + unit at digit j` (if `c`) means the content is exactly source `j` -/
theorem cont_end (sw n : Nat) (U : Nat → Nat) (a : SSt) (r u j : Nat) (c : Prop) [Decidable c]
    (hsw : 1 ≤ sw) (hu1 : 1 ≤ u) (hu : u < 2^(sw - 1)) (hU : U r = u)
    (hsm : SmallV sw n (a.N r))
    (h : a.P r = a.N r + (if c then u * 2^(sw * j) else 0)) (T : Nat) (hT : T < n) :
    gcont sw U a r T = if c ∧ T = j then 1 else 0 := by
  have hus : u < 2^sw := lt_of_lt_of_le hu (Nat.pow_le_pow_right (by norm_num) (by omega))
  have u0 : (u:ℚ) ≠ 0 := by positivity
  unfold gcont
  rw [h, hU]
  by_cases hc : c
  · have hsmall : SmallV sw n (u * 2^(sw * j)) := by
      intro T' _
      rw [dg_mul_pow sw u hus]
      by_cases hT' : T' = j
      · rw [if_pos hT']; exact hu
      · rw [if_neg hT']; exact Nat.two_pow_pos _
    rw [if_pos hc, dg_add_small sw n _ _ hsw hsm hsmall T hT, dg_mul_pow sw u hus]
    by_cases e : T = j
    · rw [if_pos e, if_pos ⟨hc, e⟩]
      push_cast
      field_simp
      ring
    · rw [if_neg e, if_neg (fun h => e h.2)]
      push_cast
      simp
  · rw [if_neg hc, if_neg (fun h => hc h.1), Nat.add_zero]
    simp

theorem beqK_eq : ∀ (a b : Trie), beqK a b = true → a = b := by
  intro a
  induction a with
  | leaf x =>
    intro b h
    cases b with
    | leaf x' =>
      have h' : Nat.beq x x' = true := h
      rw [beq_true h']
    | node l' r' => exact absurd (show false = true from h) Bool.false_ne_true
  | node l r il ir =>
    intro b h
    cases b with
    | leaf x' => exact absurd (show false = true from h) Bool.false_ne_true
    | node l' r' =>
      have h' : guard (beqK l l') (beqK r r') = true := h
      obtain ⟨h1, h2⟩ := guard_true h'
      rw [il l' h1, ir r' h2]

#print axioms gFin_sound
#print axioms cont_start
#print axioms cont_end
#print axioms beqK_eq

end GS
