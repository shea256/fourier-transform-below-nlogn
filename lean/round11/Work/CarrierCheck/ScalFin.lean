import Work.CarrierCheck.ScalId

/-!
# (key: carrier-check) An accepted scalar check: the four states

`CCert.Valid.scalar_states`: if `c.scalarCheck = true` there are abstract states
`a0 → a1 → a2 → a3` (start, after phase A, after the scatter, after phase B) joined by `SRun`
on the micro-programs `mA`, `scatL`, `mB`, where `a0` holds `x_t` in the x role `t` and nothing
elsewhere, and `a3` holds exactly `x_S` (two half units) in every `y_S`.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace SSC
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM OAI.PowerSaving.SS Finset Matrix

theorem sInitK_succ (sw n i : Nat) (t : Trie) (k : Trie → Bool) :
    sInitK sw (n+1) i t k = forceN (Nat.shiftLeft 1 (Nat.mul sw i)) fun b =>
      forceN (Nat.succ i) fun i2 => sInitK sw n i2 (t.set i b) k := rfl

theorem sInitK_sound (d sw : Nat) : ∀ (n i : Nat) (t : Trie) (k : Trie → Bool), t.wf d →
    i + n ≤ 2^d → sInitK sw n i t k = true →
    ∃ t', t'.wf d ∧ k t' = true ∧ ∀ r, absS (2^d) t' r
      = if i ≤ r ∧ r < i + n then 1 * 2^(sw * r) else absS (2^d) t r := by
  intro n
  induction n with
  | zero =>
    intro i t k hwf _ h
    refine ⟨t, hwf, h, fun r => ?_⟩
    have hn : ¬ (i ≤ r ∧ r < i + 0) := by omega
    rw [if_neg hn]
  | succ n ih =>
    intro i t k hwf hle h
    rw [sInitK_succ, forceN_eq, forceN_eq] at h
    have hi : i < 2^d := by omega
    obtain ⟨t', hwf', hk, hval⟩ := ih (i+1) (t.set i (Nat.shiftLeft 1 (Nat.mul sw i))) k
      (Trie.wf_set d t hwf _ _) (by omega) h
    refine ⟨t', hwf', hk, fun r => ?_⟩
    rw [hval r, absS_set d t hwf i _ hi]
    by_cases e : r = i
    · have h1 : ¬ (i + 1 ≤ r ∧ r < i + 1 + n) := by omega
      have h2 : i ≤ r ∧ r < i + (n + 1) := by omega
      rw [if_neg h1, if_pos h2, e, Function.update_self]
      exact Nat.shiftLeft_eq 1 (sw * i)
    · rw [Function.update_of_ne e]
      by_cases hA : i + 1 ≤ r ∧ r < i + 1 + n
      · have h2 : i ≤ r ∧ r < i + (n + 1) := by omega
        rw [if_pos hA, if_pos h2]
      · have h2 : ¬ (i ≤ r ∧ r < i + (n + 1)) := by omega
        rw [if_neg hA, if_neg h2]

theorem sFinK_succ (sw y0 : Nat) (tP tN : Trie) (n S : Nat) :
    sFinK sw y0 tP tN (n+1) S = tP.getK (Nat.add y0 S) fun P => tN.getK (Nat.add y0 S) fun N =>
      guard (Nat.beq P (Nat.add N (Nat.shiftLeft 2 (Nat.mul sw S))))
        (forceN (Nat.succ S) (sFinK sw y0 tP tN n)) := rfl

theorem sFinK_sound (d sw y0 : Nat) (tP tN : Trie) (hwP : tP.wf d) (hwN : tN.wf d) :
    ∀ (n S : Nat), sFinK sw y0 tP tN n S = true → ∀ j, j < n →
      absS (2^d) tP (y0 + (S + j)) = absS (2^d) tN (y0 + (S + j)) + 2 * 2^(sw * (S + j)) := by
  intro n
  induction n with
  | zero =>
    intro S _ j hj
    exact absurd hj (Nat.not_lt_zero _)
  | succ n ih =>
    intro S h j hj
    rw [sFinK_succ, Trie.getK_eq d tP hwP] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hr, h2⟩ := h
    rw [Trie.getK_eq d tN hwN] at h2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
    obtain ⟨_, h3⟩ := h2
    obtain ⟨hb, h4⟩ := guard_true h3
    rw [forceN_eq] at h4
    have hr' : y0 + S < 2^d := hr
    cases j with
    | zero =>
      have hv : tP.get (y0 + S) = tN.get (y0 + S) + 2 <<< (sw * S) := beq_true hb
      rw [Nat.add_zero, absS_apply d tP _ hr', absS_apply d tN _ hr', hv, Nat.shiftLeft_eq]
    | succ j =>
      have h5 := ih (S+1) h4 j (by omega)
      have e : S + (j + 1) = S + 1 + j := by omega
      rw [e]
      exact h5

namespace CCert
variable {c : CCert}

/-- the gates of the scatter, as micro-ops: `y_S += coef * slot (ret k)` -/
def scatL (c : CCert) : List Micro := scatFromM c.v c.ret (c.v + c.R) c.scat

theorem Valid.n_le (V : c.Valid) : c.n ≤ 2^c.p.d := by
  have h := (check_micro c.p c.inits c.cs (c.fins ++ [c.yfins]) c.N V.hchk).1
  have e : c.inits.length = c.n := by
    unfold inits n
    rw [List.length_append, List.length_map, List.length_replicate, V.htl]
    omega
  rw [e] at h
  exact h

/-- **the four states of an accepted scalar check** -/
theorem Valid.scalar_states (V : c.Valid) (h : c.scalarCheck = true) :
    ∃ a0 a1 a2 a3 : SSt,
      SRun c.sw c.v (c.v + c.R) a0 c.mA a1 ∧
      SRun c.sw c.v (c.v + c.R) a1 c.scatL a2 ∧
      SRun c.sw c.v (c.v + c.R) a2 c.mB a3 ∧
      (∀ r, a0.N r = 0 ∧ a0.P r = if r < c.v then 1 * 2^(c.sw * r) else 0) ∧
      (∀ S, S < c.v →
        a3.P (c.v + c.R + S) = a3.N (c.v + c.R + S) + 2 * 2^(c.sw * S)) ∧
      SmallSt c.sw c.v a3 ∧ 3 ≤ c.sw := by
  have h' : guard (decide (3 ≤ c.sw))
      (forceN (Nat.shiftLeft (rep c.sw c.v) (Nat.sub c.sw 1)) fun tm =>
        forceN (Nat.add c.v c.R) fun y0 =>
          sInitK c.sw c.v 0 (Trie.mk c.p.d) fun tP0 =>
            sChunks tm y0 c.A tP0 (Trie.mk c.p.d) fun tP1 tN1 =>
              sScat tm y0 c.v c.ret c.scat y0 tP1 tN1 fun tP2 tN2 =>
                sChunks tm y0 c.B tP2 tN2 fun tP3 tN3 => sFinK c.sw y0 tP3 tN3 c.v 0) = true := h
  obtain ⟨h3, h1⟩ := guard_true h'
  have hsw3 : 3 ≤ c.sw := by simpa using h3
  have hsw : 1 ≤ c.sw := by omega
  rw [forceN_eq, forceN_eq] at h1
  have htm : rep c.sw c.v <<< (c.sw - 1) = rep c.sw c.v <<< (c.sw - 1) := rfl
  have h1' : sInitK c.sw c.v 0 (Trie.mk c.p.d) (fun tP0 =>
      sChunks (rep c.sw c.v <<< (c.sw - 1)) (c.v + c.R) c.A tP0 (Trie.mk c.p.d) fun tP1 tN1 =>
        sScat (rep c.sw c.v <<< (c.sw - 1)) (c.v + c.R) c.v c.ret c.scat (c.v + c.R) tP1 tN1
          fun tP2 tN2 => sChunks (rep c.sw c.v <<< (c.sw - 1)) (c.v + c.R) c.B tP2 tN2
            fun tP3 tN3 => sFinK c.sw (c.v + c.R) tP3 tN3 c.v 0) = true := h1
  have hnle := V.n_le
  have hvle : 0 + c.v ≤ 2^c.p.d := by unfold n at hnle; omega
  obtain ⟨tP0, hw0, hk0, hv0⟩ := sInitK_sound c.p.d c.sw c.v 0 (Trie.mk c.p.d) _
    (Trie.wf_mk c.p.d) hvle h1'
  have hP0 : ∀ r, absS (2^c.p.d) tP0 r = if r < c.v then 1 * 2^(c.sw * r) else 0 := by
    intro r
    rw [hv0 r, absS_mk]
    by_cases hr : r < c.v
    · rw [if_pos hr, if_pos ⟨Nat.zero_le _, by omega⟩]
    · rw [if_neg hr, if_neg (fun hh => hr (by omega))]
  have h12 : 1 < 2^(c.sw - 1) := by
    have h2 : 2^1 ≤ 2^(c.sw - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : (2:Nat)^1 = 2 := rfl
    omega
  have hI0 : TOk c.p.d c.sw c.v tP0 (Trie.mk c.p.d) := by
    refine ⟨hw0, Trie.wf_mk c.p.d, fun r => ⟨?_, ?_⟩⟩
    · show SmallV c.sw c.v (absS (2^c.p.d) tP0 r)
      rw [hP0 r]
      by_cases hr : r < c.v
      · rw [if_pos hr]
        intro T _
        have h1lt : 1 < 2^c.sw := Nat.one_lt_two_pow (by omega)
        rw [dg_mul_pow c.sw 1 h1lt r T]
        by_cases hT : T = r
        · rw [if_pos hT]; exact h12
        · rw [if_neg hT]; exact Nat.two_pow_pos _
      · rw [if_neg hr]; exact small_zero _ _
    · show SmallV c.sw c.v (absS (2^c.p.d) (Trie.mk c.p.d) r)
      rw [absS_mk]; exact small_zero _ _
  obtain ⟨tP1, tN1, hI1, hk1, hrA⟩ := sChunks_sound c.p.d c.sw c.v _ (c.v + c.R) hsw htm c.A
    tP0 (Trie.mk c.p.d) _ hI0 hk0
  obtain ⟨tP2, tN2, hI2, hk2, hrS⟩ := sScat_sound c.p.d c.sw c.v _ (c.v + c.R) hsw htm c.ret
    c.scat (c.v + c.R) tP1 tN1 _ hI1 hk1
  obtain ⟨tP3, tN3, hI3, hk3, hrB⟩ := sChunks_sound c.p.d c.sw c.v _ (c.v + c.R) hsw htm c.B
    tP2 tN2 _ hI2 hk2
  have hfin := sFinK_sound c.p.d c.sw (c.v + c.R) tP3 tN3 hI3.wP hI3.wN c.v 0 hk3
  refine ⟨absT c.p.d tP0 (Trie.mk c.p.d), absT c.p.d tP1 tN1, absT c.p.d tP2 tN2,
    absT c.p.d tP3 tN3, hrA, hrS, hrB, fun r => ⟨absS_mk c.p.d r, hP0 r⟩, fun S hS => ?_,
    hI3.sm, hsw3⟩
  have h5 := hfin S hS
  rw [Nat.zero_add] at h5
  exact h5

end CCert

end SSC
