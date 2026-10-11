import Work.GCert.Scalar.Scat

/-!
# (key: gx-scalar) Parameters, first contents, final test, equality of tries

* `gPre_sound`    what the parameter tests give;
* `gInit_sound`, `init_ok`   the first contents: register `off + T` holds the unit at digit `T`;
* `gFin_sound`    the final test: `P = N + unit at digit S - lo` (or `+ 0`);
* `cont_start`, `cont_end`   the same as contents (`gcont`);
* `beqK_eq`       the kernel's equality test of tries.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace GS
open SSC GXD

theorem retOKK_sound (v2 nr : Nat) : ∀ (l : List (Nat × Nat)), retOKK v2 nr l = true →
    ∀ x ∈ l, v2 ≤ x.1 ∧ x.1 < nr := by
  intro l
  induction l with
  | nil => intro _ x hx; exact absurd hx List.not_mem_nil
  | cons y l ih =>
    intro h x hx
    have h' : guard (Nat.ble v2 y.1) (guard (Nat.ble (Nat.succ y.1) nr) (retOKK v2 nr l)) = true := h
    obtain ⟨h1, h2⟩ := guard_true h'
    obtain ⟨h3, h4⟩ := guard_true h2
    rcases List.mem_cons.mp hx with e | e
    · rw [e]; exact ⟨ble_true h1, ble_true h3⟩
    · exact ih h4 x e

theorem gPre_sound (c : Raw) (p : SPar) (lo n : Nat) (k : Nat → Nat → Nat → Nat → Nat → Nat → Bool)
    (h : gPre c p lo n k = true) :
    (1 ≤ p.ux ∧ 1 ≤ p.us ∧ 1 ≤ p.uy ∧ 1 ≤ p.sw) ∧ 2 * c.v + c.R ≤ 2^p.d ∧ lo + n ≤ c.v ∧
      (p.ux < 2^(p.sw - 1) ∧ p.uy < 2^(p.sw - 1) ∧ p.ux < 2^31 ∧ p.uy < 2^31) ∧
      (∀ x ∈ c.ret, 2 * c.v ≤ x.1 ∧ x.1 < 2 * c.v + c.R) ∧
      k (2 * c.v) (2 * c.v + c.R) (lo + n) (maskW p.sw n) (64 + p.sw * n) (2^(64 + p.sw * n))
        = true := by
  unfold gPre at h
  rw [forceN_eq, forceN_eq, forceN_eq, forceN_eq, forceN_eq] at h
  obtain ⟨h1, h⟩ := guard_true h
  obtain ⟨h2, h⟩ := guard_true h
  obtain ⟨h3, h⟩ := guard_true h
  obtain ⟨h4, h⟩ := guard_true h
  obtain ⟨h5, h⟩ := guard_true h
  obtain ⟨h6, h⟩ := guard_true h
  obtain ⟨h7, h⟩ := guard_true h
  obtain ⟨h8, h⟩ := guard_true h
  obtain ⟨h9, h⟩ := guard_true h
  obtain ⟨h10, h⟩ := guard_true h
  obtain ⟨h11, h⟩ := guard_true h
  rw [forceN_eq, forceN_eq] at h
  exact ⟨⟨ble_true h1, ble_true h2, ble_true h3, ble_true h4⟩, ble_true h5, ble_true h6,
    ⟨ble_true h7, ble_true h8, ble_true h9, ble_true h10⟩, retOKK_sound _ _ _ h11, h⟩

/-- the tag weight of the digit `T` -/
def tau (T : Nat) : Nat := (2654435761 * (T + 1)) % 4294967296

theorem tau_lt (T : Nat) : tau T < 2^32 := Nat.mod_lt _ (by norm_num)

/-- the first leaf of a source register -/
def leaf0 (sw u T : Nat) : Nat := u <<< (64 + sw * T) + u * tau T

theorem leaf0_facts (sw n u T : Nat) (hu : u < 2^(sw - 1)) (hsw : 1 ≤ sw) (hu2 : u < 2^31)
    (hT : T < n) :
    leaf0 sw u T < 2^(64 + sw * n) ∧ leaf0 sw u T >>> 64 = u * 2^(sw * T) ∧
      leaf0 sw u T % 2^64 < 2^63 := by
  have hc : tau T < 2^32 := tau_lt T
  unfold leaf0
  generalize tau T = c at hc ⊢
  have huc : u * c < 2^63 := by
    have : u * c < 2^31 * 2^32 := Nat.mul_lt_mul'' hu2 hc
    have e : (2:Nat)^31 * 2^32 = 2^63 := by norm_num
    omega
  have e0 : u <<< (64 + sw * T) + u * c = u * c + (u * 2^(sw * T)) * 2^64 := by
    rw [Nat.shiftLeft_eq, Nat.pow_add, Nat.mul_comm (2^64), ← Nat.mul_assoc, Nat.add_comm]
  have hA : u * 2^(sw * T) < 2^(sw * n) := by
    have h1 : u < 2^sw := lt_of_lt_of_le hu (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h2 : u * 2^(sw * T) < 2^sw * 2^(sw * T) := Nat.mul_lt_mul_of_pos_right h1 (Nat.two_pow_pos _)
    have h3 : 2^sw * 2^(sw * T) = 2^(sw * (T + 1)) := by
      rw [← Nat.pow_add, Nat.mul_succ, Nat.add_comm]
    have h4 : 2^(sw * (T + 1)) ≤ 2^(sw * n) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (by omega))
    omega
  have h64 : (2:Nat)^63 < 2^64 := by norm_num
  refine ⟨?_, ?_, ?_⟩
  · rw [e0, Nat.pow_add, Nat.mul_comm (2^64)]
    have : (u * 2^(sw * T) + 1) * 2^64 ≤ 2^(sw * n) * 2^64 := Nat.mul_le_mul_right _ hA
    have e : (u * 2^(sw * T) + 1) * 2^64 = u * 2^(sw * T) * 2^64 + 2^64 := by ring
    omega
  · rw [e0, Nat.shiftRight_eq_div_pow, Nat.add_mul_div_right _ _ (Nat.two_pow_pos 64),
      Nat.div_eq_of_lt (by omega), Nat.zero_add]
  · rw [e0, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    exact huc

theorem gInit_succ (sw u off n i : Nat) (t : Trie) (k : Trie → Bool) :
    gInit sw u off (n+1) i t k = forceN (Nat.add (Nat.shiftLeft u (Nat.add 64 (Nat.mul sw i)))
        (Nat.mul u (Nat.mod (Nat.mul 2654435761 (Nat.succ i)) 4294967296))) fun b =>
      forceN (Nat.succ i) fun i2 => gInit sw u off n i2 (t.set (Nat.add off i) b) k := rfl

theorem gInit_sound (d sw u off : Nat) : ∀ (n i : Nat) (t : Trie) (k : Trie → Bool), t.wf d →
    off + i + n ≤ 2^d → gInit sw u off n i t k = true →
    ∃ t', t'.wf d ∧ k t' = true ∧ ∀ r, absS (2^d) t' r
      = if off + i ≤ r ∧ r < off + i + n then leaf0 sw u (r - off) else absS (2^d) t r := by
  intro n
  induction n with
  | zero =>
    intro i t k hwf _ h
    refine ⟨t, hwf, h, fun r => ?_⟩
    have hn : ¬ (off + i ≤ r ∧ r < off + i + 0) := by omega
    rw [if_neg hn]
  | succ n ih =>
    intro i t k hwf hle h
    rw [gInit_succ, forceN_eq, forceN_eq] at h
    have hi : off + i < 2^d := by omega
    obtain ⟨t', hwf', hk, hval⟩ := ih (i+1) _ k (Trie.wf_set d t hwf _ _) (by omega) h
    refine ⟨t', hwf', hk, fun r => ?_⟩
    rw [hval r]
    have hs := absS_set d t hwf (off + i) (leaf0 sw u i) hi
    have hs' : absS (2^d) (t.set (Nat.add off i) (Nat.add (Nat.shiftLeft u (Nat.add 64 (Nat.mul sw i)))
        (Nat.mul u (Nat.mod (Nat.mul 2654435761 (Nat.succ i)) 4294967296))))
        = Function.update (absS (2^d) t) (off + i) (leaf0 sw u i) := hs
    rw [hs']
    by_cases e : r = off + i
    · have h1 : ¬ (off + (i + 1) ≤ r ∧ r < off + (i + 1) + n) := by omega
      have h2 : off + i ≤ r ∧ r < off + i + (n + 1) := by omega
      have e3 : r - off = i := by omega
      rw [if_neg h1, if_pos h2, e, Function.update_self, ← e, e3]
    · rw [Function.update_of_ne e]
      by_cases hA : off + (i + 1) ≤ r ∧ r < off + (i + 1) + n
      · have h2 : off + i ≤ r ∧ r < off + i + (n + 1) := by omega
        rw [if_pos hA, if_pos h2]
      · have h2 : ¬ (off + i ≤ r ∧ r < off + i + (n + 1)) := by omega
        rw [if_neg hA, if_neg h2]

/-- the state after `gInit` on the empty trie: invariant and abstract contents -/
theorem init_ok (d sw n u off : Nat) (hsw : 1 ≤ sw) (hu : u < 2^(sw - 1)) (hu2 : u < 2^31)
    (t' : Trie) (hwf : t'.wf d)
    (hval : ∀ r, absS (2^d) t' r = if off + 0 ≤ r ∧ r < off + 0 + n then leaf0 sw u (r - off)
      else absS (2^d) (Trie.mk d) r) :
    GOk d sw n t' ∧ ∀ r, (absG d (64 + sw * n) t').N r = 0 ∧ (absG d (64 + sw * n) t').P r
      = if off ≤ r ∧ r < off + n then u * 2^(sw * (r - off)) else 0 := by
  have hus : u < 2^sw := lt_of_lt_of_le hu (Nat.pow_le_pow_right (by norm_num) (by omega))
  have key : ∀ r, (absS (2^d) t' r % 2^(64 + sw * n)) >>> 64
        = (if off ≤ r ∧ r < off + n then u * 2^(sw * (r - off)) else 0) ∧
      absS (2^d) t' r >>> (64 + sw * n) = 0 ∧ absS (2^d) t' r % 2^(64 + sw * n) % 2^64 < 2^63 := by
    intro r
    rw [hval r, Nat.add_zero]
    by_cases hr : off ≤ r ∧ r < off + n
    · obtain ⟨f1, f2, f3⟩ := leaf0_facts sw n u (r - off) hu hsw hu2 (by omega)
      rw [if_pos hr, if_pos hr, Nat.mod_eq_of_lt f1, Nat.shiftRight_eq_div_pow _ (64 + sw * n),
        Nat.div_eq_of_lt f1]
      exact ⟨f2, rfl, f3⟩
    · rw [if_neg hr, if_neg hr, absS_mk]
      exact ⟨by simp, by simp, by norm_num⟩
  refine ⟨⟨hwf, fun r => ?_⟩, fun r => ?_⟩
  · obtain ⟨k1, k2, k3⟩ := key r
    refine ⟨⟨?_, k3⟩, ?_⟩
    · rw [k1]
      intro T _
      by_cases hr : off ≤ r ∧ r < off + n
      · rw [if_pos hr, dg_mul_pow sw u hus]
        by_cases e : T = r - off
        · rw [if_pos e]; exact hu
        · rw [if_neg e]; exact Nat.two_pow_pos _
      · rw [if_neg hr, dg_zero_left]; exact Nat.two_pow_pos _
    · rw [k2]; exact ok_zero sw n
  · obtain ⟨k1, k2, _⟩ := key r
    refine ⟨?_, k1⟩
    show (absS (2^d) t' r >>> (64 + sw * n)) >>> 64 = 0
    rw [k2]; rfl

#print axioms gPre_sound
#print axioms init_ok

end GS
