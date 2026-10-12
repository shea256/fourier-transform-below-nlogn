import Work.Scratch.Engine
import Work.SharedSumChecker.Check

/-!
# Shared-sum checker: bit-level facts about the packed labels

`spread`, `upd`, `updS` of `Check.lean` are single big-number expressions (so that the kernel
evaluates a move in a handful of steps).  Here their bits are computed.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.deprecated false

namespace SSC

theorem forceN_eq {α : Type} (n : Nat) (k : Nat → α) : forceN n k = k n := by
  cases n <;> rfl

theorem guard_eq (b k : Bool) : guard b k = (b && k) := by cases b <;> rfl

theorem rep_zero (u : Nat) : rep u 0 = 0 := rfl
theorem rep_succ (u n : Nat) : rep u (n+1) = 2^u * rep u n + 1 := rfl

theorem Par.K_eq (p : Par) : p.K = p.w * p.h := rfl
theorem Par.K2_eq (p : Par) : p.K2 = 2 * (p.w * p.h) := rfl
theorem Par.K3_eq (p : Par) : p.K3 = 3 * (p.w * p.h) := rfl
theorem Par.hm_eq (p : Par) : p.hm = 2^p.h - 1 := rfl
theorem Par.km_eq (p : Par) : p.km = rep (p.w - 1) p.h := rfl
theorem Par.mm_eq (p : Par) : p.mm = rep p.w p.h := rfl
theorem Par.n_eq (p : Par) : p.n = 2^p.d := rfl

private theorem step_idx (u q r : Nat) (hu : 0 < u) :
    ¬ (u*(q+1) + r < u) ∧ u*(q+1) + r - u = u*q + r := by
  have h : u*(q+1) = u*q + u := Nat.mul_succ u q
  constructor <;> omega

theorem rep_bit (u : Nat) (hu : 0 < u) (n q r : Nat) (hr : r < u) :
    (rep u n).testBit (u*q + r) = (decide (r = 0) && decide (q < n)) := by
  induction n generalizing q with
  | zero => simp [rep_zero]
  | succ n ih =>
    rw [rep_succ, Nat.testBit_two_pow_mul_add _ (Nat.one_lt_two_pow (Nat.pos_iff_ne_zero.mp hu))]
    cases q with
    | zero =>
      simp only [Nat.mul_zero, Nat.zero_add, hr, ite_true]
      cases r with
      | zero => simp
      | succ r => simp [Nat.testBit_add_one]
    | succ q =>
      obtain ⟨h1, h2⟩ := step_idx u q r hu
      rw [if_neg h1, h2, ih q]
      simp

theorem mul_rep_bit (u : Nat) (hu : 0 < u) (y : Nat) (hy : y < 2^u) (n q r : Nat) (hr : r < u) :
    (y * rep u n).testBit (u*q + r) = (decide (q < n) && y.testBit r) := by
  induction n generalizing q with
  | zero => simp [rep_zero]
  | succ n ih =>
    have e : y * rep u (n+1) = 2^u * (y * rep u n) + y := by rw [rep_succ]; ring
    rw [e, Nat.testBit_two_pow_mul_add _ hy]
    cases q with
    | zero => simp [hr]
    | succ q =>
      obtain ⟨h1, h2⟩ := step_idx u q r hu
      rw [if_neg h1, h2, ih q]
      simp

/-- reference form of `spread`: bit `q` of `z` (`q < n`) at position `w*q` -/
def sp (w : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, z => 2^w * sp w n (z/2) + z % 2

theorem sp_succ (w n z : Nat) : sp w (n+1) z = 2^w * sp w n (z/2) + z % 2 := rfl

private theorem mod2_lt (w z : Nat) (hw : 0 < w) : z % 2 < 2^w :=
  lt_of_lt_of_le (Nat.mod_lt _ (by norm_num))
    (by simpa using Nat.pow_le_pow_right (show 0 < 2 by norm_num) hw)

theorem sp_bit (w : Nat) (hw : 0 < w) (n z q r : Nat) (hr : r < w) :
    (sp w n z).testBit (w*q + r) = (decide (r = 0) && decide (q < n) && z.testBit q) := by
  induction n generalizing z q with
  | zero => simp [sp]
  | succ n ih =>
    rw [sp_succ, Nat.testBit_two_pow_mul_add _ (mod2_lt w z hw)]
    cases q with
    | zero =>
      simp only [Nat.mul_zero, Nat.zero_add, hr, ite_true]
      cases r with
      | zero => simp [Nat.testBit_zero]
      | succ r =>
        have h2 : (z % 2).testBit (r+1) = false :=
          Nat.testBit_lt_two_pow (lt_of_lt_of_le (Nat.mod_lt _ (by norm_num))
            (by simpa using Nat.pow_le_pow_right (show 0 < 2 by norm_num) (Nat.succ_pos r)))
        simp [h2]
    | succ q =>
      obtain ⟨h1, h2⟩ := step_idx w q r hw
      rw [if_neg h1, h2, ih (z/2) q]
      simp [Nat.testBit_add_one]

theorem sp_mul_bit (w : Nat) (hw : 0 < w) (y : Nat) (hy : y < 2^w) (n z q r : Nat) (hr : r < w) :
    (sp w n z * y).testBit (w*q + r) = (decide (q < n) && z.testBit q && y.testBit r) := by
  induction n generalizing z q with
  | zero => simp [sp]
  | succ n ih =>
    have hlt : z % 2 * y < 2^w := by
      rcases Nat.mod_two_eq_zero_or_one z with h | h <;> simp [h, hy]
    have e : sp w (n+1) z * y = 2^w * (sp w n (z/2) * y) + z % 2 * y := by
      rw [sp_succ]; ring
    rw [e, Nat.testBit_two_pow_mul_add _ hlt]
    cases q with
    | zero =>
      simp only [Nat.mul_zero, Nat.zero_add, hr, ite_true]
      rcases Nat.mod_two_eq_zero_or_one z with h | h <;> simp [h, Nat.testBit_zero]
    | succ q =>
      obtain ⟨h1, h2⟩ := step_idx w q r hw
      rw [if_neg h1, h2, ih (z/2) q]
      simp [Nat.testBit_add_one]

section
variable (p : Par) (hh : 0 < p.h) (hw : p.h < p.w)
include hh hw

theorem spread_bit (z q r : Nat) (hr : r < p.w) :
    (spread p z).testBit (p.w*q + r) = (decide (r = 0) && decide (q < p.h) && z.testBit q) := by
  have hw0 : 0 < p.w := by omega
  show (((z &&& p.hm) * p.km) &&& p.mm).testBit (p.w*q + r) = _
  rw [Nat.testBit_and]
  have hmm : p.mm.testBit (p.w*q + r) = (decide (r = 0) && decide (q < p.h)) :=
    rep_bit p.w hw0 p.h q r hr
  rw [hmm]
  by_cases h0 : r = 0
  · by_cases hq : q < p.h
    · subst h0
      have hy : z &&& p.hm < 2^(p.w - 1) := by
        have h1 : z &&& p.hm < 2^p.h :=
          Nat.and_lt_two_pow _ (show 2^p.h - 1 < 2^p.h from
            Nat.sub_lt (Nat.two_pow_pos _) Nat.one_pos)
        exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) (by omega))
      have e : p.w * q + 0 = (p.w - 1) * q + q := by
        rw [Nat.add_zero, ← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
      have hb := mul_rep_bit (p.w - 1) (by omega) (z &&& p.hm) hy p.h q q (by omega)
      rw [e]
      show (((z &&& p.hm) * rep (p.w - 1) p.h).testBit _ && _) = _
      rw [hb, Nat.testBit_and]
      have hm : p.hm.testBit q = true := by
        show (2^p.h - 1).testBit q = true
        rw [Nat.testBit_two_pow_sub_one]; simpa using hq
      simp [hq, hm]
    · simp [hq]
  · simp [h0]

theorem spread_eq_sp (z : Nat) : spread p z = sp p.w p.h z := by
  have hw0 : 0 < p.w := by omega
  apply Nat.eq_of_testBit_eq
  intro k
  have hk : p.w * (k / p.w) + k % p.w = k := Nat.div_add_mod k p.w
  rw [← hk, spread_bit p hh hw z _ _ (Nat.mod_lt _ hw0), sp_bit p.w hw0 p.h z _ _ (Nat.mod_lt _ hw0)]

theorem and_hm_lt (z : Nat) : z &&& p.hm < 2^p.w :=
  lt_of_lt_of_le (Nat.and_lt_two_pow _ (show 2^p.h - 1 < 2^p.h from
    Nat.sub_lt (Nat.two_pow_pos _) Nat.one_pos)) (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- bits of the outer product -/
theorem outer_bit (z i j : Nat) (hi : i < p.h) (hj : j < p.h) :
    (spread p z * (z &&& p.hm)).testBit (p.w*i + j) = (z.testBit i && z.testBit j) := by
  have hw0 : 0 < p.w := by omega
  rw [spread_eq_sp p hh hw, sp_mul_bit p.w hw0 _ (and_hm_lt p hh hw z) p.h z i j (by omega),
    Nat.testBit_and]
  have hm : p.hm.testBit j = true := by
    show (2^p.h - 1).testBit j = true
    rw [Nat.testBit_two_pow_sub_one]; simpa using hj
  simp [hi, hm]

theorem wi_lt (i : Nat) (hi : i < p.h) : p.w * i < p.K := by
  have h1 := Nat.mul_le_mul_left p.w (show i + 1 ≤ p.h from hi)
  rw [Nat.mul_succ] at h1
  show p.w * i < p.w * p.h
  omega

theorem spread_hi (z q r : Nat) (hr : r < p.w) (hq : p.h ≤ q) :
    (spread p z).testBit (p.w*q + r) = false := by
  rw [spread_bit p hh hw z q r hr]
  have : ¬ q < p.h := by omega
  simp [this]

theorem spread_lo (z i : Nat) (hi : i < p.h) : (spread p z).testBit (p.w*i) = z.testBit i := by
  have h := spread_bit p hh hw z i 0 (by omega)
  rw [Nat.add_zero] at h
  rw [h]; simp [hi]

/-! ### bits of a label after a kernel move -/

theorem updX_c0 (L z i : Nat) (hi : i < p.h) :
    (updX p L (spread p z) z).testBit (p.w*i) = (L.testBit (p.w*i) ^^ z.testBit i) := by
  have hlt := wi_lt p hh hw i hi
  have hK2 : p.K2 = 2 * p.K := rfl
  show (L ^^^ (spread p z ^^^ (((L &&& spread p z) <<< p.K) ^^^
    ((spread p z * (z &&& p.hm)) <<< p.K2)))).testBit (p.w*i) = _
  rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_shiftLeft,
    Nat.testBit_shiftLeft, spread_lo p hh hw z i hi]
  have h1 : ¬ (p.w * i ≥ p.K) := by omega
  have h2 : ¬ (p.w * i ≥ p.K2) := by omega
  simp [h1, h2]

theorem updX_c1 (L z i : Nat) (hi : i < p.h) :
    (updX p L (spread p z) z).testBit (p.K + p.w*i)
      = (L.testBit (p.K + p.w*i) ^^ (L.testBit (p.w*i) && z.testBit i)) := by
  have hlt := wi_lt p hh hw i hi
  have hK2 : p.K2 = 2 * p.K := rfl
  have e : p.K + p.w*i = p.w*(p.h + i) + 0 := by
    show p.w * p.h + p.w * i = _
    ring
  have hs : (spread p z).testBit (p.K + p.w*i) = false := by
    rw [e]; exact spread_hi p hh hw z _ 0 (by omega) (by omega)
  show (L ^^^ (spread p z ^^^ (((L &&& spread p z) <<< p.K) ^^^
    ((spread p z * (z &&& p.hm)) <<< p.K2)))).testBit (p.K + p.w*i) = _
  rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_shiftLeft,
    Nat.testBit_shiftLeft, hs, Nat.testBit_and]
  have h1 : p.K + p.w * i ≥ p.K := by omega
  have h2 : ¬ (p.K + p.w * i ≥ p.K2) := by omega
  have h3 : p.K + p.w * i - p.K = p.w * i := by omega
  rw [h3, spread_lo p hh hw z i hi]
  simp [h1, h2]

theorem updX_B (L z i j : Nat) (hi : i < p.h) (hj : j < p.h) :
    (updX p L (spread p z) z).testBit (p.K2 + p.w*i + j)
      = (L.testBit (p.K2 + p.w*i + j) ^^ (z.testBit i && z.testBit j)) := by
  have hK2 : p.K2 = 2 * p.K := rfl
  have e : p.K2 + p.w*i + j = p.w*(2*p.h + i) + j := by
    show 2 * (p.w * p.h) + p.w * i + j = _
    ring
  have e' : p.K + p.w*i + j = p.w*(p.h + i) + j := by
    show p.w * p.h + p.w * i + j = _
    ring
  have hs : (spread p z).testBit (p.K2 + p.w*i + j) = false := by
    rw [e]; exact spread_hi p hh hw z _ j (by omega) (by omega)
  have hs' : (spread p z).testBit (p.K + p.w*i + j) = false := by
    rw [e']; exact spread_hi p hh hw z _ j (by omega) (by omega)
  show (L ^^^ (spread p z ^^^ (((L &&& spread p z) <<< p.K) ^^^
    ((spread p z * (z &&& p.hm)) <<< p.K2)))).testBit (p.K2 + p.w*i + j) = _
  rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_shiftLeft,
    Nat.testBit_shiftLeft, hs, Nat.testBit_and]
  have h1 : p.K2 + p.w * i + j ≥ p.K := by omega
  have h2 : p.K2 + p.w * i + j ≥ p.K2 := by omega
  have h3 : p.K2 + p.w * i + j - p.K = p.K + p.w * i + j := by omega
  have h4 : p.K2 + p.w * i + j - p.K2 = p.w * i + j := by omega
  rw [h3, h4, hs', outer_bit p hh hw z i j hi hj]
  simp [h1, h2]

/-! ### the move counter -/

omit hh hw in
theorem testBit_add_shift (X c K i : Nat) (hi : i < K) : (X + c <<< K).testBit i = X.testBit i := by
  have h1 : (X + c <<< K) % 2^K = X % 2^K := by
    rw [Nat.shiftLeft_eq, Nat.add_mul_mod_self_right]
  have h2 := Nat.testBit_mod_two_pow (X + c <<< K) K i
  have h3 := Nat.testBit_mod_two_pow X K i
  rw [h1] at h2
  simp only [hi, decide_true, Bool.true_and] at h2 h3
  rw [← h2, h3]

theorem spread_big (z k : Nat) (hk : p.K ≤ k) : (spread p z).testBit k = false := by
  have hw0 : 0 < p.w := by omega
  have e : p.w * (k / p.w) + k % p.w = k := Nat.div_add_mod k p.w
  have hq : p.h ≤ k / p.w := (Nat.le_div_iff_mul_le hw0).mpr (by
    have : p.K = p.w * p.h := rfl
    rw [Nat.mul_comm]; omega)
  rw [← e]
  exact spread_hi p hh hw z _ _ (Nat.mod_lt _ hw0) hq

theorem outer_big (z k : Nat) (hk : p.K ≤ k) :
    (spread p z * (z &&& p.hm)).testBit k = false := by
  have hw0 : 0 < p.w := by omega
  have e : p.w * (k / p.w) + k % p.w = k := Nat.div_add_mod k p.w
  have hq : p.h ≤ k / p.w := (Nat.le_div_iff_mul_le hw0).mpr (by
    have : p.K = p.w * p.h := rfl
    rw [Nat.mul_comm]; omega)
  rw [← e, spread_eq_sp p hh hw, sp_mul_bit p.w hw0 _ (and_hm_lt p hh hw z) p.h z _ _ (Nat.mod_lt _ hw0)]
  have : ¬ k / p.w < p.h := by omega
  simp [this]

theorem updX_hi (L z i : Nat) (hi : p.K3 ≤ i) :
    (updX p L (spread p z) z).testBit i = L.testBit i := by
  have hK2 : p.K2 = 2 * p.K := rfl
  have hK3 : p.K3 = 3 * p.K := rfl
  show (L ^^^ (spread p z ^^^ (((L &&& spread p z) <<< p.K) ^^^
    ((spread p z * (z &&& p.hm)) <<< p.K2)))).testBit i = _
  rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_shiftLeft,
    Nat.testBit_shiftLeft, Nat.testBit_and, spread_big p hh hw z i (by omega),
    spread_big p hh hw z (i - p.K) (by omega), outer_big p hh hw z (i - p.K2) (by omega)]
  simp

theorem upd_c0 (L z i : Nat) (hi : i < p.h) :
    (upd p L (spread p z) z).testBit (p.w*i) = (L.testBit (p.w*i) ^^ z.testBit i) := by
  have hlt := wi_lt p hh hw i hi
  have hK3 : p.K3 = 3 * p.K := rfl
  show (updX p L (spread p z) z + p.cnt <<< p.K3).testBit (p.w*i) = _
  rw [testBit_add_shift _ _ _ _ (by omega), updX_c0 p hh hw L z i hi]

theorem upd_c1 (L z i : Nat) (hi : i < p.h) :
    (upd p L (spread p z) z).testBit (p.K + p.w*i)
      = (L.testBit (p.K + p.w*i) ^^ (L.testBit (p.w*i) && z.testBit i)) := by
  have hlt := wi_lt p hh hw i hi
  have hK3 : p.K3 = 3 * p.K := rfl
  show (updX p L (spread p z) z + p.cnt <<< p.K3).testBit (p.K + p.w*i) = _
  rw [testBit_add_shift _ _ _ _ (by omega), updX_c1 p hh hw L z i hi]

theorem upd_B (L z i j : Nat) (hi : i < p.h) (hj : j < p.h) :
    (upd p L (spread p z) z).testBit (p.K2 + p.w*i + j)
      = (L.testBit (p.K2 + p.w*i + j) ^^ (z.testBit i && z.testBit j)) := by
  have hK2 : p.K2 = 2 * p.K := rfl
  have hK3 : p.K3 = 3 * p.K := rfl
  have h1 := Nat.mul_le_mul_left p.w (show i + 1 ≤ p.h from hi)
  rw [Nat.mul_succ] at h1
  have hK : p.K = p.w * p.h := rfl
  show (updX p L (spread p z) z + p.cnt <<< p.K3).testBit (p.K2 + p.w*i + j) = _
  rw [testBit_add_shift _ _ _ _ (by omega), updX_B p hh hw L z i j hi hj]

theorem cnt_upd (L z : Nat) : cntOf p (upd p L (spread p z) z) = cntOf p L + p.cnt := by
  have hx : (updX p L (spread p z) z) >>> p.K3 = L >>> p.K3 := by
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_shiftRight, Nat.testBit_shiftRight, updX_hi p hh hw L z _ (by omega)]
  show (updX p L (spread p z) z + p.cnt <<< p.K3) >>> p.K3 = L >>> p.K3 + p.cnt
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
    ← Nat.shiftRight_eq_div_pow, hx]

theorem cnt_updS (L s : Nat) : cntOf p (updS p L s) = cntOf p L := by
  have hK3 : p.K3 = 3 * p.K := rfl
  apply Nat.eq_of_testBit_eq
  intro j
  show ((L ^^^ (spread p s <<< p.K)) >>> p.K3).testBit j = (L >>> p.K3).testBit j
  rw [Nat.testBit_shiftRight, Nat.testBit_shiftRight, Nat.testBit_xor, Nat.testBit_shiftLeft,
    spread_big p hh hw s _ (by omega)]
  simp

/-! ### bits of a label after a free shift -/

theorem updS_c0 (L s i : Nat) (hi : i < p.h) :
    (updS p L s).testBit (p.w*i) = L.testBit (p.w*i) := by
  have hlt := wi_lt p hh hw i hi
  show (L ^^^ (spread p s <<< p.K)).testBit (p.w*i) = _
  rw [Nat.testBit_xor, Nat.testBit_shiftLeft]
  have h1 : ¬ (p.w * i ≥ p.K) := by omega
  simp [h1]

theorem updS_c1 (L s i : Nat) (hi : i < p.h) :
    (updS p L s).testBit (p.K + p.w*i) = (L.testBit (p.K + p.w*i) ^^ s.testBit i) := by
  show (L ^^^ (spread p s <<< p.K)).testBit (p.K + p.w*i) = _
  rw [Nat.testBit_xor, Nat.testBit_shiftLeft]
  have h1 : p.K + p.w * i ≥ p.K := by omega
  have h3 : p.K + p.w * i - p.K = p.w * i := by omega
  rw [h3, spread_lo p hh hw s i hi]
  simp [h1]

theorem updS_B (L s i j : Nat) (hj : j < p.h) :
    (updS p L s).testBit (p.K2 + p.w*i + j) = L.testBit (p.K2 + p.w*i + j) := by
  have hK2 : p.K2 = 2 * p.K := rfl
  have e' : p.K + p.w*i + j = p.w*(p.h + i) + j := by
    show p.w * p.h + p.w * i + j = _
    ring
  have hs' : (spread p s).testBit (p.K + p.w*i + j) = false := by
    rw [e']; exact spread_hi p hh hw s _ j (by omega) (by omega)
  show (L ^^^ (spread p s <<< p.K)).testBit (p.K2 + p.w*i + j) = _
  rw [Nat.testBit_xor, Nat.testBit_shiftLeft]
  have h3 : p.K2 + p.w * i + j - p.K = p.K + p.w * i + j := by omega
  rw [h3, hs']
  simp

end

/-! ### the stored form -/

theorem dec_enc (L : Nat) : dec (enc L) = L := by
  show (L <<< 64 + L % 18446744073709551615) >>> 64 = L
  rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.mul_comm, Nat.mul_add_div (by norm_num),
    Nat.div_eq_of_lt, Nat.add_zero]
  exact lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num)

theorem dec_zero : dec 0 = 0 := rfl

end SSC
