import Work.SharedSumChecker.Bits
import Work.GCert.Labels.Def

/-!
# (key: gx-labels) Bits of the packed numbers of the label check

* `dig h P p`       digit `p` (width `h`) of `P`; `dig_bit`;
* `sel_mul_bit`     `(X &&& rep h K) * y` carries `y` in every digit `q < K` with bit `h*q` of `X`;
* `acc_bit`         appending `h` digits below a packed number;
* `rep_of_mul`      the selector computed by one division is `rep h K`.

No `sorry`.
-/

set_option linter.unusedVariables false

namespace GLab
open SSC

/-- digit `p` (width `h`) of `P` -/
def dig (h P p : Nat) : Nat := (P >>> (h * p)) &&& (2 ^ h - 1)

theorem digK_eq (h P p : Nat) : digK h (2 ^ h - 1) P p = dig h P p := rfl

theorem dig_bit (h P p q : Nat) :
    (dig h P p).testBit q = (decide (q < h) && P.testBit (h * p + q)) := by
  unfold dig
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, Bool.and_comm]

theorem dig_lt (h P p : Nat) : dig h P p < 2 ^ h :=
  Nat.lt_of_le_of_lt Nat.and_le_right (Nat.sub_lt (Nat.two_pow_pos h) Nat.one_pos)

private theorem and_rep_succ (h : Nat) (hh : 0 < h) (X R : Nat) :
    X &&& (2 ^ h * R + 1) = 2 ^ h * ((X >>> h) &&& R) + X % 2 := by
  have h1 : (1 : Nat) < 2 ^ h := Nat.one_lt_two_pow (Nat.pos_iff_ne_zero.mp hh)
  have h2 : X % 2 < 2 ^ h := lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) h1
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ h1, Nat.testBit_two_pow_mul_add _ h2]
  by_cases hi : i < h
  · rw [if_pos hi, if_pos hi]
    cases i with
    | zero => simp [Nat.testBit_zero]
    | succ i =>
      have e0 : 2 ≤ 2 ^ (i + 1) := by
        have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (Nat.succ_pos i)
        simpa using this
      have e1 : (1 : Nat).testBit (i + 1) = false := Nat.testBit_lt_two_pow (by omega)
      have e2 : (X % 2).testBit (i + 1) = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) e0)
      rw [e1, e2, Bool.and_false]
  · rw [if_neg hi, if_neg hi, Nat.testBit_and, Nat.testBit_shiftRight]
    have e : h + (i - h) = i := by omega
    rw [e]

/-- `(X &&& rep h K) * y` carries `y` in the digits `q < K` at which `X` has bit `h * q`. -/
theorem sel_mul_bit (h : Nat) (hh : 0 < h) (y : Nat) (hy : y < 2 ^ h) (K X q r : Nat)
    (hr : r < h) :
    ((X &&& rep h K) * y).testBit (h * q + r)
      = (decide (q < K) && X.testBit (h * q) && y.testBit r) := by
  induction K generalizing X q with
  | zero => simp [rep_zero]
  | succ K ih =>
    have hlt : X % 2 * y < 2 ^ h := by
      rcases Nat.mod_two_eq_zero_or_one X with e | e <;> simp [e, hy]
    have e : (X &&& rep h (K + 1)) * y = 2 ^ h * (((X >>> h) &&& rep h K) * y) + X % 2 * y := by
      rw [rep_succ, and_rep_succ h hh]; ring
    rw [e, Nat.testBit_two_pow_mul_add _ hlt]
    cases q with
    | zero =>
      simp only [Nat.mul_zero, Nat.zero_add, hr, ite_true]
      rcases Nat.mod_two_eq_zero_or_one X with e | e <;> simp [e, Nat.testBit_zero]
    | succ q =>
      have h0 : h * (q + 1) = h * q + h := Nat.mul_succ h q
      have h1 : ¬ (h * (q + 1) + r < h) := by omega
      have h2 : h * (q + 1) + r - h = h * q + r := by omega
      rw [if_neg h1, h2, ih (X >>> h) q, Nat.testBit_shiftRight]
      have h3 : h + h * q = h * (q + 1) := by omega
      rw [h3]
      simp

/-- appending the `h` digits of `Pa` below `A`. -/
theorem acc_bit (h A Pa j q : Nat) (hP : Pa < 2 ^ (h * h)) (hq : q < h) :
    (A <<< (h * h) + Pa).testBit (h * j + q)
      = if j < h then Pa.testBit (h * j + q) else A.testBit (h * (j - h) + q) := by
  have e : A <<< (h * h) + Pa = 2 ^ (h * h) * A + Pa := by rw [Nat.shiftLeft_eq, Nat.mul_comm]
  rw [e, Nat.testBit_two_pow_mul_add _ hP]
  by_cases hj : j < h
  · have h1 : h * j + h ≤ h * h := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left h hj
    rw [if_pos hj, if_pos (by omega)]
  · obtain ⟨d, rfl⟩ : ∃ d, j = h + d := ⟨j - h, by omega⟩
    have h1 : h * (h + d) = h * h + h * d := Nat.mul_add h h d
    have h2 : h + d - h = d := by omega
    rw [if_neg hj, if_neg (by omega), h2]
    congr 1
    omega

theorem rep_mul (h K : Nat) : rep h K * (2 ^ h - 1) + 1 = 2 ^ (h * K) := by
  induction K with
  | zero => simp [rep_zero]
  | succ K ih =>
    have h1 : 2 ^ h - 1 + 1 = 2 ^ h := Nat.sub_add_cancel (Nat.two_pow_pos h)
    have e : rep h (K + 1) * (2 ^ h - 1) + 1
        = 2 ^ h * (rep h K * (2 ^ h - 1) + 1) + (2 ^ h - 1 + 1) - 2 ^ h := by
      rw [rep_succ]
      have : (2 ^ h * rep h K + 1) * (2 ^ h - 1) + 1 + 2 ^ h
          = 2 ^ h * (rep h K * (2 ^ h - 1) + 1) + (2 ^ h - 1 + 1) := by ring
      omega
    rw [e, ih, h1, Nat.add_sub_cancel, Nat.mul_succ, pow_add, Nat.mul_comm]

/-- the selector computed by one division is `rep h K`. -/
theorem rep_of_mul (h K O : Nat) (hh : 0 < h) (e : O * (2 ^ h - 1) = 2 ^ (h * K) - 1) :
    O = rep h K := by
  have h1 : 1 < 2 ^ h := Nat.one_lt_two_pow (Nat.pos_iff_ne_zero.mp hh)
  have h2 := rep_mul h K
  have h3 : rep h K * (2 ^ h - 1) = 2 ^ (h * K) - 1 := by omega
  exact Nat.eq_of_mul_eq_mul_right (by omega) (e.trans h3.symm)

end GLab

#print axioms GLab.sel_mul_bit
#print axioms GLab.acc_bit
#print axioms GLab.rep_of_mul
