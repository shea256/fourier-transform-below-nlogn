import Work.SharedSumChecker.Bits

/-!
# Shared-sum checker: the phase of a packed label

`Phi p L y` is the phase that the frame with label `L` applies at the Walsh address whose
pull-back to `F_2^h` is `y`.  A kernel move along `z` multiplies it by `tint (z·y)`, a shift by
`sign (z·y)`; these are exactly the label updates `upd`, `updS` of the checker.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace SSC
open OAI.PowerSaving.Binary Finset

/-- `x` if the bit is set, else `1` -/
noncomputable def bp : Bool → ℂ → ℂ
  | true, x => x
  | false, _ => 1

theorem bp_true (x : ℂ) : bp true x = x := rfl
theorem bp_false (x : ℂ) : bp false x = 1 := rfl

/-- the vector of `F_2^h` with bit mask `z` -/
def vec (z : Nat) : Nat → F := fun i => if z.testBit i then 1 else 0

/-- phase of the label `L` at `y` -/
noncomputable def Phi (p : Par) (L : Nat) (y : Nat → F) : ℂ :=
  ∏ i ∈ range p.h, (bp (L.testBit (p.w*i)) (tint (y i)) * bp (L.testBit (p.K + p.w*i)) (sign (y i)) *
    ∏ j ∈ range i, bp (L.testBit (p.K2 + p.w*j + i)) (sign (y j * y i)))

theorem Phi_zero (p : Par) (y : Nat → F) : Phi p 0 y = 1 := by
  simp [Phi, bp_false]

theorem tint_sum_range (a : Nat → F) (n : Nat) :
    tint (∑ i ∈ range n, a i) = ∏ i ∈ range n, (tint (a i) * ∏ j ∈ range i, sign (a j * a i)) := by
  induction n with
  | zero => simp [tint]
  | succ n ih =>
    rw [sum_range_succ, prod_range_succ, tint_add, ih, sum_mul, OAI.PowerSaving.Binary.sign_sum]
    ring

theorem bp_step (c0 c1 zi : Bool) (T S : ℂ) (hT : T * T = S) (hS : S * S = 1) :
    bp (c0 ^^ zi) T * bp (c1 ^^ (c0 && zi)) S = bp c0 T * bp c1 S * bp zi T := by
  subst hT
  cases c0 <;> cases c1 <;> cases zi <;>
    simp only [bp_true, bp_false, Bool.xor_true, Bool.xor_false, Bool.true_xor, Bool.false_xor,
      Bool.and_true, Bool.and_false, Bool.true_and, Bool.false_and, Bool.not_true, Bool.not_false] <;>
    first | ring1 | linear_combination -hS | linear_combination hS

theorem bp_xor (b c : Bool) (s : ℂ) (hs : s * s = 1) : bp (b ^^ c) s = bp b s * bp c s := by
  cases b <;> cases c <;>
    simp only [bp_true, bp_false, Bool.xor_true, Bool.xor_false, Bool.true_xor, Bool.false_xor,
      Bool.not_true, Bool.not_false] <;>
    first | ring1 | linear_combination -hs | linear_combination hs

theorem tint_vec (z i : Nat) (y : Nat → F) : tint (vec z i * y i) = bp (z.testBit i) (tint (y i)) := by
  unfold vec
  cases z.testBit i <;> simp [bp_true, bp_false, tint]

theorem sign_vec (z i : Nat) (y : Nat → F) : sign (vec z i * y i) = bp (z.testBit i) (sign (y i)) := by
  unfold vec
  cases z.testBit i <;> simp [bp_true, bp_false, sign]

theorem sign_vec2 (z j i : Nat) (y : Nat → F) :
    sign (vec z j * y j * (vec z i * y i)) = bp (z.testBit j && z.testBit i) (sign (y j * y i)) := by
  unfold vec
  cases z.testBit j <;> cases z.testBit i <;> simp [bp_true, bp_false, sign]

section
variable (p : Par) (hh : 0 < p.h) (hw : p.h < p.w)
include hh hw

/-- **A kernel move along `z` multiplies the phase by `tint (z·y)`.** -/
theorem Phi_upd (L z : Nat) (y : Nat → F) :
    Phi p (upd p L (spread p z) z) y = Phi p L y * tint (∑ i ∈ range p.h, vec z i * y i) := by
  rw [tint_sum_range]
  unfold Phi
  rw [← prod_mul_distrib]
  apply prod_congr rfl
  intro i hi
  have hi' : i < p.h := mem_range.mp hi
  have hB : ∏ j ∈ range i, bp ((upd p L (spread p z) z).testBit (p.K2 + p.w*j + i)) (sign (y j * y i))
      = (∏ j ∈ range i, bp (L.testBit (p.K2 + p.w*j + i)) (sign (y j * y i))) *
        ∏ j ∈ range i, sign (vec z j * y j * (vec z i * y i)) := by
    rw [← prod_mul_distrib]
    apply prod_congr rfl
    intro j hj
    have hj' : j < p.h := lt_trans (mem_range.mp hj) hi'
    rw [upd_B p hh hw L z j i hj' hi', bp_xor _ _ _ (sign_sq _), sign_vec2]
  rw [hB, upd_c0 p hh hw L z i hi', upd_c1 p hh hw L z i hi',
    bp_step _ _ _ _ _ (tint_sq (y i)) (sign_sq (y i)), tint_vec]
  ring

/-- **A shift along `s` multiplies the phase by `sign (s·y)`.** -/
theorem Phi_updS (L s : Nat) (y : Nat → F) :
    Phi p (updS p L s) y = Phi p L y * sign (∑ i ∈ range p.h, vec s i * y i) := by
  rw [OAI.PowerSaving.Binary.sign_sum]
  unfold Phi
  rw [← prod_mul_distrib]
  apply prod_congr rfl
  intro i hi
  have hi' : i < p.h := mem_range.mp hi
  have hB : ∏ j ∈ range i, bp ((updS p L s).testBit (p.K2 + p.w*j + i)) (sign (y j * y i))
      = ∏ j ∈ range i, bp (L.testBit (p.K2 + p.w*j + i)) (sign (y j * y i)) := by
    apply prod_congr rfl
    intro j hj
    rw [updS_B p hh hw L s j i hi']
  rw [hB, updS_c0 p hh hw L s i hi', updS_c1 p hh hw L s i hi', bp_xor _ _ _ (sign_sq _), sign_vec]
  ring

end

end SSC
