import Work.BlockAccounting.Moment
set_option maxRecDepth 4000
namespace OAI.PowerSaving.BlockAccounting
open Finset
/-- 72 copies of PR588 atm3 with source copies, #401 dedicated banks, and an explicit cyclic schedule. -/
def blocksC588x : List (ℕ × ℕ) := [(1, 189360), (2, 35424), (3, 20160), (4, 16704), (5, 4032), (6, 4032), (8, 14088), (16, 3584), (32, 3584), (48, 3584)]

/-- total rank of one unit (= number of unit moves it stands for): `W * m - D` -/
theorem blocksC588x_rank : (blocksC588x.map fun b => b.1 * b.2).sum = 12208 * 73 - 2560 := by
  norm_num [blocksC588x]

/-- the same as a price: the unit list at the price list `r ↦ r` (shape of `hPid` in `RAM.engine_program_group_perRank`) -/
theorem blocksC588x_tally : (blocksC588x.map fun b => (b.2:ℝ) * ((b.1:ℕ):ℝ)).sum = ((12208:ℕ):ℝ) * ((73:ℕ):ℝ) - ((2560:ℕ):ℝ) := by
  norm_num [blocksC588x]

theorem blocksC588x_count : (blocksC588x.map fun b => b.2).sum = 294552 := by
  norm_num [blocksC588x]

theorem blocksC588x_proper : ∀ b ∈ blocksC588x, 1 ≤ b.1 ∧ b.1 < 73 := by
  decide

/-- **whole-block fact** of `blocksC588x` at exponent `1 - 12331686/10^10`, fill parameter `s = 40`: the hypothesis `hnum` of `RAM.engine_program_group_list` (u = 73, W = 12208).  Relative slack of the rational certificate: 5.00e-11. -/
theorem fold_C588x :
    ((2:ℝ)^40 - 1) * moment 73 (1 - 12331686/(10:ℝ)^10) blocksC588x
      + ((12208:ℕ):ℝ) * (T 73 (1 - 12331686/(10:ℝ)^10) (73 - 1) 1 + T 73 (1 - 12331686/(10:ℝ)^10) 1 1)
      < (2:ℝ)^40 * ((12208:ℕ):ℝ) := by
  have hsum : moment 73 (1 - 12331686/(10:ℝ)^10) blocksC588x
      = T 73 (1 - 12331686/(10:ℝ)^10) 1 189360 + (T 73 (1 - 12331686/(10:ℝ)^10) 2 35424 + (T 73 (1 - 12331686/(10:ℝ)^10) 3 20160 + (T 73 (1 - 12331686/(10:ℝ)^10) 4 16704 + (T 73 (1 - 12331686/(10:ℝ)^10) 5 4032 + (T 73 (1 - 12331686/(10:ℝ)^10) 6 4032 + (T 73 (1 - 12331686/(10:ℝ)^10) 8 14088 + (T 73 (1 - 12331686/(10:ℝ)^10) 16 3584 + (T 73 (1 - 12331686/(10:ℝ)^10) 32 3584 + (T 73 (1 - 12331686/(10:ℝ)^10) 48 3584 + 0))))))))) := rfl
  have b0 : T 73 (1 - 12331686/(10:ℝ)^10) 1 189360 ≤ ((1303866670219:ℝ)/500000000) :=
    term_le 73 1 189360 (12331686/(10:ℝ)^10) ((85809188823:ℝ)/20000000000) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_of_le_expsum _ _ 26 (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
      (by norm_num) (by norm_num)
  have b1 : T 73 (1 - 12331686/(10:ℝ)^10) 2 35424 ≤ ((974835435117:ℝ)/1000000000) :=
    term_le 73 2 35424 (12331686/(10:ℝ)^10) ((359731226059:ℝ)/100000000000) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_of_le_expsum _ _ 24 (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
      (by norm_num) (by norm_num)
  have b2 : T 73 (1 - 12331686/(10:ℝ)^10) 3 20160 ≤ ((83176059977:ℝ)/100000000) :=
    term_le 73 3 20160 (12331686/(10:ℝ)^10) ((1595923576241:ℝ)/500000000000) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_of_le_expsum _ _ 23 (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
      (by norm_num) (by norm_num)
  have b3 : T 73 (1 - 12331686/(10:ℝ)^10) 4 16704 ≤ ((183714298611:ℝ)/200000000) :=
    term_le 73 4 16704 (12331686/(10:ℝ)^10) ((290416508003:ℝ)/100000000000) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_of_le_expsum _ _ 22 (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
      (by norm_num) (by norm_num)
  have b4 : T 73 (1 - 12331686/(10:ℝ)^10) 5 4032 ≤ ((55415787283:ℝ)/200000000) :=
    term_le 73 5 4032 (12331686/(10:ℝ)^10) ((670255382179:ℝ)/250000000000) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_of_le_expsum _ _ 21 (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
      (by norm_num) (by norm_num)
  have b5 : T 73 (1 - 12331686/(10:ℝ)^10) 6 4032 ≤ ((83104994029:ℝ)/250000000) :=
    term_le 73 6 4032 (12331686/(10:ℝ)^10) ((1249349985961:ℝ)/500000000000) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_of_le_expsum _ _ 21 (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
      (by norm_num) (by norm_num)
  have b6 : T 73 (1 - 12331686/(10:ℝ)^10) 8 14088 ≤ ((1548105663161:ℝ)/1000000000) :=
    term_le 73 8 14088 (12331686/(10:ℝ)^10) ((221101789947:ℝ)/100000000000) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_of_le_expsum _ _ 20 (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
      (by norm_num) (by norm_num)
  have b7 : T 73 (1 - 12331686/(10:ℝ)^10) 16 3584 ≤ ((787005979367:ℝ)/1000000000) :=
    term_le 73 16 3584 (12331686/(10:ℝ)^10) ((151787071891:ℝ)/100000000000) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_of_le_expsum _ _ 17 (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
      (by norm_num) (by norm_num)
  have b8 : T 73 (1 - 12331686/(10:ℝ)^10) 32 3584 ≤ ((786333559543:ℝ)/500000000) :=
    term_le 73 32 3584 (12331686/(10:ℝ)^10) ((16494470767:ℝ)/20000000000) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_of_le_expsum _ _ 14 (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
      (by norm_num) (by norm_num)
  have b9 : T 73 (1 - 12331686/(10:ℝ)^10) 48 3584 ≤ ((2357821456869:ℝ)/1000000000) :=
    term_le 73 48 3584 (12331686/(10:ℝ)^10) ((209629215121:ℝ)/500000000000) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_of_le_expsum _ _ 11 (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
      (by norm_num) (by norm_num)
  have b10 : T 73 (1 - 12331686/(10:ℝ)^10) 72 1 ≤ ((986318147:ℝ)/1000000000) :=
    term_le 73 72 1 (12331686/(10:ℝ)^10) ((6896661067:ℝ)/500000000000) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_of_le_expsum _ _ 6 (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
      (by norm_num) (by norm_num)
  have b11 : T 73 (1 - 12331686/(10:ℝ)^10) 1 1 ≤ ((137713:ℝ)/10000000) :=
    term_le 73 1 1 (12331686/(10:ℝ)^10) ((85809188823:ℝ)/20000000000) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (log_le_of_le_expsum _ _ 26 (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ, Nat.factorial]))
      (by norm_num) (by norm_num)
  have e1 : ((2:ℝ)^40 - 1) = 1099511627775 := by norm_num
  have e2 : (2:ℝ)^40 = 1099511627776 := by norm_num
  have e3 : ((12208:ℕ):ℝ) = 12208 := by norm_num
  have e4 : T 73 (1 - 12331686/(10:ℝ)^10) (73 - 1) 1 = T 73 (1 - 12331686/(10:ℝ)^10) 72 1 := rfl
  rw [e1, e2, e3, e4, hsum]
  linarith

end OAI.PowerSaving.BlockAccounting
#print axioms OAI.PowerSaving.BlockAccounting.fold_C588x
