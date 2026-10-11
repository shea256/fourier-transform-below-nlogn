import Work.FoldRate.Arith

/-!
# (key: fold-rate) Tools for the per-rank fact and for sharpness

* `rank_fact`        the per-rank hypothesis `2^s W (u - u^(1-ε)) < (2^s - 1) D` of
                     `RAM.engine_program_group_perRank` from a rational upper bound `L` of
                     `log u`:  `u - u^(1-ε) ≤ u ε L`;
* `rank_fact_sharp`  `D ≤ W (u - u^(1-ε))` from a rational LOWER bound `L` of `log u`
                     (`u - u^(1-ε) ≥ u (x - x²/2)`, `x = ε L ≤ 1`): then the per-rank
                     inequality fails for every table made of copies and idle roles;
* `block_fails`      if `W ≤ M` (moment of one unit at least its number of live roles) the
                     moment of ANY table `k` copies of `g` units plus `p` idle roles is at
                     least its number of live roles;
* `rank_fails`       the per-rank companion.

Imports only Mathlib (through `Work.FoldRate.Arith`).  No `sorry`.
-/

namespace OAI
namespace PowerSaving
namespace FoldRate

/-- `u - u^(1-ε) ≤ u ε L` when `log u ≤ L`. -/
lemma sub_rpow_le (u ε L : ℝ) (hu : 0 < u) (hε : 0 ≤ ε) (hL : Real.log u ≤ L) :
    u - u^(1 - ε) ≤ u * (ε * L) := by
  have h1 : u^(1 - ε) = u * Real.exp (-(ε * Real.log u)) := by
    rw [Real.rpow_def_of_pos hu,
      show Real.log u * (1 - ε) = Real.log u + -(ε * Real.log u) by ring,
      Real.exp_add, Real.exp_log hu]
  have h2 : -(ε * Real.log u) + 1 ≤ Real.exp (-(ε * Real.log u)) := Real.add_one_le_exp _
  have h3 : ε * Real.log u ≤ ε * L := mul_le_mul_of_nonneg_left hL hε
  have h4 : u * (-(ε * Real.log u) + 1) ≤ u * Real.exp (-(ε * Real.log u)) :=
    mul_le_mul_of_nonneg_left h2 hu.le
  have h5 : u * (ε * Real.log u) ≤ u * (ε * L) := mul_le_mul_of_nonneg_left h3 hu.le
  rw [h1]
  linarith

/-- **per-rank fact** from a rational upper bound of `log u`. -/
lemma rank_fact (u W D s : ℕ) (ε L : ℝ) (hu : 0 < u) (hε : 0 ≤ ε)
    (hL : Real.log (u:ℝ) ≤ L)
    (hq : (2:ℝ)^s * (W:ℝ) * ((u:ℝ) * (ε * L)) < ((2:ℝ)^s - 1) * (D:ℝ)) :
    (2:ℝ)^s * (W:ℝ) * ((u:ℝ) - (u:ℝ)^(1 - ε)) < ((2:ℝ)^s - 1) * (D:ℝ) := by
  have hu0 : (0:ℝ) < (u:ℝ) := by exact_mod_cast hu
  have h1 := sub_rpow_le (u:ℝ) ε L hu0 hε hL
  have h2 : (0:ℝ) ≤ (2:ℝ)^s * (W:ℝ) := by positivity
  have h3 := mul_le_mul_of_nonneg_left h1 h2
  linarith

/-- `exp (-y) ≥ 1 - y + y²/2 - y³/4` on `[0,1]`. -/
lemma exp_neg_ge (y : ℝ) (h0 : 0 ≤ y) (h1 : y ≤ 1) :
    1 - y + y^2/2 - y^3/4 ≤ Real.exp (-y) := by
  have hE : Real.exp y ≤ 1 + y + y^2/2 + y^3*(2/9) := BlockAccounting.exp_le_cubic y h0 h1
  have h6 : Real.exp (-y) * Real.exp y = 1 := by
    rw [← Real.exp_add]
    simp
  by_cases hq : 0 ≤ 1 - y + y^2/2 - y^3/4
  · have hexp : (1 - y + y^2/2 - y^3/4) * (1 + y + y^2/2 + y^3*(2/9))
        = 1 - y^3 * (1/36 + (2/9)*y + y^2/72 + y^3/18) := by ring
    have hnn : 0 ≤ y^3 * (1/36 + (2/9)*y + y^2/72 + y^3/18) := by positivity
    have hle : (1 - y + y^2/2 - y^3/4) * Real.exp y
        ≤ (1 - y + y^2/2 - y^3/4) * (1 + y + y^2/2 + y^3*(2/9)) :=
      mul_le_mul_of_nonneg_left hE hq
    have hge : (1 - y + y^2/2 - y^3/4) * Real.exp y ≤ Real.exp (-y) * Real.exp y := by
      rw [h6]
      linarith
    exact le_of_mul_le_mul_right hge (Real.exp_pos _)
  · have hneg : 1 - y + y^2/2 - y^3/4 < 0 := lt_of_not_ge hq
    exact (hneg.trans (Real.exp_pos _)).le

/-- `u - u^(1-ε) ≤ u (x - x²/2 + x³/4)` with `x = ε L ≤ 1`, when `log u ≤ L`. -/
lemma sub_rpow_le3 (u ε L : ℝ) (hu : 0 < u) (hε : 0 ≤ ε) (hL0 : 0 ≤ L)
    (hL : Real.log u ≤ L) (hx1 : ε * L ≤ 1) :
    u - u^(1 - ε) ≤ u * (ε * L - (ε * L)^2 / 2 + (ε * L)^3 / 4) := by
  have h1 : u^(1 - ε) = u * Real.exp (-(ε * Real.log u)) := by
    rw [Real.rpow_def_of_pos hu,
      show Real.log u * (1 - ε) = Real.log u + -(ε * Real.log u) by ring,
      Real.exp_add, Real.exp_log hu]
  have h3 : ε * Real.log u ≤ ε * L := mul_le_mul_of_nonneg_left hL hε
  have h4 : Real.exp (-(ε * L)) ≤ Real.exp (-(ε * Real.log u)) :=
    Real.exp_le_exp.mpr (by linarith)
  have h5 := exp_neg_ge (ε * L) (mul_nonneg hε hL0) hx1
  have h6 : u * (1 - ε * L + (ε * L)^2 / 2 - (ε * L)^3 / 4)
      ≤ u * Real.exp (-(ε * Real.log u)) :=
    mul_le_mul_of_nonneg_left (h5.trans h4) hu.le
  rw [h1]
  linarith

/-- **per-rank fact, third order** from a rational upper bound of `log u`. -/
lemma rank_fact3 (u W D s : ℕ) (ε L : ℝ) (hu : 0 < u) (hε : 0 ≤ ε) (hL0 : 0 ≤ L)
    (hL : Real.log (u:ℝ) ≤ L) (hx1 : ε * L ≤ 1)
    (hq : (2:ℝ)^s * (W:ℝ) * ((u:ℝ) * (ε * L - (ε * L)^2 / 2 + (ε * L)^3 / 4))
      < ((2:ℝ)^s - 1) * (D:ℝ)) :
    (2:ℝ)^s * (W:ℝ) * ((u:ℝ) - (u:ℝ)^(1 - ε)) < ((2:ℝ)^s - 1) * (D:ℝ) := by
  have hu0 : (0:ℝ) < (u:ℝ) := by exact_mod_cast hu
  have h1 := sub_rpow_le3 (u:ℝ) ε L hu0 hε hL0 hL hx1
  have h2 : (0:ℝ) ≤ (2:ℝ)^s * (W:ℝ) := by positivity
  have h3 := mul_le_mul_of_nonneg_left h1 h2
  linarith

/-- `u (x - x²/2) ≤ u - u^(1-ε)` with `x = ε L`, when `0 ≤ L ≤ log u` and `ε L ≤ 1`. -/
lemma le_sub_rpow (u ε L : ℝ) (hu : 0 < u) (hε : 0 ≤ ε) (hL0 : 0 ≤ L) (hL : L ≤ Real.log u)
    (hx1 : ε * L ≤ 1) :
    u * (ε * L - (ε * L)^2 / 2) ≤ u - u^(1 - ε) := by
  have h1 : u^(1 - ε) = u * Real.exp (-(ε * Real.log u)) := by
    rw [Real.rpow_def_of_pos hu,
      show Real.log u * (1 - ε) = Real.log u + -(ε * Real.log u) by ring,
      Real.exp_add, Real.exp_log hu]
  have hx0 : 0 ≤ ε * L := mul_nonneg hε hL0
  have h3 : ε * L ≤ ε * Real.log u := mul_le_mul_of_nonneg_left hL hε
  have h4 : Real.exp (-(ε * Real.log u)) ≤ Real.exp (-(ε * L)) :=
    Real.exp_le_exp.mpr (by linarith)
  -- exp (-x) ≤ 1 - x + x²/2 for 0 ≤ x ≤ 1, from exp x ≥ 1 + x + x²/2
  have h5 : 1 + ε * L + (ε * L)^2 / 2 ≤ Real.exp (ε * L) := by
    have h := Real.sum_le_exp_of_nonneg hx0 3
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith
  have h6 : Real.exp (-(ε * L)) * Real.exp (ε * L) = 1 := by
    rw [← Real.exp_add]
    simp
  have h7 : Real.exp (-(ε * L)) ≤ 1 - ε * L + (ε * L)^2 / 2 := by
    have hpos : 0 < Real.exp (-(ε * L)) := Real.exp_pos _
    have hq : 0 ≤ 1 - ε * L + (ε * L)^2 / 2 := by nlinarith
    -- (1 - x + x²/2)(1 + x + x²/2) = 1 + x⁴/4 ≥ 1
    have hprod : 1 ≤ (1 - ε * L + (ε * L)^2 / 2) * (1 + ε * L + (ε * L)^2 / 2) := by
      have : (1 - ε * L + (ε * L)^2 / 2) * (1 + ε * L + (ε * L)^2 / 2)
          = 1 + (ε * L)^4 / 4 := by ring
      rw [this]
      have : 0 ≤ (ε * L)^4 / 4 := by positivity
      linarith
    have hle : (1 - ε * L + (ε * L)^2 / 2) * (1 + ε * L + (ε * L)^2 / 2)
        ≤ (1 - ε * L + (ε * L)^2 / 2) * Real.exp (ε * L) :=
      mul_le_mul_of_nonneg_left h5 hq
    have hge : Real.exp (-(ε * L)) * Real.exp (ε * L)
        ≤ (1 - ε * L + (ε * L)^2 / 2) * Real.exp (ε * L) := by
      rw [h6]
      linarith
    exact le_of_mul_le_mul_right hge (Real.exp_pos _)
  have h8 : u * Real.exp (-(ε * Real.log u)) ≤ u * (1 - ε * L + (ε * L)^2 / 2) :=
    mul_le_mul_of_nonneg_left (h4.trans h7) hu.le
  rw [h1]
  linarith

/-- **per-rank sharpness** from a rational lower bound of `log u`. -/
lemma rank_fact_sharp (u W D : ℕ) (ε L : ℝ) (hu : 0 < u) (hε : 0 ≤ ε) (hL0 : 0 ≤ L)
    (hL : L ≤ Real.log (u:ℝ)) (hx1 : ε * L ≤ 1)
    (hq : (D:ℝ) ≤ (W:ℝ) * ((u:ℝ) * (ε * L - (ε * L)^2 / 2))) :
    (D:ℝ) ≤ (W:ℝ) * ((u:ℝ) - (u:ℝ)^(1 - ε)) := by
  have hu0 : (0:ℝ) < (u:ℝ) := by exact_mod_cast hu
  have h1 := le_sub_rpow (u:ℝ) ε L hu0 hε hL0 hL hx1
  have h2 : (0:ℝ) ≤ (W:ℝ) := Nat.cast_nonneg W
  have h3 := mul_le_mul_of_nonneg_left h1 h2
  linarith

/-- **whole-block: no table helps.**  If the moment `M` of one unit is at least its number
`w` of live roles, any table of `k` copies of `g` units and `p` idle roles (price `c ≥ 1`
each) has moment at least its number of live roles. -/
lemma block_fails (k g w p M c : ℝ) (hk : 0 ≤ k) (hg : 0 ≤ g) (hp : 0 ≤ p) (hc : 1 ≤ c)
    (hM : w ≤ M) : k * (g * w) + p ≤ k * (g * M) + p * c := by
  have h1 : k * (g * w) ≤ k * (g * M) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hM hg) hk
  have h2 : p * 1 ≤ p * c := mul_le_mul_of_nonneg_left hc hp
  linarith

/-- **per-rank: no table helps.**  If `D ≤ w X` (`X = m - m^z`, `D` the deficit of one
unit), then `k g D ≤ (k g w + p) X` for every table: the per-rank inequality fails. -/
lemma rank_fails (k g w p X D : ℝ) (hk : 0 ≤ k) (hg : 0 ≤ g) (hp : 0 ≤ p) (hX : 0 ≤ X)
    (hD : D ≤ w * X) : k * (g * D) ≤ (k * (g * w) + p) * X := by
  have h1 : k * (g * D) ≤ k * (g * (w * X)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hD hg) hk
  have h2 : 0 ≤ p * X := mul_nonneg hp hX
  linarith

end FoldRate
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.FoldRate.rank_fact
#print axioms OAI.PowerSaving.FoldRate.rank_fact_sharp
#print axioms OAI.PowerSaving.FoldRate.block_fails
#print axioms OAI.PowerSaving.FoldRate.rank_fails
