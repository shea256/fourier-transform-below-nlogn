import Work.BlockAccounting.Moment

/-!
# (key: fold-rate) Table arithmetic for a certificate made of `G` equal units, `G` opaque

A folded network has `G * W` live roles, where `W` is the number of live roles of one UNIT and
`G` is the size of a group that Lean must never evaluate.  The table is chosen symbolically:

* `tableExp n s = clog2 n + s`        the exponent `a` of the table (`n = G * W`);
* `copiesN n s  = 2^a / n`            the number of copies of the certificate;
* `padN n s     = 2^a % n`            the number of idle roles.

Facts: `copiesN * n + padN = 2^a` (`table_split`), `padN < n` (`pad_lt`), `2^s ≤ copiesN`
(`copies_ge`).  So the idle roles are fewer than `2^(a-s)`: the fill is at least `1 - 2^-s`.

Two pure inequalities over `ℝ` turn ONE numeric fact about one unit into the hypothesis of the
engine for the whole table:

* `block_arith`   whole-block:  `(t-1) M + W c < t W`  gives  `K G M + pad c < K G W + pad`
                  (`t = 2^s ≤ K`, `pad ≤ G W`, `c ≥ 1` the price of an idle role);
* `rank_arith`    per-rank:     `t W X < (t-1) D`     gives  `(K G W + pad) X < K G D`
                  (`X = m - m^z`, `D` the deficit of one unit).

`spare_ge_one`: an idle role costs at least one full role when `z ≤ 1`.
Imports only Mathlib (through `Work.BlockAccounting.Moment`).  No `sorry`.
-/

namespace OAI
namespace PowerSaving
namespace FoldRate

/-- exponent of the table for `n` live roles of the certificate and fill parameter `s` -/
def tableExp (n s : ℕ) : ℕ := Nat.clog 2 n + s

/-- number of copies of the certificate in the table -/
def copiesN (n s : ℕ) : ℕ := 2^(tableExp n s) / n

/-- number of idle roles in the table -/
def padN (n s : ℕ) : ℕ := 2^(tableExp n s) % n

lemma table_split (n s : ℕ) : copiesN n s * n + padN n s = 2^(tableExp n s) := by
  unfold copiesN padN
  rw [Nat.mul_comm]
  exact Nat.div_add_mod _ _

lemma pad_lt (n s : ℕ) (hn : 0 < n) : padN n s < n := Nat.mod_lt _ hn

lemma copies_ge (n s : ℕ) (hn : 0 < n) : 2^s ≤ copiesN n s := by
  unfold copiesN tableExp
  rw [Nat.le_div_iff_mul_le hn]
  calc 2^s * n ≤ 2^s * 2^(Nat.clog 2 n) :=
        Nat.mul_le_mul_left _ (Nat.le_pow_clog (by norm_num) n)
    _ = 2^(Nat.clog 2 n + s) := by ring

/-- **whole-block arithmetic.**  `k` copies of `g` units of `w` live roles and moment `M`
each, plus `p ≤ g w` idle roles of price `c ≥ 1`, in a table of `k g w + p` live roles. -/
lemma block_arith (k g w p t M c : ℝ) (ht : 1 ≤ t) (hk : t ≤ k) (hg : 0 < g) (hw : 0 ≤ w)
    (hp : p ≤ g * w) (hc : 1 ≤ c) (hnum : (t - 1) * M + w * c < t * w) :
    k * (g * M) + p * c < k * (g * w) + p := by
  have hd1 : w * (c - 1) < (t - 1) * (w - M) := by linarith
  have hd0 : 0 ≤ w * (c - 1) := mul_nonneg hw (by linarith)
  have hd : 0 < w - M := by
    by_contra hneg
    have h0 : (t - 1) * (w - M) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    linarith
  have h1 : p * (c - 1) ≤ g * w * (c - 1) := mul_le_mul_of_nonneg_right hp (by linarith)
  have h2 : g * (w * (c - 1)) < g * ((t - 1) * (w - M)) := mul_lt_mul_of_pos_left hd1 hg
  have h3 : g * ((t - 1) * (w - M)) ≤ g * (k * (w - M)) := by
    apply mul_le_mul_of_nonneg_left _ hg.le
    apply mul_le_mul_of_nonneg_right _ hd.le
    linarith
  linarith

/-- **per-rank arithmetic.**  `X` is `m - m^z`, `D` the deficit of one unit. -/
lemma rank_arith (k g w p t X D : ℝ) (ht : 1 ≤ t) (hk : t ≤ k) (hg : 0 < g)
    (hp : p ≤ g * w) (hD : 0 ≤ D) (hpos : 0 < k * (g * w) + p)
    (hnum : t * w * X < (t - 1) * D) :
    (k * (g * w) + p) * X < k * (g * D) := by
  have hk0 : 0 < k := by linarith
  by_cases hX : 0 ≤ X
  · have ha : t * (p * X) ≤ t * ((g * w) * X) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      exact mul_le_mul_of_nonneg_right hp hX
    have hb : g * (t * w * X) < g * ((t - 1) * D) := mul_lt_mul_of_pos_left hnum hg
    have hc : k * g * (t * w * X) < k * g * ((t - 1) * D) :=
      mul_lt_mul_of_pos_left hnum (mul_pos hk0 hg)
    have hd : g * D * ((k + 1) * (t - 1)) ≤ g * D * (t * k) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hg.le hD)
      have he : (k + 1) * (t - 1) = t * k - (k - (t - 1)) := by ring
      rw [he]
      linarith
    have hfin : t * ((k * (g * w) + p) * X) < t * (k * (g * D)) := by linarith
    exact lt_of_mul_lt_mul_left hfin (by linarith)
  · have hX' : X < 0 := lt_of_not_ge hX
    have h1 : (k * (g * w) + p) * X < 0 := mul_neg_of_pos_of_neg hpos hX'
    have h2 : 0 ≤ k * (g * D) := mul_nonneg hk0.le (mul_nonneg hg.le hD)
    linarith

/-- An idle role, cut into blocks of ranks `u-1` and `1`, costs at least one full role when
the exponent is at most 1. -/
lemma spare_ge_one (u : ℕ) (hu : 2 ≤ u) (z : ℝ) (hz1 : z ≤ 1) :
    1 ≤ (((u - 1 : ℕ):ℝ)/(u:ℝ))^z + (((1:ℕ):ℝ)/(u:ℝ))^z := by
  have hu0 : (0:ℝ) < (u:ℝ) := by exact_mod_cast (show 0 < u by omega)
  have hc1 : ((u - 1 : ℕ):ℝ) = (u:ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  have hx : ∀ x : ℝ, 0 < x → x ≤ 1 → x ≤ x^z := by
    intro x h0 h1
    have h := Real.rpow_le_rpow_of_exponent_ge h0 h1 hz1
    rwa [Real.rpow_one] at h
  have ha0 : (0:ℝ) < ((u - 1 : ℕ):ℝ)/(u:ℝ) := by
    apply div_pos _ hu0
    exact_mod_cast (show 0 < u - 1 by omega)
  have ha1 : ((u - 1 : ℕ):ℝ)/(u:ℝ) ≤ 1 := by
    rw [div_le_one hu0, hc1]
    linarith
  have hb0 : (0:ℝ) < ((1:ℕ):ℝ)/(u:ℝ) := by
    apply div_pos _ hu0
    norm_num
  have hb1 : ((1:ℕ):ℝ)/(u:ℝ) ≤ 1 := by
    rw [div_le_one hu0]
    exact_mod_cast (show 1 ≤ u by omega)
  have hsum : ((u - 1 : ℕ):ℝ)/(u:ℝ) + ((1:ℕ):ℝ)/(u:ℝ) = 1 := by
    rw [hc1, ← add_div]
    simp only [Nat.cast_one, sub_add_cancel]
    exact div_self hu0.ne'
  have h1 := hx _ ha0 ha1
  have h2 := hx _ hb0 hb1
  linarith

end FoldRate
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.FoldRate.table_split
#print axioms OAI.PowerSaving.FoldRate.copies_ge
#print axioms OAI.PowerSaving.FoldRate.block_arith
#print axioms OAI.PowerSaving.FoldRate.rank_arith
#print axioms OAI.PowerSaving.FoldRate.spare_ge_one
