"""Lean texts of the instance module of the BRIDGED word B_2 (library; used by crate.py): the CONDITIONAL
theorems (from any block certificate with G units), whole-block and per-rank, and the sharpness statements.
crate.py sets VARIANTS (suffix of the Lean names, suffix of the rate module, price, words) and HYP before use.
"""
VARIANTS = None  # set by crate.py


HILLS = '''    (cl : Paint) (m : Bool) {ι : Type U} (k : ι→ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*envelope (1 - %d/(10:ℝ)^%d) (k i))'''


WHT = '    ∃ solve W, WHT.WHTProgram solve W ∧ BlockWHT.WHTTimeBoundsAt (1 - %d/(10:ℝ)^%d) W'


def block_thms(sfx, blk, rate, pr, d, m, W, tag=''):
    """whole-block engine + WHT + sharpness for one variant; `tag` = 'x' for the ten-decimal version"""
    A, Af, B, s = d['A'], d['A_fails'], d['B'], d['s']
    n = sfx + tag
    us = ('_' + n) if n else ''
    hyp = HYP % dict(P='unitPrice' + sfx)
    bx = (', blocks_x' + sfx) if tag else ''
    return f'''
/-- **Whole-block engine at `1 - {A}/10^{B}` from a certificate of `G` units** ({pr}; fill parameter `s = {s}`). -/
theorem hills_of_bcert{us} {hyp}
{HILLS % (A, B)} :=
  engine_program_group_list {m} hα (by norm_num) e he G {W} hG (by norm_num)
    (hσ.trans (by rw [unit_live])) c h
    BlockAccounting.{blk} (fun φ => by rw [hc, unit_cost{sfx}{bx}]) {s} (1 - {A}/(10:ℝ)^{B})
    (by norm_num) (by norm_num) BlockAccounting.fold_{rate} cl m k v

/-- **Walsh-Hadamard transform at `1 - {A}/10^{B}` from a certificate of `G` units** ({pr}). -/
theorem wht_of_bcert{us} {hyp} :
{WHT % (A, B)} :=
  BlockWHT.wht_main_of_engine (1 - {A}/(10:ℝ)^{B}) (by norm_num) (by norm_num)
    (fun k v => hills_of_bcert{us} hα e he G hG hσ c h hc Paint.left false k v)

/-- **Sharpness, whole-block** ({pr}): at exponent `1 - {Af}/10^{B}` EVERY table of `K` copies of `G`
units and `p` idle roles has moment at least its number of live roles, so the moment criterion of the
block engine cannot give that exponent for this unit. -/
theorem table_sharp{us} (K G p : ℕ) :
    (K:ℝ) * ((G:ℝ) * (({W}:ℕ):ℝ)) + (p:ℝ)
      ≤ (K:ℝ) * ((G:ℝ) * BlockAccounting.moment {m} (1 - {Af}/(10:ℝ)^{B}) BlockAccounting.{blk})
        + (p:ℝ) * (BlockAccounting.T {m} (1 - {Af}/(10:ℝ)^{B}) ({m} - 1) 1
          + BlockAccounting.T {m} (1 - {Af}/(10:ℝ)^{B}) 1 1) :=
  table_block_fails {m} {W} (by norm_num) (1 - {Af}/(10:ℝ)^{B}) (by norm_num) _
    BlockAccounting.fold_{rate}_sharp K G p
'''


HYP0 = '''{α ρ σ : Type} [Fintype α] [DecidableEq α] [Fintype ρ]
    [DecidableEq ρ] [Fintype σ] [DecidableEq σ]
    (hα : Fintype.card α = %(m)d) (e : σ → ρ) (he : Function.Injective e)
    (G : ℕ) (hG : 1 ≤ G) (hσ : Fintype.card σ = G * (4 * cert.v + cert.R))
    (c : (ℕ → ℝ) → ℝ) (h : BCert α e c)'''


HYP = None      # HYP0 with the price hypothesis, set in main


def rank_thms(sfx, d, m, W, D, tag=''):
    """per-rank theorems: generic in the price (only its tally is used), then one corollary per variant"""
    Ar, Arf, B, s = d['A_rank'], d['A_rank_fails'], d['B'], d['s']
    t = ('_' + tag) if tag else ''
    rate = d['name']
    o = f'''
/-- **Per-rank engine at `1 - {Ar}/10^{B}` from a certificate of `G` units, for ANY unit price `P`**: only the
tally `P (r ↦ r) = W m - D = {W} * {m} - {D}` of the price is used (fill parameter `s = {s}`). -/
theorem hills_perRank_of_price{t} {HYP0 % dict(m=m)}
    (P : (ℕ → ℝ) → ℝ) (hc : ∀ φ : ℕ → ℝ, c φ = (G:ℝ) * P φ)
    (hP : P (fun r => (r:ℝ)) = (({W}:ℕ):ℝ) * (({m}:ℕ):ℝ) - (({D}:ℕ):ℝ))
{HILLS % (Ar, B)} :=
  engine_program_group_perRank {m} hα (by norm_num) e he G {W} hG (by norm_num)
    (hσ.trans (by rw [unit_live])) c h P hc
    {D} hP {s} (1 - {Ar}/(10:ℝ)^{B}) (by norm_num) BlockAccounting.foldRank_{rate} cl m k v

/-- **Walsh-Hadamard transform, per-rank, at `1 - {Ar}/10^{B}`, for ANY unit price with the tally `W m - D`.** -/
theorem wht_perRank_of_price{t} {HYP0 % dict(m=m)}
    (P : (ℕ → ℝ) → ℝ) (hc : ∀ φ : ℕ → ℝ, c φ = (G:ℝ) * P φ)
    (hP : P (fun r => (r:ℝ)) = (({W}:ℕ):ℝ) * (({m}:ℕ):ℝ) - (({D}:ℕ):ℝ)) :
{WHT % (Ar, B)} :=
  BlockWHT.wht_main_of_engine (1 - {Ar}/(10:ℝ)^{B}) (by norm_num) (by norm_num)
    (fun k v => hills_perRank_of_price{t} hα e he G hG hσ c h P hc hP Paint.left false k v)

/-- **Per-rank from the tally of the certificate alone**: `c (r ↦ r) = G * (W m - D)`; no price formula. -/
theorem wht_perRank_of_tally{t} {HYP0 % dict(m=m)}
    (hT : c (fun r => (r:ℝ)) = (G:ℝ) * ((({W}:ℕ):ℝ) * (({m}:ℕ):ℝ) - (({D}:ℕ):ℝ))) :
{WHT % (Ar, B)} := by
  have hG0 : (G:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  refine wht_perRank_of_price{t} hα e he G hG hσ c h (fun φ => c φ / (G:ℝ)) (fun φ => ?_) ?_
  · field_simp
  · show c (fun r => (r:ℝ)) / (G:ℝ) = _
    rw [hT]
    field_simp
'''
    for sf, _, _, pr in VARIANTS:
        us = ('_' + sf + tag) if (sf + tag) else ''
        hyp = HYP % dict(P='unitPrice' + sf)
        o += f'''
/-- **Walsh-Hadamard transform, per-rank, at `1 - {Ar}/10^{B}`** ({pr}). -/
theorem wht_perRank_of_bcert{us} {hyp} :
{WHT % (Ar, B)} :=
  wht_perRank_of_price{t} hα e he G hG hσ c h unitPrice{sf} hc unit_tally{sf}
'''
    o += f'''
/-- **Sharpness, per-rank**: at exponent `1 - {Arf}/10^{B}` the per-rank inequality `tally / 2^a < m^z`
fails for every table of `K` copies of `G` units and `p` idle roles (`tally = (K G W + p) m - K G D`). -/
theorem table_sharp_perRank{t} (K G p : ℕ) :
    (K:ℝ) * ((G:ℝ) * (({D}:ℕ):ℝ))
      ≤ ((K:ℝ) * ((G:ℝ) * (({W}:ℕ):ℝ)) + (p:ℝ))
        * ((({m}:ℕ):ℝ) - (({m}:ℕ):ℝ)^(1 - {Arf}/(10:ℝ)^{B})) :=
  table_rank_fails {m} {W} {D} (by norm_num) (1 - {Arf}/(10:ℝ)^{B}) (by norm_num)
    BlockAccounting.foldRank_{rate}_sharp K G p
'''
    return o
