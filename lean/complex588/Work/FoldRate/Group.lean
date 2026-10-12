import Work.BlockApply.Copies
import Work.FoldRate.Arith

/-!
# (key: fold-rate) The engine fed with a block certificate made of `G` equal units, `G` opaque

Input: a block scratch certificate `BCert α e c` (`Work.BlockApply.Copies`) with
`card σ = G * W` live roles and price `c φ = G * P φ` for every price list `φ`.  `G ≥ 1` is an
arbitrary natural number that is never evaluated (for the folded word: the size of the group).

Table: `a = clog2 (G * W) + s`, `K = 2^a / (G * W)` copies of the certificate
(`BCert.copies`), `2^a - K G W` idle roles cut `(m-1) + 1`.  All three numbers stay symbolic.

* `RAM.engine_program_group`          whole-block engine, from ONE numeric fact about one unit:
      `(2^s - 1) * P (r ↦ (r/m)^z) + W * (((m-1)/m)^z + (1/m)^z) < 2^s * W`;
* `RAM.engine_program_group_list`     the same with `P φ = listCost φ U` for a block list `U`
      of one unit; the fact reads
      `(2^s - 1) * moment m z U + W * (T m z (m-1) 1 + T m z 1 1) < 2^s * W`;
* `RAM.engine_program_group_perRank`  per-rank engine (`engine_program_scratch` on the flat
      word), from `P (r ↦ r) = W * m - D` and `2^s * W * (m - m^z) < (2^s - 1) * D`;
* `BlockWHT.wht_main_of_group`, `_list`, `_perRank`   the Walsh-Hadamard corollaries.

The conclusions have exactly the shape of upstream `hills_program` (TensorProgram.lean:95) with
envelope `⌈(k+1)^z⌉`.  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving

namespace FoldRate
open RAM Binary Matrix Finset
section
variable {α ρ σ : Type} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]

/-- live roles of the table: `K` copies of the certificate's live roles and `p` idle roles -/
abbrev TLive (σ : Type) (K p : ℕ) : Type := (Fin K × σ) ⊕ Fin p

/-- all roles of the table -/
abbrev TRole (ρ : Type) (K p : ℕ) : Type := (Fin K × ρ) ⊕ Fin p

/-- the live roles inside the roles -/
def tEmb (e : σ → ρ) (K p : ℕ) : TLive σ K p → TRole ρ K p :=
  Sum.map (Prod.map (id : Fin K → Fin K) e) (id : Fin p → Fin p)

lemma tEmb_injective (e : σ → ρ) (he : Function.Injective e) (K p : ℕ) :
    Function.Injective (tEmb e K p) := by
  intro x y hxy
  rcases x with ⟨i, x⟩ | x <;> rcases y with ⟨j, y⟩ | y
  · have h := Sum.inl.inj hxy
    have h1 : i = j := congrArg Prod.fst h
    have h2 : e x = e y := congrArg Prod.snd h
    rw [h1, he h2]
  · exact absurd hxy (by simp [tEmb])
  · exact absurd hxy (by simp [tEmb])
  · have h := Sum.inr.inj hxy
    exact congrArg Sum.inr h

/-- the table has `2^a` live roles -/
lemma card_tLive (n s : ℕ) (hσ : Fintype.card σ = n) :
    Fintype.card (TLive σ (copiesN n s) (padN n s)) = 2^(tableExp n s) := by
  rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, hσ]
  exact table_split n s

/-- `2^a` as a real number, split into copies and idle roles -/
lemma two_pow_table (G W s : ℕ) :
    (2:ℝ)^(tableExp (G * W) s)
      = (copiesN (G * W) s : ℝ) * ((G:ℝ) * (W:ℝ)) + (padN (G * W) s : ℝ) := by
  have h := congrArg (Nat.cast : ℕ → ℝ) (table_split (G * W) s)
  push_cast at h
  linarith

lemma copies_ge_real (G W s : ℕ) (hG : 1 ≤ G) (hW : 1 ≤ W) :
    (2:ℝ)^s ≤ (copiesN (G * W) s : ℝ) := by
  have h := copies_ge (G * W) s (Nat.mul_pos hG hW)
  exact_mod_cast h

lemma pad_le_real (G W s : ℕ) (hG : 1 ≤ G) (hW : 1 ≤ W) :
    (padN (G * W) s : ℝ) ≤ (G:ℝ) * (W:ℝ) := by
  have h := (pad_lt (G * W) s (Nat.mul_pos hG hW)).le
  exact_mod_cast h

/-- **The table certificate**: `K` copies and `p` idle roles of a certificate with price
`G * P φ`; price `K * (G * P φ) + p * (φ (m-1) + φ 1)`. -/
theorem table_bcert (e : σ → ρ) (G : ℕ) (c P : (ℕ → ℝ) → ℝ) (h : BCert α e c)
    (hc : ∀ φ, c φ = (G:ℝ) * P φ) (K p : ℕ) (hm : 2 ≤ Fintype.card α) :
    BCert α (tEmb e K p)
      (fun φ => (K:ℝ) * ((G:ℝ) * P φ) + (p:ℝ) * (φ (Fintype.card α - 1) + φ 1)) :=
  (BCert.copies K p hm h).cast (fun φ => by rw [hc])

end
end FoldRate

namespace RAM
open Binary Matrix Ty Finset FoldRate
universe U

/-- **Whole-block engine from a certificate of `G` equal units** (`G` opaque).  `P φ` is the
price of ONE unit, `W` its number of live roles, `u` the label dimension, `s` the fill
parameter (the table has at least `2^s` copies, so idle roles are below the fraction `2^-s`).
The only numeric hypothesis is `hnum`, a statement about one unit. -/
theorem engine_program_group {α ρ σ : Type} [Fintype α] [DecidableEq α] [Fintype ρ]
    [DecidableEq ρ] [Fintype σ] [DecidableEq σ]
    (u : ℕ) (hα : Fintype.card α = u) (hu : 3 ≤ u)
    (e : σ → ρ) (he : Function.Injective e)
    (G W : ℕ) (hG : 1 ≤ G) (hW : 1 ≤ W) (hσ : Fintype.card σ = G * W)
    (c : (ℕ → ℝ) → ℝ) (h : BCert α e c)
    (P : (ℕ → ℝ) → ℝ) (hc : ∀ φ, c φ = (G:ℝ) * P φ)
    (s : ℕ) (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hnum : ((2:ℝ)^s - 1) * P (fun r => ((r:ℝ)/(u:ℝ))^z)
        + (W:ℝ) * ((((u - 1 : ℕ):ℝ)/(u:ℝ))^z + (((1:ℕ):ℝ)/(u:ℝ))^z) < (2:ℝ)^s * (W:ℝ))
    (cl : Paint) (m : Bool) {ι : Type U} (k : ι→ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*envelope z (k i)) := by
  subst hα
  obtain ⟨w, hP, hcost, hw⟩ := table_bcert e G c P h hc (copiesN (G * W) s) (padN (G * W) s)
    (by omega)
  refine engine_program_block_costR (Fintype.card α) (tableExp (G * W) s) rfl
    (card_tLive (G * W) s hσ) hu _ (tEmb_injective e he _ _) w hw hP z hz ?_ cl m k v
  rw [hcost, two_pow_table]
  have hW0 : (0:ℝ) ≤ (W:ℝ) := Nat.cast_nonneg W
  have hG0 : (0:ℝ) < (G:ℝ) := by exact_mod_cast hG
  exact block_arith _ _ _ _ ((2:ℝ)^s) _ _ (one_le_pow₀ (by norm_num))
    (copies_ge_real G W s hG hW) hG0 hW0 (pad_le_real G W s hG hW)
    (spare_ge_one (Fintype.card α) (by omega) z hz1) hnum

/-- **The same with a block list `U` for one unit**: the price of the certificate is
`G * listCost φ U`, and the numeric fact is a statement about the moment of `U`. -/
theorem engine_program_group_list {α ρ σ : Type} [Fintype α] [DecidableEq α] [Fintype ρ]
    [DecidableEq ρ] [Fintype σ] [DecidableEq σ]
    (u : ℕ) (hα : Fintype.card α = u) (hu : 3 ≤ u)
    (e : σ → ρ) (he : Function.Injective e)
    (G W : ℕ) (hG : 1 ≤ G) (hW : 1 ≤ W) (hσ : Fintype.card σ = G * W)
    (c : (ℕ → ℝ) → ℝ) (h : BCert α e c)
    (U : List (ℕ × ℕ)) (hc : ∀ φ, c φ = (G:ℝ) * listCost φ U)
    (s : ℕ) (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hnum : ((2:ℝ)^s - 1) * BlockAccounting.moment u z U
        + (W:ℝ) * (BlockAccounting.T u z (u - 1) 1 + BlockAccounting.T u z 1 1)
        < (2:ℝ)^s * (W:ℝ))
    (cl : Paint) (m : Bool) {ι : Type U} (k : ι→ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*envelope z (k i)) := by
  refine engine_program_group u hα hu e he G W hG hW hσ c h (fun φ => listCost φ U) hc
    s z hz hz1 ?_ cl m k v
  have h1 : listCost (fun r => ((r:ℝ)/(u:ℝ))^z) U = BlockAccounting.moment u z U := rfl
  have h2 : BlockAccounting.T u z (u - 1) 1 = (((u - 1 : ℕ):ℝ)/(u:ℝ))^z := by
    unfold BlockAccounting.T
    rw [Nat.cast_one, one_mul]
  have h3 : BlockAccounting.T u z 1 1 = (((1:ℕ):ℝ)/(u:ℝ))^z := by
    unfold BlockAccounting.T
    rw [Nat.cast_one, one_mul]
  rw [h2, h3] at hnum
  rw [h1]
  exact hnum

/-- **Per-rank engine from a certificate of `G` equal units** (`G` opaque): the unit-move
word of the table certificate in the engine `engine_program_scratch` (one family of recursive
calls per unit move).  `D` is the deficit of one unit: the unit stands for `W * u - D` unit
moves (`hPid`: the price of the unit for the price list `r ↦ r`). -/
theorem engine_program_group_perRank {α ρ σ : Type} [Fintype α] [DecidableEq α] [Fintype ρ]
    [DecidableEq ρ] [Fintype σ] [DecidableEq σ]
    (u : ℕ) (hα : Fintype.card α = u) (hu : 3 ≤ u)
    (e : σ → ρ) (he : Function.Injective e)
    (G W : ℕ) (hG : 1 ≤ G) (hW : 1 ≤ W) (hσ : Fintype.card σ = G * W)
    (c : (ℕ → ℝ) → ℝ) (h : BCert α e c)
    (P : (ℕ → ℝ) → ℝ) (hc : ∀ φ, c φ = (G:ℝ) * P φ)
    (D : ℕ) (hPid : P (fun r => (r:ℝ)) = (W:ℝ) * (u:ℝ) - (D:ℝ))
    (s : ℕ) (z : ℝ) (hz : 0 ≤ z)
    (hnum : (2:ℝ)^s * (W:ℝ) * ((u:ℝ) - (u:ℝ)^z) < ((2:ℝ)^s - 1) * (D:ℝ))
    (cl : Paint) (m : Bool) {ι : Type U} (k : ι→ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*envelope z (k i)) := by
  subst hα
  obtain ⟨w, hP, hcost, hw⟩ := table_bcert e G c P h hc (copiesN (G * W) s) (padN (G * W) s)
    (by omega)
  refine engine_program_scratch (Fintype.card α) (tableExp (G * W) s) rfl
    (card_tLive (G * W) s hσ) hu _ (tEmb_injective e he _ _) w.flat hw z hz ?_ cl m k v
  have hG0 : (0:ℝ) < (G:ℝ) := by exact_mod_cast hG
  have hc1 : ((Fintype.card α - 1 : ℕ):ℝ) = (Fintype.card α:ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  have ht : (tally w.flat : ℝ)
      = (copiesN (G * W) s : ℝ) * ((G:ℝ) * ((W:ℝ) * (Fintype.card α:ℝ) - (D:ℝ)))
        + (padN (G * W) s : ℝ) * (Fintype.card α:ℝ) := by
    rw [tally_flat]
    have h3 : ((w.cost id : ℕ) : ℝ) = w.costR (fun r => (r:ℝ)) := BWord.cost_cast id w
    have h4 : w.costR (fun r => (r:ℝ))
        = (copiesN (G * W) s : ℝ) * ((G:ℝ) * P (fun r => (r:ℝ)))
          + (padN (G * W) s : ℝ) * (((Fintype.card α - 1 : ℕ):ℝ) + ((1:ℕ):ℝ)) :=
      hcost (fun r => (r:ℝ))
    rw [h3, h4, hPid, hc1]
    simp only [Nat.cast_one, sub_add_cancel]
  have hpos : (0:ℝ) < (2:ℝ)^(tableExp (G * W) s) := by positivity
  rw [div_lt_iff₀ hpos, ht]
  have hA := rank_arith (copiesN (G * W) s : ℝ) (G:ℝ) (W:ℝ) (padN (G * W) s : ℝ) ((2:ℝ)^s)
    ((Fintype.card α:ℝ) - (Fintype.card α:ℝ)^z) (D:ℝ) (one_le_pow₀ (by norm_num))
    (copies_ge_real G W s hG hW) hG0 (pad_le_real G W s hG hW) (Nat.cast_nonneg D)
    (by rw [← two_pow_table]; exact hpos) hnum
  rw [two_pow_table]
  linarith

end RAM

namespace BlockWHT
open RAM Binary FoldRate

/-- **Walsh-Hadamard transform from a certificate of `G` equal units, whole-block.** -/
theorem wht_main_of_group {α ρ σ : Type} [Fintype α] [DecidableEq α] [Fintype ρ]
    [DecidableEq ρ] [Fintype σ] [DecidableEq σ]
    (u : ℕ) (hα : Fintype.card α = u) (hu : 3 ≤ u)
    (e : σ → ρ) (he : Function.Injective e)
    (G W : ℕ) (hG : 1 ≤ G) (hW : 1 ≤ W) (hσ : Fintype.card σ = G * W)
    (c : (ℕ → ℝ) → ℝ) (h : BCert α e c)
    (P : (ℕ → ℝ) → ℝ) (hc : ∀ φ, c φ = (G:ℝ) * P φ)
    (s : ℕ) (z : ℝ) (hz : 0 ≤ z) (hz1 : z < 1)
    (hnum : ((2:ℝ)^s - 1) * P (fun r => ((r:ℝ)/(u:ℝ))^z)
        + (W:ℝ) * ((((u - 1 : ℕ):ℝ)/(u:ℝ))^z + (((1:ℕ):ℝ)/(u:ℝ))^z) < (2:ℝ)^s * (W:ℝ)) :
    ∃ solve W', WHT.WHTProgram solve W' ∧ WHTTimeBoundsAt z W' :=
  wht_main_of_engine z hz hz1 (fun k v =>
    engine_program_group u hα hu e he G W hG hW hσ c h P hc s z hz hz1.le hnum
      Paint.left false k v)

/-- **The same with a block list for one unit.** -/
theorem wht_main_of_group_list {α ρ σ : Type} [Fintype α] [DecidableEq α] [Fintype ρ]
    [DecidableEq ρ] [Fintype σ] [DecidableEq σ]
    (u : ℕ) (hα : Fintype.card α = u) (hu : 3 ≤ u)
    (e : σ → ρ) (he : Function.Injective e)
    (G W : ℕ) (hG : 1 ≤ G) (hW : 1 ≤ W) (hσ : Fintype.card σ = G * W)
    (c : (ℕ → ℝ) → ℝ) (h : BCert α e c)
    (U : List (ℕ × ℕ)) (hc : ∀ φ, c φ = (G:ℝ) * listCost φ U)
    (s : ℕ) (z : ℝ) (hz : 0 ≤ z) (hz1 : z < 1)
    (hnum : ((2:ℝ)^s - 1) * BlockAccounting.moment u z U
        + (W:ℝ) * (BlockAccounting.T u z (u - 1) 1 + BlockAccounting.T u z 1 1)
        < (2:ℝ)^s * (W:ℝ)) :
    ∃ solve W', WHT.WHTProgram solve W' ∧ WHTTimeBoundsAt z W' :=
  wht_main_of_engine z hz hz1 (fun k v =>
    engine_program_group_list u hα hu e he G W hG hW hσ c h U hc s z hz hz1.le hnum
      Paint.left false k v)

/-- **Walsh-Hadamard transform from a certificate of `G` equal units, per-rank.** -/
theorem wht_main_of_group_perRank {α ρ σ : Type} [Fintype α] [DecidableEq α] [Fintype ρ]
    [DecidableEq ρ] [Fintype σ] [DecidableEq σ]
    (u : ℕ) (hα : Fintype.card α = u) (hu : 3 ≤ u)
    (e : σ → ρ) (he : Function.Injective e)
    (G W : ℕ) (hG : 1 ≤ G) (hW : 1 ≤ W) (hσ : Fintype.card σ = G * W)
    (c : (ℕ → ℝ) → ℝ) (h : BCert α e c)
    (P : (ℕ → ℝ) → ℝ) (hc : ∀ φ, c φ = (G:ℝ) * P φ)
    (D : ℕ) (hPid : P (fun r => (r:ℝ)) = (W:ℝ) * (u:ℝ) - (D:ℝ))
    (s : ℕ) (z : ℝ) (hz : 0 ≤ z) (hz1 : z < 1)
    (hnum : (2:ℝ)^s * (W:ℝ) * ((u:ℝ) - (u:ℝ)^z) < ((2:ℝ)^s - 1) * (D:ℝ)) :
    ∃ solve W', WHT.WHTProgram solve W' ∧ WHTTimeBoundsAt z W' :=
  wht_main_of_engine z hz hz1 (fun k v =>
    engine_program_group_perRank u hα hu e he G W hG hW hσ c h P hc D hPid s z hz hnum
      Paint.left false k v)

end BlockWHT

end PowerSaving
end OAI

#print axioms OAI.PowerSaving.FoldRate.table_bcert
#print axioms OAI.PowerSaving.RAM.engine_program_group
#print axioms OAI.PowerSaving.RAM.engine_program_group_list
#print axioms OAI.PowerSaving.RAM.engine_program_group_perRank
#print axioms OAI.PowerSaving.BlockWHT.wht_main_of_group
#print axioms OAI.PowerSaving.BlockWHT.wht_main_of_group_list
#print axioms OAI.PowerSaving.BlockWHT.wht_main_of_group_perRank
