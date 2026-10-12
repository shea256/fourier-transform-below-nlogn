import Work.GFrame.Engine.Cert
import Work.GFrame.Engine.Main
import Work.FoldRate.Group

/-!
# GFrame engine, part 11: the engine fed with a generalised certificate of `G` equal units
(agent key: eng-ram)

Analogue of `Work/FoldRate/Group.lean` with `BCert` replaced by `GCert`.  The table
(`a = clog2 (G * W) + s`, `K = 2^a / (G * W)` copies, idle roles cut `(m-1) + 1`), the
arithmetic (`block_arith`) and the ONE numeric hypothesis are those of the block engine,
verbatim.

* `gtable_cert`                    `K` copies and `p` idle roles of a `GCert`;
* `RAM.engine_program_ggroup`      = `engine_program_group` for a `GCert`;
* `RAM.engine_program_ggroup_list` = `engine_program_group_list` for a `GCert`;
* `BlockWHT.wht_main_of_ggroup`, `_list`   the Walsh-Hadamard corollaries.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving

namespace GF
open RAM Binary Matrix Finset FoldRate
section
variable {α ρ σ : Type} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]

/-- **The table certificate**: `K` copies and `p` idle roles of a generalised certificate with
price `G * P φ`; price `K * (G * P φ) + p * (φ (m-1) + φ 1)`. -/
theorem gtable_cert (e : σ → ρ) (G : ℕ) (c P : (ℕ → ℝ) → ℝ) (h : GCert α e c)
    (hc : ∀ φ, c φ = (G:ℝ) * P φ) (K p : ℕ) (hm : 2 ≤ Fintype.card α) :
    GCert α (tEmb e K p)
      (fun φ => (K:ℝ) * ((G:ℝ) * P φ) + (p:ℝ) * (φ (Fintype.card α - 1) + φ 1)) :=
  (GCert.copies K p hm h).cast (fun φ => by rw [hc])

end
end GF

namespace RAM
open Binary Matrix Ty Finset FoldRate GF
universe U

/-- **Whole-block engine from a generalised certificate of `G` equal units** (`G` opaque).
Same statement and same numeric hypothesis `hnum` as `engine_program_group`. -/
theorem engine_program_ggroup {α ρ σ : Type} [Fintype α] [DecidableEq α] [Fintype ρ]
    [DecidableEq ρ] [Fintype σ] [DecidableEq σ]
    (u : ℕ) (hα : Fintype.card α = u) (hu : 3 ≤ u)
    (e : σ → ρ) (he : Function.Injective e)
    (G W : ℕ) (hG : 1 ≤ G) (hW : 1 ≤ W) (hσ : Fintype.card σ = G * W)
    (c : (ℕ → ℝ) → ℝ) (h : GCert α e c)
    (P : (ℕ → ℝ) → ℝ) (hc : ∀ φ, c φ = (G:ℝ) * P φ)
    (s : ℕ) (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hnum : ((2:ℝ)^s - 1) * P (fun r => ((r:ℝ)/(u:ℝ))^z)
        + (W:ℝ) * ((((u - 1 : ℕ):ℝ)/(u:ℝ))^z + (((1:ℕ):ℝ)/(u:ℝ))^z) < (2:ℝ)^s * (W:ℝ))
    (cl : Paint) (m : Bool) {ι : Type U} (k : ι→ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*envelope z (k i)) := by
  subst hα
  obtain ⟨w, hP, hcost, hw⟩ := gtable_cert e G c P h hc (copiesN (G * W) s) (padN (G * W) s)
    (by omega)
  refine engine_program_g_costR (Fintype.card α) (tableExp (G * W) s) rfl
    (card_tLive (G * W) s hσ) hu _ (tEmb_injective e he _ _) w hw hP z hz ?_ cl m k v
  rw [hcost, two_pow_table]
  have hW0 : (0:ℝ) ≤ (W:ℝ) := Nat.cast_nonneg W
  have hG0 : (0:ℝ) < (G:ℝ) := by exact_mod_cast hG
  exact block_arith _ _ _ _ ((2:ℝ)^s) _ _ (one_le_pow₀ (by norm_num))
    (copies_ge_real G W s hG hW) hG0 hW0 (pad_le_real G W s hG hW)
    (spare_ge_one (Fintype.card α) (by omega) z hz1) hnum

/-- **The same with a block list `U` for one unit**: same statement and same numeric
hypothesis as `engine_program_group_list`. -/
theorem engine_program_ggroup_list {α ρ σ : Type} [Fintype α] [DecidableEq α] [Fintype ρ]
    [DecidableEq ρ] [Fintype σ] [DecidableEq σ]
    (u : ℕ) (hα : Fintype.card α = u) (hu : 3 ≤ u)
    (e : σ → ρ) (he : Function.Injective e)
    (G W : ℕ) (hG : 1 ≤ G) (hW : 1 ≤ W) (hσ : Fintype.card σ = G * W)
    (c : (ℕ → ℝ) → ℝ) (h : GCert α e c)
    (U : List (ℕ × ℕ)) (hc : ∀ φ, c φ = (G:ℝ) * listCost φ U)
    (s : ℕ) (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hnum : ((2:ℝ)^s - 1) * BlockAccounting.moment u z U
        + (W:ℝ) * (BlockAccounting.T u z (u - 1) 1 + BlockAccounting.T u z 1 1)
        < (2:ℝ)^s * (W:ℝ))
    (cl : Paint) (m : Bool) {ι : Type U} (k : ι→ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*envelope z (k i)) := by
  refine engine_program_ggroup u hα hu e he G W hG hW hσ c h (fun φ => listCost φ U) hc
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

end RAM

namespace BlockWHT
open RAM Binary FoldRate GF

/-- **Walsh-Hadamard transform from a generalised certificate of `G` equal units.** -/
theorem wht_main_of_ggroup {α ρ σ : Type} [Fintype α] [DecidableEq α] [Fintype ρ]
    [DecidableEq ρ] [Fintype σ] [DecidableEq σ]
    (u : ℕ) (hα : Fintype.card α = u) (hu : 3 ≤ u)
    (e : σ → ρ) (he : Function.Injective e)
    (G W : ℕ) (hG : 1 ≤ G) (hW : 1 ≤ W) (hσ : Fintype.card σ = G * W)
    (c : (ℕ → ℝ) → ℝ) (h : GCert α e c)
    (P : (ℕ → ℝ) → ℝ) (hc : ∀ φ, c φ = (G:ℝ) * P φ)
    (s : ℕ) (z : ℝ) (hz : 0 ≤ z) (hz1 : z < 1)
    (hnum : ((2:ℝ)^s - 1) * P (fun r => ((r:ℝ)/(u:ℝ))^z)
        + (W:ℝ) * ((((u - 1 : ℕ):ℝ)/(u:ℝ))^z + (((1:ℕ):ℝ)/(u:ℝ))^z) < (2:ℝ)^s * (W:ℝ)) :
    ∃ solve W', WHT.WHTProgram solve W' ∧ WHTTimeBoundsAt z W' :=
  wht_main_of_engine z hz hz1 (fun k v =>
    engine_program_ggroup u hα hu e he G W hG hW hσ c h P hc s z hz hz1.le hnum
      Paint.left false k v)

/-- **The same with a block list for one unit.** -/
theorem wht_main_of_ggroup_list {α ρ σ : Type} [Fintype α] [DecidableEq α] [Fintype ρ]
    [DecidableEq ρ] [Fintype σ] [DecidableEq σ]
    (u : ℕ) (hα : Fintype.card α = u) (hu : 3 ≤ u)
    (e : σ → ρ) (he : Function.Injective e)
    (G W : ℕ) (hG : 1 ≤ G) (hW : 1 ≤ W) (hσ : Fintype.card σ = G * W)
    (c : (ℕ → ℝ) → ℝ) (h : GCert α e c)
    (U : List (ℕ × ℕ)) (hc : ∀ φ, c φ = (G:ℝ) * listCost φ U)
    (s : ℕ) (z : ℝ) (hz : 0 ≤ z) (hz1 : z < 1)
    (hnum : ((2:ℝ)^s - 1) * BlockAccounting.moment u z U
        + (W:ℝ) * (BlockAccounting.T u z (u - 1) 1 + BlockAccounting.T u z 1 1)
        < (2:ℝ)^s * (W:ℝ)) :
    ∃ solve W', WHT.WHTProgram solve W' ∧ WHTTimeBoundsAt z W' :=
  wht_main_of_engine z hz hz1 (fun k v =>
    engine_program_ggroup_list u hα hu e he G W hG hW hσ c h U hc s z hz hz1.le hnum
      Paint.left false k v)

end BlockWHT
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.GF.gtable_cert
#print axioms OAI.PowerSaving.RAM.engine_program_ggroup
#print axioms OAI.PowerSaving.RAM.engine_program_ggroup_list
#print axioms OAI.PowerSaving.BlockWHT.wht_main_of_ggroup
#print axioms OAI.PowerSaving.BlockWHT.wht_main_of_ggroup_list
