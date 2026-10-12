import Work.GFrame.Engine.Recursion

/-!
# GFrame engine, part 6: the engine theorems for generalised words (agent key: eng-ram)

Same conclusions and the SAME numeric hypotheses as `engine_all_block`, `engine_program_block`
(`Work/Block/Engine.lean`) and `engine_program_block_costR` (`Work/Block/Bridge.lean`); the
certificate is `GLiveKernel e w` for a `GWord` (old letters, free address permutations, free
diagonal phases) instead of `LiveKernel e w.flat` for a `BWord`.

* `engine_all_g`, `engine_program_g`   moment of an upper bound `H` of the rank histogram;
* `engine_program_g_costR`             moment given as the additive cost `w.costR`;
* `engine_program_block_costR_via_g`   sanity: the old theorem is the special case `GWord.ofB`.
-/

set_option linter.unusedSectionVars false

namespace OAI.PowerSaving
open RAM Cluster

namespace RAM
open Binary Matrix Ty Finset GF
universe U

/-- **The generalised engine, all live slots at once.** -/
theorem engine_all_g {α ρ σ : Type} [Fintype α] [DecidableEq α] [Fintype ρ]
    [DecidableEq ρ] [Fintype σ] [DecidableEq σ]
    (u a : ℕ) (hα : Fintype.card α = u) (hσ : Fintype.card σ = 2^a) (hu : 3 ≤ u)
    (e : σ → ρ) (he : Function.Injective e)
    (w : GWord α ρ) (hw : GLiveKernel e w) (hP : w.Proper u)
    (H : ℕ → ℕ) (hH : ∀ r, w.hist r ≤ H r) (s : Finset ℕ) (hs : ∀ r, H r ≠ 0 → r ∈ s)
    (z : ℝ) (hz : 0 ≤ z)
    (hmom : ∑ r ∈ s, (H r:ℝ) * ((r:ℝ)/(u:ℝ))^z < (2:ℝ)^a)
    (cl : Paint) (m : Bool) {ι : Type U} (k : ι→ℕ) (v : ∀ i, Sim σ (k i)→ℂ) :
    let Q := Layout.someLayout σ
    Can m (fun i => 2^k i) (simIn cl) (bundle cl) (fun i => loaded cl Q (k i) (v i))
      (fun i => (sim Q (k i)).tape (whole (k i) (v i)))
      (fun i => 2^k i*envelope z (k i)) := by
  intro Q
  let X := Layout.someLayout α
  let R := Layout.someLayout ρ
  have hq : Q.n=2^a := Q.card.symm.trans hσ
  have hx : X.n=u := X.card.symm.trans hα
  have h := grecurse_run cl m X R Q e he u a hx hu hq w hw hP k v
  have hM := lt_of_le_of_lt (moment_le u w.hist H hH z s hs) hmom
  obtain ⟨c,hc⟩ := total_envelopeB u a w.hist hu (GWord.hist_zero u w hP) z hz hM
  exact h.weaken ⟨c,fun i => hc (k i)⟩

/-- **The generalised engine, one array.**  Conclusion: exactly the shape of upstream
`hills_program` (TensorProgram.lean:95) with envelope `⌈(k+1)^z⌉`. -/
theorem engine_program_g {α ρ σ : Type} [Fintype α] [DecidableEq α] [Fintype ρ]
    [DecidableEq ρ] [Fintype σ] [DecidableEq σ]
    (u a : ℕ) (hα : Fintype.card α = u) (hσ : Fintype.card σ = 2^a) (hu : 3 ≤ u)
    (e : σ → ρ) (he : Function.Injective e)
    (w : GWord α ρ) (hw : GLiveKernel e w) (hP : w.Proper u)
    (H : ℕ → ℕ) (hH : ∀ r, w.hist r ≤ H r) (s : Finset ℕ) (hs : ∀ r, H r ≠ 0 → r ∈ s)
    (z : ℝ) (hz : 0 ≤ z)
    (hmom : ∑ r ∈ s, (H r:ℝ) * ((r:ℝ)/(u:ℝ))^z < (2:ℝ)^a)
    (cl : Paint) (m : Bool) {ι : Type U} (k : ι→ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*envelope z (k i)) := by
  have ht := engine_all_g u a hα hσ hu e he w hw hP H hH s hs z hz hmom cl m k
    (fun i (j : Sim σ (k i)) => v i j.2)
  have Hn : Nonempty σ := Fintype.card_pos_iff.mp (by rw [hσ]; positivity)
  obtain ⟨l⟩ := Hn
  exact project_envB (envelope z) (envelope_pos z) cl m k v (Layout.someLayout σ) l ht

/-- **The generalised engine with the moment given as the additive cost of the word**
(the analogue of `engine_program_block_costR`; same numeric hypothesis). -/
theorem engine_program_g_costR {α ρ σ : Type} [Fintype α] [DecidableEq α] [Fintype ρ]
    [DecidableEq ρ] [Fintype σ] [DecidableEq σ]
    (u a : ℕ) (hα : Fintype.card α = u) (hσ : Fintype.card σ = 2^a) (hu : 3 ≤ u)
    (e : σ → ρ) (he : Function.Injective e)
    (w : GWord α ρ) (hw : GLiveKernel e w) (hP : w.Proper u)
    (z : ℝ) (hz : 0 ≤ z)
    (hmom : w.costR (fun r => ((r:ℝ)/(u:ℝ))^z) < (2:ℝ)^a)
    (cl : Paint) (m : Bool) {ι : Type U} (k : ι→ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*envelope z (k i)) := by
  refine engine_program_g u a hα hσ hu e he w hw hP w.hist (fun _ => le_rfl)
    (Finset.range u) (fun r hr => ?_) z hz ?_ cl m k v
  · rw [Finset.mem_range]
    by_contra h
    exact hr (GWord.hist_large u w hP r (Nat.le_of_not_lt h))
  · rw [GWord.costR_eq_sum u _ w hP] at hmom
    rw [← Fin.sum_univ_eq_sum_range (fun r => (w.hist r:ℝ) * ((r:ℝ)/(u:ℝ))^z) u]
    exact hmom

/-- Sanity: the old block engine theorem is the special case of old words. -/
theorem engine_program_block_costR_via_g {α ρ σ : Type} [Fintype α] [DecidableEq α]
    [Fintype ρ] [DecidableEq ρ] [Fintype σ] [DecidableEq σ]
    (u a : ℕ) (hα : Fintype.card α = u) (hσ : Fintype.card σ = 2^a) (hu : 3 ≤ u)
    (e : σ → ρ) (he : Function.Injective e)
    (w : BWord α ρ) (hw : LiveKernel e w.flat) (hP : w.Proper u)
    (z : ℝ) (hz : 0 ≤ z)
    (hmom : w.costR (fun r => ((r:ℝ)/(u:ℝ))^z) < (2:ℝ)^a)
    (cl : Paint) (m : Bool) {ι : Type U} (k : ι→ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*envelope z (k i)) :=
  engine_program_g_costR u a hα hσ hu e he (GWord.ofB w) (GLiveKernel.ofB hw)
    (GWord.proper_ofB hP) z hz (by rw [GWord.costR_ofB]; exact hmom) cl m k v

end RAM
end OAI.PowerSaving

#print axioms OAI.PowerSaving.RAM.engine_all_g
#print axioms OAI.PowerSaving.RAM.engine_program_g
#print axioms OAI.PowerSaving.RAM.engine_program_g_costR
#print axioms OAI.PowerSaving.RAM.engine_program_block_costR_via_g
