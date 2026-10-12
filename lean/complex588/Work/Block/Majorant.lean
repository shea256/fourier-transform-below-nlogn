import Work.Block.Port

/-!
# Block moves, part 14: cheaper ways to discharge the moment inequality

(agent key: block-engine).  The moment `∑ over blocks (rk/u)^z` needs the whole histogram of
block ranks.  Two weaker but much cheaper sufficient conditions:

* `engine_program_block_majorant`, `engine_program_broute_majorant`
      any weight function `ψ` with `(r/u)^z ≤ ψ r` for `1 ≤ r < u` may replace `(r/u)^z`
      (so the path calculus can be run with a LINEAR weight `ψ r = lam * r + mu`, whose cost only
      needs masses and block counts, exactly like upstream's bookkeeping);
* `engine_program_block_jensen`
      from ONLY the number of blocks `B = w.blocks` and the number of unit moves
      `R = tally w.flat`: for any `x0 > 0`,
      `(x0/u)^z * ((1-z) * B + z * R / x0) < 2^a` suffices (tangent line of the concave function
      `x^z` at `x0`; `x0 = R/B` gives Jensen's bound `B^(1-z) * R^z / u^z`).

NOTHING here constructs a network; these are engine-side corollaries.
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving.Binary
noncomputable section
section
variable {α ρ : Type*}

lemma BWord.costR_mono (u : ℕ) (φ ψ : ℕ → ℝ) (h : ∀ r, 1 ≤ r → r < u → φ r ≤ ψ r)
    (w : BWord α ρ) (hw : w.Proper u) : w.costR φ ≤ w.costR ψ := by
  induction w with
  | nil => simp
  | cons mv w ih =>
    rw [BWord.costR_cons, BWord.costR_cons]
    refine add_le_add ?_ (ih hw.tail)
    have hp := hw.head
    cases mv with
    | localM g => simp [BMove.costR, BMove.rk?]
    | shift l z => simp [BMove.costR, BMove.rk?]
    | block l rk z ind =>
      obtain ⟨h1, h2⟩ : 1 ≤ rk ∧ rk < u := hp
      simpa [BMove.costR, BMove.rk?] using h rk h1 h2

/-- Number of blocks of a word. -/
def BWord.blocks (w : BWord α ρ) : ℕ := w.cost (fun _ => 1)

/-- A linear weight only sees the total rank and the number of blocks. -/
lemma BWord.costR_linear (lam mu : ℝ) (w : BWord α ρ) :
    w.costR (fun r => lam * (r:ℝ) + mu) =
      lam * ((w.cost id : ℕ):ℝ) + mu * ((w.blocks : ℕ):ℝ) := by
  induction w with
  | nil => simp [BWord.blocks]
  | cons mv w ih =>
    rw [BWord.costR_cons, ih]
    unfold BWord.blocks
    rw [BWord.cost_cons, BWord.cost_cons]
    push_cast
    cases mv with
    | localM g => simp [BMove.costR, BMove.cost, BMove.rk?]
    | shift l z => simp [BMove.costR, BMove.cost, BMove.rk?]
    | block l rk z ind =>
      simp only [BMove.costR, BMove.cost, BMove.rk?, id]
      ring

end

/-- Tangent line of the concave function `x ↦ x^z` (`0 ≤ z ≤ 1`) at `x0 > 0`. -/
lemma rpow_tangent (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (x x0 : ℝ) (hx : 0 ≤ x)
    (hx0 : 0 < x0) : x^z ≤ x0^z * ((1 - z) + z * x / x0) := by
  have hq : 0 ≤ x / x0 := div_nonneg hx hx0.le
  have hs : -1 ≤ x / x0 - 1 := by linarith
  have hb := _root_.rpow_one_add_le_one_add_mul_self hs hz0 hz1
  have e1 : 1 + (x / x0 - 1) = x / x0 := by ring
  rw [e1] at hb
  have e2 : x^z = x0^z * (x/x0)^z := by
    rw [← Real.mul_rpow hx0.le hq]
    congr 1
    field_simp
  rw [e2]
  have h0 : 0 ≤ x0^z := Real.rpow_nonneg hx0.le z
  calc x0^z * (x/x0)^z ≤ x0^z * (1 + z * (x/x0 - 1)) := mul_le_mul_of_nonneg_left hb h0
    _ = x0^z * ((1 - z) + z * x / x0) := by ring

end
end PowerSaving.Binary

namespace PowerSaving.RAM
open Binary Matrix Finset
noncomputable section
universe U

/-- The block engine with a majorant `ψ` of the weight `(r/u)^z`. -/
theorem engine_program_block_majorant {α ρ σ : Type} [Fintype α] [DecidableEq α] [Fintype ρ]
    [DecidableEq ρ] [Fintype σ] [DecidableEq σ]
    (u a : ℕ) (hα : Fintype.card α = u) (hσ : Fintype.card σ = 2^a) (hu : 3 ≤ u)
    (e : σ → ρ) (he : Function.Injective e)
    (w : BWord α ρ) (hw : LiveKernel e w.flat) (hP : w.Proper u)
    (z : ℝ) (hz : 0 ≤ z)
    (ψ : ℕ → ℝ) (hψ : ∀ r, 1 ≤ r → r < u → ((r:ℝ)/(u:ℝ))^z ≤ ψ r)
    (hmom : w.costR ψ < (2:ℝ)^a)
    (cl : Paint) (m : Bool) {ι : Type U} (k : ι→ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*envelope z (k i)) :=
  engine_program_block_costR u a hα hσ hu e he w hw hP z hz
    (lt_of_le_of_lt (BWord.costR_mono u _ ψ hψ w hP) hmom) cl m k v

/-- The block engine fed with a block route whose weights `ψ` majorise `(r/u)^z`. -/
theorem engine_program_broute_majorant {α ρ σ : Type} [Fintype α] [DecidableEq α] [Fintype ρ]
    [DecidableEq ρ] [Fintype σ] [DecidableEq σ]
    (u a : ℕ) (hα : Fintype.card α = u) (hσ : Fintype.card σ = 2^a) (hu : 3 ≤ u)
    (e : σ → ρ) (he : Function.Injective e)
    (z : ℝ) (hz : 0 ≤ z)
    (ψ : ℕ → ℝ) (hψ : ∀ r, 1 ≤ r → r < u → ((r:ℝ)/(u:ℝ))^z ≤ ψ r)
    (S S' T : ρ → CMat α) (hS : ∀ r, S r * S' r = 1)
    (g : (ρ→ℂ) → (ρ→ℂ)) (c : ℝ)
    (h : BRoute ψ S T g c) (hc : c < (2:ℝ)^a)
    (hg : ∀ x : ρ → ℂ, (∀ s, (∀ l, e l ≠ s) → x s = 0) → ∀ l, g x (e l) = x (e l))
    (hT : ∀ l, T (e l) = kernel α * S (e l))
    (cl : Paint) (m : Bool) {ι : Type U} (k : ι→ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*envelope z (k i)) := by
  obtain ⟨w, hP, hcost, hw⟩ := BRoute.liveKernel e S S' T hS g c h hg hT
  rw [hα] at hP
  exact engine_program_block_majorant u a hα hσ hu e he w hw hP z hz ψ hψ
    (lt_of_le_of_lt hcost hc) cl m k v

/-- **Jensen form: only the number of blocks and the number of unit moves are needed.**
For `0 ≤ z ≤ 1` and any `x0 > 0` (take `x0` close to `tally / blocks`). -/
theorem engine_program_block_jensen {α ρ σ : Type} [Fintype α] [DecidableEq α] [Fintype ρ]
    [DecidableEq ρ] [Fintype σ] [DecidableEq σ]
    (u a : ℕ) (hα : Fintype.card α = u) (hσ : Fintype.card σ = 2^a) (hu : 3 ≤ u)
    (e : σ → ρ) (he : Function.Injective e)
    (w : BWord α ρ) (hw : LiveKernel e w.flat) (hP : w.Proper u)
    (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1) (x0 : ℝ) (hx0 : 0 < x0)
    (hJ : (x0/(u:ℝ))^z * ((1 - z) * (w.blocks:ℝ) + z * (tally w.flat:ℝ) / x0) < (2:ℝ)^a)
    (cl : Paint) (m : Bool) {ι : Type U} (k : ι→ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*envelope z (k i)) := by
  have hu0 : (0:ℝ) < (u:ℝ) := by exact_mod_cast (show 0 < u by omega)
  have hxu : 0 < x0/(u:ℝ) := div_pos hx0 hu0
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = (x0/(u:ℝ))^z * z / x0 := ⟨_, rfl⟩
  obtain ⟨mu, hmu⟩ : ∃ mu : ℝ, mu = (x0/(u:ℝ))^z * (1 - z) := ⟨_, rfl⟩
  refine engine_program_block_majorant u a hα hσ hu e he w hw hP z hz
    (fun r => lam * (r:ℝ) + mu) ?_ ?_ cl m k v
  · intro r _ _
    have ht := rpow_tangent z hz hz1 ((r:ℝ)/(u:ℝ)) (x0/(u:ℝ)) (by positivity) hxu
    refine ht.trans (le_of_eq ?_)
    rw [hlam, hmu]
    field_simp
    ring
  · rw [BWord.costR_linear, ← tally_flat]
    refine lt_of_le_of_lt (le_of_eq ?_) hJ
    rw [hlam, hmu]
    field_simp
    ring

end
end PowerSaving.RAM
end OAI

#print axioms OAI.PowerSaving.RAM.engine_program_block_majorant
#print axioms OAI.PowerSaving.RAM.engine_program_broute_majorant
#print axioms OAI.PowerSaving.RAM.engine_program_block_jensen
