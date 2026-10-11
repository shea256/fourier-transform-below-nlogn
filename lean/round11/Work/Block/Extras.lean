import Work.Block.Paths

/-!
# Block moves, part 11: sanity lemmas, convenience lemmas and a plumbing instance

(agent key: block-engine).

* `allotB_single`        with only rank-1 blocks the block recurrence IS upstream's `allot`;
* `splitCost_zero`, `splitCost_of_lt`, `splitCost_full`   evaluation of `splitCost`;
* `BRoute.shifts`        free translations of all roles as a block route of cost 0;
* `demo_block_engine`    a complete (deliberately tiny, exponent 2, NO saving) instance that
                         runs the whole pipeline `BPath.reframe → engine_program_broute` with a
                         rank-2 block and the `(m-1)+1` split.  Its only purpose is to show that
                         the hypotheses of the engine are jointly satisfiable through the path
                         calculus.
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving.Binary
noncomputable section

lemma splitCost_zero (φ : ℕ → ℝ) (m : ℕ) : splitCost φ m 0 = 0 := by
  simp [splitCost]

lemma splitCost_of_lt (φ : ℕ → ℝ) {m q : ℕ} (h0 : q ≠ 0) (h : q < m) :
    splitCost φ m q = φ q := by
  simp [splitCost, h0, h]

lemma splitCost_full (φ : ℕ → ℝ) {m : ℕ} (hm : m ≠ 0) :
    splitCost φ m m = φ (m-1) + φ 1 := by
  simp [splitCost, hm]

end
end PowerSaving.Binary

namespace PowerSaving.RAM
open Binary Matrix Finset
noncomputable section

/-- **The block recurrence specialises to upstream's**: with `D` blocks of rank one and no
other block, `allotB` is `allot u a D` (RecursionBounds.lean:12). -/
lemma allotB_single (u a D k : ℕ) (hu : 3 ≤ u) :
    allotB u a (fun r => if r = 1 then D else 0) k = allot u a D k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : threshold u a ≤ k
    · rw [allotB_big u a _ k hu hk, allot, dif_pos ⟨down_lt hu hk, hk⟩]
      congr 1
      rw [Finset.sum_eq_single (⟨1, by omega⟩ : Fin u)]
      · change (if (1:ℕ) = 1 then D else 0) * batchesB u a 1 k *
          allotB u a (fun r => if r = 1 then D else 0) (1 * (k/u)) = _
        rw [if_pos rfl, batchesB_one, Nat.one_mul, ih (k/u) (down_lt hu hk)]
      · intro b _ hb
        have hb1 : ¬ (b:ℕ) = 1 := fun h => hb (Fin.ext h)
        simp [hb1]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [allotB_small u a _ k hk, allot, dif_neg (fun h => hk h.2)]

section
variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

/-- Free translations of all roles (upstream `translateAll`) as a block route of cost 0. -/
theorem BRoute.shifts {φ : ℕ → ℝ} (hm : 2 ≤ Fintype.card α) (S : ρ → CMat α)
    (z : ρ → Space α) :
    BRoute φ S (fun r => shift (z r) * S r) id 0 := by
  obtain ⟨p, hp, hw⟩ := translateAll (ρ := ρ) z
  refine ⟨BWord.ofPWord p, BWord.proper_ofPWord _ hm p, ?_, ?_⟩
  · rw [BWord.costR_ofPWord, hp]; simp
  · intro f x
    rw [BWord.flat_ofPWord, hw, show point f id x = x from rfl]
    funext r
    simp [multiAct]

end

universe U

/-- **Plumbing instance (no saving; exponent 2).**  Label space of 3 coordinates, one role,
one live slot.  The role goes from the empty frame to the full frame: `BPath.reframe` emits the
`(m-1)+1` split, i.e. one block of rank 2 and one of rank 1; the moment is
`(2/3)^2 + (1/3)^2 = 5/9 < 1 = 2^0`; the engine concludes `O(2^k (k+1)^2)`. -/
theorem demo_block_engine (cl : Paint) (m : Bool) {ι : Type U} (k : ι→ℕ)
    (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*envelope 2 (k i)) := by
  let A : Fin 1 → OBase (Fin 3) := fun _ => OBase.canonical (Fin 3)
  have hpath := BPath.reframe (φ := fun r : ℕ => ((r:ℝ)/((3:ℕ):ℝ))^(2:ℝ)) (ρ := Fin 1)
    (by simp) A (fun _ => ∅) (fun _ => Finset.univ)
  refine engine_program_broute 3 0 (by simp) (by simp) (by norm_num) id Function.injective_id
    2 (by norm_num) (fun r => frame (A r) ∅) (fun _ => 1) (fun r => frame (A r) Finset.univ)
    (fun r => by simp) id _ hpath ?_ (fun x _ l => rfl) (fun l => by simp) cl m k v
  simp only [Fin.sum_univ_one, Fintype.card_fin, Finset.empty_sdiff, Finset.sdiff_empty,
    Finset.card_empty, Finset.card_univ]
  rw [splitCost_zero, splitCost_full _ (by norm_num), zero_add]
  norm_num [Real.rpow_two]

end
end PowerSaving.RAM
end OAI

#print axioms OAI.PowerSaving.RAM.allotB_single
#print axioms OAI.PowerSaving.RAM.BRoute.shifts
#print axioms OAI.PowerSaving.RAM.demo_block_engine
