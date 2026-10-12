import Work.Block.Engine

/-!
# Block moves, part 8: the bridge from unit-move certificates, and sanity instances

(agent key: block-engine).

The action of a block word is, by definition, upstream's `walk` of its unit-move word
`w.flat`.  So "regrouping" an existing unit-move certificate `p` means exhibiting a block word
`w` with `w.flat = p` (or `w.flat` equal to `p` up to swaps of commuting moves).

* `BWord.ofPWord`, `BWord.flat_ofPWord`   the trivial grouping: every `dir` is a rank-1 block;
* `BMove.flat_block_split`                a block of rank `a+b` and the two blocks of ranks
                                          `a`, `b` have the SAME unit-move word (in particular
                                          the `(m-1)+1` split of a rank-`m` step);
* `SwapEq`, `SwapEq.walk_eq`, `SwapEq.liveKernel_iff`
                                          adjacent `dir`/`shift` moves may be swapped;
* `BWord.costR`, `engine_program_block_costR`
                                          the moment as an additive real-valued cost of the word;
* `engine_program_block_of_tally`         for `z ≤ 1` the block engine is never worse than the
                                          one-move-per-rank (scratch) engine, whatever the grouping;
* `hills_program_via_block`               upstream's `hills_program`, verbatim, through the block
                                          engine.
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving.Binary
open Matrix Finset
noncomputable section

section
variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

/-- Trivial grouping of one unit move: a `dir` becomes a block of rank one. -/
def BMove.ofMove : Move α ρ → BMove α ρ
  | .localM g => .localM g
  | .shift l z => .shift l z
  | .dir l z nz => .block l 1 (fun _ => z) (linearIndependent_single z nz)

/-- Trivial grouping of a unit-move word. -/
def BWord.ofPWord (p : PWord α ρ) : BWord α ρ := p.map BMove.ofMove

lemma BMove.flat_ofMove (mv : Move α ρ) : (BMove.ofMove mv).flat = [mv] := by
  cases mv with
  | localM g => rfl
  | shift l z => rfl
  | dir l z nz => simp [BMove.ofMove, BMove.flat]

lemma BWord.flat_ofPWord (p : PWord α ρ) : (BWord.ofPWord p).flat = p := by
  induction p with
  | nil => rfl
  | cons mv p ih =>
    change (BMove.ofMove mv).flat ++ (BWord.ofPWord p).flat = mv :: p
    rw [BMove.flat_ofMove, ih]; rfl

lemma BWord.proper_ofPWord (u : ℕ) (hu : 2 ≤ u) (p : PWord α ρ) :
    (BWord.ofPWord p).Proper u := by
  intro mv hmv
  obtain ⟨m0, _, rfl⟩ := List.mem_map.mp hmv
  cases m0 with
  | localM g => trivial
  | shift l z => trivial
  | dir l z nz => exact ⟨le_rfl, hu⟩

/-- **Splitting / merging blocks does not change the unit-move word.**  A block of rank
`a+b` has the same unit-move word as the block of its first `a` directions followed by the
block of its last `b` directions.  With `a = m-1`, `b = 1` this is the `(m-1)+1` split of a
step of full rank `m`, which the program cannot execute as one block. -/
lemma BMove.flat_block_split (l : ρ) (a b : ℕ) (z : Fin (a+b) → Space α)
    (ind : LinearIndependent F z) :
    (BMove.block l (a+b) z ind).flat =
      (BMove.block l a (fun i => z (Fin.castAdd b i))
        (ind.comp _ (Fin.castAdd_injective a b))).flat ++
      (BMove.block l b (fun j => z (Fin.natAdd a j))
        (ind.comp _ (Fin.natAdd_injective b a))).flat := by
  simp only [BMove.flat]
  exact List.ofFn_add

/-- Regrouping in one line: if `w.flat = p`, the block word `w` has the action of `p`. -/
lemma BWord.walk_of_flat_eq (w : BWord α ρ) (p : PWord α ρ) (h : w.flat = p) (f : ℕ)
    (x : Data α ρ f) : walk f w.flat x = walk f p x := by rw [h]

/-! ### Swapping commuting unit moves -/

/-- The moves that are diagonal in the Walsh basis: `dir` and `shift` (not `localM`). -/
def Move.Diagonal : Move α ρ → Prop
  | .localM _ => False
  | _ => True

lemma roleAct_comm (f : ℕ) (r r' : ρ) (M N : CMat α) (h : M * N = N * M)
    (x : Data α ρ f) :
    roleAct f r M (roleAct f r' N x) = roleAct f r' N (roleAct f r M x) := by
  by_cases hr : r = r'
  · subst hr
    rw [roleAct_mul, roleAct_mul, h]
  · funext j
    by_cases h1 : j = r
    · subst h1
      have h2 : ¬ j = r' := hr
      simp [roleAct, h2]
    · by_cases h2 : j = r'
      · subst h2
        simp [roleAct, h1]
      · simp [roleAct, h1, h2]

lemma dir_comm_dir (z y : Space α) : dir z * dir y = dir y * dir z := by
  rw [dir_phase, dir_phase]; apply wrap_comm
lemma dir_comm_shift (z y : Space α) : dir z * shift y = shift y * dir z := by
  rw [dir_phase, shift_phase]; apply wrap_comm
lemma shift_comm_shift (z y : Space α) : shift z * shift y = shift y * shift z := by
  rw [shift_phase, shift_phase]; apply wrap_comm

/-- Two diagonal moves commute, on the same role or on different roles. -/
lemma go_comm_diag (f : ℕ) (a b : Move α ρ) (ha : a.Diagonal) (hb : b.Diagonal)
    (x : Data α ρ f) : b.go f (a.go f x) = a.go f (b.go f x) := by
  cases a with
  | localM g => exact absurd ha id
  | dir r z nz =>
    cases b with
    | localM g => exact absurd hb id
    | dir r' z' nz' => exact roleAct_comm f r' r _ _ (dir_comm_dir z' z) x
    | shift r' z' => exact roleAct_comm f r' r _ _ (dir_comm_shift z z').symm x
  | shift r z =>
    cases b with
    | localM g => exact absurd hb id
    | dir r' z' nz' => exact roleAct_comm f r' r _ _ (dir_comm_shift z' z) x
    | shift r' z' => exact roleAct_comm f r' r _ _ (shift_comm_shift z' z) x

/-- Words equal up to swaps of adjacent diagonal moves.  A `dir`/`shift` is never moved
across a `localM` gate. -/
inductive SwapEq : PWord α ρ → PWord α ρ → Prop
  | refl (p : PWord α ρ) : SwapEq p p
  | swap (p q : PWord α ρ) (a b : Move α ρ) (ha : a.Diagonal) (hb : b.Diagonal) :
      SwapEq (p ++ a :: b :: q) (p ++ b :: a :: q)
  | trans {p q r : PWord α ρ} : SwapEq p q → SwapEq q r → SwapEq p r

theorem SwapEq.walk_eq {p q : PWord α ρ} (h : SwapEq p q) (f : ℕ) (x : Data α ρ f) :
    walk f p x = walk f q x := by
  induction h generalizing x with
  | refl p => rfl
  | swap p q a b ha hb =>
    rw [walk_append, walk_append]
    change walk f q (b.go f (a.go f (walk f p x))) = walk f q (a.go f (b.go f (walk f p x)))
    rw [go_comm_diag f a b ha hb]
  | trans _ _ ih1 ih2 => rw [ih1, ih2]

theorem SwapEq.tally_eq {p q : PWord α ρ} (h : SwapEq p q) : tally p = tally q := by
  induction h with
  | refl p => rfl
  | swap p q a b ha hb =>
    simp only [tally, List.map_append, List.map_cons, List.sum_append, List.sum_cons]
    omega
  | trans _ _ ih1 ih2 => rw [ih1, ih2]

end

/-! ### The moment as an additive cost of the word -/

section
variable {α ρ : Type*}

/-- Real-valued cost of a letter when a block of rank `rk` costs `φ rk`. -/
def BMove.costR (φ : ℕ → ℝ) (mv : BMove α ρ) : ℝ :=
  match mv.rk? with
  | some rk => φ rk
  | none => 0

/-- Real-valued cost of a block word: `∑ over its blocks of φ (rank)`.  With
`φ r = (r/u)^z` this is the MOMENT of the word. -/
def BWord.costR (φ : ℕ → ℝ) (w : BWord α ρ) : ℝ := (w.map (BMove.costR φ)).sum

@[simp] lemma BWord.costR_nil (φ : ℕ → ℝ) : BWord.costR φ ([] : BWord α ρ) = 0 := rfl
lemma BWord.costR_cons (φ : ℕ → ℝ) (mv : BMove α ρ) (w : BWord α ρ) :
    BWord.costR φ (mv :: w) = mv.costR φ + BWord.costR φ w := by simp [BWord.costR]
lemma BWord.costR_append (φ : ℕ → ℝ) (w w' : BWord α ρ) :
    BWord.costR φ (w ++ w') = BWord.costR φ w + BWord.costR φ w' := by simp [BWord.costR]

lemma BWord.costR_eq_sum (u : ℕ) (φ : ℕ → ℝ) (w : BWord α ρ) (hw : w.Proper u) :
    BWord.costR φ w = ∑ r : Fin u, (w.hist r:ℝ) * φ r := by
  induction w with
  | nil => simp
  | cons mv w ih =>
    rw [BWord.costR_cons, ih hw.tail]
    simp_rw [BWord.hist_cons]
    push_cast
    simp_rw [add_mul, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    have hp := hw.head
    cases mv with
    | localM g' => simp [BMove.costR, BMove.rk?]
    | shift l z => simp [BMove.costR, BMove.rk?]
    | block l rk z ind =>
      obtain ⟨_, h2⟩ : 1 ≤ rk ∧ rk < u := hp
      simp only [BMove.costR, BMove.rk?, Option.some.injEq]
      rw [Finset.sum_eq_single (⟨rk,h2⟩ : Fin u)]
      · simp
      · intro b _ hb
        have : ¬ rk = b.val := fun h => hb (Fin.ext h.symm)
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h

end
end
end PowerSaving.Binary

namespace PowerSaving.RAM
open Binary Matrix Ty Finset Cluster
noncomputable section
universe U

theorem SwapEq.liveKernel_iff {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ]
    [DecidableEq ρ] {p q : PWord α ρ} (h : SwapEq p q) (e : σ → ρ) :
    LiveKernel e p ↔ LiveKernel e q := by
  constructor
  · intro hp f v hv l; rw [← h.walk_eq]; exact hp f v hv l
  · intro hq f v hv l; rw [h.walk_eq]; exact hq f v hv l

/-- The block engine with the moment given as the additive cost `w.costR` of the word. -/
theorem engine_program_block_costR {α ρ σ : Type} [Fintype α] [DecidableEq α] [Fintype ρ]
    [DecidableEq ρ] [Fintype σ] [DecidableEq σ]
    (u a : ℕ) (hα : Fintype.card α = u) (hσ : Fintype.card σ = 2^a) (hu : 3 ≤ u)
    (e : σ → ρ) (he : Function.Injective e)
    (w : BWord α ρ) (hw : LiveKernel e w.flat) (hP : w.Proper u)
    (z : ℝ) (hz : 0 ≤ z)
    (hmom : w.costR (fun r => ((r:ℝ)/(u:ℝ))^z) < (2:ℝ)^a)
    (cl : Paint) (m : Bool) {ι : Type U} (k : ι→ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*envelope z (k i)) := by
  refine engine_program_block u a hα hσ hu e he w hw hP w.hist (fun _ => le_rfl)
    (Finset.range u) (fun r hr => ?_) z hz ?_ cl m k v
  · rw [Finset.mem_range]
    by_contra h
    exact hr (BWord.hist_large u w hP r (Nat.le_of_not_lt h))
  · rw [BWord.costR_eq_sum u _ w hP] at hmom
    rw [← Fin.sum_univ_eq_sum_range (fun r => (w.hist r:ℝ) * ((r:ℝ)/(u:ℝ))^z) u]
    exact hmom

/-- **The block engine is never worse than one move per unit of rank** (for exponents
`z ≤ 1`): if the unit-move word of `w` satisfies the scratch-engine rate inequality
`tally / 2^a < u^z`, the block engine gives the same conclusion, for EVERY grouping `w`. -/
theorem engine_program_block_of_tally {α ρ σ : Type} [Fintype α] [DecidableEq α] [Fintype ρ]
    [DecidableEq ρ] [Fintype σ] [DecidableEq σ]
    (u a : ℕ) (hα : Fintype.card α = u) (hσ : Fintype.card σ = 2^a) (hu : 3 ≤ u)
    (e : σ → ρ) (he : Function.Injective e)
    (w : BWord α ρ) (hw : LiveKernel e w.flat) (hP : w.Proper u)
    (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hD : (tally w.flat:ℝ)/(2:ℝ)^a < (u:ℝ)^z)
    (cl : Paint) (m : Bool) {ι : Type U} (k : ι→ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*envelope z (k i)) := by
  have hu0 : (0:ℝ) < (u:ℝ) := by exact_mod_cast (show 0 < u by omega)
  have huz : 0 < (u:ℝ)^z := Real.rpow_pos_of_pos hu0 z
  refine engine_program_block_costR u a hα hσ hu e he w hw hP z hz ?_ cl m k v
  rw [BWord.costR_eq_sum u _ w hP]
  have ht : (tally w.flat:ℝ) = ∑ r : Fin u, (w.hist r:ℝ) * ((r:ℕ):ℝ) := by
    rw [tally_flat, BWord.cost_eq_sum u id w hP]
    push_cast
    rfl
  have hterm : ∀ r : Fin u, (w.hist r:ℝ) * (((r:ℕ):ℝ)/(u:ℝ))^z ≤
      (w.hist r:ℝ) * ((r:ℕ):ℝ) / (u:ℝ)^z := by
    intro r
    by_cases h0 : (r:ℕ) = 0
    · have : w.hist r = 0 := by rw [h0]; exact BWord.hist_zero u w hP
      rw [this]; simp
    · have h1 : (1:ℝ) ≤ ((r:ℕ):ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h0
      have h2 : ((r:ℕ):ℝ)^z ≤ ((r:ℕ):ℝ) := by
        have := Real.rpow_le_rpow_of_exponent_le h1 hz1
        rwa [Real.rpow_one] at this
      rw [Real.div_rpow (by positivity) hu0.le, mul_div_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_div_of_nonneg_right h2 huz.le
  calc ∑ r : Fin u, (w.hist r:ℝ) * (((r:ℕ):ℝ)/(u:ℝ))^z
      ≤ ∑ r : Fin u, (w.hist r:ℝ) * ((r:ℕ):ℝ) / (u:ℝ)^z := Finset.sum_le_sum (fun r _ => hterm r)
    _ = (tally w.flat:ℝ) / (u:ℝ)^z := by rw [ht, Finset.sum_div]
    _ < (2:ℝ)^a := by
        rw [div_lt_iff₀ huz]
        rw [div_lt_iff₀ (by positivity)] at hD
        linarith

/-- **Sanity instance: upstream's `hills_program`, verbatim, through the block engine.**
Upstream's own certificate, every directional move a block of rank one. -/
theorem hills_program_via_block (cl : Paint) (m : Bool) {ι : Type U} (k : ι→ℕ)
    (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*hills (k i)) := by
  obtain ⟨p,hp,hw⟩ := certificate
  have hflat : (BWord.ofPWord p).flat = p := BWord.flat_ofPWord p
  have hD : (tally (BWord.ofPWord p).flat:ℝ)/(2:ℝ)^50 < (mcol:ℝ)^alpha := by
    rw [hflat, hp]; exact network_rate
  exact engine_program_block_of_tally mcol 50 card_block card_role (by norm_num [mcol])
    id Function.injective_id (BWord.ofPWord p)
    (by rw [hflat]; exact LiveKernel.of_full p hw)
    (BWord.proper_ofPWord mcol (by norm_num [mcol]) p)
    alpha alpha_pos.le alpha_lt.le hD cl m k v

end
end PowerSaving.RAM
end OAI

#print axioms OAI.PowerSaving.RAM.engine_program_block_costR
#print axioms OAI.PowerSaving.RAM.engine_program_block_of_tally
#print axioms OAI.PowerSaving.RAM.hills_program_via_block
#print axioms OAI.PowerSaving.Binary.SwapEq.walk_eq
