import Work.Block.Extras
import WHTCheck.Solution

/-!
# Block moves, part 12: the Walsh-Hadamard corollary for ANY engine exponent

(agent key: block-engine).  Generic form of the per-network derivation that the generated
network files repeat (e.g. checks/wht4/two-stage-in-engine/TwoStageCentre.lean, namespace `WHT`,
`wht_can_Two20c .. wht_main_Two20c`; originally checks/wht2/generalize/Exponent.lean).

* `BlockWHT.WHTTimeBoundsAt β W`   `W = O(2^k (k+1)^β)` and `W = o(2^k k)` (same definition as in
                                    the generated files; `WHTTimeBounds` of `WHTCheck/Solution.lean`
                                    is the case `β = 1 - 2/10^11`);
* `BlockWHT.wht_main_of_engine`     from a kernel engine of the `hills_program` shape with
                                    envelope `⌈(k+1)^z⌉`, `0 < z < 1`:
                                    `∃ solve W, WHTProgram solve W ∧ WHTTimeBoundsAt z W`;
* `BlockWHT.wht_main_of_block`      the same directly from the hypotheses of
                                    `engine_program_block_costR`.
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving

lemma envelope_le (z : ℝ) (hz1 : z ≤ 1) (k : ℕ) : envelope z k ≤ k+1 := by
  have hk : 1≤(k:ℝ)+1 := by simp
  apply Nat.ceil_le.mpr
  simpa using Real.rpow_le_rpow_of_exponent_le hk hz1

lemma envelope_real (z : ℝ) (hz : 0 ≤ z) (k : ℕ) : (envelope z k:ℝ) ≤ 2*((k:ℝ)+1)^z := by
  have h := Real.one_le_rpow (show 1≤(k:ℝ)+1 by simp) hz
  have hh : (envelope z k:ℝ) < ((k:ℝ)+1)^z+1 := Nat.ceil_lt_add_one (by positivity)
  linarith

namespace BlockWHT
noncomputable section
open RAM RAM.Ty RAM.Bench Binary Matrix Finset Complex WHT
universe U V

/-- `W = O(2^k (k+1)^β)` and `W = o(2^k k)`. -/
def WHTTimeBoundsAt (β : ℝ) (W : ℕ → ℕ) : Prop :=
  let W' := fun k : ℕ => (W k : ℝ)
  Asymptotics.IsBigO Filter.atTop W' (fun k : ℕ => (2:ℝ)^k * ((k:ℝ)+1)^β) ∧
  Asymptotics.IsLittleO Filter.atTop W' (fun k : ℕ => (2:ℝ)^k * (k:ℝ))

/-- **Walsh-Hadamard engine from a kernel engine**, in the `Can` framework: same shape and
same work bound, with the kernel `ripple k` replaced by the Walsh matrix `wal (Fin k)`. -/
theorem wht_can_of (E : ℕ → ℕ) (hE : ∀ k, 1 ≤ E k) (cl : Paint) (m : Bool) {ι : Type U}
    (k : ι → ℕ)
    (H : ∀ u : ∀ i, Bits (k i) → ℂ,
      Can m (fun i => 2^k i) (simIn cl) (bundle cl)
        (fun i => givenBits cl (k i) (u i)) (fun i => (bits (k i)).tape (ripple (k i) (u i)))
        (fun i => 2^k i*E (k i)))
    (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i))
      (fun i => (bits (k i)).tape (wal (Fin (k i)) *ᵥ v i))
      (fun i => 2^k i*E (k i)) := by
  let B (i : ι) : ℕ := 2^k i
  let W (i : ι) : ℕ := 2^k i*E (k i)
  let x (i : ι) : T (simIn cl) := givenBits cl (k i) (v i)
  let L (i : ι) : Layout (Bits (k i)) := bits (k i)
  let u (i : ι) (y : Bits (k i)) : ℂ := lum y * v i y
  let r (i : ι) : Bits (k i) → ℂ := ripple (k i) (u i)
  have hd : Dom W B := Dom.of_le (fun i => Nat.le_mul_of_pos_right _ (hE _))
  have sB : Small B fun i => (L i).n := Small.self B
  have sp : Small B fun i => 2^k i := Small.self B
  have sk : Small B k := (Small.self B).mono fun i => Nat.lt_two_pow_self.le
  -- what the input environment `(k, I, tape v)` offers at constant cost
  have hk : Knows m B (simIn cl) x k := Can.first
  have hI : Has m B (simIn cl) sc x (fun _ => I) := Can.second.fst
  have hX : Has m B (simIn cl) (bundle cl) x fun i => (L i).tape (v i) := Can.second.snd
  have hl : Knows m B (simIn cl) x fun i => (L i).n := hX.len (Small.self B)
  -- step 1: pre-scale by lum
  have A1 : Can m B (simIn cl) (bundle cl) x (fun i => (L i).tape (u i)) B := by
    refine Can.bind (lum_tables hk sk sp hI).1 (g := ?_)
    let s1 := p (simIn cl) (a sc)
    let e1 (i : ι) : T s1 := (x i,(L i).tape (fun y => lum y))
    have f1 : Has m B s1 (simIn cl) e1 x := Can.first
    exact scale_tape (L:=L) (t:=fun (i : ι) (y : Bits (k i)) => lum y) (v:=v) (x:=e1)
      (f1.then_do hl) sB Can.second (f1.then_do hX)
  -- step 2: the kernel engine on the pre-scaled vector
  have A2 : Can m B (simIn cl) (bundle cl) x (fun i => (L i).tape (r i)) W := by
    refine Can.then_do ?_ (H u)
    exact Can.pair Can.first ((Can.second.fst).pair (A1.weaken hd))
  -- step 3: post-scale by (1-I)^k * lum
  refine Can.bind A2 (g := ?_)
  let s2 := p (simIn cl) (bundle cl)
  let e2 (i : ι) : T s2 := (x i,(L i).tape (r i))
  change Can m B s2 (bundle cl) e2 _ W
  have f2 : Has m B s2 (simIn cl) e2 x := Can.first
  have T2 := (lum_tables (f2.then_do hk) sk sp (f2.then_do hI)).2
  refine Can.bind (T2.weaken hd) (g := ?_)
  let s3 := p s2 (a sc)
  let e3 (i : ι) : T s3 := (e2 i,(L i).tape (fun y => (1 - I)^k i * lum y))
  have f3 : Has m B s3 s2 e3 e2 := Can.first
  have A3 := scale_tape (L:=L) (t:=fun (i : ι) (y : Bits (k i)) => (1 - I)^k i * lum y)
    (v:=r) (x:=e3) (cl:=cl)
    (f3.then_do (f2.then_do hl)) sB Can.second (f3.then_do Can.second)
  refine Can.cong (A3.weaken hd) (fun _ => rfl) (fun i => ?_)
  exact congrArg (L i).tape (funext fun y => (wal_ripple (k i) (v i) y).symm)

section Explicit
open Filter Asymptotics

/-- One fixed program computing the Walsh-Hadamard transform within `C*(2^k*E k+1)` operations,
from a kernel engine with envelope `E` (`1 ≤ E k ≤ k+1`). -/
theorem wht_program_exists_of (E : ℕ → ℕ) (hE : ∀ k, 1 ≤ E k) (hE' : ∀ k, E k ≤ k+1)
    (H : ∀ (k : (Σ k : ℕ, (Bits k → ℂ)) → ℕ) (u : ∀ i, Bits (k i) → ℂ),
      Can false (fun i => 2^k i) (simIn Paint.left) (bundle Paint.left)
        (fun i => givenBits Paint.left (k i) (u i))
        (fun i => (bits (k i)).tape (ripple (k i) (u i)))
        (fun i => 2^k i*E (k i))) :
    ∃ (solve : Prog false whtInKind whtOutKind) (C : ℕ),
      WHTProgram solve (fun k => C*(2^k*E k+1)) := by
  let ι := Σ k : ℕ, (Bits k → ℂ)
  have H' := wht_can_of E hE Paint.left false (ι:=ι) (fun i => i.1) (H (fun i => i.1))
    (fun i => i.2)
  obtain ⟨f,C,d,hf⟩ := Can.unfold_bound H'
  have hh : Small (fun k : ℕ => 2^k) (fun k => E k) :=
    (Small.self _).mono fun k => (hE' k).trans (Nat.succ_le_of_lt Nat.lt_two_pow_self)
  have hs : Small (fun k : ℕ => 2^k) (fun k => C*(2^k*E k+1) + 10*(2^k+2)) :=
    ((Small.const _ C).mul (((Small.self _).mul hh).add (Small.const _ 1))).add
      ((Small.const _ 10).mul ((Small.self _).add (Small.const _ 2)))
  obtain ⟨d',hd'⟩ := hs
  refine ⟨f,C,⟨max d d',fun k => ⟨?_,fun x => ?_⟩⟩⟩
  · exact (hd' k).trans (Small.pow_mono_degree _ (le_max_right d d'))
  · let v : Bits k → ℂ := fun y => x ((bits k).toIx y)
    have h : (run f (givenBits Paint.left k v)).OK ((bits k).tape (wal (Fin k) *ᵥ v))
        (C*(2^k*E k+1)) ((2^k+2)^d) := hf ⟨k,v⟩
    have e1 : givenBits Paint.left k v = (k, Complex.I, (⟨2^k,x⟩ : Tape ℂ)) := by
      unfold givenBits
      rw [tape_of_fin]
    rw [e1] at h
    intro result
    exact ⟨h.valid, h.bound.trans (Small.pow_mono_degree _ (le_max_left d d')), h.time,
      h.result.trans (wht_tape k x)⟩

lemma rpow_little (z : ℝ) (hz1 : z < 1) :
    (fun k : ℕ => ((k:ℝ)+1)^z) =o[atTop] (fun k : ℕ => (k:ℝ)) := by
  rw [isLittleO_iff]
  intro cc hc
  have hy : 0 < 1 - z := sub_pos.mpr hz1
  have ht : Tendsto (fun k : ℕ => (k:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hz := ((tendsto_rpow_neg_atTop hy).comp ht).eventually (gt_mem_nhds (half_pos hc))
  filter_upwards [hz, eventually_ge_atTop 1] with k hk h1
  have hk' : ((k:ℝ)+1)^(-(1-z)) < cc/2 := hk
  have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast h1
  have hpos : (0:ℝ) < (k:ℝ)+1 := by positivity
  have hnn : (0:ℝ) ≤ ((k:ℝ)+1)^(-(1-z)) := by positivity
  have hsplit : ((k:ℝ)+1)^z = ((k:ℝ)+1) * ((k:ℝ)+1)^(-(1-z)) := by
    have hal : z = 1 + -(1-z) := by ring
    conv_lhs => rw [hal]
    rw [Real.rpow_add hpos, Real.rpow_one]
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), hsplit]
  nlinarith [mul_le_mul_of_nonneg_right (by linarith : (k:ℝ)+1 ≤ 2*k) hnn,
    mul_le_mul_of_nonneg_left hk'.le (by linarith : (0:ℝ) ≤ 2*k)]

theorem wht_time_of (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z < 1) (C : ℕ) :
    WHTTimeBoundsAt z (fun k => C*(2^k*envelope z k+1)) := by
  have hO : (fun k : ℕ => ((C*(2^k*envelope z k+1) : ℕ) : ℝ)) =O[atTop]
      (fun k : ℕ => (2:ℝ)^k * ((k:ℝ)+1)^z) := by
    refine IsBigO.of_bound (3*C) (Eventually.of_forall fun k => ?_)
    have h1 : (1:ℝ) ≤ ((k:ℝ)+1)^z := Real.one_le_rpow (by simp) hz0
    have h2 : (1:ℝ) ≤ (2:ℝ)^k := one_le_pow₀ (by norm_num)
    have h3 := envelope_real z hz0 k
    have hB : (1:ℝ) ≤ (2:ℝ)^k * ((k:ℝ)+1)^z := one_le_mul_of_one_le_of_one_le h2 h1
    have hA : (2:ℝ)^k * (envelope z k:ℝ) ≤ 2 * ((2:ℝ)^k * ((k:ℝ)+1)^z) := by
      have := mul_le_mul_of_nonneg_left h3 (by positivity : (0:ℝ) ≤ (2:ℝ)^k)
      linarith
    have hC : (0:ℝ) ≤ (C:ℝ) := Nat.cast_nonneg C
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left (by linarith :
      (2:ℝ)^k * (envelope z k:ℝ) + 1 ≤ 3 * ((2:ℝ)^k * ((k:ℝ)+1)^z)) hC]
  exact ⟨hO, hO.trans_isLittleO ((isBigO_refl _ _).mul_isLittleO (rpow_little z hz1))⟩

/-- **Walsh-Hadamard transform from any kernel engine of the `hills_program` shape** with
envelope `⌈(k+1)^z⌉`, `0 ≤ z < 1`: one fixed RAM program, `O(2^k (k+1)^z)` and `o(2^k k)`
operations (the statement `WHTGoal` of `WHTCheck/Challenge.lean` with the exponent `z`). -/
theorem wht_main_of_engine (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z < 1)
    (H : ∀ (k : (Σ k : ℕ, (Bits k → ℂ)) → ℕ) (u : ∀ i, Bits (k i) → ℂ),
      Can false (fun i => 2^k i) (simIn Paint.left) (bundle Paint.left)
        (fun i => givenBits Paint.left (k i) (u i))
        (fun i => (bits (k i)).tape (ripple (k i) (u i)))
        (fun i => 2^k i*envelope z (k i))) :
    ∃ solve W, WHTProgram solve W ∧ WHTTimeBoundsAt z W := by
  obtain ⟨s,C,h⟩ := wht_program_exists_of (envelope z) (envelope_pos z)
    (envelope_le z hz1.le) H
  exact ⟨s,_,h,wht_time_of z hz0 hz1 C⟩

/-- **Walsh-Hadamard transform from a block certificate**: the hypotheses of
`engine_program_block_costR` with `z < 1` give the Walsh-Hadamard statement at exponent `z`. -/
theorem wht_main_of_block {α ρ σ : Type} [Fintype α] [DecidableEq α] [Fintype ρ]
    [DecidableEq ρ] [Fintype σ] [DecidableEq σ]
    (u a : ℕ) (hα : Fintype.card α = u) (hσ : Fintype.card σ = 2^a) (hu : 3 ≤ u)
    (e : σ → ρ) (he : Function.Injective e)
    (w : BWord α ρ) (hw : LiveKernel e w.flat) (hP : w.Proper u)
    (z : ℝ) (hz : 0 ≤ z) (hz1 : z < 1)
    (hmom : w.costR (fun r => ((r:ℝ)/(u:ℝ))^z) < (2:ℝ)^a) :
    ∃ solve W, WHTProgram solve W ∧ WHTTimeBoundsAt z W :=
  wht_main_of_engine z hz hz1 (fun k v =>
    engine_program_block_costR u a hα hσ hu e he w hw hP z hz hmom Paint.left false k v)

end Explicit
end
end BlockWHT
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.BlockWHT.wht_main_of_engine
#print axioms OAI.PowerSaving.BlockWHT.wht_main_of_block
