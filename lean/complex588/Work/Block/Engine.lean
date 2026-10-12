import Work.Block.Recursion

/-!
# Block moves, part 7: the cost bound and the engine theorem

(agent key: block-engine).

* `allotB_bound`           the whole-block recurrence is `O(2^k (k+1)^z)` as soon as the MOMENT
                           `sum over ranks rk of N rk * (rk/u)^z` is strictly below `2^a`;
* `engine_all_block`, `engine_program_block`
                           same conclusion as upstream `hills_all` / `hills_program`
                           (TensorProgram.lean:11, :95) with envelope `⌈(k+1)^z⌉`, from a scratch
                           certificate in block form plus the moment inequality;
* `hills_program_via_block` sanity instance: upstream's own certificate, every directional move
                           a block of rank one, gives upstream's `hills_program` verbatim.
-/

set_option linter.unusedSectionVars false

namespace OAI.PowerSaving
open RAM Cluster

namespace RAM

/-- **Analytic bound for the whole-block recurrence** (style of upstream `allot_bound`,
TensorSaving.lean:11; the multi-branch induction is that of
checks/wht3/saving/BlockRecurrence.lean `block_bound`, here for the recurrence `allotB` that
the program `recurse_runB` actually satisfies). -/
theorem allotB_bound (u a : ℕ) (N : ℕ → ℕ) (hu : 3≤u) (hN0 : N 0 = 0) (z : ℝ) (hz : 0≤z)
    (hM : ∑ rk : Fin u, (N rk:ℝ) * (((rk:ℕ):ℝ)/(u:ℝ))^z < (2:ℝ)^a) :
    ∃ C : ℝ, 1≤C ∧ ∀ k : ℕ,
      (allotB u a N k : ℝ) ≤ C*(2:ℝ)^k*((k:ℝ)+1)^z := by
  obtain ⟨Qa, hQa⟩ : ∃ Qa : ℝ, Qa = (2:ℝ)^a := ⟨_, rfl⟩
  have hQ : 0<Qa := by rw [hQa]; positivity
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = ∑ rk : Fin u, (N rk:ℝ) * (((rk:ℕ):ℝ)/(u:ℝ))^z := ⟨_, rfl⟩
  rw [← hMdef, ← hQa] at hM
  have hM0 : 0 ≤ M := by
    rw [hMdef]; exact Finset.sum_nonneg (fun rk _ => by positivity)
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = M / Qa := ⟨_, rfl⟩
  have hS1 : S < 1 := by rw [hS, div_lt_one hQ]; exact hM
  have hS0 : 0 ≤ S := by rw [hS]; exact div_nonneg hM0 hQ.le
  have h1S : 0 < 1 - S := by linarith
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = 1+(1-S)⁻¹ := ⟨_, rfl⟩
  have hc : 1≤C := by
    rw [hCdef]
    have : 0 ≤ (1-S)⁻¹ := inv_nonneg.mpr h1S.le
    linarith
  have hg : 1 ≤ C*(1-S) := by
    rw [hCdef, add_mul, inv_mul_cancel₀ h1S.ne']; linarith
  have hC0 : 0 ≤ C := by linarith
  have hu0 : (0:ℝ) < (u:ℝ) := by exact_mod_cast (show 0 < u by omega)
  have H (k : ℕ) (hk : 0<k) :
      (allotB u a N k : ℝ) ≤ C*(2:ℝ)^k*(k:ℝ)^z := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      have hk' : 1 ≤ (k:ℝ) := Nat.one_le_cast.mpr hk
      have hgk : 1≤(k:ℝ)^z := Real.one_le_rpow hk' hz
      have hkz0 : 0 ≤ (k:ℝ)^z := by linarith
      by_cases hthr : threshold u a ≤ k
      · rw [allotB_big u a N k hu hthr]
        have hlt := down_lt hu hthr
        have hf : 1 ≤ k/u := by
          have h := hthr
          unfold threshold at h
          apply (Nat.le_div_iff_mul_le (by omega)).2
          calc
            _ ≤ u*(a+1) := by simp [mul_add]
            _ ≤ _ := h
        have hfu : k/u * u ≤ k := Nat.div_mul_le_self k u
        obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (2:ℝ)^k := ⟨_, rfl⟩
        have hx0 : 0 < x := by rw [hx]; positivity
        have hterm : ∀ rk : Fin u,
            (N rk:ℝ) * (batchesB u a rk k:ℝ) * (allotB u a N (rk * (k/u)):ℝ)
              ≤ (x * C * (k:ℝ)^z / Qa) * ((N rk:ℝ) * (((rk:ℕ):ℝ)/(u:ℝ))^z) := by
          intro rk
          by_cases h0 : (rk:ℕ) = 0
          · have hN : N rk = 0 := by rw [h0]; exact hN0
            rw [hN]; simp
          · have hrk1 : 1 ≤ (rk:ℕ) := Nat.pos_of_ne_zero h0
            have hj1 : 0 < (rk:ℕ) * (k/u) := Nat.mul_pos hrk1 hf
            have hjk : (rk:ℕ) * (k/u) < k := sub_order_lt hlt rk.isLt
            have hi := ih ((rk:ℕ) * (k/u)) hjk hj1
            have he : x = (batchesB u a rk k:ℝ) * (Qa * (2:ℝ)^((rk:ℕ) * (k/u))) := by
              rw [hx, hQa]
              exact_mod_cast (rounds_eqB u a k rk hu hthr rk.isLt).symm
            have hfk : (((rk:ℕ) * (k/u) : ℕ):ℝ) ≤ ((rk:ℕ):ℝ)/(u:ℝ) * (k:ℝ) := by
              have h3 : ((k/u : ℕ):ℝ) * (u:ℝ) ≤ (k:ℝ) := by exact_mod_cast hfu
              have hb0 : (0:ℝ) ≤ ((rk:ℕ):ℝ) := by positivity
              rw [Nat.cast_mul, div_mul_eq_mul_div, le_div_iff₀ hu0]
              nlinarith
            have hpow : (((rk:ℕ) * (k/u) : ℕ):ℝ)^z ≤ (((rk:ℕ):ℝ)/(u:ℝ))^z * (k:ℝ)^z := by
              rw [← Real.mul_rpow (by positivity) (by positivity)]
              exact Real.rpow_le_rpow (by positivity) hfk hz
            calc (N rk:ℝ) * (batchesB u a rk k:ℝ) * (allotB u a N (rk * (k/u)):ℝ)
                ≤ (N rk:ℝ) * (batchesB u a rk k:ℝ) *
                    (C*(2:ℝ)^((rk:ℕ) * (k/u))*(((rk:ℕ) * (k/u) : ℕ):ℝ)^z) :=
                  mul_le_mul_of_nonneg_left hi (by positivity)
              _ ≤ (N rk:ℝ) * (batchesB u a rk k:ℝ) *
                    (C*(2:ℝ)^((rk:ℕ) * (k/u))*((((rk:ℕ):ℝ)/(u:ℝ))^z * (k:ℝ)^z)) :=
                  mul_le_mul_of_nonneg_left
                    (mul_le_mul_of_nonneg_left hpow (by positivity)) (by positivity)
              _ = ((batchesB u a rk k:ℝ) * (Qa * (2:ℝ)^((rk:ℕ) * (k/u)))) * C * (k:ℝ)^z / Qa *
                    ((N rk:ℝ) * (((rk:ℕ):ℝ)/(u:ℝ))^z) := by
                  field_simp
              _ = _ := by rw [← he]
        have hsum : (∑ rk : Fin u,
            (N rk:ℝ) * (batchesB u a rk k:ℝ) * (allotB u a N (rk * (k/u)):ℝ))
            ≤ (x * C * (k:ℝ)^z / Qa) * M := by
          rw [hMdef, Finset.mul_sum]
          exact Finset.sum_le_sum (fun rk _ => hterm rk)
        have heq : x * C * (k:ℝ)^z / Qa * M = x * (C * S * (k:ℝ)^z) := by
          rw [hS]; field_simp
        have hfin : 1 + C * S * (k:ℝ)^z ≤ C * (k:ℝ)^z := by
          have h5 : C*(1-S) ≤ C*(1-S)*(k:ℝ)^z :=
            le_mul_of_one_le_right (mul_nonneg hC0 h1S.le) hgk
          nlinarith
        push_cast
        rw [← hx]
        calc x + ∑ rk : Fin u,
              (N rk:ℝ) * (batchesB u a rk k:ℝ) * (allotB u a N (rk * (k/u)):ℝ)
            ≤ x + x * (C * S * (k:ℝ)^z) := by rw [← heq]; linarith
          _ = x * (1 + C * S * (k:ℝ)^z) := by ring
          _ ≤ x * (C * (k:ℝ)^z) := mul_le_mul_of_nonneg_left hfin hx0.le
          _ = C * x * (k:ℝ)^z := by ring
      · rw [allotB_small u a N k hthr]
        push_cast
        calc
          _ = 1*(2:ℝ)^k*1 := by simp
          _ ≤ _ := by gcongr
  refine ⟨C,hc,fun k => ?_⟩
  by_cases he : k=0
  · subst k
    have hthr : ¬ threshold u a ≤ 0 := by
      unfold threshold
      have : 0 < u*(a+1) := by positivity
      omega
    rw [allotB_small u a N 0 hthr]
    simpa using hc
  · apply (H k (Nat.pos_of_ne_zero he)).trans
    gcongr
    first | exact hz | simp

end RAM

/-- Natural-number form of `allotB_bound` (generic form of upstream `total_hills`). -/
lemma total_envelopeB (u a : ℕ) (N : ℕ → ℕ) (hu : 3 ≤ u) (hN0 : N 0 = 0) (z : ℝ) (hz : 0 ≤ z)
    (hM : ∑ rk : Fin u, (N rk:ℝ) * (((rk:ℕ):ℝ)/(u:ℝ))^z < (2:ℝ)^a) :
    ∃ c : ℕ, ∀ k : ℕ, RAM.allotB u a N k + 1 ≤ c*(2^k*envelope z k + 1) := by
  obtain ⟨C,hC,h⟩ := RAM.allotB_bound u a N hu hN0 z hz hM
  obtain ⟨c,hc⟩ := exists_nat_ge C
  have ht : 1≤c := Nat.one_le_cast.mp (hC.trans hc)
  refine ⟨c,fun k => ?_⟩
  specialize h k
  have hg : (RAM.allotB u a N k : ℝ) ≤ c*((2:ℝ)^k*(envelope z k:ℝ)) := by
    rw [← mul_assoc]
    refine h.trans ?_
    have hh : ((k:ℝ)+1)^z ≤ (envelope z k:ℝ) := Nat.le_ceil _
    gcongr
  have he : RAM.allotB u a N k ≤ c*(2^k*envelope z k) := by exact_mod_cast hg
  rw [mul_add,mul_one]
  omega

/-- Moment over `Fin u` of a histogram, bounded by the moment of any pointwise upper bound
`H` summed over any finite set containing the support of `H`. -/
lemma moment_le (u : ℕ) (N H : ℕ → ℕ) (hNH : ∀ r, N r ≤ H r) (z : ℝ)
    (s : Finset ℕ) (hs : ∀ r, H r ≠ 0 → r ∈ s) :
    ∑ rk : Fin u, (N rk:ℝ) * (((rk:ℕ):ℝ)/(u:ℝ))^z ≤
      ∑ r ∈ s, (H r:ℝ) * ((r:ℝ)/(u:ℝ))^z := by
  have hpos (r : ℕ) : (0:ℝ) ≤ ((r:ℝ)/(u:ℝ))^z := by positivity
  calc ∑ rk : Fin u, (N rk:ℝ) * (((rk:ℕ):ℝ)/(u:ℝ))^z
      ≤ ∑ rk : Fin u, (H rk:ℝ) * (((rk:ℕ):ℝ)/(u:ℝ))^z := by
        apply Finset.sum_le_sum
        intro rk _
        apply mul_le_mul_of_nonneg_right _ (hpos rk)
        exact_mod_cast hNH rk
    _ = ∑ r ∈ Finset.range u, (H r:ℝ) * ((r:ℝ)/(u:ℝ))^z :=
        Fin.sum_univ_eq_sum_range (fun r => (H r:ℝ) * ((r:ℝ)/(u:ℝ))^z) u
    _ = ∑ r ∈ (Finset.range u).filter (fun r => r ∈ s), (H r:ℝ) * ((r:ℝ)/(u:ℝ))^z := by
        symm
        apply Finset.sum_filter_of_ne
        intro r _ hr
        apply hs
        intro h0
        apply hr
        rw [h0]; simp
    _ ≤ ∑ r ∈ s, (H r:ℝ) * ((r:ℝ)/(u:ℝ))^z := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro r hr; exact (Finset.mem_filter.mp hr).2
        · intro r _ _; exact mul_nonneg (by positivity) (hpos r)

namespace RAM
open Binary Matrix Ty Finset
universe U

/-- Copy of upstream's private `hills_project` (TensorProgram.lean:30-93) with the envelope
`hills` replaced by an arbitrary `E` with `1 ≤ E k` (the copy in `Work/Scratch/Engine.lean`
is private there). -/
theorem project_envB {ρ : Type*} (E : ℕ → ℕ) (hE : ∀ k, 1 ≤ E k)
    (cl : Paint) (m : Bool) {ι : Type U}
    (k : ι → ℕ) (v : ∀ i, Bits (k i) → ℂ) (R : Layout ρ) (l : ρ)
    (h : Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => loaded cl R (k i) (fun j => v i j.2))
      (fun i => (sim R (k i)).tape (whole (k i) (fun j => v i j.2)))
      (fun i => 2^k i*E (k i))) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*E (k i)) := by
  let B i := 2^k i
  let W i := 2^k i*E (k i)
  let x i := givenBits cl (k i) (v i)
  let L i := bits (k i)
  let M i := sim R (k i)
  let E' (i) (j : Sim ρ (k i)) := v i j.2
  have hd : Dom W B := Dom.of_le (fun i => Nat.le_mul_of_pos_right _ (hE _))
  have he : Dom W (fun i => (M i).n) := by
    refine hd.trans ?_
    refine ⟨R.n+1,fun i => ?_⟩
    change R.n*B i+1 ≤ _
    simp only [mul_add,add_mul,mul_one,one_mul]
    gcongr <;> simp
  have HX : Has m B (simIn cl) (bundle cl) x fun i => (L i).tape (v i) :=
    Can.second.snd
  have hl : Knows m B (simIn cl) x fun i => (L i).n := HX.len (Small.self B)
  have hh : Can m B (simIn cl) (bundle cl) x (fun i => (M i).tape (E' i)) W := by
    let Q := Σ i, Sim ρ (k i)
    have hb : Small B fun i => (M i).n :=
      (Small.const B R.n).mul (Small.self B)
    have ht : Has m (fun d : Q => B d.1) (p (simIn cl) w) (c cl)
        (fun d => (x d.1,(M d.1).loc d.2)) (fun d => E' d.1 d.2) := by
      let σ := Sigma.fst (β:=fun i => Sim ρ (k i))
      exact Can.fetch (t:=c cl) (L:=fun i => L i.1) (v:=fun i => v i.1)
        (i:=fun i : Q => i.2.2)
        (Can.first.then_do (HX.reindex σ)) (Can.addr_low
          (L:=fun _ => R) (R:=fun i : Q => L i.1) (u:=fun d : Q => d.2)
          Can.second (Can.then_do (Can.first (s:=simIn cl) (t:=w) (v:=fun d : Q => (x d.1,(M d.1).loc d.2))) (hl.reindex σ)) (hb.reindex σ))
    have H := Can.layout (L:=M) (t:=c cl) (P:=fun _ => 0) (v:=E')
      ((Can.wc R.n).times hl (Small.const B R.n) (Small.self B)) ht hb
    simp only [Nat.mul_zero,Nat.zero_add,Nat.add_zero] at H
    exact H.weaken he
  have hk : Can m B (simIn cl) (bundle cl) x
      (fun i => (M i).tape (whole (k i) (E' i))) W := by
    refine Can.then_do ?_ h
    exact Can.pair Can.first ((Can.second.fst).pair hh)
  -- locally keep x as well to supply size
  let Y i := whole (k i) (E' i)
  let s := p (simIn cl) (bundle cl)
  let env (i : ι) : T s := (x i,(M i).tape (Y i))
  refine Can.bind hk (g:=?_)
  change Can m B s (bundle cl) env _ W
  have hl' := Can.then_do (show Has m B s (simIn cl) env x from Can.first) hl
  let σ := Sigma.fst (β:=fun i => Bits (k i))
  have ht : Has m (fun d : Σ i, Bits (k i) => B d.1) (p s w) (c cl)
      (fun d => (env d.1,(L d.1).loc d.2)) (fun d => ripple _ (v d.1) d.2) := by
    exact Can.fetch (i:=fun d : Σ i,Bits (k i) => (l,d.2)) (L:=fun i => M i.1)
      (v:=fun i => Y i.1) (t:=c cl)
      (Can.first.snd) (Can.addr_join (u:=fun d : Σ i,Bits (k i) => (l,d.2)) (L:=fun _=> R)
        (R:=fun d : Σ i,Bits (k i) => L d.1) (Can.wc (R.loc l)) Can.second (Can.then_do (Can.first (s:=s) (t:=w) (v:=fun d : Σ i,Bits (k i) => (env d.1,(L d.1).loc d.2))) (hl'.reindex σ))
        (Small.const (fun d : Σ i,Bits (k i) => B d.1) R.n) ((Small.self B).reindex σ))
  have H := Can.layout (L:=L) (t:=c cl) (P:=fun _ => 0)
    (v:=fun i => ripple (k i) (v i)) hl' ht (Small.self B)
  simp only [Nat.mul_zero,Nat.zero_add,Nat.add_zero] at H
  exact H.weaken hd

/-- **The block engine, all live slots at once.**  `σ` = live slots (`2^a` of them), `ρ` = all
roles of the word (live and scratch), `e : σ → ρ` injective.  The block word `w` must satisfy
the scratch certificate `LiveKernel e w.flat`, every block must have rank `1 ≤ rk < u`, and the
moment of (an upper bound `H` of) its rank histogram must be strictly below `2^a`. -/
theorem engine_all_block {α ρ σ : Type} [Fintype α] [DecidableEq α] [Fintype ρ]
    [DecidableEq ρ] [Fintype σ] [DecidableEq σ]
    (u a : ℕ) (hα : Fintype.card α = u) (hσ : Fintype.card σ = 2^a) (hu : 3 ≤ u)
    (e : σ → ρ) (he : Function.Injective e)
    (w : BWord α ρ) (hw : LiveKernel e w.flat) (hP : w.Proper u)
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
  have h := recurse_runB cl m X R Q e he u a hx hu hq w hw hP k v
  have hM := lt_of_le_of_lt (moment_le u w.hist H hH z s hs) hmom
  obtain ⟨c,hc⟩ := total_envelopeB u a w.hist hu (BWord.hist_zero u w hP) z hz hM
  exact h.weaken ⟨c,fun i => hc (k i)⟩

/-- **The block engine, one array.**  Conclusion: exactly the shape of upstream
`hills_program` (TensorProgram.lean:95) with envelope `⌈(k+1)^z⌉`.  Hypotheses: a
scratch-engine certificate in block form (`LiveKernel e w.flat`, blocks of rank
`1 ≤ rk < u`) and the moment inequality `∑ H r * (r/u)^z < 2^a` for an upper bound `H` of the
histogram of block ranks. -/
theorem engine_program_block {α ρ σ : Type} [Fintype α] [DecidableEq α] [Fintype ρ]
    [DecidableEq ρ] [Fintype σ] [DecidableEq σ]
    (u a : ℕ) (hα : Fintype.card α = u) (hσ : Fintype.card σ = 2^a) (hu : 3 ≤ u)
    (e : σ → ρ) (he : Function.Injective e)
    (w : BWord α ρ) (hw : LiveKernel e w.flat) (hP : w.Proper u)
    (H : ℕ → ℕ) (hH : ∀ r, w.hist r ≤ H r) (s : Finset ℕ) (hs : ∀ r, H r ≠ 0 → r ∈ s)
    (z : ℝ) (hz : 0 ≤ z)
    (hmom : ∑ r ∈ s, (H r:ℝ) * ((r:ℝ)/(u:ℝ))^z < (2:ℝ)^a)
    (cl : Paint) (m : Bool) {ι : Type U} (k : ι→ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*envelope z (k i)) := by
  have ht := engine_all_block u a hα hσ hu e he w hw hP H hH s hs z hz hmom cl m k
    (fun i (j : Sim σ (k i)) => v i j.2)
  have Hn : Nonempty σ := Fintype.card_pos_iff.mp (by rw [hσ]; positivity)
  obtain ⟨l⟩ := Hn
  exact project_envB (envelope z) (envelope_pos z) cl m k v (Layout.someLayout σ) l ht

end RAM
end OAI.PowerSaving

#print axioms OAI.PowerSaving.RAM.allotB_bound
#print axioms OAI.PowerSaving.RAM.engine_all_block
#print axioms OAI.PowerSaving.RAM.engine_program_block
