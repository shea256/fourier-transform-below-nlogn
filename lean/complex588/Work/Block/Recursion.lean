import Work.Block.Batches

/-!
# Block moves, part 6: the recursive program for block words

(agent key: block-engine).  Generalises sections 4-5 of `Work/Scratch/Engine.lean`
(`amplifyS`, `rec_bodyS`, `recurse_runS`), i.e. upstream `TensorRecursion.lean` and
`RecursionBounds.lean`, from "every directional move is a call of order `k/u`" to
"every block of rank `rk` is a call of order `rk * (k/u)`".

* `allotB u a N`     the natural-number cost recurrence (`N rk` = number of blocks of rank `rk`);
* `amplifyB`         one level of the recursion (leftover bits `k % u` handled as upstream);
* `recurse_runB`     the closed recursion: ONE program, work `allotB u a w.hist k`.

Scratch roles are kept: the word lives on roles `ρ`, only the `2^a` live slots `e(σ)` cross a
call boundary, and the certificate is `LiveKernel e w.flat`.
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset
noncomputable section

/-- Number of batches of a block of rank `rk` at order `k`. -/
def batchesB (u a rk k : ℕ) := 2^(k - rk*(k/u) - a)

lemma batchesB_one (u a k : ℕ) : batchesB u a 1 k = batches u a k := by
  unfold batchesB batches; rw [Nat.one_mul]

lemma sub_order_lt {u k rk : ℕ} (hk : k/u < k) (hr : rk < u) : rk * (k/u) < k := by
  rcases Nat.eq_zero_or_pos (k/u) with h0 | hpos
  · rw [h0, Nat.mul_zero]; omega
  · have h1 : (rk+1) * (k/u) ≤ u * (k/u) := Nat.mul_le_mul_right _ hr
    have h2 : u * (k/u) ≤ k := Nat.mul_div_le k u
    rw [Nat.add_mul, Nat.one_mul] at h1
    omega

/-- **The whole-block cost recurrence.**  `N rk` = number of blocks of rank `rk`; a block of
rank `rk` is `batchesB u a rk k` recursive calls of order `rk * (k/u)`. -/
def allotB (u a : ℕ) (N : ℕ → ℕ) (k : ℕ) : ℕ :=
  if h : k/u<k ∧ threshold u a ≤ k then
    2^k + ∑ rk : Fin u, N rk * batchesB u a rk k * allotB u a N (rk * (k/u))
  else 2^k
termination_by k
decreasing_by exact sub_order_lt h.1 rk.isLt

lemma allotB_big (u a : ℕ) (N : ℕ → ℕ) (k : ℕ) (hu : 3≤u) (hk : threshold u a ≤ k) :
    allotB u a N k =
      2^k + ∑ rk : Fin u, N rk * batchesB u a rk k * allotB u a N (rk * (k/u)) := by
  rw [allotB, dif_pos ⟨down_lt hu hk, hk⟩]

lemma allotB_small (u a : ℕ) (N : ℕ → ℕ) (k : ℕ) (hk : ¬ threshold u a ≤ k) :
    allotB u a N k = 2^k := by
  rw [allotB, dif_neg (fun h => hk h.2)]

lemma rounds_eqB (u a k rk : ℕ) (hu : 3≤u) (hk : threshold u a ≤ k) (h2 : rk < u) :
    batchesB u a rk k * (2^a*2^(rk*(k/u)))=2^k := by
  have hh : a+1≤k/u := (Nat.le_div_iff_mul_le (by omega)).2 (by
    simpa [threshold,mul_comm] using hk)
  have h1 : (rk+1) * (k/u) ≤ u * (k/u) := Nat.mul_le_mul_right _ h2
  have h3 : u * (k/u) ≤ k := Nat.mul_div_le k u
  rw [Nat.add_mul, Nat.one_mul] at h1
  unfold batchesB
  rw [← pow_add, ← pow_add]
  congr 1
  omega

section
universe U
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]
variable {ι : Type U} {m : Bool}
    {k f : ι → ℕ} {cl : Paint} {b : Bank (hatch cl) ι}
    {v : ∀ i, Sim σ (k i)→ℂ}

/-- **One level of the block recursion** (replaces `amplifyS`).  Input and output are tables on
the live slots `σ`; the table on the roles `ρ` exists only inside this level.  `n rk i` =
number of batches of a rank-`rk` block, `τ rk i` = cost of one call of order `rk * f i`. -/
lemma amplifyB (m : Bool) (b : Bank (hatch cl) ι) (v : ∀ i, Sim σ (k i) → ℂ)
    (X : Layout α) (R : Layout ρ) (Q : Layout σ) (e : σ → ρ) (he : Function.Injective e)
    (r : ℕ) (hr : 3 ≤ X.n) (hq : ∀ i, X.n*f i+r=k i) (hd : r < X.n) (hQ : 0<Q.n)
    (n τ : ℕ → ι → ℕ)
    (hc : ∀ rk, 1 ≤ rk → rk < X.n → ∀ i, n rk i*(sim Q (rk * f i)).n=2^k i)
    (hk : ∀ rk, 1 ≤ rk → rk < X.n → Contract cl b (fun i => rk * f i) (τ rk) Q)
    (hB : Small b.B (fun i => 2^k i))
    (w : BWord α ρ) (hw : LiveKernel e w.flat) (hP : w.Proper X.n) :
    Able m b (simIn cl) (bundle cl) (fun i => loaded cl Q (k i) (v i))
      (fun i => (sim Q (k i)).tape (whole (k i) (v i)))
      (fun i => 2^k i) (fun i => w.cost (fun rk => n rk i * τ rk i)) := by
  let p := w.flat
  let W i := 2^k i
  let s := simIn cl
  let eQ (i : ι) := ebb X r (f i) (k i) (hq i) (v i)
  let zQ (i : ι) : Grain α σ r (f i) :=
    fun j => chords r (f i) (fun l => eQ i (j.1,l)) j.2
  let Z (i : ι) : Grain α ρ r (f i) := crossAct r (f i) (embM e) (zQ i)
  let O (i : ι) : Grain α σ r (f i) :=
    crossAct r (f i) (extM e) (coastline r (f i) p (Z i))
  let szQ i := (fleet X Q r (f i)).n
  let szR i := (fleet X R r (f i)).n
  have hszQ : Dom W szQ := by
    refine ⟨Q.n+1, fun i => ?_⟩
    unfold W szQ fleet
    rw [Layout.pair_len, book_len,hq]
    simp only [mul_add,add_mul,mul_one,one_mul]
    gcongr <;> simp
  have hszR : Dom W szR := by
    refine ⟨R.n+1, fun i => ?_⟩
    unfold W szR fleet
    rw [Layout.pair_len, book_len,hq]
    simp only [mul_add,add_mul,mul_one,one_mul]
    gcongr <;> simp
  have hn (i : ι) : 0 < W i := pow_pos (by decide) _
  have hf (i) : f i ≤ k i := by
    have g := hq i
    have h := Nat.le_mul_of_pos_left (f i) (show 0 < X.n by omega)
    omega
  have hy (i) : k i ≤ W i := Nat.lt_two_pow_self.le
  have sd := hB.mono hy
  have sq := sd.mono hf
  let p2 i := 2^f i
  have hm : Small b.B p2 :=
    hB.mono (fun i => Nat.pow_le_pow_right (by omega) (hf i))
  have hcube (i) : p2 i ^ 3 ≤ W i := by
    unfold p2 W
    rw [← pow_mul]
    apply Nat.pow_le_pow_right (by omega)
    have hh : 3*f i ≤ X.n*f i := Nat.mul_le_mul_right _ hr
    have hg := hq i
    rw [mul_comm]
    omega
  let env (i : ι) := loaded cl Q (k i) (v i)
  -- construct fields (f,p2)
  have hmf : Can m b.B s Ty.w env f W := by
    have ht : Can m b.B s Ty.w env k W := Can.first
    refine (ht.dvdW (Can.wc X.n) sd).cong (fun _ => rfl) ?_
    intro i
    rw [← hq,mul_comm X.n]
    exact Layout.div_join hd
  have hmp : Can m b.B s (Ty.p Ty.w Ty.w) env (fun i => (f i,p2 i)) W :=
    hmf.pair (hmf.wTwo sq hm (Dom.of_le (fun i => (hf i).trans (hy i))))
  let T1 := Ty.p s (Ty.p Ty.w Ty.w)
  let Y (i : ι) : T T1 := (env i,f i,p2 i)
  have hmx : Can m b.B T1 (Ty.a Ty.w) Y (fun i => xorTab (f i)) W :=
    (Can.xor_prepare (m:=m) (f:=f) (B:=b.B) (s:=T1) (x:=Y)
      (Can.fst Can.second) (Can.snd Can.second) sq hm).mono hcube
  let T2 := Ty.p T1 (Ty.a Ty.w)
  let Y' (i : ι) : T T2 := (Y i,xorTab (f i))
  -- the input, read as a table on the slots
  have hG : Rig m b.B f T2 Y' cl X Q r eQ := by
    have H : Has m b.B T2 s Y' env := Can.fst Can.first
    refine ⟨⟨?_,?_,Can.second,hm⟩,?_,?_⟩
    · exact Can.snd (Can.snd Can.first)
    · exact Can.fst (Can.snd Can.first)
    · exact H.snd.fst
    · exact H.snd.snd.cong (fun _ => rfl) (fun i => (ebb_eq ..).symm)
  -- leftover bits, still on the slots
  have HH : Can m b.B T2 (bundle cl) Y' (fun i => (fleet X Q r (f i)).tape (zQ i)) W :=
    hG.dots_cost.weaken hszQ
  let T3 := Ty.p T2 (bundle cl)
  let A (i) : T T3 := (Y' i,(fleet X Q r (f i)).tape (zQ i))
  have Hg := hG.gather id A (t:=T3) Can.first
  have G : Rig m b.B f T3 A cl X Q r zQ := ⟨Hg.gear,Hg.imag,Can.second⟩
  -- embed the slots into the table of roles; scratch roles are created as zero
  have HE : Can m b.B T3 (bundle cl) A (fun i => (fleet X R r (f i)).tape (Z i)) W :=
    (G.cross_point R (embM e)).weaken hszR
  let T4 := Ty.p T3 (bundle cl)
  let A4 (i) : T T4 := (A i,(fleet X R r (f i)).tape (Z i))
  have Hg4 := G.gather id A4 (t:=T4) Can.first
  have G4 : Rig m b.B f T4 A4 cl X R r Z := ⟨Hg4.gear,Hg4.imag,Can.second⟩
  -- NEW: the BLOCK word on the table of roles
  have Hy := G4.sweepB n τ Q hQ hk
    (fun rk h1 h2 i => by rw [book_len,hq]; exact hc rk h1 h2 i) w hP
  -- extract the slots; scratch roles are dropped
  let T5 := Ty.p T4 (bundle cl)
  let A5 (i) : T T5 := (A4 i,(fleet X R r (f i)).tape (coastline r (f i) p (Z i)))
  have Hg5 := G4.gather id A5 (t:=T5) Can.first
  have G5 : Rig m b.B f T5 A5 cl X R r (fun i => coastline r (f i) p (Z i)) :=
    ⟨Hg5.gear,Hg5.imag,Can.second⟩
  have HX : Can m b.B T5 (bundle cl) A5 (fun i => (fleet X Q r (f i)).tape (O i)) W :=
    (G5.cross_point Q (extM e)).weaken hszQ
  have heq (i) : O i = ebb X r (f i) (k i) (hq i) (whole (k i) (v i)) :=
    amplifiesS X r (f i) (k i) (hq i) e he p hw (v i)
  have ha (i) : (fleet X Q r (f i)).tape (O i) =
      (sim Q (k i)).tape (whole (k i) (v i)) := by
    rw [heq]; exact ebb_eq ..
  have Ho := ((Hy.weaken hszR (fun _ => le_rfl)).save_keep
    (Able.of_can (b:=b) HX)).cong (fun _ => rfl) ha
  have Hx := (Able.of_can (b:=b) hmp).save_keep
    ((Able.of_can (b:=b) hmx).save_keep ((Able.of_can (b:=b) HH).save_keep
      ((Able.of_can (b:=b) HE).save_keep Ho)))
  simpa only [Nat.zero_add,Nat.add_zero] using Hx

end

/-! ## Closing the recursion -/

section
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]

/-- Parameters of the open-code guarantee: the handler must serve every sub-order
`rk * (k/u)`, `1 ≤ rk < u`. -/
structure DescB (cl : Paint) (u a : ℕ) (Q : Layout σ) where
  k : ℕ
  v : Sim σ k → ℂ
  use : Handler (hatch cl)
  tau : ℕ → ℕ
  peak : ℕ
  works : threshold u a ≤ k → ∀ rk, 1 ≤ rk → rk < u →
    ∀ (v : Sim σ (rk*(k/u))→ℂ), (use (loaded cl Q (rk*(k/u)) v)).OK
      ((sim Q (rk*(k/u))).tape (whole (rk*(k/u)) v)) (tau rk) peak

def fundsB (cl : Paint) (u a : ℕ) (Q : Layout σ) :
    Bank (hatch cl) (DescB cl u a Q) := ⟨fun i => 2^i.k, DescB.peak, DescB.use⟩

def chargingB {cl u a} {Q : Layout σ} (N : ℕ → ℕ) (i : DescB cl u a Q) :=
  if threshold u a ≤ i.k then ∑ rk : Fin u, N rk * batchesB u a rk i.k * i.tau rk else 0

lemma rec_bodyB (cl : Paint) (m : Bool) (X : Layout α) (R : Layout ρ) (Q : Layout σ)
    (e : σ → ρ) (he : Function.Injective e) (u a : ℕ)
    (hX : X.n=u) (hu : 3≤u) (hQ : Q.n=2^a) (w : BWord α ρ)
    (hw : LiveKernel e w.flat) (hP : w.Proper u) :
    let B := fundsB cl u a Q
    Able m B (simIn cl) (bundle cl) (fun i => loaded cl Q i.k i.v)
      (fun i => (sim Q i.k).tape (whole i.k i.v)) B.B (chargingB w.hist) := by
  intro B
  let Y := DescB cl u a Q
  let K := threshold u a
  let x (i : Y) := loaded cl Q i.k i.v
  have hx : Can m B.B (simIn cl) Ty.w x (fun i => i.k) B.B := Can.first
  have hQpos : 0<Q.n := by rw [hQ]; positivity
  apply Able.branch (hx.wlt (Can.wc K)) (fun i => K ≤ i.k)
    (fun i => by split <;> omega)
  -- big k. split according to r
  · let G := {i : Y // K ≤ i.k}
    let g (i : G) := i.1.k%u
    have hd (i : G) : g i<u := Nat.mod_lt _ (by omega)
    have hw' : Small (fun i : G => B.B i.1) g :=
      (Small.const _ u).mono (fun i => (hd i).le)
    apply Able.dispatch (n:=g) u ((hx.reindex (fun i : G => i.1)).wmod (Can.wc u) hw') hd
    intro r hr
    let L := {i : G // g i=r}
    let l (i : L) : Y := i.1.1
    let T0 := B.comap l
    let k (i : L) := (l i).k
    let f (i : L) := k i/u
    let n (rk : ℕ) (i : L) := batchesB u a rk (k i)
    let τ (rk : ℕ) (i : L) := (l i).tau rk
    have HH (i : L) : threshold u a ≤ k i := i.1.2
    have HK (rk : ℕ) (h1 : 1 ≤ rk) (h2 : rk < X.n) :
        Contract cl T0 (fun i => rk * f i) (τ rk) Q :=
      fun i => (l i).works (HH i) rk h1 (hX ▸ h2)
    have H := amplifyB (k:=k) (f:=f) m T0 (fun i => (l i).v)
      X R Q e he r (by omega) (fun i => by
        have h := Nat.div_add_mod (k i) u
        have hj : k i%u=r := i.2
        rw [hX,← hj]; exact h
        ) (by omega) hQpos n τ
      (fun rk _ h2 i => by
        change batchesB u a rk (k i)*(Q.n*2^(rk * (k i/u)))=2^k i
        rw [hQ]
        exact rounds_eqB u a _ rk hu (HH i) (hX ▸ h2)) HK (Small.self _) w hw
      (hX ▸ hP)
    exact H.mono (fun _ => le_rfl) (fun i => by
      change _ ≤ chargingB w.hist (l i)
      have hi : threshold u a ≤ (l i).k := HH i
      rw [chargingB, if_pos hi, BWord.cost_eq_sum u _ w hP]
      apply le_of_eq
      apply Finset.sum_congr rfl
      intro rk _
      rw [Nat.mul_assoc])
  · let L := {i : Y // ¬ K ≤ i.k}
    have hl (i : L) : i.1.k<K := Nat.lt_of_not_ge i.2
    apply Able.dispatch K (hx.reindex (fun i : L => i.1)) hl
    intro j hj
    let T0 := {i : L // i.1.k=j}
    let l (i : T0) := i.1.1
    let Q' := B.comap l
    have H := almost_fixed m (fun i => Q'.B i) (fun i => Q'.B i) cl
      (fun i => (l i).k) j (fun i => i.2) Q (fun i => (l i).v)
    exact (Able.of_can (b:=Q') H).mono (fun _ => le_rfl) (fun _ => Nat.zero_le _)

/-- **Recursion closed for block words (with scratch roles).**  One fixed program; its work on
an input of order `k` is at most `Const * allotB u a w.hist k`, where every block of rank `rk`
of the word costs `2^(k - rk*(k/u) - a)` recursive calls of order `rk * (k/u)`. -/
theorem recurse_runB (cl : Paint) (m : Bool) (X : Layout α) (R : Layout ρ) (Q : Layout σ)
    (e : σ → ρ) (he : Function.Injective e) (u a : ℕ)
    (hX : X.n=u) (hu : 3≤u) (hQ : Q.n=2^a) (w : BWord α ρ)
    (hw : LiveKernel e w.flat) (hP : w.Proper u) {ι : Type*}
    (k : ι→ℕ) (v : ∀ i,Sim σ (k i)→ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl) (fun i => loaded cl Q (k i) (v i))
      (fun i => (sim Q (k i)).tape (whole (k i) (v i)))
      (fun i => allotB u a w.hist (k i)) := by
  obtain ⟨body,C,d,hc⟩ := rec_bodyB cl m X R Q e he u a hX hu hQ w hw hP
  let N := w.hist
  let maxwork (k : ℕ) := allotB u a N k
  let c := 3*C+3
  let base : Prog m (simIn cl) (bundle cl) := .comp (.atom .snd) (.atom .snd)
  let fn := depthRun (base.run ()) body.run
  let P k := (2^k+2)^(d+1)
  have h (n : ℕ) (j : ℕ) (hj : j<n) (v : Sim σ j → ℂ) :
      (fn n (loaded cl Q j v)).OK ((sim Q j).tape (whole j v)) (c*maxwork j) (max (P j) n) := by
    induction n generalizing j with
    | zero => omega
    | succ n ih =>
      let peak := max (P j) (n+1)
      let tau (rk : ℕ) := c*maxwork (rk*(j/u))
      have pp (h : threshold u a ≤ j) (rk : ℕ) (_ : 1 ≤ rk) (h2 : rk < u)
          (v : Sim σ (rk*(j/u))→ℂ) :
          (fn n (loaded cl Q (rk*(j/u)) v)).OK
            ((sim Q (rk*(j/u))).tape (whole (rk*(j/u)) v)) (tau rk) peak := by
        have hi := sub_order_lt (down_lt hu h) h2
        have he := ih (rk*(j/u)) (by omega) v
        apply he.mono le_rfl
        have hh : 2^(rk*(j/u)) ≤ 2^j := Nat.pow_le_pow_right (by omega) hi.le
        exact max_le_max (by unfold P; gcongr) (by omega)
      let i : DescB cl u a Q := ⟨j,v,fn n,tau,peak,pp⟩
      have ht := hc i
      have H := ht.pay (t:=1) (z:=n+1) (le_trans
        (le_max_right (P j) (n+1))
        (show peak ≤ (fundsB cl u a Q).cap d i from le_max_right _ _))
      apply H.mono
      · change C*(2^j+1)+chargingB N i +1 ≤ c*allotB u a N j
        have hh : 1 ≤ 2^j := Nat.one_le_pow j 2 (by omega)
        have hs : C*(2^j+1)+1 ≤ c*2^j := calc
          C*(2^j+1)+1 ≤ C*(2^j+2^j)+2^j := by gcongr
          _ ≤ _ := by
            dsimp [c]
            simp only [_root_.mul_add, _root_.add_mul]
            nlinarith
        unfold chargingB
        by_cases ha : threshold u a≤j
        · have hd : threshold u a ≤ i.k := ha
          rw [allotB_big u a N j hu ha, if_pos hd]
          change C*(2^j+1)+(∑ rk : Fin u, N rk * batchesB u a rk j *
            (c*allotB u a N (rk*(j/u))))+1 ≤ _
          have he : (∑ rk : Fin u, N rk * batchesB u a rk j * (c*allotB u a N (rk*(j/u))))
              = c*(∑ rk : Fin u, N rk * batchesB u a rk j * allotB u a N (rk*(j/u))) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro rk _
            ring
          rw [he, _root_.mul_add c]; omega
        · have hd : ¬threshold u a ≤ i.k := ha
          rw [allotB_small u a N j ha, if_neg hd, Nat.add_zero]
          exact hs
      · change max _ peak ≤ peak
        apply max_le _ le_rfl
        exact (Small.pow_mono_degree (2^j) (show d≤d+1 by omega)).trans
          (le_max_left _ _)
  let W i := maxwork (k i)
  let B i := 2^k i
  let x i := loaded cl Q (k i) (v i)
  let X1 i : Ty.T (Ty.p Ty.w (simIn cl)) := (k i+1,x i)
  have L : Can m B (Ty.p Ty.w (simIn cl)) (bundle cl)
      X1 (fun i => (sim Q (k i)).tape (whole (k i) (v i))) W := by
    refine ⟨.descend base body,c+1,d+1,fun i => ?_⟩
    have hh := h (k i+1) (k i) (by omega) (v i)
    have hg : k i+1 ≤ P (k i) :=
      calc
        _ ≤ 2^(k i) := Nat.lt_two_pow_self
        _ ≤ (2^k i + 2)^1 := by simp
        _ ≤ _ := Small.pow_mono_degree _ (by omega)
    have H := hh.pay (t:=1) (z:=k i+1) (le_max_right ..)
    apply H.mono
    · change c*W i+1 ≤ _
      simp [_root_.add_mul, _root_.mul_add]
      omega
    · exact max_le (le_max_left ..) (hg.trans (le_max_left ..))
  have hsmall : Small B k :=
    (Small.self B).mono (fun i => Nat.lt_two_pow_self.le)
  have HE : Can m B (simIn cl) (Ty.p Ty.w (simIn cl)) x X1 W := by
    exact ((show Can m B (simIn cl) Ty.w x k W from Can.first).plus (Can.wc 1) hsmall
      (Small.const ..)).pair Can.id
  exact HE.then_do L

end

end
end PowerSaving.RAM
end OAI

#print axioms OAI.PowerSaving.RAM.amplifyB
#print axioms OAI.PowerSaving.RAM.recurse_runB
