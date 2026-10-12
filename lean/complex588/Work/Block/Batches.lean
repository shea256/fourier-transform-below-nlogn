import Work.Block.Address
import Work.Block.Word

/-!
# Block moves, part 5: one block move = ONE family of recursive calls of order `rk*f`

(agent key: block-engine).  Generalises sections 1-2 of `Work/Scratch/Engine.lean`
(`fillS`, `yieldTapeS`, `fillS_result`, `fill_readS`, `fill_readyS`, `direction_getS`,
`open_dirS`, `open_moveS`, `sweepS`), which are themselves upstream's
`RecursiveBatches.lean` / `RecursiveContract.lean` with a separate batch layout.

A block of rank `rk` on role `l` cuts the array of `l` into fibres of `2^(rk*f)` entries
(`Split.peel`), hands every `Q.n = 2^a` fibres to one recursive call of order `rk*f`
(`fillB`), and reads the answers back (`yieldTapeB`, `direction_getB`).

Main statements:
* `Rig.open_blockB`   one block move, cost `n * τ` with `n` = number of batches and `τ` = cost
                      of one call of order `rk*f`;
* `Rig.sweepB`        a whole block word, cost = sum over its blocks (`BWord.cost`).
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset
noncomputable section

/-! ## 1. Batches for a block -/

section
variable {α β ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- A matrix applied to the array of one role, on a grid with leftover bits. -/
def ferryM [DecidableEq ρ] (r f : ℕ) (l : ρ) (N : CMat α) (v : Grain α ρ r f) :
    Grain α ρ r f :=
  fun x => roleAct f l N (fun i j => v (i,x.2.1,j)) x.1 x.2.2

variable {rk : ℕ}

/-- Source data for one recursive call of order `rk*f`: the batch slots `σ` receive
fibres of role `l`. -/
def fillB (l : ρ) (S : Split α β (Fin rk)) {r f t : ℕ} (X' : Layout β)
    (Q : Layout σ) (h : t*Q.n=(book X' r f).n)
    (v : Grain α ρ r f) (b : Fin t) : Sim σ (rk*f) → ℂ :=
  fun (k,i) => v (l,(S.peel r f).symm ((cut r f t X' Q h) (b,k),i))

/-- Collection of returned answers. -/
def yieldTapeB (l : ρ) (S : Split α β (Fin rk)) {r f t} (X' : Layout β)
    (Q : Layout σ) (h : t*Q.n=(book X' r f).n) (v : Grain α ρ r f) : Tape (Tape ℂ) :=
  (Layout.std t).tape fun b =>
    (sim Q (rk*f)).tape (whole (rk*f) (fillB l S X' Q h v b))

lemma fillB_result [DecidableEq ρ] (l : ρ) (S : Split α β (Fin rk)) {r f t}
    (X' : Layout β) (Q : Layout σ) h (v : Grain α ρ r f) (a : Grid α r f) :
    let q := S.peel r f a
    let w := (cut r f t X' Q h).symm q.1
    ferryM r f l (S.lift (kernel (Fin rk))) v (l,a) =
      whole (rk*f) (fillB l S X' Q h v w.1) (w.2,q.2) := by
  intro q w
  unfold ferryM roleAct
  simp only [ite_true]
  have H := S.act r f (fun p => v (l,p)) a
  refine H.trans ?_
  unfold whole fillB
  simp only [q,w,Prod.mk.eta,Equiv.apply_symm_apply]

end

section
universe U
variable {α β ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype ρ] [DecidableEq ρ]
variable {ι : Type U}
variable {m : Bool} {B f n : ι → ℕ} {s : Ty} {x : ι → T s}
    {cl : Paint} {X : Layout α} {R : Layout ρ} {r : ℕ} {v : ∀ i, Grain α ρ r (f i)}

namespace Rig
variable (h : Rig m B f s x cl X R r v)
include h

lemma simSmallB (Q : Layout σ) (rk : ℕ) : Small B fun i => (sim Q (rk * f i)).n :=
  (Small.const B Q.n).mul (h.gear.boundB rk)

lemma simSizeB (Q : Layout σ) (rk : ℕ) : Knows m B s x fun i => (sim Q (rk * f i)).n :=
  Can.times (Can.wc Q.n) (h.gear.powerB rk) (Small.const B Q.n) (h.gear.boundB rk)

variable (l : ρ) {rk : ℕ} (S : Split α β (Fin rk)) (X' : Layout β) (Q : Layout σ)
variable (hg : ∀ i, n i*Q.n = (book X' r (f i)).n)
include hg

lemma batchSmallB (hr : 0<Q.n) :
    Small B n :=
  (h.gear.grid_small X' r).mono (fun i => by
    rw [← hg]
    exact Nat.le_mul_of_pos_right _ hr)

lemma batchSizeB (hr : 0<Q.n) :
    Knows m B s x n :=
  ((h.gear.grid_size X' r).dvdW (Can.wc Q.n) (h.gear.grid_small X' r)).cong
    (fun _ => rfl) (fun i => by rw [← hg]; exact Nat.mul_div_cancel _ hr)

lemma fill_readB (hQ : 0<Q.n) (a : ∀ i, Sim σ (rk * f i)) (b : ∀ i, Fin (n i))
    (hd : Knows m B s x fun i => (sim Q (rk * f i)).loc (a i))
    (ha : Knows m B s x fun i => (b i).val) :
    Has m B s (c cl) x fun i => fillB l S X' Q (hg i) (v i) (b i) (a i) := by
  let L i := bits (rk * f i)
  have hu := Can.addr_high (u:=a) (L:=fun _ => Q) (R:=L) hd (h.gear.powerB rk)
    (h.simSmallB Q rk)
  have hw := Can.addr_low (u:=a) (L:=fun _ => Q) (R:=L) hd (h.gear.powerB rk)
    (h.simSmallB Q rk)
  let C i := cut r (f i) (n i) X' Q (hg i)
  let K i : Grid β r (f i) × Bits (rk * f i) :=
    (C i (b i,(a i).1),(a i).2)
  have hs := Can.addr_join (L:=fun i => Layout.std (n i)) (R:=fun _ => Q)
    (u:=fun i => (b i,(a i).1)) ha hu (Can.wc Q.n)
    (h.batchSmallB X' Q hg hQ) (Small.const B Q.n)
  have hm : Knows m B s x fun i => (book X' r (f i)).loc (K i).1 :=
    hs.cong (fun _ => rfl) (fun i => (cut_eq r (f i) (n i) X' Q _ _).symm)
  have hk := h.gear.to_gridB X r S X' K hm hw
  exact h.read (fun i => (l,(S.peel r (f i)).symm (K i))) (Can.wc (R.loc l)) hk

lemma fill_readyB (hQ : 0<Q.n) (b : ∀ i, Fin (n i))
    (ha : Knows m B s x fun i => (b i).val) :
    Can m B s (simIn cl) x
      (fun i => loaded cl Q (rk * f i) (fillB l S X' Q (hg i) (v i) (b i)))
      (fun i => (sim Q (rk * f i)).n) := by
  let W i := (sim Q (rk * f i)).n
  let V (i : ι) := fillB l S X' Q (hg i) (v i) (b i)
  have hd : Can m B s (bundle cl) x (fun i => (sim Q (rk * f i)).tape (V i)) W := by
    let S' := Σ i, Sim σ (rk * f i)
    let env (d : S') : T (p s w) := (x d.1,(sim Q (rk * f d.1)).loc d.2)
    have G := h.gather (fun d : S' => d.1) env (t:=p s w) Can.first
    have hh := G.fill_readB l S X' Q (n:=fun d=>n d.1) (fun d => hg d.1) hQ
      (fun d => d.2) (fun d => b d.1) Can.second
      (Can.first.then_do (ha.reindex (Sigma.fst (β:=fun i => Sim σ (rk * f i)))))
    have ht := Can.layout (t:=c cl) (P:=fun _ => 0)
      (L:=fun i => sim Q (rk * f i)) (v:=V) (h.simSizeB Q rk) hh (h.simSmallB Q rk)
    simpa [W] using ht
  exact ((h.gear.givenB rk).mono (fun i => Nat.zero_le (W i))).pair
    ((h.imag.mono (fun i => Nat.zero_le (W i))).pair hd)

/-- Compute the outcome of a block move from the packed answers (and from unchanged roles). -/
lemma direction_getB
    (H : Has m B s (Ty.a (bundle cl)) x fun i => yieldTapeB l S X' Q (hg i) (v i))
    (a : ∀ i, Beach α ρ r (f i)) (ha : Knows m B s x fun i => (fleet X R r (f i)).loc (a i)) :
    Has m B s (c cl) x fun i =>
      ferryM r (f i) l (S.lift (kernel (Fin rk))) (v i) (a i) := by
  obtain ⟨hx,hy⟩ := h.addrs a ha
  let C i := cut r (f i) (n i) X' Q (hg i)
  let K i := S.peel r (f i) (a i).2
  let Q' i := (C i).symm (K i).1
  let Y i := ((Layout.std (n i)).pair Q).loc (Q' i)
  obtain ⟨hd,he⟩ := h.gear.from_gridB X r S X' (fun i => (a i).2) hy
  have hY : Knows m B s x Y :=
    hd.cong (fun _ => rfl) (fun i => uncut_eq r (f i) (n i) X' Q _ (K i).1)
  have ls : Small B fun i => n i * Q.n :=
    (h.gear.grid_small X' r).mono (fun i => le_of_eq (hg i))
  have hA := Can.addr_high (L:=fun i => Layout.std (n i)) (R:=fun _ => Q)
    (u:=Q') hY (Can.wc Q.n) ls
  have hB := Can.addr_low (L:=fun i => Layout.std (n i)) (R:=fun _ => Q)
    (u:=Q') hY (Can.wc Q.n) ls
  let F i b := fillB l S X' Q (hg i) (v i) b
  have hD := Can.fetch (t:=bundle cl) (L:=fun i => Layout.std (n i))
    (i:=fun i => (Q' i).1)
    (v:=fun i b => (sim Q (rk * f i)).tape (whole (rk * f i) (F i b))) H hA
  have hh := Can.fetch (t:=c cl) (L:=fun i => sim Q (rk * f i))
    (i:=fun i => ((Q' i).2,(K i).2)) (v:=fun i => whole (rk * f i) (F i (Q' i).1))
    hD (Can.addr_join (L:=fun _ => Q) (R:=fun i => bits (rk * f i))
      (u:=fun i => ((Q' i).2,(K i).2))
      hB he (h.gear.powerB rk) (Small.const B Q.n) (h.gear.boundB rk))
  apply Can.cases_code (q:=fun i => (a i).1) R hx
  intro r'
  by_cases hL : r'=l
  · refine (hh.reindex (fun i : {i // (a i).1=r'} => i.val)).cong (fun _ => rfl)
      (fun i => ?_)
    have ht := fillB_result l S (t:=n i.val)
      X' Q (hg i.val) (v i.val) (a i.val).2
    have hC : (l,(a i.val).2) = (a i.val) := Prod.ext (i.property.trans hL).symm rfl
    exact ht.symm.trans (congr_arg _ hC)
  · refine ((h.read a hx hy).reindex (fun i : {i // (a i).1=r'} => i.val)).cong
      (fun _ => rfl) (fun i => ?_)
    have H : (a i.val).1≠l := fun hh => hL (i.property.symm.trans hh)
    simp only [ferryM,roleAct, H,ite_false, Prod.mk.eta]

end Rig
end

/-! ## 2. Running a block word -/

section
universe U
variable {α β ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype ρ] [DecidableEq ρ]
variable {ι : Type U}
variable {m : Bool} {f : ι → ℕ} {s : Ty} {x : ι → T s}
    {cl : Paint} {X : Layout α} {R : Layout ρ} {r : ℕ} {v : ∀ i, Grain α ρ r (f i)}
    {b : Bank (hatch cl) ι}

/-- The action of one letter of a block word on a grid with leftover bits. -/
def ferryB (r f : ℕ) (mv : BMove α ρ) (v : Grain α ρ r f) : Grain α ρ r f :=
  fun x => mv.act f (fun i j => v (i,x.2.1,j)) x.1 x.2.2

omit [Fintype β] [DecidableEq β] in
theorem coast_flat_cons (r f : ℕ) (mv : BMove α ρ) (w : BWord α ρ) (v : Grain α ρ r f) :
    coastline r f (BWord.flat (mv :: w)) v = coastline r f w.flat (ferryB r f mv v) := by
  funext y
  unfold coastline
  rw [walk_flat_cons]
  rfl

namespace Rig
variable (h : Rig m b.B f s x cl X R r v)
include h

/-- **One block move.**  `n i` batches, each one recursive call of order `rk * f i`
costing `τ i`. -/
lemma open_blockB {n τ : ι → ℕ} (Q : Layout σ) (hQ : 0<Q.n) {rk : ℕ}
    (S : Split α β (Fin rk)) (X' : Layout β) (hX' : X'.n + rk = X.n)
    (hk : Contract cl b (fun i => rk * f i) τ Q)
    (hg : ∀ i, n i*(sim Q (rk * f i)).n=(book X r (f i)).n)
    (l : ρ) :
    Able m b s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape
        (ferryM r (f i) l (S.lift (kernel (Fin rk))) (v i)))
      (fun i => (fleet X R r (f i)).n) (fun i => n i*τ i) := by
  have he (i) : n i * Q.n=(book X' r (f i)).n := by
    have hz := hg i
    change n i*(Q.n*2^(rk * f i)) = 2^r*(2^f i)^X.n at hz
    change n i * Q.n = 2^r*(2^f i)^X'.n
    have h1 : (2^f i)^X.n = (2^f i)^X'.n * 2^(rk * f i) := by
      rw [← hX', pow_add, ← pow_mul (2:ℕ) (f i) rk, Nat.mul_comm (f i) rk]
    rw [h1, ← mul_assoc, ← mul_assoc] at hz
    exact Nat.eq_of_mul_eq_mul_right (by positivity) hz
  let w i := (fleet X R r (f i)).n
  let y i := yieldTapeB l S X' Q (he i) (v i)
  let sz i := (sim Q (rk * f i)).n
  let Tt := a (bundle cl)
  have hl : 0 < R.n := lt_of_le_of_lt (Nat.zero_le _) (R.bd l)
  have hy : Able m b s Tt x y w (fun i => n i*τ i) := by
    let arg (i) (k : Fin (n i)) := fillB l S X' Q (he i) (v i) k
    let g (i) (k : Fin (n i)) := (sim Q (rk * f i)).tape (whole (rk * f i) (arg i k))
    let I (i : ι) := Fin (n i)
    let E0 (d : Σ i, I i) := (x d.1,(d.2:ℕ))
    have hs : Able m (b.comap (Sigma.fst (β:=I))) (p s Ty.w) (bundle cl)
        E0 (fun d => g d.1 d.2) (fun d => sz d.1) (fun d => τ d.1) := by
      have HH := h.gather (Sigma.fst (β:=I)) E0 (t:=p s Ty.w) Can.first
      have Hp := HH.fill_readyB l S X' Q (n:=fun d=> n d.1) (fun d => he d.1) hQ
        (fun d : Σ i,I i => d.2) Can.second
      have Hq : Able m (b.comap (Sigma.fst (β:=I))) (p s Ty.w) (simIn cl) E0
          (fun d => loaded cl Q (rk * f d.1) (arg d.1 d.2))
          (fun d => sz d.1) (fun _ => 0) := Able.of_can Hp
      have HG := Hq.comp (Able.use_call (ι:=Σ i,I i) (s:=simIn cl) (t:=bundle cl) (m:=m)
        (b:=b.comap (Sigma.fst (β:=I))) (Z:=fun d => τ d.1) (y:=fun d => g d.1 d.2)
        (fun d => hk d.1 (arg d.1 d.2)))
      simpa [Nat.zero_add] using HG
    have HT : Able m b s Ty.w x n (fun _=>0) (fun _=>0) :=
      Able.of_can (h.batchSizeB X' Q he hQ)
    have HH := Able.layout (L:=fun i => Layout.std (n i)) (v:=g) (t:=bundle cl)
      (P:=sz) (H:=τ) HT hs (h.batchSmallB X' Q he hQ)
    refine HH.weaken ⟨2,fun i => ?_⟩ ?_
    · change 0+n i+n i*sz i+1 ≤ _
      have hj := hg i
      have hsz : sz i>0 := Nat.mul_pos hQ (by change 0<2^(rk * f i); positivity)
      have hy : n i*sz i ≤ w i :=
        calc
          _ = (book X r (f i)).n := hj
          _ ≤ R.n*(book X r (f i)).n := Nat.le_mul_of_pos_left _ hl
          _ = _ := rfl
      have gr : n i ≤ n i*sz i := Nat.le_mul_of_pos_right _ hsz
      omega
    · intro i; change 0+n i*τ i ≤ n i*τ i; omega
  let K := fun i => ferryM r (f i) l (S.lift (kernel (Fin rk))) (v i)
  have hh :
      Can m b.B (p s Tt) (bundle cl)
        (fun i => (x i,y i)) (fun i => (fleet X R r (f i)).tape (K i)) w := by
    let s' := p s Tt
    let env i : T s' := (x i,y i)
    have h' : Rig m b.B f s' env cl X R r v := h.gather id env Can.first
    refine h'.chart _ ?_
    let I (i : ι) := Beach α ρ r (f i)
    let u (d : Σ i, I i) : T (p s' Ty.w) := (env d.1,(fleet X R r (f d.1)).loc d.2)
    have HG := h'.gather (Sigma.fst (β:=I)) u (t:=p s' Ty.w) Can.first
    exact HG.direction_getB l S X' Q (n:=fun d => n d.1) (fun d => he d.1)
      (Can.snd Can.first) (fun d => d.2) Can.second
  exact hy.save_keep (Able.of_can hh)

omit [Fintype β] [DecidableEq β] in
/-- One letter of a block word.  `n rk i` = number of batches of a rank-`rk` block,
`τ rk i` = cost of one call of order `rk * f i`. -/
lemma open_moveB (n τ : ℕ → ι → ℕ) (Q : Layout σ) (hQ : 0<Q.n)
    (hk : ∀ rk, 1 ≤ rk → rk < X.n → Contract cl b (fun i => rk * f i) (τ rk) Q)
    (hg : ∀ rk, 1 ≤ rk → rk < X.n → ∀ i,
      n rk i*(sim Q (rk * f i)).n=(book X r (f i)).n)
    (mv : BMove α ρ) (hp : mv.Proper X.n) :
    Able m b s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape (ferryB r (f i) mv (v i)))
      (fun i => (fleet X R r (f i)).n) (fun i => mv.cost (fun rk => n rk i * τ rk i)) := by
  cases mv with
  | localM M =>
    exact (show Able _ b _ _ _ _ _ _ from Able.of_can (b:=b) (h.point_cost M))
  | shift l z =>
    exact (show Able _ b _ _ _ _ _ _ from Able.of_can (b:=b) (h.shift_cost l z))
  | block l rk z ind =>
    obtain ⟨h1, h2⟩ : 1 ≤ rk ∧ rk < X.n := hp
    obtain ⟨S, hS⟩ := exists_split z ind
    let X' := Layout.someLayout (Fin (Fintype.card α - rk))
    have hX' : X'.n + rk = X.n := by
      have e1 : X'.n = Fintype.card α - rk := by
        rw [← Layout.card X']; simp
      have e2 : Fintype.card α = X.n := Layout.card X
      omega
    have H := h.open_blockB (n:=n rk) (τ:=τ rk) Q hQ S X' hX' (hk rk h1 h2) (hg rk h1 h2) l
    have hM : blockMat z = S.lift (kernel (Fin rk)) := blockMat_eq_lift S z hS
    refine H.cong (fun _ => rfl) (fun i => ?_)
    rw [← hM]
    rfl

omit [Fintype β] [DecidableEq β] in
/-- **A whole block word**: cost = sum over its blocks. -/
lemma sweepB (n τ : ℕ → ι → ℕ) (Q : Layout σ) (hQ : 0<Q.n)
    (hk : ∀ rk, 1 ≤ rk → rk < X.n → Contract cl b (fun i => rk * f i) (τ rk) Q)
    (hg : ∀ rk, 1 ≤ rk → rk < X.n → ∀ i,
      n rk i*(sim Q (rk * f i)).n=(book X r (f i)).n)
    (P : BWord α ρ) (hP : P.Proper X.n) :
    Able m b s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape (coastline r (f i) P.flat (v i)))
      (fun i => (fleet X R r (f i)).n)
      (fun i => P.cost (fun rk => n rk i * τ rk i)) := by
  induction P generalizing s v with
  | nil =>
    have ht := h.items.mono (W':=fun i => (fleet X R r (f i)).n) (fun _ => Nat.zero_le _)
    have hz := Able.of_can (b:=b) ht
    simp only [BWord.cost_nil]
    exact hz
  | cons g pth ih =>
    let v' i := ferryB r (f i) g (v i)
    let env i : T (Ty.p s (bundle cl)) := (x i,(fleet X R r (f i)).tape (v' i))
    have hk' := h.gather id env (t:=Ty.p s (bundle cl)) Can.first
    have hl : Rig m b.B f (Ty.p s (bundle cl)) env cl X R r v' :=
      ⟨hk'.gear,hk'.imag,Can.second⟩
    have hh := ih hl hP.tail
    have H := (h.open_moveB (b:=b) n τ Q hQ hk hg g hP.head).save_keep hh
    simpa only [coast_flat_cons, BWord.cost_cons] using H

end Rig
end

end
end PowerSaving.RAM
end OAI

#print axioms OAI.PowerSaving.RAM.Rig.open_blockB
#print axioms OAI.PowerSaving.RAM.Rig.sweepB
