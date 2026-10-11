import OAI.Computability.FourierTransform.Main

/-!
# Scratch file (key: scratch-arrays): the family-130 tensor engine with scratch roles

Checked ONLY with `lake env lean` (single file).  Nothing upstream is modified.  No `sorry`.

## Where upstream forces "arbitrary data in every role"

Upstream's engine (`recurse_run`, RecursionBounds.lean:112) uses ONE role layout `R` for two
different jobs:

* the table on which the certificate word acts (`fleet X R r f`, one array per role);
* the shape of a recursive call (`sim R f`, RecursiveBatches.lean:10): to apply one
  directional move to role `l`, the array of `l` is cut into fibres and every `R.n` fibres
  are handed to one recursive call (`cut`/`fill`, RecursiveBatches.lean:24-51).

A child's roles are therefore not "its own" roles: they are `R.n` unrelated fibres of the
parent's role `l`, all of which are real data that must come back transformed
(`Contract`, RecursiveContract.lean:13: `∀ v`, output `whole` = kernel on every role).
The child then reads that batch, with no copying, as its own table of roles
(`ebb_eq`, TensorRecursion.lean:20), so the word has to give the kernel on every role for
arbitrary data (`certificate`, TensorCertificate.lean:189).

## The extension proved here

The two layouts are separated.  The word acts on roles `ρ` (layout `R`, any size).  A
recursive call is a batch of `Q.n = 2^a` fibres indexed by a second type `σ` ("live slots"),
embedded in the roles by an injective `e : σ → ρ`.  Roles outside the range of `e` are
SCRATCH.  At every level the program

1. reads the incoming batch as a table on the slots, applies the leftover-bit step;
2. NEW: builds the table on the roles, live roles copied, scratch roles zero (`cross_point`);
3. runs the word on that table; every directional move, on a live or on a scratch role,
   is `2^(k-k/u-a)` recursive calls on batches of `2^a` fibres (`sweepS`);
4. NEW: copies the live roles back and drops the scratch roles (`cross_point`).

Scratch never crosses a call boundary, so nothing has to be restored.  The word only needs

  `LiveKernel e p`:  for every input that is zero on scratch, `walk f p v (e l)` is the
  kernel of `v (e l)` for every live slot `l`.

Main results (all without `sorry`, axioms `propext, Classical.choice, Quot.sound`):

* `recurse_runS`            the recursion, work `allot u a (tally p)` with `2^a` = LIVE slots
                            and `tally p` = ALL directional moves (live and scratch roles);
* `engine_all_scratch`, `engine_program_scratch`
                            same conclusion as upstream `hills_all` / `hills_program`, from
                            `LiveKernel e p` and `tally p / 2^a < u^z`;
* `hills_program_via_scratch` upstream's `hills_program` is the instance `σ = ρ`, `e = id`;
* `allotC_bound`            the recurrence bound with any per-level linear overhead;
* `LiveKernel.iff_erase_first`, `no_erase_first`
                            zero-initialising scratch is a free `localM` move under the new
                            contract and impossible (as a first move) under upstream's;
* `Route`, `Route.gate`, `Route.on_role`, `Route.of_path`, `LiveKernel.of_route`
                            bookkeeping for words that copy / overwrite / erase roles;
* `endpoint_reversible` (2 moves) vs `endpoint_by_copy` (1 move)
                            the two-stage endpoint correction per bank pair;
* `two_stage_rate_28`, `two_stage_rate_33`, `two_stage_h24_if_word`
                            arithmetic for the REPORTED two-stage counts at `h = 24`, and the
                            engine conclusion CONDITIONAL on a word with those counts.

NOT proved here: that any two-stage word exists.  No network is constructed in this file.
Whole-block recursion (one call per residual block) is not touched.

Sections 1, 2, 5 are copies of upstream proofs with the batch layout renamed (`R` ↦ `Q`);
sections 3, 4 contain the new steps; `envelope`, `total_envelope`, `project_env`,
`log_le_of_pow_le`, `rate_of_counts` are copied from
checks/wht3/saving/EngineOfCertificate.lean.
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset
noncomputable section

/-! ## 1. Batches with their own layout (copy of RecursiveBatches.lean:46-192) -/

section
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α]

/-- Source data for one recursive call: the batch slots `σ` receive fibres of role `l`. -/
def fillS (l : ρ) (j : α) (z : Space α) {r f t : ℕ} (X : Layout (Minus j))
    (Q : Layout σ) (h : t*Q.n=(book X r f).n)
    (v : Grain α ρ r f) (b : Fin t) : Sim σ f → ℂ :=
  fun (k,i) => v (l,(peelBook j z r f).symm
    ((cut r f t X Q h) (b,k),i))

/-- Collection of returned answers. -/
def yieldTapeS (l : ρ) (j : α) (z : Space α) {r f t} (X : Layout (Minus j))
    (Q : Layout σ) (h : t*Q.n=(book X r f).n) (v : Grain α ρ r f) : Tape (Tape ℂ) :=
  (Layout.std t).tape fun b =>
    (sim Q f).tape (whole f (fillS l j z X Q h v b))

lemma fillS_result [Fintype ρ] [DecidableEq ρ] (l : ρ) (j : α) (z : Space α)
    (hz : z j=1) (hn : z≠0) {r f t} (X : Layout (Minus j)) (Q : Layout σ) h
    (v : Grain α ρ r f) (a : Grid α r f) :
    let q := peelBook j z r f a
    let w := (cut r f t X Q h).symm q.1
    ferry r f (.dir l z hn) v (l,a) = whole f (fillS l j z X Q h v w.1) (w.2,q.2) := by
  intro q w
  unfold ferry Move.go roleAct
  simp only [ite_true]
  have H := peel_act j z hz r f (fun p => v (l,p)) a
  refine H.trans ?_
  unfold whole fillS
  simp only [q,w,Prod.mk.eta,Equiv.apply_symm_apply]

end

section
universe U
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
variable {ι : Type U}
variable {m : Bool} {B f n : ι → ℕ} {s : Ty} {x : ι → T s}
    {cl : Paint} {X : Layout α} {R : Layout ρ} {r : ℕ} {v : ∀ i, Grain α ρ r (f i)}

namespace Rig
variable (h : Rig m B f s x cl X R r v)
include h

lemma simSmallS (Q : Layout σ) : Small B fun i => (sim Q (f i)).n :=
  (Small.const B Q.n).mul h.gear.bound

lemma simSizeS (Q : Layout σ) : Knows m B s x fun i => (sim Q (f i)).n :=
  Can.times (Can.wc Q.n) h.gear.power (Small.const B Q.n) h.gear.bound

variable (l : ρ) (j : α) (z : Space α) (X' : Layout (Minus j)) (Q : Layout σ)
variable (hg : ∀ i, n i*Q.n = (book X' r (f i)).n)
include hg

lemma batchSmallS (hr : 0<Q.n) :
    Small B n :=
  (h.gear.grid_small X' r).mono (fun i => by
    rw [← hg]
    exact Nat.le_mul_of_pos_right _ hr)

lemma batchSizeS (hr : 0<Q.n) :
    Knows m B s x n :=
  ((h.gear.grid_size X' r).dvdW (Can.wc Q.n) (h.gear.grid_small X' r)).cong
    (fun _ => rfl) (fun i => by rw [← hg]; exact Nat.mul_div_cancel _ hr)

lemma fill_readS (hQ : 0<Q.n) (a : ∀ i, Sim σ (f i)) (b : ∀ i, Fin (n i))
    (hd : Knows m B s x fun i => (sim Q (f i)).loc (a i))
    (ha : Knows m B s x fun i => (b i).val) :
    Has m B s (c cl) x fun i => fillS l j z X' Q (hg i) (v i) (b i) (a i) := by
  let L i := bits (f i)
  have hu := Can.addr_high (u:=a) (L:=fun _ => Q) (R:=L) hd h.gear.power (h.simSmallS Q)
  have hw := Can.addr_low (u:=a) (L:=fun _ => Q) (R:=L) hd h.gear.power (h.simSmallS Q)
  let C i := cut r (f i) (n i) X' Q (hg i)
  let K i : Grid (Minus j) r (f i) × Bits (f i) :=
    (C i (b i,(a i).1),(a i).2)
  have hs := Can.addr_join (L:=fun i => Layout.std (n i)) (R:=fun _ => Q)
    (u:=fun i => (b i,(a i).1)) ha hu (Can.wc Q.n)
    (h.batchSmallS j X' Q hg hQ) (Small.const B Q.n)
  have hm : Knows m B s x fun i => (book X' r (f i)).loc (K i).1 :=
    hs.cong (fun _ => rfl) (fun i => (cut_eq r (f i) (n i) X' Q _ _).symm)
  have hk := h.gear.to_grid X r j X' z K hm hw
  exact h.read (fun i => (l,(peelBook j z r (f i)).symm (K i))) (Can.wc (R.loc l)) hk

lemma fill_readyS (hQ : 0<Q.n) (b : ∀ i, Fin (n i))
    (ha : Knows m B s x fun i => (b i).val) :
    Can m B s (simIn cl) x
      (fun i => loaded cl Q (f i) (fillS l j z X' Q (hg i) (v i) (b i)))
      (fun i => (sim Q (f i)).n) := by
  let W i := (sim Q (f i)).n
  let V (i : ι) := fillS l j z X' Q (hg i) (v i) (b i)
  have hd : Can m B s (bundle cl) x (fun i => (sim Q (f i)).tape (V i)) W := by
    let S := Σ i, Sim σ (f i)
    let env (d : S) : T (p s w) := (x d.1,(sim Q (f d.1)).loc d.2)
    have G := h.gather (fun d : S => d.1) env (t:=p s w) Can.first
    have hh := G.fill_readS l j z X' Q (n:=fun d=>n d.1) (fun d => hg d.1) hQ
      (fun d => d.2) (fun d => b d.1) Can.second
      (Can.first.then_do (ha.reindex (Sigma.fst (β:=fun i => Sim σ (f i)))))
    have ht := Can.layout (t:=c cl) (P:=fun _ => 0)
      (L:=fun i => sim Q (f i)) (v:=V) (h.simSizeS Q) hh (h.simSmallS Q)
    simpa [W] using ht
  exact (h.gear.given.mono (fun i => Nat.zero_le (W i))).pair
    ((h.imag.mono (fun i => Nat.zero_le (W i))).pair hd)

-- compute a directional outcome from the packed answers (and from unchanged roles)
lemma direction_getS (hn : z≠0) (hz : z j=1)
    (H : Has m B s (Ty.a (bundle cl)) x fun i => yieldTapeS l j z X' Q (hg i) (v i))
    (a : ∀ i, Beach α ρ r (f i)) (ha : Knows m B s x fun i => (fleet X R r (f i)).loc (a i)) :
    Has m B s (c cl) x fun i => ferry r (f i) (.dir l z hn) (v i) (a i) := by
  obtain ⟨hx,hy⟩ := h.addrs a ha
  let C i := cut r (f i) (n i) X' Q (hg i)
  let K i := peelBook j z r (f i) (a i).2
  let Q' i := (C i).symm (K i).1
  let Y i := ((Layout.std (n i)).pair Q).loc (Q' i)
  obtain ⟨hd,he⟩ := h.gear.from_grid X r j X' z (fun i => (a i).2) hy
  have hY : Knows m B s x Y :=
    hd.cong (fun _ => rfl) (fun i => uncut_eq r (f i) (n i) X' Q _ (K i).1)
  have ls : Small B fun i => n i * Q.n :=
    (h.gear.grid_small X' r).mono (fun i => le_of_eq (hg i))
  have hA := Can.addr_high (L:=fun i => Layout.std (n i)) (R:=fun _ => Q)
    (u:=Q') hY (Can.wc Q.n) ls
  have hB := Can.addr_low (L:=fun i => Layout.std (n i)) (R:=fun _ => Q)
    (u:=Q') hY (Can.wc Q.n) ls
  let F i b := fillS l j z X' Q (hg i) (v i) b
  have hD := Can.fetch (t:=bundle cl) (L:=fun i => Layout.std (n i))
    (i:=fun i => (Q' i).1) (v:=fun i b => (sim Q (f i)).tape (whole (f i) (F i b))) H hA
  have hh := Can.fetch (t:=c cl) (L:=fun i => sim Q (f i))
    (i:=fun i => ((Q' i).2,(K i).2)) (v:=fun i => whole (f i) (F i (Q' i).1))
    hD (Can.addr_join (L:=fun _ => Q) (R:=fun i => bits (f i)) (u:=fun i => ((Q' i).2,(K i).2))
      hB he h.gear.power (Small.const B Q.n) h.gear.bound)
  apply Can.cases_code (q:=fun i => (a i).1) R hx
  intro r'
  by_cases hL : r'=l
  · refine (hh.reindex (fun i : {i // (a i).1=r'} => i.val)).cong (fun _ => rfl)
      (fun i => ?_)
    have ht := fillS_result l j z hz hn (t:=n i.val)
      X' Q (hg i.val) (v i.val) (a i.val).2
    have hC : (l,(a i.val).2) = (a i.val) := Prod.ext (i.property.trans hL).symm rfl
    exact ht.symm.trans (congr_arg _ hC)
  · refine ((h.read a hx hy).reindex (fun i : {i // (a i).1=r'} => i.val)).cong
      (fun _ => rfl) (fun i => ?_)
    have H : (a i.val).1≠l := fun hh => hL (i.property.symm.trans hh)
    simp only [ferry,Move.go,roleAct, H,ite_false, Prod.mk.eta]

end Rig
end

/-! ## 2. Running a word whose directional moves call batches of shape `Q`
(copy of RecursiveContract.lean:25-130; `Contract` itself is upstream's, taken at `Q`) -/

section
universe U
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
variable {ι : Type U}
variable {m : Bool} {f n τ : ι → ℕ} {s : Ty} {x : ι → T s}
    {cl : Paint} {X : Layout α} {R : Layout ρ} {r : ℕ} {v : ∀ i, Grain α ρ r (f i)}
    {b : Bank (hatch cl) ι}

namespace Rig
variable (h : Rig m b.B f s x cl X R r v)
include h

lemma open_dirS (Q : Layout σ) (hQ : 0<Q.n) (hk : Contract cl b f τ Q)
    (hg : ∀ i, n i*(sim Q (f i)).n=(book X r (f i)).n)
    (l : ρ) (z : Space α) (hz : z≠0) :
    Able m b s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape (ferry r (f i) (.dir l z hz) (v i)))
      (fun i => (fleet X R r (f i)).n) (fun i => n i*τ i) := by
  obtain ⟨j,hj⟩ := choose_pivot hz
  let X' := Layout.someLayout (Minus j)
  have he (i) : n i * Q.n=(book X' r (f i)).n := by
    have hy : X'.n+1=X.n := by
      rw [← Layout.card X',← Layout.card X]; exact card_minus j
    have hz := hg i
    change n i*(Q.n*2^f i) = 2^r*(2^f i)^X.n at hz
    change n i * Q.n = 2^r*(2^f i)^X'.n
    rw [← hy,pow_succ, ← mul_assoc, ← mul_assoc] at hz
    exact Nat.eq_of_mul_eq_mul_right (by positivity) hz
  let w i := (fleet X R r (f i)).n
  let y i := yieldTapeS l j z X' Q (he i) (v i)
  let sz i := (sim Q (f i)).n
  let Tt := a (bundle cl)
  have hl : 0 < R.n := lt_of_le_of_lt (Nat.zero_le _) (R.bd l)
  have hy : Able m b s Tt x y w (fun i => n i*τ i) := by
    let arg (i) (k : Fin (n i)) := fillS l j z X' Q (he i) (v i) k
    let g (i) (k : Fin (n i)) := (sim Q (f i)).tape (whole (f i) (arg i k))
    let I (i : ι) := Fin (n i)
    let E0 (d : Σ i, I i) := (x d.1,(d.2:ℕ))
    have hs : Able m (b.comap (Sigma.fst (β:=I))) (p s Ty.w) (bundle cl)
        E0 (fun d => g d.1 d.2) (fun d => sz d.1) (fun d => τ d.1) := by
      have HH := h.gather (Sigma.fst (β:=I)) E0 (t:=p s Ty.w) Can.first
      have Hp := HH.fill_readyS l j z X' Q (n:=fun d=> n d.1) (fun d => he d.1) hQ
        (fun d : Σ i,I i => d.2) Can.second
      have Hq : Able m (b.comap (Sigma.fst (β:=I))) (p s Ty.w) (simIn cl) E0
          (fun d => loaded cl Q (f d.1) (arg d.1 d.2))
          (fun d => sz d.1) (fun _ => 0) := Able.of_can Hp
      have HG := Hq.comp (Able.use_call (ι:=Σ i,I i) (s:=simIn cl) (t:=bundle cl) (m:=m) (b:=b.comap (Sigma.fst (β:=I))) (Z:=fun d => τ d.1) (y:=fun d => g d.1 d.2)
        (fun d => hk d.1 (arg d.1 d.2)))
      simpa [Nat.zero_add] using HG
    have HT : Able m b s Ty.w x n (fun _=>0) (fun _=>0) :=
      Able.of_can (h.batchSizeS j X' Q he hQ)
    have HH := Able.layout (L:=fun i => Layout.std (n i)) (v:=g) (t:=bundle cl)
      (P:=sz) (H:=τ) HT hs (h.batchSmallS j X' Q he hQ)
    refine HH.weaken ⟨2,fun i => ?_⟩ ?_
    · change 0+n i+n i*sz i+1 ≤ _
      have hj := hg i
      have hsz : sz i>0 := Nat.mul_pos hQ (by change 0<2^(f i); positivity)
      have hy : n i*sz i ≤ w i :=
        calc
          _ = (book X r (f i)).n := hj
          _ ≤ R.n*(book X r (f i)).n := Nat.le_mul_of_pos_left _ hl
          _ = _ := rfl
      have gr : n i ≤ n i*sz i := Nat.le_mul_of_pos_right _ hsz
      omega
    · intro i; change 0+n i*τ i ≤ n i*τ i; omega
  let K := fun i => ferry r (f i) (.dir l z hz) (v i)
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
    exact HG.direction_getS l j z X' Q (n:=fun d => n d.1) (fun d => he d.1) hz hj
      (Can.snd Can.first) (fun d => d.2) Can.second
  exact hy.save_keep (Able.of_can hh)

lemma open_moveS (Q : Layout σ) (hQ : 0<Q.n) (hk : Contract cl b f τ Q)
    (hg : ∀ i, n i*(sim Q (f i)).n=(book X r (f i)).n)
    (z : Move α ρ) :
    Able m b s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape (ferry r (f i) z (v i)))
      (fun i => (fleet X R r (f i)).n) (fun i => toll z * n i * τ i) := by
  cases z with
  | localM M =>
    simpa [toll,Nat.zero_mul] using
      (show Able _ b _ _ _ _ _ _ from Able.of_can (b:=b) (h.point_cost M))
  | shift r z =>
    simpa [toll,Nat.zero_mul] using
      (show Able _ b _ _ _ _ _ _ from Able.of_can (b:=b) (h.shift_cost r z))
  | dir l z hz => simpa [toll,one_mul] using h.open_dirS Q hQ hk hg l z hz

lemma sweepS (Q : Layout σ) (hQ : 0<Q.n) (hk : Contract cl b f τ Q)
    (hg : ∀ i, n i*(sim Q (f i)).n=(book X r (f i)).n)
    (P : PWord α ρ) :
    Able m b s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape (coastline r (f i) P (v i)))
      (fun i => (fleet X R r (f i)).n) (fun i => tally P * n i * τ i) := by
  induction P generalizing s v with
  | nil =>
    have ht := h.items.mono (W':=fun i => (fleet X R r (f i)).n) (fun _ => Nat.zero_le _)
    have hz := Able.of_can (b:=b) ht
    -- coast nil
    have hg (i j) : coastline r (f i) [] (v i) j=v i j := rfl
    simp only [tally,List.map_nil,List.sum_nil, Nat.zero_mul]
    exact hz
  | cons g pth ih =>
    let v' i := ferry r (f i) g (v i)
    let env i : T (Ty.p s (bundle cl)) := (x i,(fleet X R r (f i)).tape (v' i))
    have hk' := h.gather id env (t:=Ty.p s (bundle cl)) Can.first
    have hl : Rig m b.B f (Ty.p s (bundle cl)) env cl X R r v' :=
      ⟨hk'.gear,hk'.imag,Can.second⟩
    have hh := ih hl
    have H := (h.open_moveS (b:=b) (τ:=τ) Q hQ hk hg g).save_keep hh
    simpa only [coast_cons,tally,List.map_cons,List.sum_cons,_root_.add_mul] using H

end Rig
end

/-! ## 3. New steps: moving between a table on the slots `σ` and a table on the roles `ρ` -/

section
variable {α ρ σ : Type*}

/-- A rectangular role map: target role `d` is the `M d`-combination of the source roles. -/
def crossAct [Fintype ρ] (r f : ℕ) (M : Matrix σ ρ ℚ) (v : Grain α ρ r f) : Grain α σ r f :=
  fun d => ∑ j, (M d.1 j : ℂ) * v (j,d.2)

/-- Embedding of the live slots into the roles (scratch roles receive zero). -/
def embM [DecidableEq ρ] (e : σ → ρ) : Matrix ρ σ ℚ := fun s l => if e l = s then 1 else 0
/-- Extraction of the live slots from the roles (scratch roles are dropped). -/
def extM [DecidableEq ρ] (e : σ → ρ) : Matrix σ ρ ℚ := fun l s => if s = e l then 1 else 0

lemma crossAct_emb [Fintype σ] [DecidableEq σ] [DecidableEq ρ] (e : σ → ρ)
    (he : Function.Injective e) (r f : ℕ) (v : Grain α σ r f) (l : σ) (a : Grid α r f) :
    crossAct r f (embM e) v (e l,a) = v (l,a) := by
  unfold crossAct embM
  rw [sum_eq_single l]
  · simp
  · intro j _ hj
    have : e j ≠ e l := fun h => hj (he h)
    simp [this]
  · simp

lemma crossAct_emb_off [Fintype σ] [DecidableEq ρ] (e : σ → ρ) (r f : ℕ)
    (v : Grain α σ r f) (s : ρ) (hs : ∀ l, e l ≠ s) (a : Grid α r f) :
    crossAct r f (embM e) v (s,a) = 0 := by
  unfold crossAct embM
  apply sum_eq_zero
  intro j _
  simp [hs j]

lemma crossAct_ext [Fintype ρ] [DecidableEq ρ] (e : σ → ρ) (r f : ℕ)
    (v : Grain α ρ r f) (l : σ) (a : Grid α r f) :
    crossAct r f (extM e) v (l,a) = v (e l,a) := by
  unfold crossAct extM
  rw [sum_eq_single (e l)]
  · simp
  · intro j _ hj; simp [hj]
  · simp

end

section
universe U V
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
variable {ι : Type U}
variable {m : Bool} {B f : ι → ℕ} {s : Ty} {x : ι → T s}
    {cl : Paint} {X : Layout α} {R : Layout ρ} {r : ℕ} {v : ∀ i, Grain α ρ r (f i)}

/-- RAM cost of a rectangular role map: linear in the size of the target table
(modelled on upstream `Rig.chart` + `Rig.ferry_point`, RoleArrays.lean:83-107). -/
lemma Rig.cross_point (h : Rig m B f s x cl X R r v) [Fintype σ] [DecidableEq σ]
    (Q : Layout σ) (M : Matrix σ ρ ℚ) :
    Can m B s (a (c cl)) x
      (fun i => (fleet X Q r (f i)).tape (crossAct r (f i) M (v i)))
      (fun i => (fleet X Q r (f i)).n) := by
  have hsize : Knows m B s x fun i => (fleet X Q r (f i)).n :=
    (Can.wc Q.n).times (h.gear.grid_size X r) (Small.const B Q.n) (h.gear.grid_small X r)
  have hlarge : Small B fun i => (fleet X Q r (f i)).n :=
    (Small.const B Q.n).mul (h.gear.grid_small X r)
  let S := Σ i, Beach α σ r (f i)
  let env (d : S) : T (p s w) := (x d.1,(fleet X Q r (f d.1)).loc d.2)
  have hg := h.gather (fun d : S => d.1) env (t:=p s w) Can.first
  have ha : Knows m (fun d : S => B d.1) (p s w) env
      (fun d => (fleet X Q r (f d.1)).loc d.2) := Can.second
  have hl : Knows m (fun d : S => B d.1) (p s w) env (fun d => Q.loc d.2.1) :=
    Can.addr_high (u:=fun d : S => d.2) (L:=fun _ => Q) (R:=fun d : S => book X r (f d.1))
      ha (hg.gear.grid_size X r) (hlarge.reindex (fun d : S => d.1))
  have hk : Knows m (fun d : S => B d.1) (p s w) env
      (fun d => (book X r (f d.1)).loc d.2.2) :=
    Can.addr_low (u:=fun d : S => d.2) (L:=fun _ => Q) (R:=fun d : S => book X r (f d.1))
      ha (hg.gear.grid_size X r) (hlarge.reindex (fun d : S => d.1))
  have ht : Has m (fun d : S => B d.1) (p s w) (c cl) env
      (fun d => crossAct r (f d.1) M (v d.1) d.2) := by
    change Can m _ _ (c cl) env (fun d => ∑ j, (M d.2.1 j : ℂ) * v d.1 (j,d.2.2)) _
    apply Can.sum_cconst
    intro j
    have hx : Has m (fun d : S => B d.1) (p s w) sc env (fun d => (M d.2.1 j : ℂ)) := by
      apply Can.cases_code (q:=fun d : S => d.2.1) Q hl
      intro l
      convert (Can.rat (B:=fun i : {d : S // d.2.1=l} => B i.1.1) (s:=p s w)
        (x:=fun i => env i.1) (m:=m) (W:=fun _ => 0) (M l j)) using 1
      funext i; rw [i.2]
    exact hx.mul (hg.read (fun d => (j,d.2.2)) (Can.wc (R.loc j)) hk)
  have H := Can.layout (t:=c cl) (P:=fun _ => 0)
    (L:=fun i => fleet X Q r (f i)) (v:=fun i => crossAct r (f i) M (v i)) hsize ht hlarge
  simpa only [Nat.zero_add,Nat.mul_zero,Nat.add_zero] using H

end

/-! ## 4. The scratch certificate and one level of the recursion -/

section
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

/-- **Scratch certificate.**  `e` embeds the live slots `σ` into the roles `ρ`; every role
outside the range of `e` is scratch.  The word has to produce the kernel on the live roles
only, and only for inputs whose scratch roles are zero.  Nothing is required of the scratch
roles at the end (they are dropped). -/
def LiveKernel (e : σ → ρ) (p : PWord α ρ) : Prop :=
  ∀ (f : ℕ) (v : Data α ρ f), (∀ s, (∀ l, e l ≠ s) → v s = 0) →
    ∀ l, walk f p v (e l) = matAct f (kernel α) (v (e l))

/-- Upstream's contract (kernel on every role, arbitrary data) is the case `e = id`. -/
lemma LiveKernel.of_full (p : PWord α ρ)
    (hp : ∀ f v, walk f p v = multiAct f (fun _ => kernel α) v) :
    LiveKernel (id : ρ → ρ) p :=
  fun f v _ l => congrFun (hp f v) l

variable [Fintype σ] [DecidableEq σ]

/-- Semantic step (replaces upstream `amplifies`, TensorRecursion.lean:33): embed the slots,
run the word on the table of roles, extract the slots. -/
lemma amplifiesS (X : Layout α) (r f k : ℕ) (h : X.n*f+r=k) (e : σ → ρ)
    (he : Function.Injective e) (p : PWord α ρ) (hp : LiveKernel e p)
    (v : Sim σ k → ℂ) :
    let eQ := ebb X r f k h v
    let zQ : Grain α σ r f := fun i => chords r f (fun j => eQ (i.1,j)) i.2
    crossAct r f (extM e) (coastline r f p (crossAct r f (embM e) zQ)) =
      ebb X r f k h (whole k v) := by
  intro eQ zQ
  funext i
  obtain ⟨l,a⟩ := i
  rw [crossAct_ext]
  unfold coastline
  rw [hp f _ (fun s hs => funext fun j => crossAct_emb_off e r f zQ s hs (a.1,j)) l]
  have hz : (fun j => crossAct r f (embM e) zQ (e l,a.1,j)) = fun j => zQ (l,a.1,j) :=
    funext fun j => crossAct_emb e he r f zQ l (a.1,j)
  rw [hz]
  exact (ripple_grid X r f h (fun j => v (l,j)) a).symm

end

section
universe U
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]
variable {ι : Type U} {m : Bool}
    {k f n τ : ι → ℕ} {cl : Paint} {b : Bank (hatch cl) ι}
    {v : ∀ i, Sim σ (k i)→ℂ}

/-- One level with scratch roles (replaces upstream `amplify`, TensorRecursion.lean:54).
Input and output are tables on the slots `σ` only; the table on the roles `ρ` exists only
inside this level. -/
lemma amplifyS (m : Bool) (b : Bank (hatch cl) ι) (v : ∀ i, Sim σ (k i) → ℂ)
    (X : Layout α) (R : Layout ρ) (Q : Layout σ) (e : σ → ρ) (he : Function.Injective e)
    (r : ℕ) (hr : 3 ≤ X.n) (hq : ∀ i, X.n*f i+r=k i) (hd : r < X.n) (hQ : 0<Q.n)
    (hc : ∀ i, n i*(sim Q (f i)).n=2^k i)
    (hk : Contract cl b f τ Q)
    (hB : Small b.B (fun i => 2^k i))
    (p : PWord α ρ) (hp : LiveKernel e p) :
    Able m b (simIn cl) (bundle cl) (fun i => loaded cl Q (k i) (v i))
      (fun i => (sim Q (k i)).tape (whole (k i) (v i)))
      (fun i => 2^k i) (fun i => tally p*n i*τ i) := by
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
  -- NEW: embed the slots into the table of roles; scratch roles are created as zero
  have HE : Can m b.B T3 (bundle cl) A (fun i => (fleet X R r (f i)).tape (Z i)) W :=
    (G.cross_point R (embM e)).weaken hszR
  let T4 := Ty.p T3 (bundle cl)
  let A4 (i) : T T4 := (A i,(fleet X R r (f i)).tape (Z i))
  have Hg4 := G.gather id A4 (t:=T4) Can.first
  have G4 : Rig m b.B f T4 A4 cl X R r Z := ⟨Hg4.gear,Hg4.imag,Can.second⟩
  -- the word on the table of roles; batches have the shape of the slots
  have Hy := G4.sweepS Q hQ hk (n:=n)
    (fun i => by rw [book_len,hq]; exact hc i) p
  -- NEW: extract the slots; scratch roles are dropped
  let T5 := Ty.p T4 (bundle cl)
  let A5 (i) : T T5 := (A4 i,(fleet X R r (f i)).tape (coastline r (f i) p (Z i)))
  have Hg5 := G4.gather id A5 (t:=T5) Can.first
  have G5 : Rig m b.B f T5 A5 cl X R r (fun i => coastline r (f i) p (Z i)) :=
    ⟨Hg5.gear,Hg5.imag,Can.second⟩
  have HX : Can m b.B T5 (bundle cl) A5 (fun i => (fleet X Q r (f i)).tape (O i)) W :=
    (G5.cross_point Q (extM e)).weaken hszQ
  have heq (i) : O i = ebb X r (f i) (k i) (hq i) (whole (k i) (v i)) :=
    amplifiesS X r (f i) (k i) (hq i) e he p hp (v i)
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

/-! ## 5. Closing the recursion (copy of RecursionBounds.lean:56-193)

`Desc`, `funds`, `charging`, `allot`, `threshold`, `batches`, `rounds_eq` are upstream's,
used with the layout `Q` of the live slots: `2^a` is now the number of LIVE slots. -/

section
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]

lemma rec_bodyS (cl : Paint) (m : Bool) (X : Layout α) (R : Layout ρ) (Q : Layout σ)
    (e : σ → ρ) (he : Function.Injective e) (u a : ℕ)
    (hX : X.n=u) (hu : 3≤u) (hQ : Q.n=2^a) (p : PWord α ρ)
    (hp : LiveKernel e p) :
    let B := funds cl u a Q
    Able m B (simIn cl) (bundle cl) (fun i => loaded cl Q i.k i.v)
      (fun i => (sim Q i.k).tape (whole i.k i.v)) B.B (charging (tally p)) := by
  intro B
  let Y := Desc cl u a Q
  let K := threshold u a
  let x (i : Y) := loaded cl Q i.k i.v
  have hx : Can m B.B (simIn cl) w x (fun i => i.k) B.B := Can.first
  have hQpos : 0<Q.n := by rw [hQ]; positivity
  apply Able.branch (hx.wlt (Can.wc K)) (fun i => K ≤ i.k)
    (fun i => by split <;> omega)
  -- big k. split according to r
  · let G := {i : Y // K ≤ i.k}
    let g (i : G) := i.1.k%u
    have hd (i : G) : g i<u := Nat.mod_lt _ (by omega)
    have hw : Small (fun i : G => B.B i.1) g :=
      (Small.const _ u).mono (fun i => (hd i).le)
    apply Able.dispatch (n:=g) u ((hx.reindex (fun i : G => i.1)).wmod (Can.wc u) hw) hd
    intro r hr
    let L := {i : G // g i=r}
    let l (i : L) : Y := i.1.1
    let T0 := B.comap l
    let k (i : L) := (l i).k
    let f (i : L) := k i/u
    let n (i : L) := batches u a (k i)
    have HH (i : L) : threshold u a ≤ k i := i.1.2
    have HK : Contract cl T0 f (fun i => (l i).tau) Q :=
      fun i => (l i).works (HH i)
    have H := amplifyS (k:=k) (f:=f) (n:=n) m T0 (fun i => (l i).v)
      X R Q e he r (by omega) (fun i => by
        have h := Nat.div_add_mod (k i) u
        have hj : k i%u=r := i.2
        rw [hX,← hj]; exact h
        ) (by omega) hQpos
      (fun i => by
        change batches u a (k i)*(Q.n*2^(k i/u))=2^k i
        rw [hQ]
        exact rounds_eq u a _ hu (HH i)) HK (Small.self _) p hp
    exact H.mono (fun _ => le_rfl) (fun i => by
      change _ ≤ charging (tally p) (l i)
      have hi : threshold u a ≤ (l i).k := HH i
      rw [charging, ite_eq_left hi])
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

/-- **Recursion closed, with scratch roles.**  Same statement as upstream `recurse_run`
except that the word lives on roles `ρ ⊇ e(σ)` and satisfies only `LiveKernel e p`.
The work recurrence is upstream's `allot u a (tally p)` with `2^a` = number of live slots
and `tally p` = ALL directional moves of the word, on live and scratch roles alike. -/
theorem recurse_runS (cl : Paint) (m : Bool) (X : Layout α) (R : Layout ρ) (Q : Layout σ)
    (e : σ → ρ) (he : Function.Injective e) (u a : ℕ)
    (hX : X.n=u) (hu : 3≤u) (hQ : Q.n=2^a) (p : PWord α ρ)
    (hp : LiveKernel e p) {ι : Type*}
    (k : ι→ℕ) (v : ∀ i,Sim σ (k i)→ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl) (fun i => loaded cl Q (k i) (v i))
      (fun i => (sim Q (k i)).tape (whole (k i) (v i)))
      (fun i => allot u a (tally p) (k i)) := by
  obtain ⟨body,C,d,hc⟩ := rec_bodyS cl m X R Q e he u a hX hu hQ p hp
  let D := tally p
  let maxwork (k : ℕ) := allot u a D k
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
      let tau := c*maxwork (j/u)
      have pp (h : threshold u a ≤ j) (v : Sim σ (j/u)→ℂ) :
          (fn n (loaded cl Q (j/u) v)).OK ((sim Q (j/u)).tape (whole (j/u) v)) tau peak := by
        have hi := down_lt hu h
        have he := ih (j/u) (by omega) v
        apply he.mono le_rfl
        have hh : 2^(j/u) ≤ 2^j := Nat.pow_le_pow_right (by omega) hi.le
        exact max_le_max (by unfold P; gcongr) (by omega)
      let i : Desc cl u a Q := ⟨j,v,fn n,tau,peak,pp⟩
      have ht := hc i
      have H := ht.pay (t:=1) (z:=n+1) (le_trans
        (le_max_right (P j) (n+1))
        (show peak ≤ (funds cl u a Q).cap d i from le_max_right _ _))
      -- step.run definition
      apply H.mono
      · change C*(2^j+1)+charging D i +1 ≤ c*allot u a D j
        have hh : 1 ≤ 2^j := Nat.one_le_pow j 2 (by omega)
        have hs : C*(2^j+1)+1 ≤ c*2^j := calc
          C*(2^j+1)+1 ≤ C*(2^j+2^j)+2^j := by gcongr
          _ ≤ _ := by
            dsimp [c]
            simp only [_root_.mul_add, _root_.add_mul]
            nlinarith
        unfold charging
        by_cases ha : threshold u a≤j
        · have hd : threshold u a ≤ i.k := ha
          rw [allot, dite_eq_left ⟨down_lt hu ha,ha⟩, ite_eq_left hd]
          change C*(2^j+1)+D*batches u a j*(c*allot u a D (j/u))+1 ≤ _
          have he : D*batches u a j*(c*allot u a D (j/u))
              = c*(D*batches u a j*allot u a D (j/u)) := by ring
          rw [he, _root_.mul_add c]; omega
        · have hd : ¬threshold u a ≤ i.k := ha
          rw [allot, dite_eq_right (fun hp => ha hp.2), ite_eq_right hd, Nat.add_zero]
          exact hs
      · change max _ peak ≤ peak
        apply max_le _ le_rfl
        exact (Small.pow_mono_degree (2^j) (show d≤d+1 by omega)).trans
          (le_max_left _ _)
  let W i := maxwork (k i)
  let B i := 2^k i
  let x i := loaded cl Q (k i) (v i)
  let X1 i : Ty.T (Ty.p w (simIn cl)) := (k i+1,x i)
  have L : Can m B (Ty.p w (simIn cl)) (bundle cl)
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
  have HE : Can m B (simIn cl) (Ty.p w (simIn cl)) x X1 W := by
    exact ((show Can m B (simIn cl) w x k W from Can.first).plus (Can.wc 1) hsmall (Small.const ..)).pair Can.id
  exact HE.then_do L

end

end
end PowerSaving.RAM
end OAI

/-! ## 6. The engine statements

`envelope`, `total_envelope` and `project_env` are copied verbatim from
checks/wht3/saving/EngineOfCertificate.lean (that file cannot be imported). -/

namespace OAI.PowerSaving
open RAM Cluster

/-- Envelope with an arbitrary exponent; `hills = envelope alpha` (see `hills_eq_envelope`). -/
noncomputable def envelope (z : ℝ) (k : ℕ) : ℕ := Nat.ceil (((k:ℝ)+1)^z)

lemma hills_eq_envelope : hills = envelope alpha := rfl

lemma envelope_pos (z : ℝ) (k : ℕ) : 1 ≤ envelope z k :=
  Nat.one_le_ceil_iff.mpr (by positivity)

/-- Generic form of upstream `total_hills` (TensorSaving.lean:135). -/
lemma total_envelope (u a D : ℕ) (hu : 3 ≤ u) (z : ℝ) (hz : 0 ≤ z)
    (hD : (D:ℝ)/(2:ℝ)^a < (u:ℝ)^z) :
    ∃ c : ℕ, ∀ k : ℕ, RAM.allot u a D k + 1 ≤ c*(2^k*envelope z k + 1) := by
  obtain ⟨C,hC,h⟩ := RAM.allot_bound u a D hu z hz hD
  obtain ⟨c,hc⟩ := exists_nat_ge C
  have ht : 1≤c := Nat.one_le_cast.mp (hC.trans hc)
  refine ⟨c,fun k => ?_⟩
  specialize h k
  have hg : (RAM.allot u a D k : ℝ) ≤ c*((2:ℝ)^k*(envelope z k:ℝ)) := by
    rw [← mul_assoc]
    refine h.trans ?_
    have hh : ((k:ℝ)+1)^z ≤ (envelope z k:ℝ) := Nat.le_ceil _
    gcongr
  have he : RAM.allot u a D k ≤ c*(2^k*envelope z k) := by exact_mod_cast hg
  rw [mul_add,mul_one]
  omega

namespace RAM
open Binary Matrix Ty Finset
universe U

/-- Copy of upstream's private `hills_project` (TensorProgram.lean:30-93) with the envelope
`hills` replaced by an arbitrary `E` with `1 ≤ E k`. -/
private theorem project_env {ρ : Type*} (E : ℕ → ℕ) (hE : ∀ k, 1 ≤ E k)
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

/-- **The engine with scratch roles, all live slots at once.**  Generalises
`engine_all` (and upstream `hills_all`): `σ` = live slots (`2^a` of them), `ρ` = all roles of
the word, `e : σ → ρ` injective; the word only has to satisfy `LiveKernel e p`.  The number
of scratch roles `card ρ - 2^a` is unrestricted and does not enter the rate. -/
theorem engine_all_scratch {α ρ σ : Type} [Fintype α] [DecidableEq α] [Fintype ρ]
    [DecidableEq ρ] [Fintype σ] [DecidableEq σ]
    (u a : ℕ) (hα : Fintype.card α = u) (hσ : Fintype.card σ = 2^a) (hu : 3 ≤ u)
    (e : σ → ρ) (he : Function.Injective e)
    (p : PWord α ρ) (hw : LiveKernel e p)
    (z : ℝ) (hz : 0 ≤ z) (hD : (tally p:ℝ)/(2:ℝ)^a < (u:ℝ)^z)
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
  have h := recurse_runS cl m X R Q e he u a hx hu hq p hw k v
  obtain ⟨c,hc⟩ := total_envelope u a (tally p) hu z hz hD
  exact h.weaken ⟨c,fun i => hc (k i)⟩

/-- **The engine with scratch roles, one array.**  Same conclusion as upstream
`hills_program` (TensorProgram.lean:95) with envelope `⌈(k+1)^z⌉`, from a scratch
certificate: a word on roles `ρ` that produces the kernel on the `2^a` live roles `e(σ)`
whenever the other roles start as zero, with `tally p / 2^a < u^z`. -/
theorem engine_program_scratch {α ρ σ : Type} [Fintype α] [DecidableEq α] [Fintype ρ]
    [DecidableEq ρ] [Fintype σ] [DecidableEq σ]
    (u a : ℕ) (hα : Fintype.card α = u) (hσ : Fintype.card σ = 2^a) (hu : 3 ≤ u)
    (e : σ → ρ) (he : Function.Injective e)
    (p : PWord α ρ) (hw : LiveKernel e p)
    (z : ℝ) (hz : 0 ≤ z) (hD : (tally p:ℝ)/(2:ℝ)^a < (u:ℝ)^z)
    (cl : Paint) (m : Bool) {ι : Type U} (k : ι→ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*envelope z (k i)) := by
  have ht := engine_all_scratch u a hα hσ hu e he p hw z hz hD cl m k
    (fun i (j : Sim σ (k i)) => v i j.2)
  have H : Nonempty σ := Fintype.card_pos_iff.mp (by rw [hσ]; positivity)
  obtain ⟨l⟩ := H
  exact project_env (envelope z) (envelope_pos z) cl m k v (Layout.someLayout σ) l ht

/-- Sanity check 1: with no scratch roles (`σ = ρ`, `e = id`) this is the earlier
`engine_program`; in particular upstream's `hills_program` is the instance
`α = Blocks`, `ρ = σ = Role`, `z = alpha`. -/
theorem hills_program_via_scratch (cl : Paint) (m : Bool) {ι : Type U} (k : ι→ℕ)
    (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*hills (k i)) := by
  obtain ⟨p,hp,hw⟩ := certificate
  have hD : (tally p:ℝ)/(2:ℝ)^50 < (mcol:ℝ)^alpha := by rw [hp]; exact network_rate
  exact engine_program_scratch mcol 50 card_block card_role (by norm_num [mcol])
    id Function.injective_id p (LiveKernel.of_full p hw) alpha alpha_pos.le hD cl m k v

end RAM
end OAI.PowerSaving

/-! ## 7. Certificate side: what a word may do with a scratch role

All statements are about upstream's own word semantics (`walk`, `Move`, DirectionalWords.lean).
No new kind of move is introduced: copying, overwriting and erasing a role are `localM` moves
with a non-invertible rational matrix, which upstream's `Move.localM` already allows and
which cost no directional move.  What upstream's `Path` bookkeeping cannot express is that
such a gate RESETS the frame of the role it overwrites; `Route.gate` below does. -/

namespace OAI.PowerSaving.RAM
open Binary Matrix Finset
noncomputable section
section
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

lemma matAct_zero (f : ℕ) (M : CMat α) : matAct f M (0 : Sky α f → ℂ) = 0 := by
  unfold matAct; exact Matrix.mulVec_zero _

/-- Rational matrix that erases the roles in `Z` and keeps the others. -/
def eraseM (Z : Finset ρ) : Matrix ρ ρ ℚ := fun i j => if i = j ∧ i ∉ Z then 1 else 0

lemma actPoint_erase (Z : Finset ρ) (x : ρ → ℂ) (r : ρ) :
    actPoint (eraseM Z) x r = if r ∈ Z then 0 else x r := by
  unfold actPoint eraseM
  by_cases h : r ∈ Z
  · simp [h]
  · rw [sum_eq_single r]
    · simp [h]
    · intro j _ hj
      have : ¬ r = j := fun g => hj g.symm
      simp [this]
    · simp

lemma walk_erase_first (Z : Finset ρ) (p : PWord α ρ) (f : ℕ) (v : Data α ρ f) :
    walk f (.localM (eraseM Z) :: p) v = walk f p (fun r => if r ∈ Z then 0 else v r) := by
  change walk f p (point f (actPoint (eraseM Z)) v) = _
  congr 1
  funext r i
  change actPoint (eraseM Z) (fun r => v r i) r = _
  rw [actPoint_erase]; split <;> rfl

/-- **Zero-initialisation is free.**  A scratch certificate (kernel on the live roles when
scratch starts as zero) is the same thing as a word that, after one erasing `localM` move
in front, gives the kernel on the live roles for ARBITRARY contents of every role. -/
theorem LiveKernel.iff_erase_first (e : σ → ρ) (Z : Finset ρ)
    (hZ : ∀ s, s ∈ Z ↔ ∀ l, e l ≠ s) (p : PWord α ρ) :
    LiveKernel e p ↔ ∀ (f : ℕ) (v : Data α ρ f) (l : σ),
      walk f (.localM (eraseM Z) :: p) v (e l) = matAct f (kernel α) (v (e l)) := by
  constructor
  · intro hp f v l
    rw [walk_erase_first, hp f _ (fun s hs => by simp [(hZ s).2 hs]) l]
    have : e l ∉ Z := fun h => (hZ _).1 h l rfl
    simp [this]
  · intro h f v hv l
    have hv' : (fun r => if r ∈ Z then 0 else v r) = v := by
      funext r; by_cases hr : r ∈ Z
      · simp [hr, hv r ((hZ r).1 hr)]
      · simp [hr]
    have := h f v l
    rw [walk_erase_first, hv'] at this
    exact this

lemma walk_zero (f : ℕ) (p : PWord α ρ) : walk f p (0 : Data α ρ f) = 0 := by
  induction p with
  | nil => rfl
  | cons mv p ih =>
    change walk f p (mv.go f 0) = 0
    have h0 : mv.go f (0 : Data α ρ f) = 0 := by
      cases mv with
      | localM g =>
        funext r i
        change actPoint g (fun _ => (0:ℂ)) r = 0
        simp [actPoint]
      | dir r z nz =>
        funext j
        change (if j = r then matAct f (Binary.dir z) (0 : Sky α f → ℂ) else 0) = 0
        rw [matAct_zero]; simp
      | shift r z =>
        funext j
        change (if j = r then matAct f (Binary.shift z) (0 : Sky α f → ℂ) else 0) = 0
        rw [matAct_zero]; simp
    rw [h0, ih]

/-- **Under upstream's contract a certificate cannot begin by erasing or overwriting a
role** (not even a spare one): the first gate must be injective.  Contrast with
`LiveKernel.iff_erase_first`: under the scratch contract an erasing first gate is free.
(The same holds for a gate anywhere in a full certificate, because every prefix of an
invertible linear map on a finite-dimensional space is invertible; only the first-gate
case is formalised here.) -/
theorem no_erase_first (g : Matrix ρ ρ ℚ) (p : PWord α ρ)
    (hp : ∀ f v, walk f (.localM g :: p) v = multiAct f (fun _ => kernel α) v)
    (x : ρ → ℂ) (hx : actPoint g x = 0) : x = 0 := by
  let v : Data α ρ 0 := fun r _ => x r
  have h := hp 0 v
  have h0 : walk 0 (.localM g :: p) v = 0 := by
    change walk 0 p (point 0 (actPoint g) v) = 0
    have hz : point 0 (actPoint g) v = 0 := by
      funext r i
      change actPoint g (fun r => x r) r = 0
      rw [hx]; rfl
    rw [hz, walk_zero]
  rw [h0] at h
  funext r
  have hr : (0 : Sky α 0 → ℂ) = matAct 0 (kernel α) (v r) := congrFun h r
  have h2 := congrArg (matAct 0 (unframe (OBase.canonical α) univ)) hr
  rw [matAct_mul, ← frame_univ (OBase.canonical α), unframe_left, matAct_one, matAct_zero] at h2
  exact (congrFun h2 (fun i => i.elim0)).symm

/-- With no scratch roles the scratch certificate is exactly upstream's certificate. -/
theorem LiveKernel.id_iff (p : PWord α ρ) :
    LiveKernel (id : ρ → ρ) p ↔ ∀ f v, walk f p v = multiAct f (fun _ => kernel α) v :=
  ⟨fun h f v => funext fun l => h f v (fun s hs => absurd rfl (hs s)) l,
   LiveKernel.of_full p⟩

/-- A word that carries role `r` from the matrix `S r` to the matrix `T r` while the scalar
network does `g`, using `c` directional moves.  Upstream's `Path` is the special case in
which all matrices are frames of one fixed basis per role, with a mass identity that copies
and erasures do not satisfy. -/
def Route (S T : ρ → CMat α) (g : (ρ→ℂ) → (ρ→ℂ)) (c : ℕ) : Prop :=
  ∃ p : PWord α ρ, tally p = c ∧
    ∀ (f : ℕ) (x : Data α ρ f), walk f p (multiAct f S x) = multiAct f T (point f g x)

namespace Route
variable {S T U : ρ → CMat α}

theorem trans {g h i j} (a : Route S T g i) (b : Route T U h j) :
    Route S U (h ∘ g) (i+j) := by
  obtain ⟨p,hp,ap⟩ := a
  obtain ⟨q,hq,aq⟩ := b
  refine ⟨p++q, by rw [tally_append, hp, hq], ?_⟩
  intro f x
  rw [walk_append, ap, aq]; rfl

/-- Every upstream `Path` is a `Route` (its tally is determined by the mass identity). -/
theorem of_path {A : ρ → OBase α} {s t : ρ → Finset α} {g L}
    (h : Path A s t g L) :
    ∃ c, c + mass s = mass t + 2*L ∧
      Route (fun r => frame (A r) (s r)) (fun r => frame (A r) (t r)) g c := by
  obtain ⟨p,hp,hw⟩ := h
  exact ⟨tally p, hp, p, rfl, hw⟩

/-- **Copy / overwrite / erase gate.**  A point gate may give role `i` a NEW matrix `T i`,
provided every role `j` it reads for `i` currently has that matrix.  A zero row (erase) puts
no condition on `T i`; a row with one foreign entry (copy) gives the copy the matrix of its
source.  Upstream `Path.gate` is the case `T = S`. -/
theorem gate (g : Matrix ρ ρ ℚ) (S T : ρ → CMat α)
    (cond : ∀ i j, g i j ≠ 0 → T i = S j) :
    Route S T (actPoint g) 0 := by
  refine ⟨[.localM g], by simp [tally,toll], ?_⟩
  intro f x
  let M (r : ρ) := digitProd (fun _ : Fin f => S r)
  let N (r : ρ) := digitProd (fun _ : Fin f => T r)
  funext r i
  change ∑ j, (g r j:ℂ)* (∑ a, M j i a * x j a)
    = ∑ a, N r i a * (∑ j, (g r j:ℂ)*x j a)
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro j hj
  by_cases gh : g r j = 0
  · simp [gh]
  · dsimp only [M, N]
    rw [cond r j gh]
    ac_rfl

/-- A word acting on one role only moves the matrix of that role. -/
theorem on_role (S : ρ → CMat α) (r : ρ) (N : CMat α) (c : ℕ)
    (hN : ∃ q : PWord α ρ, tally q = c ∧ ∀ f x, walk f q x = roleAct f r N x) :
    Route S (fun j => if j = r then N * S j else S j) id c := by
  obtain ⟨q,hq,hw⟩ := hN
  refine ⟨q, hq, fun f x => ?_⟩
  have hpt : point f id x = x := rfl
  rw [hw, hpt]
  funext j
  by_cases h : j = r
  · subst h; simp [roleAct, multiAct]
  · simp [roleAct, multiAct, h]

end Route

/-- One directional move (plus a free shift) removes one orthogonal line from a frame:
the matrix `shift z * delta z` is the inverse of `delta z`. -/
lemma down_word (r : ρ) (z : Space α) (hz : dot z z = 1) :
    ∃ q : PWord α ρ, tally q = 1 ∧
      ∀ f (x : Data α ρ f), walk f q x = roleAct f r (shift z * delta z) x := by
  have hn : z ≠ 0 := by
    intro h; rw [h] at hz; simp [dot] at hz
  obtain he|he := lum_of_unit z hz
  · refine ⟨[.dir r z hn,.shift r z], by simp [tally,toll], fun f x => ?_⟩
    change roleAct f r _ (roleAct f r _ x) = _
    rw [roleAct_mul, delta_pos z he]
  · refine ⟨[.dir r z hn], by simp [tally,toll], fun f x => ?_⟩
    change roleAct f r _ x = _
    rw [delta_neg z he, ← mul_assoc, shift_sq, one_mul]

/-- **Assembling a scratch certificate from a route.**  If the route starts from invertible
matrices, ends at `kernel * (start)` on every live role, and its scalar network returns the
live inputs whenever the scratch inputs are zero, its word is a scratch certificate. -/
theorem LiveKernel.of_route (e : σ → ρ) (S S' T : ρ → CMat α) (hS : ∀ r, S r * S' r = 1)
    (g : (ρ→ℂ) → (ρ→ℂ)) (c : ℕ) (h : Route S T g c)
    (hg : ∀ x : ρ → ℂ, (∀ s, (∀ l, e l ≠ s) → x s = 0) → ∀ l, g x (e l) = x (e l))
    (hT : ∀ l, T (e l) = kernel α * S (e l)) :
    ∃ p : PWord α ρ, tally p = c ∧ LiveKernel e p := by
  obtain ⟨p,hp,hw⟩ := h
  refine ⟨p, hp, ?_⟩
  intro f v hv l
  let y : Data α ρ f := multiAct f S' v
  have hy : multiAct f S y = v := by
    funext r; simp [y, multiAct, hS]
  have hy0 (s : ρ) (hs : ∀ l, e l ≠ s) : y s = 0 := by
    change matAct f (S' s) (v s) = 0
    rw [hv s hs]; exact matAct_zero f _
  have hpt : point f g y (e l) = y (e l) := by
    funext i
    exact hg (fun r => y r i) (fun s hs => by rw [hy0 s hs]; rfl) l
  have h1 := congrFun (hw f y) (e l)
  rw [hy] at h1
  rw [h1]
  change matAct f (T (e l)) (point f g y (e l)) = _
  rw [hpt, hT, ← matAct_mul]
  exact congrArg _ (congrFun hy (e l))

end
end
end OAI.PowerSaving.RAM

/-! ## 8. Worked example: the two-stage endpoint correction, with and without a copy

After two shear stages a bank pair is in the state "role `ra` holds scalar `a` at the full
frame (the kernel), role `rb` holds scalar `b` at the frame `univ \ {q}`", and the third
shear `b := b + a` is still owed.  Both roles must keep their matrices.

* `endpoint_reversible`: without scratch, `rb` climbs to the full frame, takes the gate and
  comes back: 2 directional moves.
* `endpoint_by_copy`: with one scratch role, copy `ra`, move THE COPY down one line, add it
  to `rb`, erase the copy: 1 directional move.  The scratch role's contents before and after
  are irrelevant (it is overwritten, then erased). -/

namespace OAI.PowerSaving.RAM
open Binary Matrix Finset
noncomputable section
section
variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

/-- `rt := ra`; every other role unchanged. -/
def copyM (ra rt : ρ) : Matrix ρ ρ ℚ :=
  fun i j => if i = rt then (if j = ra then 1 else 0) else (if i = j then 1 else 0)

/-- `rb := rb + rt`, then `rt := 0`; every other role unchanged. -/
def addEraseM (rb rt : ρ) : Matrix ρ ρ ℚ :=
  fun i j => if i = rt then 0 else
    if i = rb then (if j = rb ∨ j = rt then 1 else 0) else (if i = j then 1 else 0)

/-- `rb := rb + ra`; every other role unchanged. -/
def addM (ra rb : ρ) : Matrix ρ ρ ℚ :=
  fun i j => if i = rb then (if j = rb ∨ j = ra then 1 else 0) else (if i = j then 1 else 0)

lemma sum_ind_left (a : ρ) (x : ρ → ℂ) :
    ∑ j, ((if j = a then (1:ℚ) else 0 : ℚ) : ℂ) * x j = x a := by
  rw [sum_eq_single a]
  · simp
  · intro j _ hj; simp [hj]
  · simp

lemma sum_ind_right (a : ρ) (x : ρ → ℂ) :
    ∑ j, ((if a = j then (1:ℚ) else 0 : ℚ) : ℂ) * x j = x a := by
  rw [sum_eq_single a]
  · simp
  · intro j _ hj; simp [Ne.symm hj]
  · simp

lemma sum_pair_ind (a b : ρ) (hab : a ≠ b) (x : ρ → ℂ) :
    ∑ j, ((if j = a ∨ j = b then (1:ℚ) else 0 : ℚ) : ℂ) * x j = x a + x b := by
  have h (j : ρ) : ((if j = a ∨ j = b then (1:ℚ) else 0 : ℚ) : ℂ) * x j =
      (if j = a then x j else 0) + (if j = b then x j else 0) := by
    by_cases ha : j = a
    · subst ha; simp [hab]
    · by_cases hb : j = b
      · subst hb; simp [ha]
      · simp [ha, hb]
  simp_rw [h]
  rw [sum_add_distrib]
  simp

lemma actPoint_copy (ra rt : ρ) (x : ρ → ℂ) (r : ρ) :
    actPoint (copyM ra rt) x r = if r = rt then x ra else x r := by
  unfold actPoint copyM
  by_cases h : r = rt
  · simp only [h, ↓reduceIte]
    exact sum_ind_left ra x
  · simp only [h, ↓reduceIte]
    exact sum_ind_right r x

lemma actPoint_addErase (rb rt : ρ) (hbt : rb ≠ rt) (x : ρ → ℂ) (r : ρ) :
    actPoint (addEraseM rb rt) x r =
      if r = rt then 0 else if r = rb then x rb + x rt else x r := by
  unfold actPoint addEraseM
  by_cases h : r = rt
  · simp [h]
  · by_cases h' : r = rb
    · subst h'
      simp only [h, ↓reduceIte]
      exact sum_pair_ind r rt hbt x
    · simp only [h, h', ↓reduceIte]
      exact sum_ind_right r x

lemma actPoint_add (ra rb : ρ) (hab : ra ≠ rb) (x : ρ → ℂ) (r : ρ) :
    actPoint (addM ra rb) x r = if r = rb then x rb + x ra else x r := by
  unfold actPoint addM
  by_cases h' : r = rb
  · subst h'
    simp only [↓reduceIte]
    exact sum_pair_ind r ra (Ne.symm hab) x
  · simp only [h', ↓reduceIte]
    exact sum_ind_right r x

/-- One directional move (possibly with a free shift) adds one orthogonal line. -/
lemma up_word (r : ρ) (z : Space α) (hz : dot z z = 1) :
    ∃ q : PWord α ρ, tally q = 1 ∧
      ∀ f (x : Data α ρ f), walk f q x = roleAct f r (delta z) x := by
  have hn : z ≠ 0 := by
    intro h; rw [h] at hz; simp [dot] at hz
  obtain he|he := lum_of_unit z hz
  · refine ⟨[.dir r z hn], by simp [tally,toll], fun f x => ?_⟩
    change roleAct f r _ x = _
    rw [delta_pos z he]
  · refine ⟨[.dir r z hn,.shift r z], by simp [tally,toll], fun f x => ?_⟩
    change roleAct f r _ (roleAct f r _ x) = _
    rw [roleAct_mul, delta_neg z he]

lemma kernel_split (A : OBase α) (q : α) :
    kernel α = delta (A.v q) * frame A (univ \ {q}) := by
  have h := frame_ins A (univ \ {q}) q (by simp)
  have hs : insert q (univ \ ({q}:Finset α)) = univ := by
    ext i; by_cases i=q <;> simp [*]
  rwa [hs, frame_univ] at h

/-- Endpoint correction WITHOUT scratch: 2 directional moves. -/
theorem endpoint_reversible (A : OBase α) (q : α) (ra rb : ρ) (hab : ra ≠ rb)
    (S : ρ → CMat α) (hSa : S ra = kernel α) (hSb : S rb = frame A (univ \ {q})) :
    Route S S (fun x r => if r = rb then x rb + x ra else x r) 2 := by
  let z := A.v q
  have hk : kernel α = delta z * frame A (univ \ {q}) := kernel_split A q
  let S1 : ρ → CMat α := fun j => if j = rb then kernel α else S j
  have h1 := Route.on_role S rb (delta z) 1 (up_word rb z (A.self q))
  have e1 : (fun j => if j = rb then delta z * S j else S j) = S1 := by
    funext j
    by_cases hj : j = rb
    · simp only [S1, hj, ite_true]; rw [hSb, ← hk]
    · simp [S1, hj]
  rw [e1] at h1
  have h2 : Route S1 S1 (actPoint (addM ra rb)) 0 := by
    apply Route.gate
    intro i j hij
    by_cases hb : i = rb
    · have hj : j = rb ∨ j = ra := by
        by_contra hj; apply hij; simp [addM, hb, hj]
      rcases hj with hj|hj
      · rw [hb, hj]
      · simp [S1, hj, hb, hab, hSa]
    · have hj : i = j := by
        by_contra hj; apply hij; simp [addM, hb, hj]
      rw [hj]
  have h3 := Route.on_role S1 rb (shift z * delta z) 1 (down_word rb z (A.self q))
  have e3 : (fun j => if j = rb then shift z * delta z * S1 j else S1 j) = S := by
    funext j
    by_cases hj : j = rb
    · simp only [S1, hj, ite_true]
      rw [hSb, hk, ← mul_assoc, mul_assoc (shift z), delta_sq z (A.self q), shift_sq, one_mul]
    · simp [S1, hj]
  rw [e3] at h3
  have h := (h1.trans h2).trans h3
  have hg : (id ∘ actPoint (addM ra rb) ∘ id : (ρ → ℂ) → ρ → ℂ) =
      fun x r => if r = rb then x rb + x ra else x r := by
    funext x r
    simp only [Function.comp_apply, id]
    exact actPoint_add ra rb hab x r
  rw [hg] at h
  exact h

/-- **Endpoint correction WITH a copy: 1 directional move.**  `rt` is a scratch role; its
matrix `S rt` and its contents are arbitrary before, and it is left erased. -/
theorem endpoint_by_copy (A : OBase α) (q : α) (ra rb rt : ρ) (hbt : rb ≠ rt)
    (S : ρ → CMat α) (hSa : S ra = kernel α) (hSb : S rb = frame A (univ \ {q})) :
    Route S S (fun x r => if r = rt then 0 else if r = rb then x rb + x ra else x r) 1 := by
  let z := A.v q
  have hk : kernel α = delta z * frame A (univ \ {q}) := kernel_split A q
  -- step 1: copy `ra` into the scratch role; the copy takes the matrix of its source
  let S1 : ρ → CMat α := fun j => if j = rt then kernel α else S j
  have h1 : Route S S1 (actPoint (copyM ra rt)) 0 := by
    apply Route.gate
    intro i j hij
    by_cases hi : i = rt
    · have hj : j = ra := by
        by_contra hj; apply hij; simp [copyM, hi, hj]
      simp [S1, hi, hj, hSa]
    · have hj : i = j := by
        by_contra hj; apply hij; simp [copyM, hi, hj]
      simp [S1, hi, ← hj]
  -- step 2: ONE directional move, on the copy
  let S2 : ρ → CMat α := fun j => if j = rt then frame A (univ \ {q}) else S j
  have h2 := Route.on_role S1 rt (shift z * delta z) 1 (down_word rt z (A.self q))
  have e2 : (fun j => if j = rt then shift z * delta z * S1 j else S1 j) = S2 := by
    funext j
    by_cases hj : j = rt
    · simp only [S1, S2, hj, ite_true]
      rw [hk, ← mul_assoc, mul_assoc (shift z), delta_sq z (A.self q), shift_sq, one_mul]
    · simp [S1, S2, hj]
  rw [e2] at h2
  -- step 3: add the copy into `rb` and erase it; the erased role may take any matrix
  have h3 : Route S2 S (actPoint (addEraseM rb rt)) 0 := by
    apply Route.gate
    intro i j hij
    by_cases hi : i = rt
    · exact absurd (by simp [addEraseM, hi]) hij
    · by_cases hb : i = rb
      · have hj : j = rb ∨ j = rt := by
          by_contra hj; apply hij; simp [addEraseM, hb, hj]
        rcases hj with hj|hj
        · simp [S2, hj, hb, hbt]
        · simp [S2, hj, hb, hSb]
      · have hj : i = j := by
          by_contra hj; apply hij; simp [addEraseM, hi, hb, hj]
        simp [S2, ← hj, hi]
  have h := (h1.trans h2).trans h3
  have hg : (actPoint (addEraseM rb rt) ∘ id ∘ actPoint (copyM ra rt) : (ρ → ℂ) → ρ → ℂ) =
      fun x r => if r = rt then 0 else if r = rb then x rb + x ra else x r := by
    funext x r
    simp only [Function.comp_apply, id]
    rw [actPoint_addErase rb rt hbt]
    simp only [actPoint_copy]
    by_cases h1 : r = rt
    · simp [h1]
    · simp [h1, hbt]
  rw [hg] at h
  exact h

end
end
end OAI.PowerSaving.RAM

/-! ## 9. Arithmetic, and the conditional two-stage statement

`log_le_of_pow_le`, `rate_of_counts` are copied verbatim from
checks/wht3/saving/EngineOfCertificate.lean. -/

namespace OAI.PowerSaving
open RAM

lemma log_le_of_pow_le (u c b : ℕ) (hu : 0 < u) (hc : 0 < c) (h : u^c ≤ 2^b) :
    Real.log (u:ℝ) ≤ (b:ℝ)/(c:ℝ) * 0.6931471808 := by
  have hu' : (0:ℝ) < (u:ℝ) := by exact_mod_cast hu
  have hc' : (0:ℝ) < (c:ℝ) := by exact_mod_cast hc
  have h1 : ((u:ℝ))^c ≤ (2:ℝ)^b := by exact_mod_cast h
  have h2 : Real.log (((u:ℝ))^c) ≤ Real.log ((2:ℝ)^b) :=
    Real.log_le_log (by positivity) h1
  rw [Real.log_pow, Real.log_pow] at h2
  have h3 : (b:ℝ) * Real.log 2 ≤ (b:ℝ) * 0.6931471808 :=
    mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le (by positivity)
  rw [div_mul_eq_mul_div, le_div_iff₀ hc']
  nlinarith [h2, h3]

lemma rate_of_counts (u a Δ : ℕ) (L ε : ℝ) (hu : 0 < u) (hε : 0 ≤ ε)
    (hL : Real.log (u:ℝ) ≤ L)
    (hΔ : ε * L * ((2:ℝ)^a * (u:ℝ)) < (Δ:ℝ)) :
    (((2:ℝ)^a * (u:ℝ) - (Δ:ℝ)))/(2:ℝ)^a < (u:ℝ)^(1 - ε) := by
  have hm : (0:ℝ) < (u:ℝ) := by exact_mod_cast hu
  have ht : (u:ℝ) ^ (1 - ε) = (u:ℝ) * Real.exp (-(Real.log (u:ℝ)) * ε) := by
    rw [Real.rpow_def_of_pos hm,
      show Real.log (u:ℝ) * (1 - ε) = Real.log (u:ℝ) + -(Real.log (u:ℝ)) * ε from by ring,
      Real.exp_add, Real.exp_log hm]
  have h1 : 1 - L * ε ≤ -(Real.log (u:ℝ)) * ε + 1 := by nlinarith
  have h2 : (u:ℝ) * (1 - L * ε) ≤ (u:ℝ) ^ (1 - ε) := by
    rw [ht]
    exact mul_le_mul_of_nonneg_left (h1.trans (Real.add_one_le_exp _)) hm.le
  refine lt_of_lt_of_le ?_ h2
  have hp : (0:ℝ) < (2:ℝ)^a := by positivity
  rw [div_lt_iff₀ hp]
  nlinarith

/-- Counts REPORTED for the two-stage complex network at `h = 24`
(Swapnil-jain/integer-mult-kappa, lean/Round6.lean `cx_rank_sum`): `m = 576`,
`W = 207387136` live roles, rank sum `s = 119453132304`.  Lean checks only the arithmetic:
`W m - s = 1858032 = v (v - 2 ((h-1)^2 + h))` with `v = C(24,3) = 2024`, and `W ≤ 2^28`. -/
example : 207387136 * 576 - 119453132304 = 1858032 ∧
    2024 * (2024 - 2*((24-1)^2 + 24)) = 1858032 ∧ Nat.choose 24 3 = 2024 ∧
    207387136 ≤ 2^28 := by
  refine ⟨by norm_num, by norm_num, by decide, by norm_num⟩

set_option exponentiation.threshold 2000 in
/-- Rate inequality for those counts in one `2^28` table (the `2^28 - W` unused live slots
get the plain `m`-move kernel): exponent saving `1.89e-6`. -/
lemma two_stage_rate_28 :
    (((2:ℝ)^28 * ((576:ℕ):ℝ) - ((1858032:ℕ):ℝ)))/(2:ℝ)^28
      < ((576:ℕ):ℝ)^(1 - 189/(10:ℝ)^8) := by
  have hL := log_le_of_pow_le 576 100 917 (by norm_num) (by norm_num) (by norm_num)
  exact rate_of_counts 576 28 1858032 _ (189/(10:ℝ)^8) (by norm_num)
    (by norm_num) hL (by norm_num)

set_option exponentiation.threshold 2000 in
/-- The same with 41 disjoint copies of the network in one `2^33` table (fill `0.990`):
exponent saving `2.42e-6`.  (The limit of many copies is `1858032/(W m ln m) = 2.447e-6`.) -/
lemma two_stage_rate_33 :
    41 * 207387136 ≤ 2^33 ∧
    (((2:ℝ)^33 * ((576:ℕ):ℝ) - ((41*1858032:ℕ):ℝ)))/(2:ℝ)^33
      < ((576:ℕ):ℝ)^(1 - 242/(10:ℝ)^8) := by
  refine ⟨by norm_num, ?_⟩
  have hL := log_le_of_pow_le 576 100 917 (by norm_num) (by norm_num) (by norm_num)
  exact rate_of_counts 576 33 (41*1858032) _ (242/(10:ℝ)^8) (by norm_num)
    (by norm_num) hL (by norm_num)

namespace RAM

/-- The work recurrence with a linear overhead `c * 2^k` per level (creating the table of
roles with zeroed scratch, dropping the scratch, or any other per-level pass). -/
def allotC (u a D c : ℕ) (k : ℕ) : ℕ :=
  if h : k/u<k ∧ threshold u a ≤ k then
    c*2^k + D*batches u a k*allotC u a D c (k/u)
  else c*2^k
termination_by k

lemma allotC_eq (u a D c k : ℕ) : allotC u a D c k = c * allot u a D k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rw [allotC, allot]
    split
    next h => rw [ih _ h.1]; ring
    next => rfl

/-- **Analytic bound for the recurrence of the scratch engine** (style of upstream
`allot_bound`, TensorSaving.lean:11).  `D` = all directional moves of the word (live and
scratch roles), `2^a` = number of LIVE slots, `c` = any per-level linear overhead.  The
exponent `z` is admissible as soon as `D / 2^a < u^z`: neither the number of scratch roles
nor the overhead `c` enters the rate. -/
theorem allotC_bound (u a D c : ℕ) (hu : 3≤u) (z : ℝ) (hz : 0≤z)
    (hD : (D:ℝ)/(2:ℝ)^a < (u:ℝ)^z) :
    ∃ C : ℝ, ∀ k : ℕ, (allotC u a D c k : ℝ) ≤ C*(2:ℝ)^k*((k:ℝ)+1)^z := by
  obtain ⟨C,_,h⟩ := allot_bound u a D hu z hz hD
  refine ⟨c*C, fun k => ?_⟩
  rw [allotC_eq]
  push_cast
  calc (c:ℝ) * (allot u a D k:ℝ) ≤ (c:ℝ) * (C*(2:ℝ)^k*((k:ℝ)+1)^z) :=
        mul_le_mul_of_nonneg_left (h k) (by positivity)
    _ = _ := by ring

/-- If a scratch role had to be handed back clean by REVERSIBLE moves only (no erasure),
the undo word `q` is charged like any other moves: the rate uses `tally p + tally q`. -/
lemma tally_with_undo {α ρ : Type*} (p q : Binary.PWord α ρ) :
    Binary.tally (p ++ q) = Binary.tally p + Binary.tally q := Binary.tally_append p q

end RAM

namespace RAM
open Binary Matrix Ty Finset
universe U

/-- **Conditional two-stage statement (the word is NOT constructed here).**
IF some word on `576` coordinates is a scratch certificate for `2^28` live slots with at
most `2^28·576 - 1858032` directional moves in total (on live and scratch roles together),
THEN the engine has exponent `1 - 1.89e-6`.  The hypothesis `hw`/`ht` is exactly what a
machine-checked two-stage network would have to supply; nothing else is missing on the
engine side for the one-move-per-rank accounting. -/
theorem two_stage_h24_if_word {α ρ σ : Type} [Fintype α] [DecidableEq α] [Fintype ρ]
    [DecidableEq ρ] [Fintype σ] [DecidableEq σ]
    (hα : Fintype.card α = 576) (hσ : Fintype.card σ = 2^28)
    (e : σ → ρ) (he : Function.Injective e)
    (p : PWord α ρ) (hw : LiveKernel e p) (ht : tally p ≤ 2^28*576 - 1858032)
    (cl : Paint) (m : Bool) {ι : Type U} (k : ι→ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*envelope (1 - 189/(10:ℝ)^8) (k i)) := by
  have hD : (tally p:ℝ)/(2:ℝ)^28 < ((576:ℕ):ℝ)^(1 - 189/(10:ℝ)^8) := by
    refine lt_of_le_of_lt ?_ two_stage_rate_28
    have h1 : (tally p:ℝ) ≤ (2:ℝ)^28 * ((576:ℕ):ℝ) - ((1858032:ℕ):ℝ) := by
      have : ((tally p:ℕ):ℝ) ≤ ((2^28*576 - 1858032:ℕ):ℝ) := by exact_mod_cast ht
      refine this.trans (le_of_eq ?_)
      norm_num
    gcongr
  exact engine_program_scratch 576 28 hα hσ (by norm_num) e he p hw _ (by norm_num) hD cl m k v

end RAM
end OAI.PowerSaving

#print axioms OAI.PowerSaving.RAM.recurse_runS
#print axioms OAI.PowerSaving.RAM.engine_all_scratch
#print axioms OAI.PowerSaving.RAM.engine_program_scratch
#print axioms OAI.PowerSaving.RAM.hills_program_via_scratch
#print axioms OAI.PowerSaving.RAM.LiveKernel.iff_erase_first
#print axioms OAI.PowerSaving.RAM.no_erase_first
#print axioms OAI.PowerSaving.RAM.Route.gate
#print axioms OAI.PowerSaving.RAM.LiveKernel.of_route
#print axioms OAI.PowerSaving.RAM.endpoint_reversible
#print axioms OAI.PowerSaving.RAM.endpoint_by_copy
#print axioms OAI.PowerSaving.two_stage_rate_28
#print axioms OAI.PowerSaving.two_stage_rate_33
#print axioms OAI.PowerSaving.RAM.two_stage_h24_if_word
#print axioms OAI.PowerSaving.RAM.allotC_bound
