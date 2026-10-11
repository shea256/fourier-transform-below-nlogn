import OAI.Computability.FourierTransform.RoleArrays

namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset
noncomputable section

/-- An instance of the simultaneous kernel program. -/
abbrev Sim (ρ : Type*) (k : ℕ) := ρ × Bits k
def sim {ρ : Type*} (R : Layout ρ) (k : ℕ) := R.pair (bits k)

abbrev bundle := fun cl => a (c cl)
abbrev simIn := fun cl => p w (p sc (bundle cl))
abbrev hatch := fun cl => some (simIn cl,bundle cl)

def whole {ρ : Type*} (k : ℕ) (v : Sim ρ k → ℂ) : Sim ρ k → ℂ :=
  fun (l,i) => ripple k (fun j => v (l,j)) i

def loaded {ρ : Type*} (cl : Paint) (R : Layout ρ) (k : ℕ) (v : Sim ρ k → ℂ) :
    T (simIn cl) :=
  (k,Complex.I,(sim R k).tape v)

-- cut t groups of R.n fibers from the peeled coordinates
def cut {β ρ} (r f t : ℕ) (X : Layout β) (R : Layout ρ)
    (h : t*R.n = (book X r f).n) :
    (Fin t × ρ) ≃ Grid β r f :=
  let L := (Layout.std t).pair R
  (L.index.trans (finCongr h)).trans (book X r f).index.symm

lemma cut_eq {β ρ} (r f t) (X : Layout β) (R : Layout ρ) h
    (z : Fin t × ρ) :
    (book X r f).loc (cut r f t X R h z) = z.1.val * R.n + R.loc z.2 :=
  Layout.loc_atFin _ _

lemma uncut_eq {β ρ} (r f t) (X : Layout β) (R : Layout ρ) h
    (q : Grid β r f) :
    let v := (cut r f t X R h).symm q
    (book X r f).loc q = v.1.val*R.n+R.loc v.2 := by
  intro v
  have hh := cut_eq r f t X R h v
  simpa only [v,Equiv.apply_symm_apply] using hh

section
variable {α ρ : Type*} [Fintype α] [DecidableEq α]

/-- Source data for one recursive call (one batch). -/
def fill (l : ρ) (j : α) (z : Space α) {r f t : ℕ} (X : Layout (Minus j))
    (R : Layout ρ) (h : t*R.n=(book X r f).n)
    (v : Grain α ρ r f) (b : Fin t) : Sim ρ f → ℂ :=
  fun (k,i) => v (l,(peelBook j z r f).symm
    ((cut r f t X R h) (b,k),i))

/-- Collection of returned answers. -/
def yieldTape (l : ρ) (j : α) (z : Space α) {r f t} (X : Layout (Minus j))
    (R : Layout ρ) (h : t*R.n=(book X r f).n) (v : Grain α ρ r f) : Tape (Tape ℂ) :=
  (Layout.std t).tape fun b =>
    (sim R f).tape (whole f (fill l j z X R h v b))

-- proof calculation for one direction
lemma fill_result [Fintype ρ] [DecidableEq ρ] (l : ρ) (j : α) (z : Space α)
    (hz : z j=1) (hn : z≠0) {r f t} (X : Layout (Minus j)) (R : Layout ρ) h
    (v : Grain α ρ r f) (a : Grid α r f) :
    let q := peelBook j z r f a
    let w := (cut r f t X R h).symm q.1
    ferry r f (.dir l z hn) v (l,a) = whole f (fill l j z X R h v w.1) (w.2,q.2) := by
  intro q w
  unfold ferry Move.go roleAct
  simp only [ite_true]
  have H := peel_act j z hz r f (fun p => v (l,p)) a
  refine H.trans ?_
  unfold whole fill
  simp only [q,w,Prod.mk.eta,Equiv.apply_symm_apply]

end

section
universe U
variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
variable {ι : Type U}
variable {m : Bool} {B f n : ι → ℕ} {s : Ty} {x : ι → T s}
    {cl : Paint} {X : Layout α} {R : Layout ρ} {r : ℕ} {v : ∀ i, Grain α ρ r (f i)}

namespace Rig
variable (h : Rig m B f s x cl X R r v)
include h

omit [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] in
lemma simSmall : Small B fun i => (sim R (f i)).n :=
  (Small.const B R.n).mul h.gear.bound

omit [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] in
lemma simSize : Knows m B s x fun i => (sim R (f i)).n :=
  Can.times (Can.wc R.n) h.gear.power (Small.const B R.n) h.gear.bound

variable (l : ρ) (j : α) (z : Space α) (X' : Layout (Minus j))
variable (hg : ∀ i, n i*R.n = (book X' r (f i)).n)
include hg

omit [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] in
lemma batchSmall (hr : 0<R.n) :
    Small B n :=
  (h.gear.grid_small X' r).mono (fun i => by
    rw [← hg]
    exact Nat.le_mul_of_pos_right _ hr)

omit [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ] in
lemma batchSize (hr : 0<R.n) :
    Knows m B s x n :=
  ((h.gear.grid_size X' r).dvdW (Can.wc R.n) (h.gear.grid_small X' r)).cong
    (fun _ => rfl) (fun i => by rw [← hg]; exact Nat.mul_div_cancel _ hr)

omit [Fintype ρ] [DecidableEq ρ] in
lemma fill_read (a : ∀ i, Sim ρ (f i)) (b : ∀ i, Fin (n i))
    (hd : Knows m B s x fun i => (sim R (f i)).loc (a i))
    (ha : Knows m B s x fun i => (b i).val) :
    Has m B s (c cl) x fun i => fill l j z X' R (hg i) (v i) (b i) (a i) := by
  let L i := bits (f i)
  have hu := Can.addr_high (u:=a) (L:=fun _ => R) (R:=L) hd h.gear.power h.simSmall
  have hw := Can.addr_low (u:=a) (L:=fun _ => R) (R:=L) hd h.gear.power h.simSmall
  have hr : 0<R.n := lt_of_le_of_lt (Nat.zero_le _) (R.bd l)
  let C i := cut r (f i) (n i) X' R (hg i)
  let K i : Grid (Minus j) r (f i) × Bits (f i) :=
    (C i (b i,(a i).1),(a i).2)
  have hs := Can.addr_join (L:=fun i => Layout.std (n i)) (R:=fun _ => R)
    (u:=fun i => (b i,(a i).1)) ha hu (Can.wc R.n)
    (h.batchSmall j X' hg hr) (Small.const B R.n)
  have hm : Knows m B s x fun i => (book X' r (f i)).loc (K i).1 :=
    hs.cong (fun _ => rfl) (fun i => (cut_eq r (f i) (n i) X' R _ _).symm)
  have hk := h.gear.to_grid X r j X' z K hm hw
  exact h.read (fun i => (l,(peelBook j z r (f i)).symm (K i))) (Can.wc (R.loc l)) hk

omit [Fintype ρ] [DecidableEq ρ] in
omit [Fintype ρ] [DecidableEq ρ] in
lemma fill_ready (b : ∀ i, Fin (n i))
    (ha : Knows m B s x fun i => (b i).val) :
    Can m B s (simIn cl) x
      (fun i => loaded cl R (f i) (fill l j z X' R (hg i) (v i) (b i)))
      (fun i => (sim R (f i)).n) := by
  let W i := (sim R (f i)).n
  let V (i : ι) := fill l j z X' R (hg i) (v i) (b i)
  have hd : Can m B s (bundle cl) x (fun i => (sim R (f i)).tape (V i)) W := by
    let S := Σ i, Sim ρ (f i)
    let env (d : S) : T (p s w) := (x d.1,(sim R (f d.1)).loc d.2)
    have G := h.gather (fun d : S => d.1) env (t:=p s w) Can.first
    have hh := G.fill_read l j z X' (n:=fun d=>n d.1) (fun d => hg d.1)
      (fun d => d.2) (fun d => b d.1) Can.second
      (Can.first.then_do (ha.reindex (Sigma.fst (β:=fun i => Sim ρ (f i)))))
    have ht := Can.layout (t:=c cl) (P:=fun _ => 0)
      (L:=fun i => sim R (f i)) (v:=V) h.simSize hh h.simSmall
    simpa [W] using ht
  exact (h.gear.given.mono (fun i => Nat.zero_le (W i))).pair
    ((h.imag.mono (fun i => Nat.zero_le (W i))).pair hd)

-- compute a directional outcome from the packed answers (and from unchanged roles)
lemma direction_get (hn : z≠0) (hz : z j=1)
    (H : Has m B s (Ty.a (bundle cl)) x fun i => yieldTape l j z X' R (hg i) (v i))
    (a : ∀ i, Beach α ρ r (f i)) (ha : Knows m B s x fun i => (fleet X R r (f i)).loc (a i)) :
    Has m B s (c cl) x fun i => ferry r (f i) (.dir l z hn) (v i) (a i) := by
  obtain ⟨hx,hy⟩ := h.addrs a ha
  let C i := cut r (f i) (n i) X' R (hg i)
  let K i := peelBook j z r (f i) (a i).2
  let Q i := (C i).symm (K i).1
  let Y i := ((Layout.std (n i)).pair R).loc (Q i)
  obtain ⟨hd,he⟩ := h.gear.from_grid X r j X' z (fun i => (a i).2) hy
  have hY : Knows m B s x Y :=
    hd.cong (fun _ => rfl) (fun i => uncut_eq r (f i) (n i) X' R _ (K i).1)
  have ls : Small B fun i => n i * R.n :=
    (h.gear.grid_small X' r).mono (fun i => le_of_eq (hg i))
  have hA := Can.addr_high (L:=fun i => Layout.std (n i)) (R:=fun _ => R)
    (u:=Q) hY (Can.wc R.n) ls
  have hB := Can.addr_low (L:=fun i => Layout.std (n i)) (R:=fun _ => R)
    (u:=Q) hY (Can.wc R.n) ls
  let F i b := fill l j z X' R (hg i) (v i) b
  have hD := Can.fetch (t:=bundle cl) (L:=fun i => Layout.std (n i))
    (i:=fun i => (Q i).1) (v:=fun i b => (sim R (f i)).tape (whole (f i) (F i b))) H hA
  have hh := Can.fetch (t:=c cl) (L:=fun i => sim R (f i))
    (i:=fun i => ((Q i).2,(K i).2)) (v:=fun i => whole (f i) (F i (Q i).1))
    hD (Can.addr_join (L:=fun _ => R) (R:=fun i => bits (f i)) (u:=fun i => ((Q i).2,(K i).2))
      hB he h.gear.power (Small.const B R.n) h.gear.bound)
  apply Can.cases_code (q:=fun i => (a i).1) R hx
  intro r'
  by_cases hL : r'=l
  · refine (hh.reindex (fun i : {i // (a i).1=r'} => i.val)).cong (fun _ => rfl)
      (fun i => ?_)
    have ht := fill_result l j z hz hn (t:=n i.val)
      X' R (hg i.val) (v i.val) (a i.val).2
    have hC : (l,(a i.val).2) = (a i.val) := Prod.ext (i.property.trans hL).symm rfl
    exact ht.symm.trans (congr_arg _ hC)
  · refine ((h.read a hx hy).reindex (fun i : {i // (a i).1=r'} => i.val)).cong
      (fun _ => rfl) (fun i => ?_)
    have H : (a i.val).1≠l := fun hh => hL (i.property.symm.trans hh)
    simp only [ferry,Move.go,roleAct, H,ite_false, Prod.mk.eta]

end Rig
end
end
end PowerSaving.RAM

end OAI
