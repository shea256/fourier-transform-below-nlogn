import OAI.Computability.FourierTransform.SectorPacking
import OAI.Computability.FourierTransform.BitLayout

namespace OAI
/-!
Shard effect = binary kernel applied in contiguous sectors.
-/
namespace PowerSaving.Grove
open Slant Shard Hem Binary Finset Matrix
noncomputable section

/-- natural address binary kernel -/
def fleck (i j : ℕ) : ℂ := if i=j then ca else cb
def prism : ℕ → Wood
  | 0 => fun _ _ => 1
  | k+1 => fun i j => prism k (i/2) (j/2) * fleck (i%2) (j%2)
def gleam (k : ℕ) (x : Line) : Line := graft (2^k) (prism k) x

lemma bits_next (k : ℕ) (x : Bits (k+1)) :
    (bits (k+1)).loc x = (bits k).loc (fun i => x i.succ)*2+(x 0).val := by
  rw [bits_loc,bits_loc,Fin.sum_univ_succ]
  simp [pow_succ,sum_mul,mul_assoc,Nat.add_comm]

lemma prism_loc (k : ℕ) (x y : Bits k) :
    prism k ((bits k).loc x) ((bits k).loc y) = kernel (Fin k) x y := by
  induction k with
  | zero => simp [prism,kernel]
  | succ k ih =>
    simp only [prism,bits_next]
    have hx : (x 0).val < 2 := ZMod.val_lt _
    have hy : (y 0).val < 2 := ZMod.val_lt _
    rw [chops _ _ 2 hx,chips _ _ 2 hx,chops _ _ 2 hy,chips _ _ 2 hy,ih]
    simp only [kernel,digitProd_apply,Fin.prod_univ_succ]
    have h (i j : F) : fleck i.val j.val=littleC i j := by
      have hone : (1:F).val=1 := ZMod.val_one ..
      rcases bit_cases i with rfl|rfl <;> rcases bit_cases j with rfl|rfl <;> simp [littleC,fleck,hone]
    rw [h]; ring

lemma sum_bits_addr (k : ℕ) (f : Line) :
    ∑ i ∈ range (2^k), f i = ∑ x : Bits k, f ((bits k).loc x) := by
  rw [← Fin.sum_univ_eq_sum_range f (2^k)]
  exact (Equiv.sum_comp (bits k).index (fun i => f i.val)).symm

lemma gleam_loc (k : ℕ) (v : Line) (x : Bits k) :
    gleam k v ((bits k).loc x) =
    ripple k (fun j => v ((bits k).loc j)) x := by
  unfold gleam graft; rw [sum_bits_addr]
  simp_rw [prism_loc k]
  rfl

def gleans (f g : Shard) : ℂ :=
  if f.start=g.start then prism f.height f.seat g.seat else 0

lemma leaf_gleans {n : ℕ} {u : Stroke} (h : u.Sound n) (i j : ℕ) (hi : i<n) (hj : j<n) :
    leafC u i j=gleans (hem u i) (hem u j) := by
  let s := hem u
  change _=gleans (s i) (s j)
  by_cases g : (s i).start=(s j).start
  · rw [gleans,ite_eq_left g]
    have hh := crown_class h (class_of_start h hi hj g)
    by_cases H : u.partner i=i
    · have e : j=i := hh.elim id (·.trans H); subst j
      have hu : (s i).height=0 := by simp [s,hem,up,H]
      rw [hu]
      simp [leafC,H,prism,white]
    · have hu : (s i).height=1 := by simp [s,hem,up,Ne.symm H]
      have ht (i : ℕ) : (s i).seat < 2 := by
        change tier u i<2; unfold tier; split <;> omega
      rw [hu]
      simp only [leafC,H,↓reduceIte,prism,Nat.mod_eq_of_lt (ht _),one_mul]
      rcases hh with e|e
      · subst j; simp [fleck, Ne.symm H]
      · subst j
        have HG : (s i).seat ≠ (s (u.partner i)).seat := Ne.symm (tier_partner_ne h H)
        simp [fleck, H, HG]
  · rw [gleans,ite_eq_right g]
    have G : j ≠ i := fun k => g (by rw [k])
    have H : j ≠ u.partner i := fun k => g (by
      rw [k]; exact (same_class h (crown_partner h).symm).1)
    unfold leafC white; split <;> simp

/-- The `prism` multiplies under shard composition. Need low-word append
of only two choices (0 or 1 low bits). -/
lemma prism_fringe {n l m : ℕ} {u x v y : Shard}
    (_hl : u.Mark n l) (_hl' : v.Mark n l) (hn : x.Mark m 1) (hn' : y.Mark m 1)
    (hs : x.same y) :
    prism (fringe m u x).height (fringe m u x).seat (fringe m v y).seat =
    prism u.height u.seat v.seat * prism x.height x.seat y.seat := by
  have hh := hn.tall
  have h := hn.size
  have k := hn.place; have k' := hn'.place
  have hxy := hs.2.1
  change prism (u.height+x.height) (u.seat*x.width+x.seat) (v.seat*y.width+y.seat)=_
  rcases Nat.eq_zero_or_pos x.height with g|g
  · rw [g] at h ⊢
    have ht : x.width=1 := h
    have ht' : y.width=1 := hxy ▸ ht
    have hx : x.seat=0 := by omega
    have hy : y.seat=0 := by omega
    simp [ht,ht',hx,hy,prism]
  · have hg : x.height=1 := by omega
    rw [hg] at h ⊢
    have ht : x.width=2 := h
    have ht' : y.width=2 := hxy ▸ ht
    rw [ht,ht']; rw [ht] at k; rw [ht'] at k'
    simp only [prism,chops _ _ _ k,chops _ _ _ k',chips _ _ _ k,chips _ _ _ k',
      Nat.mod_eq_of_lt k,Nat.mod_eq_of_lt k',one_mul]

lemma gleans_fringe (m n l : ℕ) {f g : ℕ → Shard} (h : Quilt n l f)
    (k : Quilt m 1 g) (i j a b : ℕ) (hi : i<n) (hj : j<n) (ha : a < m) (hb : b < m) :
    gleans (fringe m (f i) (g a)) (fringe m (f j) (g b)) =
    gleans (f i) (f j) * gleans (g a) (g b) := by
  let u := fringe m (f i) (g a)
  let v := fringe m (f j) (g b)
  have h1 : u.Mark (n*m) (l+1) := (h.mark i hi).fringe (k.mark a ha)
  have h2 : v.Mark (n*m) (l+1) := (h.mark j hj).fringe (k.mark b hb)
  have iffStart : u.start=v.start ↔
      (f i).start=(f j).start ∧ (g a).start=(g b).start := by
    constructor
    · intro H
      have hu := fr_unique _ _ (k.mark a ha) (k.mark b hb) (h.mark i hi) (h.mark j hj)
        (h.seam i hi j hj) (k.seam a ha b hb)
        (show u.start < v.tip from H ▸ h2.starts)
        (show v.start < u.tip from H.symm ▸ h1.starts)
      exact ⟨hu.1.1,hu.2.1⟩
    · rintro ⟨A,B⟩
      exact (fr_same m (h.matches_of_eq hi hj A) (k.matches_of_eq ha hb B)).1
  change gleans u v=_
  simp only [gleans]
  simp only [iffStart]
  by_cases H : (g a).start=(g b).start
  · have g' := k.matches_of_eq ha hb H
    by_cases G : (f i).start=(f j).start
    · simp only [G,H,true_and,↓reduceIte]
      exact prism_fringe (h.mark i hi) (h.mark j hj) (k.mark a ha) (k.mark b hb) g'
    · simp [H,G]
  · simp [H]

lemma canopy_gleans (r : Axes) (l : ℕ) (u : ℕ→Stroke)
    (h : Splits r l) (g : ∀ i<l, (u i).Sound (r i)) :
    ∀ i<extent r l, ∀ j<extent r l,
    canopy r (fun i => leafC (u i)) l i j =
    gleans (mosaic r u l i) (mosaic r u l j) := by
  induction l with
  | zero => intros; simp [mosaic,gleans,canopy,prism,seed]
  | succ l ih =>
    intro i hi j hj
    simp only [canopy,mosaic,Shard.attach]
    have hl := h.cut (j:=l) (by omega)
    have hh (t : ℕ) (ht : t<l) := g t (lt_trans ht (by omega : l<l+1))
    have g' := g l (by omega)
    rw [ih hl hh _ (h.div_lt hi) _ (h.div_lt hj),
      leaf_gleans g' _ _ (h.mod_lt i) (h.mod_lt j),
      gleans_fringe _ _ l (mosaic_quilt _ _ _ hl hh) (Hem.quilt g') _ _ _ _
        (h.div_lt hi) (h.div_lt hj) (h.mod_lt i) (h.mod_lt j)]

-- operation in packed addresses
def stow (n : ℕ) (f : ℕ → Shard) (x : Line) : Line :=
  fun j => x (seek n (fun i => (f i).addr) j)

def slit (n : ℕ) (f : ℕ → Shard) (x : Line) (s : ℕ) : Line :=
  fun j => stow n f x (s+j)

/-- local output from packed data at a sector address. -/
def glimpse (n : ℕ) (f : ℕ → Shard) (x : Line) (j : ℕ) : Line :=
  gleam (patch n f j).height (slit n f x j)

lemma sum_zone {A : Type*} [AddCommMonoid A] (n i m : ℕ) (h : i+m≤n) (f : ℕ→A)
    (g : ∀ j<n, f j ≠ 0 → i≤j ∧ j < i+m) :
    ∑ j ∈ range n, f j = ∑ j ∈ range m, f (i+j) := by
  classical
  have h1 : ∑ j ∈ range (i+m), f j = ∑ j ∈ range n, f j :=
    sum_subset (range_mono h)
      (fun j hj hi => Classical.byContradiction fun H =>
        hi (mem_range.mpr (g j (mem_range.mp hj) H).2))
  have h2 : ∑ j ∈ range i, f j = 0 :=
    sum_eq_zero fun j hj => Classical.byContradiction fun H => by
      have hh := mem_range.mp hj
      have ht := (g j (by omega) H).1
      omega
  rw [← h1,sum_range_add,h2,zero_add]

lemma graft_glimpse (r : Axes) (l : ℕ) (u : ℕ→Stroke)
    (h : Splits r l) (g : ∀ i<l, (u i).Sound (r i)) (x : Line)
    (i : ℕ) (hi : i<extent r l) :
    let f := mosaic r u l
    graft (extent r l) (canopy r (fun i => leafC (u i)) l) x i =
    glimpse (extent r l) f x (f i).start (f i).seat := by
  intro f
  let n := extent r l
  let s := f i
  have hh := mosaic_quilt r l u h g
  have hH : Quilt n l f := hh
  have hs : s.Mark n l := hH.mark i hi
  let pay (j : ℕ) := gleans s (patch n f j)*stow n f x j
  have he :
      graft n (canopy r (fun i => leafC (u i)) l) x i = ∑ j ∈ range n, pay j := by
    rw [← hH.reloc.sum]
    refine sum_congr rfl ?_
    intro j hj
    have hj := mem_range.mp hj
    rw [canopy_gleans _ _ _ h g _ hi _ hj]
    simp only [pay,f,s,stow] -- want f folded
    change _=gleans s (patch n f (f j).addr)*x (seek n (fun j => (f j).addr) (f j).addr)
    rw [hH.patch_at hj, hH.reloc.seeks_at hj]
  have sx (j : ℕ) (hj : j<s.width) :
      (patch n f (s.start+j)).same s ∧ (patch n f (s.start+j)).seat=j :=
    let H := hH.patch_align hi (Nat.le_add_right (s.start) j) (Nat.add_lt_add_left hj s.start)
    ⟨H.1,H.2.trans (Nat.add_sub_cancel_left ..)⟩
  have sz := sx 0 hs.positive
  rw [Nat.add_zero] at sz
  have ht (j : ℕ) (hj : j<n) (gp : pay j ≠ 0) :
      s.start ≤ j ∧ j<s.start+s.width := by
    let H := hH.patch_seam (i:=(f i).addr) (j:=j) (hH.reloc.bd i hi) hj
    have J : s.fits (patch n f j) := by simpa only [hH.patch_at hi] using H
    let p := patch n f j
    have hg : s.start=p.start := by
      by_contra hx
      have : pay j = 0 := by change gleans s p*_=0; simp [gleans,hx]
      exact gp this
    have hp : p.Mark n l := hH.patch_mark hj
    have hp' : p.addr=j := hH.patch_addr hj
    rcases J with T|T|T
    · have H := T.2.1
      have h3 := hp.place
      rw [← hp',hg]; unfold addr
      change s.width=p.width at H
      omega
    · have hf : s.tip ≤ p.start := T
      have := hs.starts; omega
    · have hf : p.tip ≤ s.start := T
      have := hp.starts; omega
  change graft n _ _ _ = glimpse n f x s.start s.seat
  rw [he,sum_zone n s.start s.width hs.endsBy pay ht,glimpse,gleam,graft,sz.1.2.2,← hs.size]
  refine sum_congr rfl ?_
  intro j hj
  have hj := mem_range.mp hj
  have H := sx j hj
  change gleans s (patch n f (s.start+j))*_ =_
  rw [gleans,ite_eq_left H.1.1.symm,H.2]; rfl

-- sector start width sums (need cost bound on packed call).
def seatfare (n : ℕ) (f : ℕ→Shard) (j : ℕ) :=
  if (patch n f j).seat=0 then (patch n f j).width else 0

lemma fare_sum (n l : ℕ) (f : ℕ → Shard) (h : Quilt n l f) :
    ∑ j ∈ range n, seatfare n f j = n := by
  let p := patch n f
  let cnt (i : ℕ) := ∑ j ∈ range n, if (p j).start=i then 1 else 0
  have hh (i : ℕ) (hi : i<n) : cnt i=seatfare n f i := by
    let s := p i
    let q := seek n (fun i => (f i).addr)
    have hq : ∀ i<n, q i<n := fun i hi => (h.reloc.seeks hi).1
    have hs : s.Mark n l := h.patch_mark hi
    have hS : s.addr=i := h.patch_addr hi
    change cnt _ = if s.seat=0 then s.width else 0
    unfold cnt; split
    · rename_i H
      have hg : s.start=i := by unfold addr at hS; omega
      rw [sum_zone n i s.width]
      · have he (j : ℕ) (hj : j ∈ range s.width) :
            (if (p (i+j)).start=i then 1 else 0)=1 := by
          have ht : i+j<s.tip := by rw [← hg]; exact Nat.add_lt_add_left (mem_range.mp hj) _
          have hu := h.patch_align (hq i hi)
            (show s.start ≤ i+j from by omega) ht
          exact ite_eq_left (hu.1.1.trans hg)
        rw [sum_congr rfl he]
        simp
      · rw [← hg]; exact hs.endsBy
      · intro j hj hj'
        have he : (p j).start=i := by split at hj' <;> first | assumption | omega
        have hx := h.patch_addr hj
        change (p j).addr=j at hx
        have hy := h.patch_mark hj
        have hu : (p j).same s :=
          h.matches_of_eq (hq j hj) (hq i hi) (he.trans hg.symm)
        have hw := hu.2.1
        have hc : (p j).seat < (p j).width := hy.place
        unfold addr at hx; omega
    · rename_i H
      refine sum_eq_zero ?_
      intro j hj
      have hj := mem_range.mp hj
      refine ite_eq_right ?_
      intro hG
      have ht : i < (p j).tip := hG ▸ (h.patch_mark hj).starts
      have hu := h.patch_align (hq j hj)
        (show (p j).start ≤ i from hG.le) ht
      apply H
      change (patch n f i).seat=0
      rw [hu.2]
      change i-(p j).start=0; omega
  rw [show (∑ j ∈ range n, seatfare n f j)=∑ j ∈ range n, cnt j from
    sum_congr rfl fun i hi => (hh i (mem_range.mp hi)).symm]
  unfold cnt; rw [sum_comm]
  have HG (j : ℕ) (hj : j ∈ range n) :
      (∑ i ∈ range n, if (p j).start=i then 1 else 0) = 1 := by
    have h' := h.patch_mark (mem_range.mp hj)
    have hm : (p j).start<n := h'.starts.trans_le h'.endsBy
    simp [hm]
  rw [sum_congr rfl HG]
  simp

end
end PowerSaving.Grove

end OAI
