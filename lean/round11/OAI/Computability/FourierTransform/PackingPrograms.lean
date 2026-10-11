import OAI.Computability.FourierTransform.WordCompilation
import OAI.Computability.FourierTransform.SectorPacking
import OAI.Computability.FourierTransform.TraversalPrograms

namespace OAI

/-! Local packing tables, printed in local polynomial time. -/
namespace PowerSaving.RAM
open Ty Finset
open Grove Shard Slant Hem
noncomputable section

abbrev chipTy := p w (p w (p w w)) -- start width height seat
abbrev sapTy := p w sc -- lookup and dye
abbrev blossomTy := p sapTy chipTy
abbrev leafTy := a blossomTy
abbrev treeTy := a leafTy

def chip (s : Shard) : T chipTy := (s.start,s.width,s.height,s.seat)

def blossom (u : Stroke) (i : ℕ) : T blossomTy :=
  ((u.ix i,u.dye i),chip (hem u i))

def leavesT (n : ℕ) (u : Stroke) : T leafTy := Tape.tab n (blossom u)
def treeT (n : ℕ) (u : Reel) : T treeTy := Tape.tab u.beats fun i => leavesT n (u.atBeat i)

universe U V
namespace Bench
variable {m : Bool} {ι : Type U} {κ : Type V} {b : Bench m ι} {q : Bench m κ}

variable {s : ι → Stroke} {n x : ι→ℕ}
namespace Band

lemma partD (h : b.Band n s) (hx : b.Digit x) (hi : ∀ i, x i<n i) :
    b.Digit fun i => (s i).partner (x i) :=
  ⟨(h.showOne hx.run hi).snd.snd,h.width.small.mono fun i => ((h.good i).bdp _ (hi i)).le⟩

lemma crownD (h : b.Band n s) (hx : b.Digit x) (hi : ∀ i, x i<n i) :
    b.Digit fun i => crown (s i) (x i) :=
  hx.minimum (h.partD hx hi)

-- if exact operations
lemma trial (hx : b.Digit n) (hy : b.Digit x) {y z : ι→ℕ} (h : b.Digit y) (g : b.Digit z) :
    b.Digit (fun i => if n i=x i then y i else z i) := by
  let P i := n i=x i
  have hh : b.Study P := Study.eq hx hy
  exact branchN hh (draw (restricted b P) h) (draw (restricted b (fun i => ¬ P i)) g)

lemma thickD (h : b.Band n s) (hx : b.Digit x) (hi : ∀ i, x i<n i) :
    b.Digit fun i => thickness (s i) (x i) :=
  trial hx (h.partD hx hi) (Digit.wc 1) (Digit.wc 2)

lemma trimD (h : b.Band n s) (hx : b.Digit x) (hi : ∀ i, x i<n i) :
    b.Digit fun i => trim (s i) (x i) :=
  trial hx (h.crownD hx hi) (h.thickD hx hi) (Digit.wc 0)

lemma sumsD (h : b.Band n s) (hx : b.Digit x) (hi : ∀ i, x i<n i) :
    b.Digit fun i => sums (s i) (x i) := by
  let S i j := sums (s i) j
  let B := b.climbs x w S
  have sm (i : ι) (j : ℕ) (hj : j≤n i) : S i j≤n i :=
    (sums_mono _ hj).trans (sum_trim (h.good i)).le
  have H : B.Digit fun i => S i.i i.j :=
    ⟨stepsum b x (t:=w) S,(h.width.small.reindex During.i).mono
      fun i => sm _ _ (i.hj.trans (hi _)).le⟩
  have F := Feeds.climbs b x (t:=w) S
  have K := (h.transfer F).trimD (stepi (t:=w) hx S) (fun i => i.hj.trans (hi _))
  refine ⟨loop (t:=w) hx S ((Makes.wc 0).congr fun i => by simp [S,sums]) ((H.add K).congr ?_).run,
    h.width.small.mono fun i => sm _ _ (hi _).le⟩
  intro i; simp [S,sums,sum_range_succ]

lemma blossomD (h : b.Band n s) (hx : b.Digit x) (hi : ∀ i, x i<n i) :
    b.Makes blossomTy fun i => blossom (s i) (x i) := by
  have hc := h.crownD hx hi
  have ht : ∀ i, crown (s i) (x i)<n i :=
    fun i => Nat.lt_of_le_of_lt (min_le_left ..) (hi i)
  have hu := trial hx (h.partD hx hi) (Digit.wc 0) (Digit.wc 1)
  have hk := trial hx hc (Digit.wc 0) (Digit.wc 1)
  have hg := (h.sumsD hc ht).run.pair ((h.thickD hx hi).run.pair (hu.run.pair hk.run))
  have hh := h.showOne hx.run hi
  exact (hh.fst.pair hh.snd.fst).pair hg

lemma leavesD (h : b.Band n s) : b.Makes leafTy fun i => leavesT (n i) (s i) :=
  tab (t:=blossomTy) h.width _
    ((h.transfer (Feeds.scan b _)).blossomD (slot h.width) During.hj)

end Band

lemma Engrave.tree {u : ι → Reel} (h : b.Engrave n u) :
    b.Makes treeTy fun i => treeT (n i) (u i) :=
  tab (t:=leafTy) h.count _
    (((h.transfer (Feeds.scan b _)).plate _ (slot h.count).run During.hj).leavesD)

-- use in array work
structure Spring (b : Bench m ι) (n : ι→ℕ) (s : ι→Stroke) : Prop where
  good : ∀ i, (s i).Sound (n i)
  tree : b.Moves (fun _ => 0) leafTy fun i => leavesT (n i) (s i)

namespace Spring

lemma transfer {n : κ→ℕ} {s : κ→Stroke} (h : q.Spring n s) {f} (g : b.Instant q f) :
    b.Spring (fun i => n (f i)) (fun i => s (f i)) :=
  ⟨fun _ => h.good _,h.tree.transfer g⟩

lemma read (h : b.Spring n s) (hx : b.Nick x) (hi : ∀ i, x i < n i) :
    b.Moves (fun _ => 0) blossomTy fun i => blossom (s i) (x i) :=
  Moves.pick (n:=n) (t:=blossomTy) _ h.tree hx.close hi
end Spring

structure Bough (b : Bench m ι) (l : ι→ℕ) (r : ι→Axes) (u : ι→ℕ→Stroke) : Prop where
  fen : b.Fen l r
  leaf : (b.scan l).Spring (fun i => r i.i i.j) (fun i => u i.i i.j)

namespace Bough
variable {l : ι→ℕ} {r : ι→Axes} {u : ι→ℕ→Stroke}

lemma good (h : b.Bough l r u) (i : ι) (j : ℕ) (hj : j<l i) :
    (u i j).Sound (r i j) :=
  h.leaf.good ⟨i,j,hj⟩

lemma transfer {l : κ→ℕ} {r : κ→Axes} {u : κ→ℕ→Stroke} (h : q.Bough l r u) {f}
    (g : b.Instant q f) :
    b.Bough (fun i => l (f i)) (fun i => r (f i)) (fun i => u (f i)) := by
  let L i := l (f i)
  have F := Instant.scan b L
  let p : During L→During l := fun i => ⟨f i.i,i.j,i.hj⟩
  have H := h.fen.transfer g
  have G : (b.scan L).Instant (q.scan l) p :=
    Instant.select (F.next g) (chop H.high).close
  exact ⟨H,h.leaf.transfer G⟩
end Bough
end Bench
end
end PowerSaving.RAM

end OAI
