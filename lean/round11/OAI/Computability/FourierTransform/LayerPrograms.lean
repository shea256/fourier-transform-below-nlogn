import OAI.Computability.FourierTransform.LayerWords
import OAI.Computability.FourierTransform.WordPrograms

namespace OAI

namespace PowerSaving.RAM

open Ty Slant Slant.Stroke
noncomputable section

abbrev arrowTy := p w (p sc w)
abbrev stripeTy := a arrowTy
abbrev filmTy := a stripeTy

def emboss (s : Stroke) (i : ℕ) : T arrowTy :=
  (s.ix i,s.dye i,s.partner i)

def stripe (n : ℕ) (s : Stroke) : T stripeTy :=
  Tape.tab n (emboss s)

def film (n : ℕ) (r : Reel) : T filmTy :=
  Tape.tab r.beats fun i => stripe n (r.atBeat i)

universe U V
namespace Bench

variable {m : Bool} {ι : Type U} {κ : Type V} {b : Bench m ι} {q : Bench m κ}

structure Band (b : Bench m ι) (n : ι→ℕ) (s : ι→Stroke) : Prop where
  good : ∀ i, (s i).Sound (n i)
  width : b.Digit n
  sheet : b.Makes stripeTy (fun i => stripe (n i) (s i))

namespace Band
variable {n e i : ι→ℕ} {s t : ι→Stroke}

lemma transfer {f : ι→κ} {n : κ→ℕ} {s : κ→Stroke} (h : q.Band n s) (g : b.Feeds q f) :
    b.Band (fun i => n (f i)) (fun i => s (f i)) :=
  ⟨fun i => h.good (f i),draw g h.width,pull g h.sheet⟩

lemma showOne (h : b.Band n s) (hk : b.Makes w i) (hI : ∀ j, i j<n j) :
    b.Makes arrowTy (fun j => emboss (s j) (i j)) :=
  Makes.pick (t:=arrowTy) (n:=n) (fun j => emboss (s j)) h.sheet hk hI

lemma fresh (h : b.Digit n) (g : ∀ i,(s i).Sound (n i))
    (a : (b.scan n).Makes arrowTy (fun j => emboss (s j.i) j.j)) :
    b.Band n s :=
  ⟨g,h,Bench.tab (t:=arrowTy) h _ a⟩

lemma noOrder (h : b.Digit n) :
    b.Band n (fun _ => Stroke.unmark) := by
  have hx := (slot h).run
  exact fresh h (fun i => Stroke.sound_unmark _) (hx.pair (Makes.one.pair hx))

lemma plain (h : b.Digit n) {l : ι→ℕ→ℕ} {u : ι→Line} (g : ∀ i, ∀ j<n i,l i j<n i)
    (hi : (b.scan n).Makes w (fun j => l j.i j.j))
    (hf : (b.scan n).Makes sc (fun j => u j.i j.j)) :
    b.Band n (fun i => Stroke.plain (n i) (l i) (u i)) := by
  refine fresh h (fun i => Stroke.plain_sound _ _ _ (g i))
    ((hi.pair (hf.pair (slot h).run)).congr ?_)
  intro d
  simp [emboss,Stroke.plain,d.hj]

lemma besideLeft {x} (h : b.Band n s) (hx : b.Digit x)
    (ha : ∀ i, x i<n i) :
    b.Makes arrowTy (fun i => emboss (Stroke.beside (n i) (s i) (t i)) (x i)) :=
  (h.showOne hx.run ha).congr (fun i => by simp [emboss,Stroke.beside,ha i])

lemma besideRight {x} (H : b.Digit n) (hx : b.Digit x) (h : b.Band e t)
    (hp : ∀ i,n i ≤ x i) (hk : ∀ i, x i-n i<e i) :
    b.Makes arrowTy (fun i => emboss (Stroke.beside (n i) (s i) (t i)) (x i)) := by
  have hd := h.showOne (hx.sub H).run hk
  have ha : b.Digit fun j => (t j).ix (x j-n j) :=
    ⟨hd.fst,h.width.small.mono (fun j => ((h.good j).bdix _ (hk j)).le)⟩
  have hb : b.Digit fun j => (t j).partner (x j-n j) :=
    ⟨hd.snd.snd,h.width.small.mono (fun j => ((h.good j).bdp _ (hk j)).le)⟩
  refine ((H.add ha).run.pair (hd.snd.fst.pair (H.add hb).run)).congr ?_
  intro d
  simp [emboss,Stroke.beside,Nat.not_lt.mpr (hp d)]

lemma beside (h : b.Band n s) (g : b.Band e t) :
    b.Band (fun i => n i+e i) (fun i => Stroke.beside (n i) (s i) (t i)) := by
  let W i := n i+e i
  have H : b.Digit W := h.width.add g.width
  refine fresh H (fun i => (h.good i).beside (g.good i)) ?_
  let M := b.scan W
  have hv := Feeds.scan b W
  have hx : M.Digit During.j := slot H
  let Q (d : During W) := d.j<n d.i
  have hs : M.Study Q := Study.lt hx (draw hv h.width)
  refine chooseM hs ?_ ?_
  · have hu := restricted M Q
    have Hw := (h.transfer hv).transfer hu
    exact besideLeft (t:=fun i => t i.val.i) Hw (draw hu hx) (fun i => i.property)
  · have hz := restricted M (fun i => ¬ Q i)
    have hf := (g.transfer hv).transfer hz
    refine besideRight (s:=fun i => s i.val.i) (draw hz (draw hv h.width)) (draw hz hx)
      hf (fun i => Nat.le_of_not_gt i.property) ?_
    intro j
    have h1 : j.val.j < n j.val.i + e j.val.i := j.val.hj
    have h2 : ¬ j.val.j<n j.val.i := j.property
    omega

lemma wider (h : b.Band n s) (k : b.Digit e) (hv : ∀ i,n i ≤ e i) :
    b.Band e s := by
  refine fresh k (fun i => (h.good i).wider (hv i)) ?_
  let P (d : During e) := d.j<n d.i
  have F := Feeds.scan b e
  have hd := h.transfer F
  have hj := slot k
  have hh : (b.scan e).Study P := Study.lt hj hd.width
  refine chooseM hh ?_ ?_
  · have G := restricted (b.scan e) P
    exact (hd.transfer G).showOne (draw G hj).run (fun i => i.property)
  · have G := restricted (b.scan e) (fun i => ¬P i)
    have hg := (draw G hj).run
    refine (hg.pair (Makes.one.pair hg)).congr ?_
    intro j
    have h1 : n j.val.i ≤ j.val.j := Nat.le_of_not_gt j.property
    simp [emboss,(h.good j.val.i).awayix _ h1,(h.good j.val.i).awayd _ h1,
      (h.good j.val.i).awayp _ h1]

end Band
end Bench
end
end PowerSaving.RAM

end OAI
