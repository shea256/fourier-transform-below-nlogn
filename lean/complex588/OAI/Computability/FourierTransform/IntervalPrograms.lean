import OAI.Computability.FourierTransform.WordCompilation
import OAI.Computability.FourierTransform.DisjointIntervals

namespace OAI

namespace PowerSaving.RAM
open Ty Slant Slant.Stroke Complex
noncomputable section

universe U V
namespace Bench
variable {m : Bool} {ι : Type U} {κ : Type V} {b : Bench m ι} {q : Bench m κ}

structure Spots (b : Bench m ι) (u : ι→Zone) : Prop where
  low : b.Digit (fun i => (u i).lo)
  wide : b.Digit (fun i => (u i).wide)

namespace Spots
variable {u v : ι→Zone} {n : ι→ℕ}
lemma transfer {f : ι→κ} {x : κ→Zone} (h : q.Spots x) (g : b.Feeds q f) :
    b.Spots (fun i => x (f i)) := ⟨draw g h.low,draw g h.wide⟩
lemma has (h : b.Spots u) {x} (hh : b.Digit x) :
    b.Study (fun i => (u i).has (x i)) :=
  (Study.le h.low hh).both (Study.lt hh (h.low.add h.wide))

lemma overlay (h : b.Spots u) {x} (hh : b.Digit x) {l : ι→Line}
    (g : b.Fabric (fun i => (u i).wide) l) {p} (hk : b.Hue p) :
    b.Hue (fun i => if (u i).has (x i) then l i (x i-(u i).lo) else p i) := by
  let P i := (u i).has (x i)
  have H := h.has hh
  refine Hue.fork H ?_ (hk.transfer (restricted b fun i => ¬P i))
  have M := restricted b P
  have hu (i : {i // P i}) := (u i.val).enter i.property
  exact (g.transfer M).pick (draw M (hh.sub h.low)).run hu

lemma shade (h : b.Spots u) (k : b.Spots v) {l g : ι→Line}
    (hf : b.Fabric (fun i => (u i).wide) l)
    (hg : b.Fabric (fun i => (v i).wide) g) (hn : b.Digit n)
    (ha : ∀ i,(u i).Fits (n i)) (hb : ∀ i,(v i).Fits (n i)) :
    b.Engrave n (fun i => Slant.shade (u i) (v i) (l i) (g i)) := by
  unfold Slant.shade
  refine Engrave.single (Band.fresh hn ?_ ?_)
  · intro i; exact sound_shade (f:=l i) (g:=g i) (ha i) (hb i) 0 (show 0<1 by omega)
  · have H := Feeds.scan b n
    have hx := slot hn
    exact hx.run.pair ((((h.transfer H).overlay hx (hf.transfer H)
      ((k.transfer H).overlay hx (hg.transfer H) Hue.one)).bright).pair hx.run)

lemma finds (h : b.Spots u) (k : b.Spots v) {x} (hh : b.Digit x) :
    b.Digit (fun i => Slant.jumps (u i) (v i) (x i)) :=
  iteN (h.has hh) (k.low.add (hh.sub h.low))
    (iteN (k.has hh) (h.low.add (hh.sub k.low)) hh)

lemma snap (h : b.Spots u) (k : b.Spots v) (hn : b.Digit n)
    (ha : ∀ i,(u i).Fits (n i)) (hb : ∀ i,(v i).Fits (n i))
    (hx : ∀ i,(u i).wide=(v i).wide) (hg : ∀ i,(u i).Sep (v i)) :
    b.Engrave n (fun i => Slant.snap (u i) (v i)) := by
  unfold Slant.snap
  refine Engrave.single (Band.fresh hn ?_ ?_)
  · intro i; exact sound_snap (ha i) (hb i) (hx i) (hg i) 0 (show 0<1 by omega)
  · have H := Feeds.scan b n
    exact (slot hn).run.pair (Makes.one.pair
      (((h.transfer H).finds (k.transfer H) (slot hn)).run))

lemma slim (h : b.Spots u) (k : b.Digit n) :
    b.Spots (fun i => (u i).slim (n i)) := ⟨h.low,k⟩

end Spots

/- Numeric convenience -/
lemma Hue.smallNumeral (b : Bench m ι) (n : ℕ) [Nat.AtLeastTwo n] :
    b.Hue (fun _ => (OfNat.ofNat n:ℂ)) := (Hue.numeral n).congr fun _ => rfl

section
variable {n : ι→ℕ} {u v : ι→Zone} (h : b.Spots u) (k : b.Spots v)
    (hn : b.Digit n)
    (ha : ∀ i,(u i).Fits (n i)) (hb : ∀ i,(v i).Fits (n i))
    (hx : ∀ i,(u i).wide=(v i).wide) (hg : ∀ i,(u i).Sep (v i))
    (hy : b.Hue fun _ => I)

include h k hn ha hb hx hg hy

lemma Spots.hinge :
    b.Engrave n (fun i => Slant.hinge (u i) (v i)) :=
  ((h.shade k Fabric.one (Fabric.flat hy) hn ha hb).stack (h.snap k hn ha hb hx hg)).stack
    (h.shade k (Fabric.flat (Hue.one.sub hy)) (Fabric.flat (Hue.one.add hy)) hn ha hb)

lemma Spots.brick :
    b.Engrave n (fun i => Slant.brick (u i) (v i)) :=
  have H := h.hinge k hn ha hb hx hg hy
  have p := h.shade k (Fabric.flat (Hue.smallNumeral b 3).neg) Fabric.one hn ha hb
  have q := h.shade k (Fabric.flat (Hue.smallNumeral b 2)) Fabric.one hn ha hb
  (((H.stack p).stack H).stack q).stack H

lemma Spots.spark {f : ι→Line}
    (hh : b.Fabric (fun i => (u i).wide) f) (hf : ∀ i, ∀ j<(u i).wide, f i j ≠ 0) :
    b.Engrave n (fun i => Slant.spark (u i) (v i) (f i)) := by
  let F (i : ι) : Line := fun j => 4*f i j/5
  let U i := (u i).wide
  have H : b.Fabric U F :=
    Hue.div ((Hue.smallNumeral (b.scan U) 4).mul hh) (Hue.smallNumeral _ 5)
      (by intro i; norm_num)
  have hx' : ∀ i, ∀ j<U i, F i j≠0 := fun i j hj => by simp [F,hf i j hj]
  have hc6 : b.Hue (fun _ => -1/6) := Hue.one.neg.div (Hue.smallNumeral _ 6) (by
    intro i; norm_num)
  have hc8 : b.Hue (fun _ => -1/8) := Hue.one.neg.div (Hue.smallNumeral _ 8) (by
    intro i; norm_num)
  have hP := h.shade k (H.inv hx') Fabric.one hn ha hb
  have hQ := h.shade k ((Fabric.flat hc8).mul H) (Fabric.flat hc6) hn ha hb
  exact (hP.stack (h.brick k hn ha hb hx hg hy)).stack hQ

lemma Spots.flash {f : ι→Line} (hh : b.Fabric (fun i => (u i).wide) f) :
    b.Engrave n (fun i => Slant.flash (u i) (v i) (f i)) := by
  have hk : b.Fabric (fun i => (u i).wide) (fun i => blaze (f i)) :=
    Fabric.one.add (hh.mul hh.flip)
  exact (h.spark k hn ha hb hx hg hy hk (fun i j _ => blaze_ne _ _)).stack
    (h.spark k hn ha hb hx hg hy (hh.sub hk) (fun i j _ => after_ne _ _))

end

lemma engrave_cameo {n : ι→ℕ} {p u v z : ι→Reel}
    (hp : b.Engrave n p) (hu : b.Engrave n u)
    (hv : b.Engrave n v) (hz : b.Engrave n z) :
    b.Engrave n fun i => cameo (p i) (u i) (v i) (z i) :=
  ((hp.stack hu).stack hv).stack hz

end Bench
end
end PowerSaving.RAM

end OAI
