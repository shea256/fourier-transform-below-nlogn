import OAI.Computability.FourierTransform.ScalarPreparation
import OAI.Computability.FourierTransform.ToeplitzUpdates

namespace OAI

namespace PowerSaving.RAM
open Ty Slant Slant.Stroke Spectral Complex
noncomputable section

universe U
namespace Bench
variable {m : Bool} {ι : Type U} {b : Bench m ι}

lemma Fabric.frequency {u : ι→Line} {n : ι→ℕ} {r : ι→ℂ}
    (h : b.Fabric n u) (g : b.Digit n) (k : b.Hue r) {a} (hk : b.Digit a) :
    b.Hue (fun i => freq (n i) (r i) (u i) (a i)) := by
  have F := Feeds.scan b n
  exact Hue.sum g (fun i j => r i ^ (a i * j) * u i j)
    (((k.transfer F).exponent ((draw F hk).mul (slot g))).mul h)

lemma Fabric.spectrum {u : ι→Line} {n : ι→ℕ} {r : ι→ℂ}
    (h : b.Fabric n u) (g : b.Digit n) (k : b.Hue r) :
    b.Fabric n (fun i => freq (n i) (r i) (u i)) := by
  have F := Feeds.scan b n
  exact (h.transfer F).frequency (draw F g) (k.transfer F) (slot g)

section
variable {u a c : ι→Zone} {n : ι→ℕ} (hv : b.Hue fun _ => I) (hk : b.Digit n)

include hv hk

lemma Spots.trail (h : b.Spots u) (g : b.Spots a) (hg : ∀ i,(u i).wide ≤ (a i).wide)
    (p : ∀ i,(u i).Fits (n i)) (s : ∀ i,(a i).Fits (n i)) (j : ∀ i,(u i).Sep (a i))
    {x : ι→ℂ} (hp : b.Hue x) :
    b.Engrave n (fun i => Slant.trail (u i) (a i) (x i)) :=
  (g.slim h.wide).flash h hk (fun i => (s i).slim (hg i)) p (fun _ => rfl)
    (fun i => ((j i).slim_right (hg i)).symm) hv (Fabric.flat hp)

lemma Spots.slice (h : b.Spots u) (g : b.Spots a) (hg : ∀ i,(u i).wide ≤ (a i).wide)
    (p : ∀ i,(u i).Fits (n i)) (s : ∀ i,(a i).Fits (n i)) (j : ∀ i,(u i).Sep (a i))
    {x : ι→ℂ} (hp : b.Hue x) :
    b.Engrave n (fun i => Slant.slice (a i) (u i) (x i)) :=
  h.flash (g.slim h.wide) hk p (fun i => (s i).slim (hg i)) (fun _ => rfl)
    (fun i => (j i).slim_right (hg i)) hv (Fabric.flat hp)

variable {e : ι→ℕ} {r : ι→ℂ} (ha : b.Spots a) (hc : b.Spots c)
    (he : b.Arch e) (hr : b.Hue r) (hz : ∀ i,r i≠0)
    (ua : ∀ i,(a i).wide=2^e i) (uc : ∀ i,(c i).wide=2^e i)
    (pa : ∀ i,(a i).Fits (n i)) (pc : ∀ i,(c i).Fits (n i)) (ac : ∀ i,(a i).Sep (c i))

include ha hc he hr hz ua uc pa pc ac

lemma Spots.eddy {f : ι→Line} (h : b.Fabric (fun i => 2^e i) f) :
    b.Engrave n (fun i => Slant.eddy (e i) (r i) (a i) (c i) (f i)) := by
  let T i := 2^e i
  have H (v : ι→Zone) (hh : b.Spots v) (tv : ∀ i,(v i).wide=T i)
      (pv : ∀ i,(v i).Fits (n i)) {x : ι→Reel} (p : b.Engrave T x) :
      b.Engrave n (fun i => Reel.atBase (v i).lo (x i)) :=
    (p.mount hh.low).wider hk fun i => by
      rw [← tv]
      exact (pv i).end_le (by rw [tv]; unfold T; positivity)
  have fp := print_pulse hv he hr
  have bp := print_backPulse hv he hr hz
  have fg := h.spectrum he.span hr
  have fg' : b.Fabric (fun i => (c i).wide) (fun i => freq (2^e i) (r i) (f i)) := by
    simp_rw [uc]
    exact fg
  have w := hc.flash ha hk pc pa (fun i => (uc i).trans (ua i).symm)
    (fun i => (ac i).symm) hv fg'
  exact ((((H a ha ua pa fp).stack (H c hc uc pc fp)).stack w).stack
    (H a ha ua pa bp)).stack (H c hc uc pc bp)

variable (hu : b.Spots u) (hg : ∀ i,(u i).wide ≤ (a i).wide)
  (pu : ∀ i,(u i).Fits (n i)) (hup : ∀ i,(u i).Sep (a i))
include hu hg pu hup
lemma Spots.duct {f : ι→Line} (h : b.Fabric (fun i => 2^e i) f) :
    b.Engrave n (fun i => Slant.duct (e i) (r i) (u i) (a i) (c i) (f i)) := by
  exact engrave_cameo (hu.trail hv hk ha hg pu pa hup Hue.one)
    (ha.eddy hv hk hc he hr hz ua uc pa pc ac h)
    (hu.trail hv hk ha hg pu pa hup Hue.one.neg)
    (ha.eddy hv hk hc he hr hz ua uc pa pc ac h.neg)

lemma Spots.well {v : ι→Zone} (hh : b.Spots v) (hy : ∀ i,(v i).wide ≤ (c i).wide)
    (pv : ∀ i,(v i).Fits (n i)) (hp : ∀ i,(v i).Sep (c i)) {f : ι→Line}
    (h : b.Fabric (fun i => 2^e i) f) :
    b.Engrave n (fun i => Slant.well (e i) (r i) (u i) (v i) (a i) (c i) (f i)) :=
  engrave_cameo (ha.duct hv hk hc he hr hz ua uc pa pc ac hu hg pu hup h)
    (hh.slice hv hk hc hy pv pc hp Hue.one)
    (ha.duct hv hk hc he hr hz ua uc pa pc ac hu hg pu hup h.neg)
    (hh.slice hv hk hc hy pv pc hp Hue.one.neg)

end

lemma Fabric.riseEntry {f : ι→Line} {n p q : ι→ℕ}
    (h : b.Fabric n f) (a : b.Digit p) (c : b.Digit q) (hk : ∀ i, p i<n i) :
    b.Hue (fun i => rise (f i) (p i) (q i)) := by
  have H := h.pick (a.sub c).run (fun i => (Nat.sub_le ..).trans_lt (hk i))
  exact Hue.fork (Study.le c a) (H.transfer (restricted ..)) Hue.zero

lemma Fabric.skirtEntry {B u v l e n j : ι→ℕ} {f : ι→Line} (h : b.Digit B)
    (a : b.Digit u) (c : b.Digit v) (d : b.Digit l) (g : b.Digit e)
    (hz : b.Fabric n f)
    (hk : ∀ i, ∀ j<v i, e i+j<n i) (hh : b.Digit j) :
    b.Hue (fun i => skirt (B i) (u i) (v i) (l i) (e i) (f i) (j i)) := by
  let f1 (i : ι) : ℂ := if j i < v i then rise (f i) (e i+j i) (l i) else 0
  have H1 : b.Hue f1 := by
    let P (i : ι) := j i<v i
    have F := restricted b P
    exact Hue.fork (Study.lt hh c) ((hz.transfer F).riseEntry (draw F (g.add hh))
      (draw F d) (fun i => hk _ _ i.property)) Hue.zero
  let w i := 2*B i-j i
  let f2 (i : ι) : ℂ := if 0<v i ∧ w i<u i then rise (f i) (e i) (l i+w i) else 0
  have H2 : b.Hue f2 := by
    let P (i : ι) := 0<v i ∧ w i<u i
    have F := restricted b P
    have hw : b.Digit w := ((Digit.wc 2).mul h).sub hh
    have hp : b.Study P := (Study.lt (Digit.wc 0) c).both (Study.lt hw a)
    exact Hue.fork hp ((hz.transfer F).riseEntry (draw F g)
      (draw F (d.add hw)) (fun i => by simpa only [add_zero] using hk _ 0 i.property.1)) Hue.zero
  exact Hue.fork (Study.lt hh h) (f:=f1) (g:=f2) (H1.transfer (restricted ..))
    (H2.transfer (restricted ..))

lemma Spots.bore {k n : ι→ℕ} {r : ι→ℂ} (hd : b.Arch k) (hr : b.Hue r)
    (hz : ∀ i,r i≠0) (hn : b.Digit n) (hi : b.Hue fun _ => I)
    {u v a c : ι→Zone} (hu : b.Spots u) (hv : b.Spots v) (ha : b.Spots a) (hc : b.Spots c)
    (ua : ∀ i,(a i).wide=2^(k i+1)) (uc : ∀ i,(c i).wide=2^(k i+1))
    (pu : ∀ i,(u i).Fits (n i)) (pv : ∀ i,(v i).Fits (n i))
    (pa : ∀ i,(a i).Fits (n i)) (pc : ∀ i,(c i).Fits (n i))
    (ac : ∀ i,(a i).Sep (c i))
    (hg : ∀ i,(u i).wide ≤ 2^k i) (hh : ∀ i,(v i).wide ≤ 2^k i)
    (hup : ∀ i,(u i).Sep (a i)) (hvc : ∀ i,(v i).Sep (c i)) {l s e : ι→ℕ}
    (hl : b.Digit l) (hs : b.Digit s)
    {f : ι→Line} (h : b.Fabric e f) (hS : ∀ i, ∀ j<(v i).wide, s i+j<e i) :
    b.Engrave n (fun i => Slant.bore (k i) (r i) (u i) (v i) (a i) (c i)
      (l i) (s i) (f i)) := by
  unfold Slant.bore
  refine ha.well hi hn hc hd.succ hr hz ua uc pa pc ac hu
    (fun i => by rw [ua,pow_succ]; have := hg i; omega) pu hup hv
    (fun i => by rw [uc,pow_succ]; have := hh i; omega) pv hvc ?_
  have F := Feeds.scan b fun i => 2^(k i+1)
  exact (h.transfer F).skirtEntry (draw F hd.span) (draw F hu.wide)
    (draw F hv.wide) (draw F hl) (draw F hs) (fun i => hS i.i) (slot hd.succ.span)

end Bench
end
end PowerSaving.RAM

end OAI
