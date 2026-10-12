import OAI.Computability.FourierTransform.ToeplitzLayers
import OAI.Computability.FourierTransform.MeasuredPrograms

namespace OAI

namespace PowerSaving.RAM
open Ty Slant Spectral Complex
noncomputable section

universe U V
namespace Bench
variable {m : Bool} {ι : Type U} {κ : Type V} {b : Bench m ι} {q : Bench m κ}

lemma reach_digit {e : ι→ℕ} (h : b.Arch e) :
    b.Digit (fun i => reachSize (e i)) := by
  have H := h.span
  have hp := h.ep
  have ha : b.Digit fun _ => 16 := Digit.wc 16
  have hb := (Digit.wc 4).mul (((Digit.wc 80).mul (hp.sub (Digit.wc 4))).add (Digit.wc 348))
  exact iteN (Study.lt hp (Digit.wc 4)) (H.mul (H.mul (H.mul (Digit.wc 26))))
    (ha.mul (ha.mul (ha.mul hb)))

lemma chorus_small {e : ι→ℕ} (h : Small b.size e) :
    Small b.size (fun i => chorus (e i)) :=
  ((Small.const b.size 10000000).mul ((h.add (Small.const _ 1)).pow 2)).mono
    fun _ => chorus_le _

lemma chorus_digit {e : ι→ℕ} (h : b.Arch e) :
    b.Digit (fun i => chorus (e i)) := by
  let f (_ : ι) (j : ℕ) := chorus j
  refine ⟨loop (t:=w) h.ep f (Makes.wc 1) ?_,chorus_small (b:=b) h.ep.small⟩
  let P := b.climbs e w f
  have F := Feeds.climbs (t:=w) b e f
  have hi : P.Arch During.j :=
    (h.transfer F).below (stepi (t:=w) h.ep f) (fun j => j.hj.le)
  have hz : P.Digit (fun i => chorus i.j) :=
    ⟨stepsum (t:=w) b e f,chorus_small (b:=P) hi.ep.small⟩
  exact (hz.add (reach_digit hi)).run

structure Library (b : Bench m ι) (n t : ι→ℕ) (h g r : ι→Line) : Prop where
  ink : b.Hue fun _ => I
  gap : b.Fabric n h
  upper : b.Fabric n g
  root : b.Fabric t r
  hz : ∀ i, ∀ j<t i,r i j≠0

namespace Library
variable {t e n v : ι→ℕ} {h g r : ι→Line}

lemma transfer {n t : κ→ℕ} {h g r : κ→Line} (a : q.Library n t h g r) {f}
    (F : b.Feeds q f) :
    b.Library (fun i => n (f i)) (fun i => t (f i)) (fun i => h (f i))
      (fun i => g (f i)) (fun i => r (f i)) :=
  ⟨a.ink.transfer F,a.gap.transfer F,a.upper.transfer F,a.root.transfer F,fun _ => a.hz _⟩

lemma buildSpan (a : b.Library n t h g r) (H : b.Arch e) (hk : b.Digit v)
    (hg : ∀ i,e i+1<t i) (hp : ∀ i, 2^e i+v i ≤ n i) :
    b.Engrave (fun i => 2^e i+v i) (fun i => bridgeSpan (e i) (v i) (h i) (g i) (r i)) := by
  let P i := e i<4
  have B : b.Study P := Study.lt H.ep (Digit.wc 4)
  unfold bridgeSpan
  refine Engrave.fork B ?_ ?_
  · exact ((carve_sand a.gap a.upper a.ink hk H.span hp).transfer (restricted b P))
  · have F := restricted b (fun i => ¬P i)
    have Hb := H.sub (Digit.wc 4)
    have Hk : ∀ i,e i-4+1<t i := by intro i; have := hg i; omega
    have hr := a.root.pick Hb.succ.ep.run Hk
    have hz i := a.hz i (e i-4+1) (Hk i)
    have hS (i : {i // ¬P i}) := desc_num _ (show ¬e i.val<4 from i.property)
    refine (carve_reef (a.gap.transfer F) (a.upper.transfer F) (a.ink.transfer F)
      (draw F hk) (Hb.transfer F) (hr.transfer F) (fun i => hz _) ?_).congr
      ?_ (fun _ => rfl)
    · intro i; exact (by simpa only [hS i] using hp i.val)
    · intro i
      rw [← hS]

lemma buildHoop (a : b.Library n t h g r) (H : b.Arch e) (hk : b.Digit v)
    (hg : ∀ i,e i+1<t i) (hp : ∀ i,v i ≤ n i) {p q : ι→Reel}
    (hP : b.Engrave (fun i => min (2^e i) (v i)) p)
    (hQ : b.Engrave (fun i => v i-2^e i) q)
    (hx : ∀ i,(p i).beats=(q i).beats) :
    b.Engrave v (fun i => hoop (e i) (v i) (h i) (g i) (r i) (p i) (q i)) := by
  have hv := (hP.parallel hQ hx).congr
    (fun i => by exact (show min (2^e i) (v i)+(v i-2^e i)=v i by omega)) (fun _ => rfl)
  unfold hoop; dsimp only
  refine hv.stack (Engrave.fork (Study.lt H.span hk) ?_ ?_)
  · let P i := 2^e i<v i
    have F := restricted b P
    have hy (i : {i // P i}) : 2^(e i.val)+(v i.val-2^e i.val)=v i.val := by
      have h1 : 2^e i.val<v i.val := i.property
      omega
    exact ((a.transfer F).buildSpan (H.transfer F) (draw F (hk.sub H.span))
      (fun i => hg _) (fun i => (hy i).le.trans (hp _))).congr hy (fun _ => rfl)
  · exact (Engrave.rest hk (reach_digit H)).transfer (restricted ..)
end Library

def clipped (e v : ℕ) := min (2^e) v

def panel (h g r : Line) (e v : ℕ) : T filmTy :=
  film (clipped e v) (harp h g r e (clipped e v))

def canopy (h g r : Line) (e v : ℕ) : T (Ty.a filmTy) :=
  Tape.tab (v+1) (panel h g r e)

private lemma fromCanopy {h g r : ι→Line} {d v w : ι→ℕ}
    (hd : b.Arch d) (hk : b.Digit w) (hg : ∀ i,w i ≤ v i) (hh : ∀ i,w i ≤ 2^d i)
    (H : b.Makes (Ty.a filmTy) (fun i => canopy (h i) (g i) (r i) (d i) (v i))) :
    b.Engrave w (fun i => harp (h i) (g i) (r i) (d i) (w i)) := by
  have hp i : clipped (d i) (w i)=w i := min_eq_right (hh i)
  refine ⟨fun i => sound_harp _ _ _ _ _ (hh i),(chorus_digit hd).congr
    (fun i => (beats_harp _ _ _ _ _).symm), hk,?_⟩
  have hy := Makes.pick (n:=fun i => v i+1) (t:=filmTy)
    (fun i => panel (h i) (g i) (r i) (d i)) H hk.run (fun i => by
      exact Nat.lt_add_one_iff.mpr (hg i))
  exact hy.congr fun i => by simp only [panel,hp]

namespace Library
variable {t d n v : ι→ℕ} {h g r : ι→Line}

private lemma buildPanel (a : b.Library n t h g r) (hd : b.Arch d)
    (hp : ∀ i,v i ≤ n i) (ht : ∀ i,d i+1<t i)
    (H : b.Makes (Ty.a filmTy) fun i => canopy (h i) (g i) (r i) (d i) (v i)) {w}
    (hh : b.Digit w) (hk : ∀ i,w i ≤ v i) :
    b.Makes filmTy (fun i => panel (h i) (g i) (r i) (d i+1) (w i)) := by
  let W i := clipped (d i+1) (w i)
  let B i := 2^d i
  have hW : b.Digit W := hd.succ.span.minimum hh
  have HS i : W i ≤ v i := (min_le_right ..).trans (hk i)
  let p i j := harp (h i) (g i) (r i) (d i) j
  have hl := fromCanopy hd (hd.span.minimum hW)
    (fun i => (min_le_right ..).trans (HS i)) (fun _ => min_le_left ..) H
  have hx := fromCanopy hd (hW.sub hd.span)
    (fun i => (Nat.sub_le ..).trans (HS i))
    (fun i => branch_smaller (d i) _ (min_le_left ..)) H
  have ht' := a.buildHoop hd hW ht (fun i => (HS i).trans (hp i)) hl hx (fun i =>
    (beats_harp _ _ _ _ _).trans (beats_harp _ _ _ _ _).symm)
  refine ht'.layers.congr ?_
  intro i
  simp only [panel, harp, W]

private lemma wholeCanopy (a : b.Library n t h g r) (hd : b.Arch d) (hA : b.Digit v)
    (hn : ∀ i,0<n i) (hp : ∀ i,v i ≤ n i) (ht : ∀ i,d i<t i) :
    b.Makes (Ty.a filmTy) (fun i => canopy (h i) (g i) (r i) (d i) (v i)) := by
  let x i e := canopy (h i) (g i) (r i) e (v i)
  let c i := v i+1
  have hc := hA.add (Digit.wc 1)
  refine loop (t:=Ty.a filmTy) hd.ep x ?_ ?_
  · refine tab (t:=filmTy) hc (fun i => panel (h i) (g i) (r i) 0) ?_
    have hw : (b.scan c).Digit (fun i => clipped 0 i.j) :=
      ((Digit.wc 1).minimum (slot hc)).congr (fun i => by rw [clipped,pow_zero])
    have hh := (a.gap.pick (Makes.wc 0) hn).transfer (Feeds.scan b c)
    have H := Engrave.swatch hw _ (Fabric.flat hh)
    exact H.layers
  · let P := b.climbs d (Ty.a filmTy) x
    have F := Feeds.climbs b d x
    have hb := draw F hc
    refine tab (t:=filmTy) hb (fun i => panel (h i.i) (g i.i) (r i.i) (i.j+1)) ?_
    have G := Feeds.scan P fun i => c i.i
    have hk : P.Arch During.j := (hd.transfer F).below (stepi hd.ep x) (fun i => i.hj.le)
    exact (a.transfer (G.next F)).buildPanel (v:=fun i => v i.i.i) (hk.transfer G)
      (fun i => hp _) (fun i => (Nat.add_one_le_iff.mpr i.i.hj).trans_lt (ht _))
      (pull G (stepsum b d x)) (slot hb) (fun i => by
        have hh : i.j<v i.i.i+1 := i.hj
        exact Nat.lt_add_one_iff.mp hh)

lemma buildHarp (a : b.Library n t h g r) (hd : b.Arch d) (hA : b.Digit v)
    (hn : ∀ i,0<n i) (hp : ∀ i,v i ≤ n i) (ht : ∀ i,d i<t i)
    (hw : ∀ i,v i ≤ 2^d i) :
    b.Engrave v (fun i => harp (h i) (g i) (r i) (d i) (v i)) :=
  fromCanopy hd hA (fun _ => le_rfl) hw (wholeCanopy a hd hA hn hp ht)

end Library
end Bench
end
end PowerSaving.RAM

end OAI
