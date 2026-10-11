import OAI.Computability.FourierTransform.LayerPrograms

namespace OAI

namespace PowerSaving.RAM
open Ty Slant Slant.Stroke
noncomputable section

universe U V
namespace Bench
variable {m : Bool} {ι : Type U} {κ : Type V} {b : Bench m ι} {q : Bench m κ}

def tickCount {ι : Type*} (r : ι→Reel) := fun i => (r i).beats

structure Engrave (b : Bench m ι) (n : ι→ℕ) (r : ι→Reel) : Prop where
  sound : ∀ i,(r i).Sound (n i)
  count : b.Digit (tickCount r)
  width : b.Digit n
  layers : b.Makes filmTy (fun i => film (n i) (r i))

namespace Engrave
variable {n e : ι→ℕ} {r u : ι→Reel}

lemma transfer {f : ι→κ} {n : κ→ℕ} {s : κ→Reel} (h : q.Engrave n s) (g : b.Feeds q f) :
    b.Engrave (fun i => n (f i)) (fun i => s (f i)) :=
  ⟨fun i => h.sound (f i),draw g h.count,draw g h.width,pull g h.layers⟩

lemma plate (h : b.Engrave n r) (t : ι→ℕ) (ht : b.Makes w t) (hz : ∀ i,t i < tickCount r i) :
    b.Band n fun i => (r i).atBeat (t i) :=
  ⟨fun i => h.sound i (t i) (hz i),h.width,Makes.pick (t:=stripeTy) (n:=tickCount r)
    (fun i j => stripe (n i) ((r i).atBeat j)) h.layers ht hz⟩

lemma full (h : ∀ i,(r i).Sound (n i)) (hk : b.Digit (tickCount r)) (hw : b.Digit n)
    (hh : (b.scan (tickCount r)).Makes stripeTy fun d => stripe (n d.i) ((r d.i).atBeat d.j)) :
    b.Engrave n r := ⟨h,hk,hw, Bench.tab (t:=stripeTy) hk _ hh⟩

lemma single {p : ι→Stroke} (h : b.Band n p) :
    b.Engrave n (fun i => Reel.tick (p i)) :=
  full (fun i => Reel.sound_tick (h.good i)) (Digit.wc 1)
    h.width (pull (Feeds.scan b (fun _ => 1)) h.sheet)

lemma rest (h : b.Digit n) {e} (hh : b.Digit e) :
    b.Engrave n (fun i => Reel.wait (e i)) :=
  full (fun _ => Reel.sound_wait _ _) hh h (pull (Feeds.scan b e) (Band.noOrder h).sheet)

lemma stack (h : b.Engrave n r) (g : b.Engrave n u) :
    b.Engrave n (fun i => (r i).stack (u i)) := by
  let M i := (r i).beats+(u i).beats
  have hm : b.Digit M := h.count.add g.count
  refine full (fun i => (h.sound i).stack (g.sound i)) hm h.width ?_
  let P := b.scan M
  have F := Feeds.scan b M
  let Q (d : During M) := d.j<(r d.i).beats
  have hp : P.Digit During.j := slot hm
  have hq := h.transfer F
  have hr : P.Study Q := Study.lt hp hq.count
  refine chooseM hr ?_ ?_
  · have H := restricted P Q
    refine ((hq.transfer H).plate _ (draw H hp).run (fun i => i.property)).sheet.congr ?_
    intro j
    simp [Reel.stack, show j.val.j<(r j.val.i).beats from j.property]
  · have G := restricted P (fun i => ¬Q i)
    have hh := (g.transfer F).transfer G
    have hk := (draw G hp).sub (draw G hq.count)
    have hx : ∀ i : {j // ¬ Q j}, i.val.j-(r i.val.i).beats < (u i.val.i).beats := by
      intro i
      have hg : i.val.j<(r i.val.i).beats+(u i.val.i).beats := i.val.hj
      have hh : ¬ i.val.j<(r i.val.i).beats := i.property
      omega
    refine (hh.plate _ hk.run hx).sheet.congr ?_
    intro j; simp [Reel.stack,tickCount,show ¬ j.val.j<(r j.val.i).beats from j.property]

lemma parallel (h : b.Engrave n r) (g : b.Engrave e u) (hk : ∀ i,(r i).beats=(u i).beats) :
    b.Engrave (fun i => n i+e i) (fun i => Reel.parallel (n i) (r i) (u i)) := by
  refine full (fun i => (h.sound i).parallel (g.sound i) (hk i)) h.count
    (h.width.add g.width) ?_
  have F := Feeds.scan b (tickCount r)
  have hi := (slot h.count).run
  have hs := (h.transfer F).plate During.j hi During.hj
  have hv : ∀ d : During (tickCount r), d.j<(u d.i).beats := by
    intro j; rw [← hk]
    exact j.hj
  exact (hs.beside ((g.transfer F).plate During.j hi hv)).sheet

lemma wider (h : b.Engrave n r) (k : b.Digit e) (hI : ∀ i,n i ≤ e i) :
    b.Engrave e r := by
  refine full (fun i => (h.sound i).wider (hI i)) h.count k ?_
  have F := Feeds.scan b (tickCount r)
  exact (((h.transfer F).plate During.j (slot h.count).run During.hj).wider (draw F k)
    (fun i => hI _)).sheet

lemma mount (h : b.Engrave n r) (k : b.Digit e) :
    b.Engrave (fun i => e i+n i) (fun i => Reel.atBase (e i) (r i)) :=
  (rest k h.count).parallel h (fun _ => rfl)

lemma switch {P : ι→Prop} (hp : b.Study P)
    (h : (b.scrutin P).Engrave (fun i => n i.val) (fun i => r i.val))
    (hh : (b.scrutin (fun i => ¬ P i)).Engrave (fun i => n i.val) (fun i => r i.val)) :
    b.Engrave n r :=
  ⟨fun i => by
    by_cases hi : P i
    · exact h.sound ⟨i,hi⟩
    · exact hh.sound ⟨i,hi⟩,
    chooseN hp h.count hh.count,chooseN hp h.width hh.width,chooseM hp h.layers hh.layers⟩

lemma congr (h : b.Engrave n r) (g : ∀ i,n i=e i) (k : ∀ i,r i=u i) :
    b.Engrave e u := by rwa [← funext g,← funext k]

lemma fork {P : ι→Prop} [DecidablePred P] (hp : b.Study P)
    (h : (b.scrutin P).Engrave (fun i => n i.val) (fun i => r i.val))
    (hh : (b.scrutin (fun i => ¬P i)).Engrave (fun i => n i.val) (fun i => u i.val)) :
    b.Engrave n (fun i => if P i then r i else u i) :=
  switch hp (h.congr (fun _ => rfl) (fun i => (ite_eq_left i.property).symm))
    (hh.congr (fun _ => rfl) (fun i => (ite_eq_right i.property).symm))

lemma plain (l : ι→ℕ→ℕ) (x : ι→Line) (h : b.Digit n)
    (ha : ∀ i, ∀ j<n i,l i j<n i)
    (g : (b.scan n).Makes w (fun i => l i.i i.j)) (k : b.Fabric n x) :
    b.Engrave n (fun i => Reel.tick (Stroke.plain (n i) (l i) (x i))) :=
  single (Band.plain h ha g k.bright)

lemma swatch (h : b.Digit n) (x : ι→Line) (k : b.Fabric n x) :
    b.Engrave n (fun i => Reel.swatch (n i) (x i)) :=
  plain _ _ h (fun _ _ hi => hi) (slot h).run k

lemma lace (l : ι→ℕ→ℕ) (h : b.Digit n)
    (ha : ∀ i, ∀ j<n i,l i j<n i)
    (g : (b.scan n).Makes w (fun i => l i.i i.j)) :
    b.Engrave n (fun i => Reel.lace (n i) (l i)) :=
  plain _ _ h ha g Fabric.one
end Engrave
end Bench
end
end PowerSaving.RAM

end OAI
