import OAI.Computability.FourierTransform.SectorAlgorithm

namespace OAI

/-! Algorithm for the synchronized forest. -/
namespace PowerSaving.RAM
open Ty Finset Grove Slant
noncomputable section

universe U V
namespace Bench
variable {m : Bool} {ι : Type U} {κ : Type V} {b : Bench m ι} {q : Bench m κ}
  {cl : Paint} {l d : ι → ℕ} {r : ι→Axes} {u : ι→ℕ→Stroke} {x : ι→Line}

lemma tapeCongr {α : Type*} (n : ℕ) (x y : ℕ → α) (h : ∀ i<n,x i=y i) :
    Tape.tab n x=Tape.tab n y := by
  unfold Tape.tab
  congr 1
  funext i; exact h _ i.isLt

namespace Bough

theorem water (h : b.Bough l r u) (hI : b.Moves (fun _ => 0) sc fun _ => Complex.I)
    (hx : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (extent (r i) (l i)) (x i)) :
    b.Moves (fun i => extent (r i) (l i)*hills (l i)) (a (c cl)) fun i =>
      Tape.tab (extent (r i) (l i))
        (graft (extent (r i) (l i)) (canopy (r i) (fun j => leafC (u i j)) (l i)) (x i)) := by
  let n i := extent (r i) (l i)
  let V i := mosaic (r i) (u i) (l i)
  let Y i := upholstery (n i) (V i)
  let D := b.extend (a chipTy) Y
  have F := Instant.extend b Y (t:=a chipTy)
  have hn : b.Nick n := ⟨hx.len h.fen.span,h.fen.span⟩
  have he : D.Matting n l V :=
    ⟨hn.transfer F,fun i => mosaic_quilt _ _ _ (h.fen.good i) (h.good i),
      cherry b Y (t:=a chipTy)⟩
  have hd : Dom (fun i => n i*hills (l i)) n :=
    Dom.of_le (fun i => Nat.le_mul_of_pos_right _ (hills_pos _))
  have ht := caseM (h.bedding.weaken hd) (he.cardT (hx.transfer F) (hI.transfer F))
  exact ht.congr fun i => tapeCongr (n i) _ _ fun j hj =>
    (graft_glimpse _ _ _ (h.fen.good i) (h.good i) _ _ hj).symm

theorem swell (h : b.Bough l r u) (hI : b.Moves (fun _ => 0) sc fun _ => Complex.I)
    (hx : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (extent (r i) (l i)) (x i)) :
    b.Moves (fun i => extent (r i) (l i)*hills (l i)) (a (c cl)) fun i =>
      Tape.tab (extent (r i) (l i))
        (graft (extent (r i) (l i)) (canopy (r i) (fun j => leafC (u i j)) (l i))
          (graft (extent (r i) (l i)) (canopy (r i) (fun j => leafM (u i j)) (l i))
            (x i))) := by
  let n i := extent (r i) (l i)
  let f i := graft (n i) (canopy (r i) (fun j => leafM (u i j)) (l i)) (x i)
  let y i := Tape.tab (n i) (f i)
  let D := b.extend (a (c cl)) y
  have F := Instant.extend b y (t:=a (c cl))
  have ht := (h.transfer F).water (x:=f) (hI.transfer F)
    (cherry b y (t:=a (c cl)))
  exact caseM ((h.glean cl x hx).weaken (Dom.of_le (fun i => Nat.le_mul_of_pos_right _
    (hills_pos _)))) ht
end Bough

/-- Given number of beats and axes, tape of trees (exact-width layer schedules + metadata). -/
structure Thicket (b : Bench m ι) (l d : ι→ℕ) (r : ι→Axes) (u : ι → ℕ → Reel) : Prop where
  fen : b.Fen l r
  beats : b.Nick d
  sounds : ∀ i, ∀ j<l i, (u i j).Sound (r i j)
  length : ∀ i, ∀ j<l i, (u i j).beats=d i
  atlas : b.Moves (fun _ => 0) (a treeTy) fun i =>
    Tape.tab (l i) fun j => treeT (r i j) (u i j)

variable {pV : ι → ℕ → Reel}
namespace Thicket

lemma transfer {l d : κ→ℕ} {r : κ→Axes} {u : κ → ℕ→Reel} (h : q.Thicket l d r u)
    {f} (g : b.Instant q f) :
    b.Thicket (fun i => l (f i)) (fun i => d (f i)) (fun i => r (f i)) (fun i => u (f i)) :=
  ⟨h.fen.transfer g,h.beats.transfer g,fun _ => h.sounds _,fun _ => h.length _,
    h.atlas.transfer g⟩

lemma digitize (h : b.Thicket l d r pV) {t} (ht : b.Nick t) (hk : ∀ i,t i<d i) :
    b.Bough l r (fun i j => (pV i j).atBeat (t i)) := by
  let T i j := treeT (r i j) (pV i j)
  let D := b.scan l
  have F := Instant.scan b l
  have hh (i : During l) : t i.i < (pV i.i i.j).beats := by rw [h.length _ _ i.hj]; exact hk _
  refine ⟨h.fen,fun i => h.sounds i.i i.j i.hj (t i.i) (hh i),?_⟩
  have hx := Moves.pick (t:=treeTy) (n:=fun i : During l => l i.i)
    (fun i => T i.i) (h.atlas.transfer F) (chop h.fen.high).close During.hj
  exact Moves.pick (t:=leafTy) (n:=fun i => (pV i.i i.j).beats) _ hx (ht.transfer F).close hh

/-- Run synchronized transform. Input tape in mixed-radix order, output likewise. -/
theorem conduct (h : b.Thicket l d r pV) (hI : b.Moves (fun _ => 0) sc fun _ => Complex.I)
    (hx : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (extent (r i) (l i)) (x i)) :
    b.Moves (fun i => d i* (extent (r i) (l i)*hills (l i)))
      (a (c cl)) fun i => Tape.tab (extent (r i) (l i))
        (forest (r i) (l i) (pV i) (x i) (d i)) := by
  let n i := extent (r i) (l i)
  let T i := forest (r i) (l i) (pV i) (x i)
  let A i j := Tape.tab (n i) (T i j)
  have F := Instant.climbs b d (t:=a (c cl)) A
  have ht := (h.transfer F).digitize (stride h.beats (t:=a (c cl)) A) During.hj
  have he := ht.swell (x:=fun i => T i.i i.j) (hI.transfer F) (tokenNow b d (t:=a (c cl)) A)
  have hu := repeatM h.beats A hx he (u:=fun i _ => n i*hills (l i)) (t:=a (c cl))
  refine hu.weaken ?_
  refine ⟨2,fun i => ?_⟩
  have hh := Nat.le_mul_of_pos_right (d i) (Nat.mul_pos (h.fen.good i).extent_pos
    (hills_pos (l i)))
  simp only [sum_const,card_range,smul_eq_mul]
  unfold n
  omega

theorem stream (h : b.Thicket l d r pV) (hI : b.Moves (fun _ => 0) sc fun _ => Complex.I)
    (hx : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (extent (r i) (l i)) (x i))
    (X : ι→ℕ→Wood) (hg : ∀ i, ∀ j<l i, Creates (pV i j) (r i j) (Grove.frame _ (X i j))) :
    b.Moves (fun i => d i*(extent (r i) (l i)*hills (l i)))
      (a (c cl)) fun i => Tape.tab (extent (r i) (l i))
        (graft (extent (r i) (l i)) (canopy (r i) (X i) (l i)) (x i)) :=
  (h.conduct hI hx).congr fun i =>
    tapeCongr _ _ _ fun j hj => forest_completes (r i) (l i) (pV i) (h.fen.good i)
      (d i) (h.sounds i) (h.length i) (X i) (hg i) (x i) j hj

end Thicket
end Bench
end
end PowerSaving.RAM

end OAI
