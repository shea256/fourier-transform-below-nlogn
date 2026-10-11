import OAI.Computability.FourierTransform.ChunkCompiler
import OAI.Computability.FourierTransform.WordCompilation

namespace OAI

namespace PowerSaving.RAM
open Ty Slant Slant.Stroke Spectral
noncomputable section

universe U
namespace Bench.Engrave

variable {m : Bool} {ι : Type U} {b : Bench m ι}
    {n l k : ι→ℕ}

lemma strand (h : b.Digit n) (hk : b.Digit k) (hl : b.Digit l)
    (r : ι→ℕ→Reel) (H : (b.scan l).Engrave (fun i => n i.i) (fun i => r i.i i.j))
    (g : ∀ i, ∀ j<l i, (r i j).beats=k i) :
    b.Engrave n fun i => Slant.strand (r i) (l i) := by
  let R i j := Slant.strand (r i) j
  have hb (i : ι) (j : ℕ) (hj : j ≤ l i) : (R i j).beats=j*k i :=
    beat_strand j _ (fun t ht => g i t (ht.trans_le hj))
  have hs (i : ι) (j : ℕ) (hj : j ≤ l i) : (R i j).Sound (n i) :=
    sound_strand _ _ fun t ht => H.sound ⟨i,t,ht.trans_le hj⟩
  refine ⟨fun i => hs i _ le_rfl, (hl.mul hk).congr (fun i => (hb i _ le_rfl).symm),h,?_⟩
  let U i j := film (n i) (R i j)
  refine loop (t:=filmTy) hl U ?_ ?_
  · exact (Engrave.rest h (Digit.wc 0)).layers
  · let P := b.climbs l filmTy U
    have F := Feeds.climbs b l U
    have hj := stepi hl U -- specify
    have hg : P.Engrave (fun i => n i.i) (fun i => R i.i i.j) :=
      ⟨fun i => hs i.i i.j i.hj.le, ((hj.mul (draw F hk)).congr (fun i => (hb i.i i.j i.hj.le).symm)),
        draw F h,stepsum b l U⟩
    exact (hg.stack (H.transfer (inspect b l U))).layers

/-- nesting scans for 3 chunk coordinates. -/
abbrev double (b : Bench m ι) (l : ι→ℕ) :=
  (b.scan l).scan fun i => l i.i
abbrev triple (b : Bench m ι) (l : ι→ℕ) :=
  (double b l).scan fun i => l i.i.i

private lemma duoStrand (h : b.Digit n) (hk : b.Digit k) (hl : b.Digit l)
    (r : ι→ℕ→ℕ→Reel)
    (H : (double b l).Engrave (fun i => n i.i.i) (fun i => r i.i.i i.i.j i.j))
    (g : ∀ i, ∀ j<l i, ∀ s<l i, (r i j s).beats=k i) :
    b.Engrave n fun i => Slant.strand (fun j => Slant.strand (r i j) (l i)) (l i) := by
  have F := Feeds.scan b l
  apply strand h (hl.mul hk) hl (fun i j => Slant.strand (r i j) (l i))
  · exact strand (draw F h) (draw F hk) (draw F hl) (fun i => r i.i i.j) H
      (fun i => g i.i i.j i.hj)
  · exact fun i j hj => beat_strand _ _ (g i j hj)

lemma riprap (h : b.Digit n) (hk : b.Digit k) (hl : b.Digit l)
    (r : ι→ℕ→ℕ→ℕ→Reel)
    (H : (triple b l).Engrave (fun i => n i.i.i.i) (fun i => r i.i.i.i i.i.i.j i.i.j i.j))
    (g : ∀ i, ∀ j<l i, ∀ s<l i, ∀ t<l i, (r i j s t).beats=k i) :
    b.Engrave n fun i => Slant.riprap (r i) (l i) := by
  have F := Feeds.scan b l
  exact strand h (hl.mul (hl.mul hk)) hl
    (fun i j => Slant.strand (fun s => Slant.strand (r i j s) (l i)) (l i))
    (duoStrand (draw F h) (draw F hk) (draw F hl) (fun i => r i.i i.j) H
      (fun i => g i.i i.j i.hj)) (fun i j hj =>
      beat_strand _ _ (fun s hs => beat_strand _ _ (g i j hj s hs)))

end Bench.Engrave
end
end PowerSaving.RAM

end OAI
