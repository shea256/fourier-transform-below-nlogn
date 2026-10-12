import OAI.Computability.FourierTransform.SynchronizedAlgorithm
import OAI.Computability.FourierTransform.ChineseRemainder

namespace OAI

/-! CRT and tensor schedule. -/
namespace PowerSaving.RAM
open Grove Slant Ty Spectral
noncomputable section
universe U V

namespace Bench
variable {m : Bool} {ι : Type U} {κ : Type V} {b : Bench m ι} {q : Bench m κ}
  {cl : Paint} {l d : ι→ℕ} {r : ι→Axes} {u : ι→ℕ→Reel} {x : ι→Line}

abbrev dualWord := p w w
def chart (r : Axes) (l : ℕ) (j : ℕ) : T dualWord := (extent r l,ford r l j)

namespace Fen

open Forks

lemma chartT (h : b.Fen l r) (hh : ∀ i, Isles (r i) (l i)) :
    b.Moves (fun i => extent (r i) (l i)) (a dualWord) fun i =>
      Tape.tab (extent (r i) (l i)) (chart (r i) (l i)) := by
  let S i := chart (r i)
  refine h.visit S ((Moves.wc 1).pair (Moves.wc 0)) ?_
  let D := Fen.stalk b l r dualWord S
  have F := Fen.stalkFeeds b l r dualWord S
  have hv := h.stalkReads S
  have hb := h.midst.reindex (During.i (n:=routes l r))
  have ha : D.Nick fun i => extent (r i.i.i) i.i.j :=
    ⟨hv.2.2.fst,hb⟩
  have hk := h.part.transfer F
  have he := ha.mul hk
  have hm : D.Nick fun i => ford (r i.i.i) i.i.j (tUp i) := by
    refine ⟨hv.2.2.snd,hb.mono ?_⟩
    intro i
    exact ((ford_rel ((hh i.i.i).cut i.i.hj.le)).bd _ (h.smaller _)).le
  exact he.close.pair (((hm.mul hk).add (hv.2.1.mul ha)).residue he).close
end Fen

namespace Thicket
variable {z : ι → ℂ}

private lemma via (h : b.Thicket l d r u) (hh : ∀ i, Isles (r i) (l i))
    (hz : ∀ i, IsPrimitiveRoot (z i) (extent (r i) (l i)))
    (hg : ∀ i, ∀ j<l i, Creates (u i j) (r i j)
      (winds _ (spray (z i) (extent (r i) (l i)) (r i j))))
    (hI : b.Moves (fun _ => 0) sc fun _ => Complex.I)
    (hF : b.Moves (fun _ => 0) (a dualWord) fun i =>
      Tape.tab (extent (r i) (l i)) (chart (r i) (l i)))
    (hx : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (extent (r i) (l i)) (x i)) :
    b.Moves (fun i => (d i+1)*(extent (r i) (l i)*hills (l i))) (a (c cl))
      fun i => Tape.tab (extent (r i) (l i)) (freq (extent (r i) (l i)) (z i) (x i)) := by
  let n i := extent (r i) (l i)
  let W i := (d i+1)*(n i*hills (l i))
  let C i := ford (r i) (l i)
  let y i j := x i (C i j)
  let A i := Tape.tab (n i) (y i)
  let V i := freq (n i) (z i) (x i)
  let Z i := Tape.tab (n i) fun j => V i (C i j)
  let M i := fun j => gale (spray (z i) (n i) (r i j))
  have H : Dom W n := Dom.of_le fun i => le_trans (Nat.le_mul_of_pos_right _
    (hills_pos _)) (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
  have hn : b.Nick n := ⟨hx.len h.fen.span,h.fen.span⟩
  have hhC i : Reloc (n i) (C i) := ford_rel (hh i)
  have hp := chop hn
  have F := Instant.scan b n
  have hc := (Moves.pick (t:=dualWord) (n:=fun i : During n => n i.i) _ (hF.transfer F) hp.close During.hj).snd
  have hy : b.Moves W (a (c cl)) A := by
    have hx' := Moves.pick (t:=c cl) (n:=fun i : During n => n i.i)
      (fun i => x i.i) (hx.transfer F) hc (fun i => (hhC i.i).bd _ i.hj)
    exact (arrayNow (t:=c cl) hn y hx').weaken H
  have hz' : b.Moves W (a (c cl)) Z := by
    let D := b.extend (a (c cl)) A
    have G := Instant.extend b A (t:=a (c cl))
    have ht := (h.transfer G).stream (x:=y) (hI.transfer G) (cherry b A (t:=a (c cl))) M hg
    refine caseM hy ((ht.congr ?_).weaken ?_)
    · intro i
      exact tapeCongr (n i) _ _ fun j hj => graft_ford (hh _) (hz _) _ j hj
    · exact Dom.of_le (fun i => Nat.mul_le_mul_right (n i*hills (l i)) (Nat.le_succ (d i)))
  let B := b.extend (a (c cl)) Z
  have G := Instant.extend b (t:=a (c cl)) Z
  have he : B.Nick n := hn.transfer G
  have I1 := Instant.scan B n
  have I2 : (B.scan n).Instant (b.scan n) id :=
    Instant.select (I1.next G) (chop he).close
  have ht := Moves.pick (b:=B.scan n) (t:=c cl) (n:=fun i => n i.i) (fun i j => V i.i (C i.i j))
    ((cherry b Z (W:=fun _=>0) (t:=a (c cl))).transfer I1) (chop he).close During.hj
  have hg' := scatterNow (t:=c cl) he (fun i j => (C i j,V i (C i j))) ((hc.transfer I2).pair ht)
  refine caseM hz' ((hg'.weaken H).congr ?_)
  intro i; rw [(hhC i).sow (fun j => V i (C i j)) _]
  exact tapeCongr (n i) _ _ fun j hj => congr_arg (V i) ((hhC i).seeks hj).2

theorem traverse (h : b.Thicket l d r u) (hh : ∀ i, Isles (r i) (l i))
    (hz : ∀ i, IsPrimitiveRoot (z i) (extent (r i) (l i)))
    (hg : ∀ i, ∀ j<l i, Creates (u i j) (r i j)
      (winds _ (spray (z i) (extent (r i) (l i)) (r i j))))
    (hI : b.Moves (fun _ => 0) sc fun _ => Complex.I)
    (hx : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (extent (r i) (l i)) (x i)) :
    b.Moves (fun i => (d i+1)*(extent (r i) (l i)*hills (l i))) (a (c cl))
      fun i => Tape.tab (extent (r i) (l i)) (freq (extent (r i) (l i)) (z i) (x i)) := by
  let n i := extent (r i) (l i)
  let A i := Tape.tab (n i) (chart (r i) (l i))
  have F := Instant.extend b A (t:=a dualWord)
  have ht := via (h.transfer F) (z:=z) hh hz hg
    (hI.transfer F) (cherry b A (t:=a dualWord)) (x:=x) (hx.transfer F)
  refine caseM ((h.fen.chartT hh).weaken ?_) ht
  exact Dom.of_le fun i => le_trans (Nat.le_mul_of_pos_right (n i)
    (hills_pos (l i))) (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))

end Thicket

end Bench
end
end PowerSaving.RAM

end OAI
