import OAI.Computability.FourierTransform.PackingPrograms

namespace OAI

/-! Compile synchronized gather slot, and synchronized sector packing metadata. -/
namespace PowerSaving.RAM
open Ty Grove
noncomputable section

universe U V

namespace Bench
open Forks Slant Shard
variable {m : Bool} {ι : Type U} {κ : Type V} {b : Bench m ι} {q : Bench m κ}
  {n : ι→ℕ} {Y : ι→Shard}

-- all chip fields within budget
structure Kit (b : Bench m ι) (Y : ι→Shard) : Prop where
  starts : b.Nick fun i => (Y i).start
  widths : b.Nick fun i => (Y i).width
  tall : b.Nick fun i => (Y i).height
  seat : b.Nick fun i => (Y i).seat

namespace Kit

lemma lend (h : b.Kit Y) : b.Moves (fun _ => 0) chipTy fun i => chip (Y i) :=
  h.starts.close.pair (h.widths.close.pair (h.tall.close.pair h.seat.close))

lemma addr (h : b.Kit Y) : b.Nick fun i => (Y i).addr := h.starts.add h.seat

lemma grab {l : ι→ℕ} (h : Small b.size n) (hh : ∀ i,(Y i).Mark (n i) (l i))
    (hg : b.Moves (fun _ => 0) chipTy fun i => chip (Y i)) : b.Kit Y := by
  have H (i : ι) := (hh i).endsBy
  have hx (i : ι) : (Y i).width ≤ n i :=
    le_trans (Nat.le_add_left (Y i).width (Y i).start) (H i)
  have hb (i : ι) : (Y i).height < (Y i).width := (hh i).size.symm ▸ Nat.lt_two_pow_self
  exact ⟨⟨hg.fst,h.mono fun i => ((hh i).starts.le.trans (H i))⟩,
    ⟨hg.snd.fst,h.mono hx⟩,
    ⟨hg.snd.snd.fst,h.mono fun i => (hb i).le.trans (hx i)⟩,
    ⟨hg.snd.snd.snd,h.mono fun i => (hh i).place.le.trans (hx i)⟩⟩

lemma transfer {Y : κ→Shard} (h : q.Kit Y) {f} (g : b.Instant q f) :
    b.Kit fun i => Y (f i) :=
  ⟨h.starts.transfer g,h.widths.transfer g,h.tall.transfer g,h.seat.transfer g⟩

lemma roll {Z : ι→Shard} (h : b.Kit Y) (g : b.Kit Z) (hh : b.Nick n) :
    b.Kit fun i => fringe (n i) (Y i) (Z i) :=
  ⟨(h.starts.mul hh).add (h.widths.mul g.starts), h.widths.mul g.widths,
    h.tall.add g.tall,(h.seat.mul g.widths).add g.seat⟩

lemma seedKit (b : Bench m ι) : b.Kit fun _ => seed :=
  ⟨Nick.wc _, Nick.wc _, Nick.wc _, Nick.wc _⟩
end Kit

variable {l : ι→ℕ} {r : ι→Axes} {u : ι → ℕ → Stroke}
namespace Bough

theorem prospect (h : b.Bough l r u) :
    b.Moves (fun i => extent (r i) (l i)) (a sapTy) fun i =>
      Tape.tab (extent (r i) (l i)) (survey (r i) (u i) (l i)) := by
  let S i := survey (r i) (u i)
  have hF := h.fen
  refine hF.visit (s:=sapTy) S ((Moves.wc 0).pair Moves.one) ?_
  let D := Fen.stalk b l r sapTy S
  have F := Fen.stalkFeeds b l r sapTy S
  have hH := hF.stalkReads (s:=sapTy) S
  let g := h.leaf.transfer F
  have hk := g.read hH.2.1 hF.lower
  have ha : D.Nick fun i => (S i.i.i i.i.j (tUp i)).1 := by
    refine ⟨hH.2.2.fst,(hF.midst.reindex During.i).mono ?_⟩
    intro i
    have hm := hF.shrunk i.i
    exact (survey_lt _ _ _ (hm.cut (by omega))
      (fun j hj => h.good i.i.i j (hj.trans i.i.hj)) _ (hF.smaller i)).le
  have hR := hF.part.transfer F
  have hc : D.Nick fun i => (u i.i.i i.i.j).ix (tOff i) :=
    ⟨hk.fst.fst,hR.small.mono fun i => ((g.good i).bdix _ (hF.lower i)).le⟩
  exact ((ha.mul hR).add hc).close.pair (hH.2.2.snd.mul hk.fst.snd)

theorem bedding (h : b.Bough l r u) :
    b.Moves (fun i => extent (r i) (l i)) (a chipTy) fun i =>
      Tape.tab (extent (r i) (l i)) fun j => chip (mosaic (r i) (u i) (l i) j) := by
  let S i j k := chip (mosaic (r i) (u i) j k)
  have hF := h.fen
  refine hF.visit (s:=chipTy) S (Kit.seedKit b).lend ?_
  let D := Fen.stalk b l r chipTy S
  have F := Fen.stalkFeeds b l r chipTy S
  have hH := hF.stalkReads (s:=chipTy) S
  let g := h.leaf.transfer F
  have hk := g.read hH.2.1 hF.lower
  have hR := hF.part.transfer F
  have hY : D.Kit (fun i => Hem.hem (u i.i.i i.i.j) (tOff i)) :=
    Kit.grab hR.small (fun i => Hem.marked (g.good i) (hF.lower i)) hk.snd
  have hX : D.Kit fun i => mosaic (r i.i.i) (u i.i.i) i.i.j (tUp i) := by
    refine Kit.grab (l:=fun i => i.i.j) (hF.midst.reindex During.i) ?_ hH.2.2
    intro d
    exact (mosaic_quilt _ _ _ ((hF.shrunk _).cut (by omega))
      (fun j hj => h.good d.i.i j (hj.trans d.i.hj))).mark _ (hF.smaller d)
  exact (hX.roll hY hR).lend

/-- Apply synchronized scaled-lookup slot to a vector. -/
theorem glean (h : b.Bough l r u) (cl : Paint) (x : ι → Line)
    (hx : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (extent (r i) (l i)) (x i)) :
    b.Moves (fun i => extent (r i) (l i)) (a (c cl)) fun i =>
      Tape.tab (extent (r i) (l i)) (graft (extent (r i) (l i))
        (canopy (r i) (fun j => leafM (u i j)) (l i)) (x i)) := by
  let n i := extent (r i) (l i)
  let S i := survey (r i) (u i) (l i)
  let D := b.extend (a sapTy) (fun i => Tape.tab (n i) (S i))
  have hn : b.Nick n := ⟨hx.len h.fen.span,h.fen.span⟩
  have F := Instant.extend b (fun i => Tape.tab (n i) (S i)) (t:=a sapTy)
  have G := Instant.scan D n
  have hg := hn.transfer F
  refine caseM h.prospect (arrayNow hg _ ?_)
  have hp : D.Moves (fun _ => 0) (a sapTy) fun i => Tape.tab (n i) (S i) :=
    cherry b _
  have HH := Moves.pick (b:=D.scan n) (t:=sapTy) (n:=fun i => n i.i) (fun i => S i.i)
    (hp.transfer G) (chop hg).close During.hj
  have hd (i : During n) : (S i.i i.j).1<n i.i :=
    survey_lt _ _ _ (h.fen.good _) (h.good _) _ i.hj
  have hX := Moves.pick (b:=D.scan n) (t:=c cl) (n:=fun i => n i.i) (fun i => x i.i)
    (hx.transfer (G.next F)) HH.fst hd
  exact (HH.snd.mul hX).congr (fun i =>
    (graft_survey _ _ _ (h.fen.good i.i) (h.good _) _ _ i.hj).symm)

end Bough
end Bench

end
end PowerSaving.RAM

end OAI
