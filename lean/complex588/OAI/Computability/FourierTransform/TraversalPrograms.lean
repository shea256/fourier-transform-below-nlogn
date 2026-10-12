import OAI.Computability.FourierTransform.PrefixTraversal
import OAI.Computability.FourierTransform.WorkBounds

namespace OAI

namespace PowerSaving.RAM
open Ty Finset Grove Slant
noncomputable section
universe U V
namespace Bench
variable {m : Bool} {ι : Type U} {κ : Type V}

structure Fen (b : Bench m ι) (l : ι→ℕ) (r : ι→Axes) : Prop where
  high : b.Nick l
  good : ∀ i,Splits (r i) (l i)
  span : Small b.size fun i => extent (r i) (l i)
  part : (b.scan l).Nick fun d => r d.i d.j

abbrev routes {ι : Type*} (l : ι→ℕ) (r : ι→Axes) (d : During l) :=
  extent (r d.i) (d.j+1)

abbrev Forks (l : ι→ℕ) (r : ι→Axes) := During (routes l r)

variable {l : ι→ℕ} {r : ι→Axes}

namespace Forks
def tUp (d : Forks l r) := d.j/r d.i.i d.i.j
def tOff (d : Forks l r) := d.j%r d.i.i d.i.j
end Forks

variable {b : Bench m ι} {q : Bench m κ}
open Forks

namespace Fen

lemma transfer {l : κ→ℕ} {r : κ→Axes} (h : q.Fen l r) {f} (g : b.Instant q f) :
    b.Fen (fun i => l (f i)) (fun i => r (f i)) := by
  let L i := l (f i)
  have F := Instant.scan b L
  let p : During L→During l := fun i => ⟨f i.i,i.j,i.hj⟩
  have G : (b.scan L).Instant (q.scan l) p :=
    Instant.select (F.next g) (chop (h.high.transfer g)).close
  exact ⟨h.high.transfer g,fun i => h.good _,(h.span.reindex f).trans g.covers,
    h.part.transfer G⟩

lemma shrunk (h : b.Fen l r) (d : During l) :
    Splits (r d.i) (d.j+1) := (h.good d.i).cut d.hj

lemma midst (h : b.Fen l r) :
    Small (fun d : During l => b.size d.i) fun d => extent (r d.i) d.j :=
  (h.span.reindex During.i).mono fun i => (h.good _).extent_le i.hj.le

lemma further (h : b.Fen l r) :
    Small (fun d : During l => b.size d.i) (routes l r) :=
  (h.span.reindex During.i).mono fun i => (h.good _).extent_le i.hj

lemma smaller (h : b.Fen l r) (d : Forks l r) :
    tUp d<extent (r d.i.i) d.i.j := (h.shrunk _).div_lt d.hj
lemma lower (h : b.Fen l r) (d : Forks l r) :
    tOff d<r d.i.i d.i.j := (h.shrunk _).mod_lt _

/-- Step bench. Indexed by the 'combined' new prefix; on tray are ambient-axis bench,
then decoded old prefix, offset, and previous state. -/
def stalk (b : Bench m ι) (l : ι→ℕ) (r : ι→Axes) (s : Ty) (S : ι → ℕ → ℕ → T s) :
    Bench m (Forks l r) :=
  ((b.scan l).along During.i).extend (p w (p w s))
    (fun i => (tUp i,tOff i,S i.i.i i.i.j (tUp i)))

lemma stalkFeeds (b : Bench m ι) (l : ι→ℕ) (r : ι→Axes) (s : Ty) (S : ι → ℕ → ℕ → T s) :
    (stalk b l r s S).Instant (b.scan l) During.i :=
  (Instant.extend ((b.scan l).along During.i) (t:=p w (p w s)) _).next
    (Instant.along (b.scan l) During.i)

variable {s : Ty}

lemma stalkReads (h : b.Fen l r) (S : ι → ℕ → ℕ → T s) :
    let B := stalk b l r s S
    B.Nick tUp ∧ B.Nick tOff ∧ B.Moves (fun _ => 0) s (fun i => S i.i.i i.i.j (tUp i)) := by
  intro B
  have H : B.Moves (fun _ => 0) (p w (p w s))
      (fun d => (tUp d,tOff d,S d.i.i d.i.j (tUp d))) :=
    cherry ((b.scan l).along During.i) (t:=p w (p w s)) _
  exact ⟨⟨H.fst,(h.midst.reindex During.i).mono fun d => (h.smaller _).le⟩,
    ⟨H.snd.fst,(h.part.small.reindex During.i).mono fun d => (h.lower _).le⟩,H.snd.snd⟩

/-- Linear array work traversal theorem (using table of active prefixes each level). -/
theorem visit (h : b.Fen l r) (S : ι → ℕ → ℕ → T s)
    (hS : b.Moves (fun _ => 0) s fun i => S i 0 0)
    (hs : (stalk b l r s S).Moves (fun _ => 0) s fun d => S d.i.i (d.i.j+1) d.j) :
    b.Moves (fun i => extent (r i) (l i)) (a s) fun i =>
      Tape.tab (extent (r i) (l i)) (S i (l i)) := by
  let M (i : ι) (j : ℕ) := Tape.tab (extent (r i) j) (S i j)
  let D := b.climbs l (a s) M
  let X := D.scan (routes l r)
  have F := Instant.climbs b l M (t:=a s)
  have hi := stride h.high M (t:=a s)
  have V : D.Instant (b.scan l) id := Instant.select F hi.close
  have T := Instant.scan D (routes l r)
  have hm := tokenNow b l M (t:=a s)
  have hg : D.Nick (routes l r) := by
    have hq : D.Nick fun i => extent (r i.i) i.j := ⟨hm.len h.midst,h.midst⟩
    exact hq.mul (h.part.transfer V)
  have hh : X.Instant (stalk b l r s S) id := by
    let K := stalk b l r s S
    have hk : X.Instant ((b.scan l).along During.i) (fun d : Forks l r => d) :=
      let U := T.next V; ⟨U.prep,U.covers⟩
    have ha := chop hg
    have hb := (h.part.transfer V).transfer T
    have hc := ha.div hb; have hd := ha.residue hb
    refine hk.supply (t:=p w (p w s)) (x:=fun d : Forks l r => (tUp d,tOff d,S d.i.i d.i.j (tUp d))) ?_
    have he := Moves.pick (b:=X) (t:=s) (n:=fun i => extent (r i.i.i) i.i.j)
      (fun i j => S i.i.i i.i.j j) (hm.transfer T) hc.close h.smaller -- typo
    exact hc.close.pair (hd.close.pair he)
  have step :
      D.Moves (routes l r) (a s) fun i => M i.i (i.j+1) :=
    arrayNow hg (fun d j => S d.i (d.j+1) j) (hs.transfer hh)
  have hB : b.Moves (fun _ => 0) (a s) fun i => M i 0 := by
    let n (_ : ι) := 1
    have hb := hS.transfer (Instant.scan b n)
    have he (d : During n) : S d.i 0 0=S d.i 0 d.j := by
      have hj : d.j<1 := d.hj
      rw [show d.j=0 by omega]
    exact (arrayNow (Nick.wc 1) _ (hb.congr he)).weaken (Dom.const _ _)
  refine (repeatM (t:=a s) h.high M (u:=fun i j => extent (r i) (j+1)) hB step).weaken ?_
  refine ⟨4,fun i => ?_⟩
  have h1 := (h.good i).axes_le
  have h2 := (h.good i).tree_bound
  rw [sum_range_succ'] at h2
  dsimp only
  omega

end Fen
end Bench
end
end PowerSaving.RAM

end OAI
