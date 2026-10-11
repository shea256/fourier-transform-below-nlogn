import OAI.Computability.FourierTransform.WorkingTransform
import OAI.Computability.FourierTransform.LocalCompiler

namespace OAI

/-! Synchronized Fourier at working length given preparation access to local roots
(including all algorithms for scalars and schedules not already explicitly inputs). -/
namespace PowerSaving.RAM
open Ty Slant Grove Spectral
noncomputable section

universe U V
namespace Bench
variable {m : Bool} {ι : Type U} {κ : Type V} {b : Bench m ι} {q : Bench m κ}
  {cl : Paint} {l e n S : ι→ℕ} {r : ι→Axes} {x : ι→Line} {z : ι→ℂ}

-- choose dyadic root canonical always
def halos : Line := fun i => root (2^i)

lemma haloSprings (n : ℕ) : Springs n halos :=
  fun i _ => root_primitive _ (by positivity)

abbrev forgeTy :=
  p w (p w (p (a w) (p sc (p (a sc) (a sc)))))

/-- local root and dimension table. -/
def forge (l e : ℕ) (r : Axes) (z : ℂ) : T forgeTy :=
  (l, e, Tape.tab l r, Complex.I,Tape.tab (e+1) halos,
    Tape.tab l fun i => spray z (extent r l) (r i))

def teams (r : Axes) (l e : ℕ) (z : ℂ) : ℕ→Reel :=
  fun i => ballad (r i) e (spray z (extent r l) (r i)) halos

abbrev kilnTy := p w (a treeTy)
def kiln (r : Axes) (l e : ℕ) (z : ℂ) : T kilnTy :=
  (score e,Tape.tab l fun i => treeT (r i) (teams r l e z i))

-- readiness via explicit finite tables
structure Foundry (b : Bench m ι) (r : ι→Axes) (l e : ι→ℕ) (z : ι→ℂ) : Prop where
  arches : ∀ i, Isles (r i) (l i)
  low : ∀ i, ∀ j<l i, r i j ≤ 2^e i
  prim : ∀ i, IsPrimitiveRoot (z i) (extent (r i) (l i))
  axes : Small b.size l
  sizes : Small b.size fun i => 2^e i
  prepared : b.Moves (fun _ => 0) forgeTy fun i => forge (l i) (e i) (r i) (z i)

namespace Foundry

lemma transfer {l e : κ→ℕ} {r : κ→Axes} {z : κ→ℂ} (h : q.Foundry r l e z)
    {f} (g : b.Instant q f) :
    b.Foundry (fun i => r (f i)) (fun i => l (f i)) (fun i => e (f i))
      (fun i => z (f i)) :=
  ⟨fun _ => h.arches _,fun _ => h.low _,fun _ => h.prim _,
    (h.axes.reindex _).trans g.covers,(h.sizes.reindex _).trans g.covers,h.prepared.transfer g⟩

lemma nickL (h : b.Foundry r l e z) : b.Nick l :=
  ⟨h.prepared.fst,h.axes⟩
lemma archE (h : b.Foundry r l e z) : b.Arch e := by
  have hh : b.Nick e :=
    ⟨h.prepared.snd.fst,h.sizes.mono fun i => Nat.lt_two_pow_self.le⟩
  exact Arch.fromSmall hh.digit h.sizes

lemma nickR (h : b.Foundry r l e z) :
    (b.scan l).Nick fun d => r d.i d.j := by
  refine ⟨Moves.pick (t:=w) (n:=fun i : During l => l i.i) (k:=During.j) (fun i => r i.i)
    (h.prepared.snd.snd.fst.transfer (Instant.scan b l))
    (chop h.nickL).close During.hj,?_⟩
  exact (h.sizes.reindex During.i).mono fun d => h.low d.i d.j d.hj

lemma unitM (h : b.Foundry r l e z) : b.Moves (fun _ => 0) sc fun _ => Complex.I :=
  h.prepared.snd.snd.snd.fst

lemma digitT (h : b.Foundry r l e z) :
    b.Digit fun i => score (e i) :=
  ((Digit.wc 2).mul (chorus_digit h.archE)).add (Digit.wc 7)

lemma kilnD (h : b.Foundry r l e z) :
    b.Makes kilnTy fun i => kiln (r i) (l i) (e i) (z i) := by
  have hP : b.Makes forgeTy fun i => forge (l i) (e i) (r i) (z i) :=
    PolyCan.of_can h.prepared (Small.const _ 0)
  have F := Feeds.scan b l
  have ht := slot h.nickL.digit
  let n (d : During l) := r d.i d.j
  let z' (d : During l) := spray (z d.i) (extent (r d.i) (l d.i)) (n d)
  have he (i : During l) : 0<n i :=
    lt_of_lt_of_le (by norm_num) ((h.arches _).good i.j i.hj)
  have hg (d : During l) : IsPrimitiveRoot (z' d) (n d) :=
    spray_axis (h.arches _) (h.prim _) _ d.hj
  have hh : (b.scan l).Hue z' :=
    Hue.of_root (Makes.pick (t:=sc) (n:=fun i : During l => l i.i) (k:=During.j) (fun i j => spray (z i.i) (extent (r i.i) (l i.i)) (r i.i j))
      (pull F hP.snd.snd.snd.snd.snd) ht.run During.hj) he (fun i => (hg i).pow_eq_one)
  let y i := e i+1
  have H := Feeds.scan b y
  have hu : b.Fabric y (fun _ => halos) :=
    Hue.of_root (n:=fun d : During y => 2^d.j)
      (Makes.pick (t:=sc) (n:=fun d => y d.i)
        (fun d : During y => halos) (pull H hP.snd.snd.snd.snd.fst)
        (slot (h.archE.ep.add (Digit.wc 1))).run During.hj)
      (fun _ => by positivity) (fun i => (haloSprings i.j _ le_rfl).pow_eq_one)
  have hk := publish (h.archE.transfer F) h.nickR.digit he (fun d => h.low _ _ d.hj)
    (hu.transfer F) (fun i => haloSprings _) hh hg (Hue.letterI (pull F hP.snd.snd.snd.fst))
  exact h.digitT.run.pair (tab (t:=treeTy) h.nickL.digit _ hk.tree)

lemma table (h : b.Foundry r l e z) (hn : Small b.size fun i => extent (r i) (l i))
    (hk : b.Moves (fun _ => 0) kilnTy fun i => kiln (r i) (l i) (e i) (z i)) :
    b.Thicket l (fun i => score (e i)) r fun i => teams (r i) (l i) (e i) (z i) :=
  ⟨⟨h.nickL,fun i => (h.arches i).good,hn,h.nickR⟩,
    ⟨hk.fst,h.digitT.small⟩,fun i j hj => sound_ballad _ _ _ _ (h.low i j hj),
    fun _ _ _ => beats_ballad _ _ _ _,hk.snd⟩
end Foundry

-- combine once after change of base; computation includes preliminary forge print
theorem effuse (h : ∀ i, Isles (r i) (l i)) (hl : ∀ i, ∀ j<l i, r i j≤2^e i)
    (hz : ∀ i, IsPrimitiveRoot (z i) (extent (r i) (l i)))
    (h1 : Small S l) (h2 : Small S fun i => 2^e i)
    (h3 : Small b.size S) (h4 : Small b.size fun i => extent (r i) (l i))
    (hp : PolyCan m b.size S b.tray forgeTy b.env fun i => forge (l i) (e i) (r i) (z i))
    (hx : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (extent (r i) (l i)) (x i)) :
    ∃ d : ℕ,
    b.Moves (fun i => (score (e i)+1)*(extent (r i) (l i)*hills (l i)) + (S i+2)^d)
      (a (c cl)) fun i => Tape.tab (extent (r i) (l i))
        (freq (extent (r i) (l i)) (z i) (x i)) := by
  let n i := extent (r i) (l i)
  let f i := forge (l i) (e i) (r i) (z i)
  let D := b.extend forgeTy f
  let q : Bench m ι := ⟨S,D.tray,D.env⟩
  have F0 := Instant.extend b f
  have Hq : q.Foundry r l e z :=
    ⟨h,hl,hz,h1,h2,cherry (Bench.mk (m:=m) S b.tray b.env) f (t:=forgeTy)⟩
  have H : D.Foundry r l e z := Hq.transfer (f:=id) (show D.Instant q id from
    ⟨envNow D,h3⟩)
  obtain ⟨d,hd⟩ := hp
  obtain ⟨a,hA⟩ := Hq.kilnD
  let V i := kiln (r i) (l i) (e i) (z i)
  let K := D.extend kilnTy V
  have F := Instant.extend D V (t:=kilnTy)
  have ht := (H.transfer F).table (hn:=h4) (cherry D V (t:=kilnTy))
  let R i := (score (e i)+1)*(n i*hills (l i))
  let W i := R i+(S i+2)^(d+a)
  have hr : K.Moves R (Ty.a (c cl)) fun i => Tape.tab (n i) (freq (n i) (z i) (x i)) :=
    ht.traverse h hz (fun i j hj => creates_ballad _ _ _ _ (hl i j hj) (haloSprings _)
      (spray_axis (h _) (hz i) _ hj)) (H.unitM.transfer F) (hx.transfer (F.next F0))
  have hd' : b.Moves W forgeTy f := hd.mono (fun i => le_trans
    (Small.pow_mono_degree _ (show d≤d+a by omega)) (Nat.le_add_left _ _))
  have hA' : D.Moves W kilnTy V := (Can.ambient hA h3).mono (fun i => le_trans
    (Small.pow_mono_degree (S i) (show a≤d+a by omega)) (Nat.le_add_left _ _))
  exact ⟨d+a,caseM hd' (caseM hA' (hr.weaken (Dom.of_le fun i => Nat.le_add_right _ _)))⟩

end Bench
end
end PowerSaving.RAM

end OAI
