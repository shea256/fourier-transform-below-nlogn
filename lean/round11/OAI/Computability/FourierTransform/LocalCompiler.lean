import OAI.Computability.FourierTransform.ToeplitzCompiler
import OAI.Computability.FourierTransform.FourierWords

namespace OAI

namespace PowerSaving.RAM
open Ty Slant Spectral Complex
noncomputable section

universe U
namespace Bench
variable {m : Bool} {ι : Type U} {b : Bench m ι}

namespace Hue

lemma either {P : ι→Prop} {f : ι→ℂ} (h : b.Study P)
    (a : (b.scrutin P).Hue (fun i => f i.val))
    (q : (b.scrutin (fun i => ¬P i)).Hue (fun i => f i.val)) :
    b.Hue f := ⟨chooseM h a.bright q.bright,
    chooseM (t:=sc) (y:=fun i => starRingEnd ℂ (f i)) h a.dull q.dull⟩

lemma gapV {u : ι→ℂ} (h : b.Hue u) {n : ι→ℕ} (hh : b.Digit n) :
    b.Hue (fun i => Spectral.gap (u i) (n i)) :=
  Hue.prod hh _ (Hue.one.sub
    ((h.transfer (Feeds.scan b n)).exponent ((slot hh).add (Digit.wc 1))))

lemma roofV {u : ι→ℂ} (h : b.Hue u) {n : ι→ℕ} (hh : b.Digit n) :
    b.Hue (fun i => Spectral.roof (u i) (n i)) :=
  Hue.prod hh _ (((h.transfer (Feeds.scan b n)).exponent (slot hh)).neg)

end Hue

private abbrev swab := Ty.a (p sc sc)
private def drum (h : Line) (n : ℕ) : T swab :=
  Tape.tab n fun i => (recoil h i, starRingEnd ℂ (recoil h i))

namespace Fabric
variable {n : ι→ℕ} {h : ι→Line} (hh : b.Fabric n h) (hg : ∀ i,h i 0≠0)

include hh hg

private lemma firstCoil (hp : ∀ i,0<n i) :
    b.Hue (fun i => recoil (h i) 0) :=
  ((hh.pick (Makes.wc 0) hp).inv hg).congr (fun i => (recoil_zero (h i)).symm)

private lemma refill {k : ι→ℕ} (hk : b.Digit k) (hy : ∀ i,k i+1 < n i)
    (hf : b.Fabric (fun i => k i+1) (fun i => recoil (h i))) :
    b.Hue (fun i => recoil (h i) (k i+1)) := by
  have hx := hk.add (Digit.wc 1)
  let U i := k i+1
  have F := Feeds.scan b U
  have hu (i : During U) : k i.i-i.j<k i.i+1 := by omega
  have hv (i : During U) : i.j+1<n i.i := (Nat.add_one_le_iff.mpr i.hj).trans_lt (hy i.i)
  have hs := (slot hx)
  have hq := ((hf.transfer F).pick ((draw F hk).sub hs).run hu).mul
    ((hh.transfer F).pick (hs.add (Digit.wc 1)).run hv)
  have hsum := Hue.sum hx (fun i j => recoil (h i) (k i-j)*h i (j+1)) hq
  have hy' i : 0<n i := lt_trans (show 0<k i+1 by omega) (hy i)
  have h0 := hh.pick (Makes.wc 0) hy'
  exact (hsum.neg.div h0 hg).congr (fun i => (recoil_next (h i) (k i)).symm)

private lemma oneLonger {k : ι→ℕ} (hk : b.Digit k) (hy : ∀ i,k i+1<n i)
    (hf : b.Fabric (fun i => k i+1) (fun i => recoil (h i))) :
    b.Fabric (fun i => k i+1+1) (fun i => recoil (h i)) := by
  let U i := k i+1
  let W i := k i+1+1
  have hu := hk.add (Digit.wc 1)
  have F := Feeds.scan b W
  let T (j : During W) := j.j<U j.i
  have hp := slot (hu.add (Digit.wc 1))
  have H : (b.scan W).Study T := Study.lt hp (draw F hu)
  unfold Bench.Fabric
  refine Hue.either H ?_ ?_
  · have G := restricted (b.scan W) T
    exact ((hf.transfer F).transfer G).pick (draw G hp).run (fun i => i.property)
  · have G := restricted (b.scan W) fun i => ¬T i
    refine (((hh.refill hg hk hy hf).transfer F).transfer G).congr ?_
    intro i
    have hh0 : i.val.j < U i.val.i+1 := i.val.hj
    have hg0 : ¬i.val.j<U i.val.i := i.property
    rw [show i.val.j=U i.val.i by omega]

lemma uncoil (hn : b.Digit n) (hp : ∀ i,0<n i) :
    b.Fabric n (fun i => recoil (h i)) := by
  let U i k := drum (h i) (k+1)
  let y i := n i-1
  have hy : b.Digit y := hn.sub (Digit.wc 1)
  have hf : b.Makes swab (fun i => drum (h i) (n i)) := by
    have H : b.Makes swab (fun i => U i (y i)) := by
      refine loop (t:=swab) hy U ?_ ?_
      · have hx := hh.firstCoil hg hp
        have H1 : b.Fabric (fun _ => 1) (fun i => recoil (h i)) := by
          refine (hx.transfer (Feeds.scan b (fun _ => 1))).congr ?_
          intro d; rw [show d.j=0 by have := d.hj; omega]
        exact H1.supply (Digit.wc 1)
      · have F := Feeds.climbs b y U
        have hw := stepi hy U
        have hq : ∀ j : During y, j.j+1<n j.i := by
          intro j; have hx : j.j<n j.i-1 := j.hj; omega
        have H1 := (hh.transfer F).oneLonger (fun i => hg _) hw hq (Fabric.recover
          (stepsum b y U))
        exact H1.supply ((hw.add (Digit.wc 1)).add (Digit.wc 1))
    exact H.congr fun i => congrArg (drum (h i)) (show y i+1=n i by unfold y; have := hp i; omega)
  exact Fabric.recover hf

end Fabric

lemma print_echo {n : ι→ℕ} (h : b.Digit n) :
    b.Engrave n (fun i => echo (n i)) :=
  Engrave.lace _ h (fun i _ _ => by omega)
    (((draw (Feeds.scan b n) (h.sub (Digit.wc 1))).sub (slot h)).run)

theorem publish {n d : ι→ℕ} {u : ι→ℂ} {r : ι→Line}
    (hd : b.Arch d) (hh : b.Digit n) (hn : ∀ i,0<n i) (hv : ∀ i,n i ≤ 2^d i)
    (hr : b.Fabric (fun i => d i+1) r) (hy : ∀ i, Springs (d i) (r i))
    (h : b.Hue u) (hu : ∀ i, IsPrimitiveRoot (u i) (n i))
    (hI : b.Hue fun _ => I) :
    b.Engrave n (fun i => ballad (n i) (d i) (u i) (r i)) := by
  have F := Feeds.scan b n
  have hX : b.Fabric n fun i => gap (u i) := (h.transfer F).gapV (slot hh)
  have hx (i : ι) (j : ℕ) (hj : j<n i) : gap (u i) j≠0 :=
    gap_ne_zero (u i) (hu i) j hj
  let f i := floorH (u i)
  have hF : b.Fabric n f := hX.inv hx
  have hg := hF.uncoil (fun i => by simp [f,floorH,gap]) hh hn
  have hL : b.Library n (fun i => d i+1) f (fun i => recoil (f i)) r :=
    ⟨hI,hF,hg,hr,fun i j hj => (hy i j (by omega)).ne_zero (by positivity)⟩
  have ht := hL.buildHarp hd hh hn (fun _ => le_rfl) (fun i => by exact Nat.lt_succ_self _)
    hv
  have hY : b.Fabric n fun i => roof (u i) := (h.transfer F).roofV (slot hh)
  have hhR : b.Fabric n fun i j => (cog (u i) j)⁻¹ :=
    (Fabric.inv (x:=fun i => cog (u i)) (hX.mul hY) (fun i => cog_ne_zero (u i) (hu i)))
  have He := print_echo hh
  have Hg := Engrave.swatch hh _ hX
  have Hh := Engrave.swatch hh _ hY
  unfold ballad ode
  exact (((Hg.stack ((He.stack ht).stack He)).stack Hh).stack
    (Engrave.swatch hh _ hhR)).stack ((Hh.stack ht).stack Hg)

end Bench
end
end PowerSaving.RAM

end OAI
