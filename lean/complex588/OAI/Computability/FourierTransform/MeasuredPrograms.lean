import OAI.Computability.FourierTransform.ChunkPrograms
import OAI.Computability.FourierTransform.ToeplitzPreparation
import OAI.Computability.FourierTransform.MeasuredFit

namespace OAI

namespace PowerSaving.RAM
open Ty Slant Spectral Complex
noncomputable section

universe U
namespace Bench
variable {m : Bool} {ι : Type U} {b : Bench m ι}

lemma spot_jetty {p w a s : ι→ℕ} (hp : b.Digit p) (hw : b.Digit w)
    (ha : b.Digit a) (hs : b.Digit s) :
    b.Spots (fun i => jetty (p i) (w i) (a i) (s i)) :=
  have h := hs.mul ha
  ⟨hp.add h,ha.minimum (hw.sub h)⟩

lemma spot_quay {j s : ι→ℕ} (h : b.Digit j) (g : b.Digit s) :
    b.Spots (fun i => quay (s i) (j i)) :=
  ⟨h.mul g,g⟩

section
variable {h g : ι→Line} {e w k : ι→ℕ} {r : ι→ℂ}
    (hh : b.Fabric e h) (hg : b.Fabric e g) (hy : b.Hue fun _ => I) (hw : b.Digit w)

include hh hg hy hw

-- speck s c j for small
lemma carve_speck {p s c j : ι→ℕ} (hp : b.Digit p)
    (hs : b.Digit s) (hc : b.Digit c) (hj : b.Digit j)
    (hb : ∀ i, c i<p i) (hb' : ∀ i, j i<p i) (hE : ∀ i,p i+w i ≤ e i) :
    b.Engrave (fun i => p i+w i) (fun i => speck (p i) (w i) (h i) (g i) (s i) (c i) (j i)) := by
  let P i := s i<w i
  have H : b.Study P := Study.lt hs hw
  unfold speck
  refine Engrave.fork H ?_ (Engrave.rest (draw (restricted ..) (hp.add hw)) (Digit.wc 26))
  have F := restricted b P
  let U i := quay 1 (j i)
  let V i := jetty (p i) (w i) 1 (s i)
  have hU : b.Spots U := spot_quay hj (Digit.wc 1)
  have hV : b.Spots V := spot_jetty hp hw (Digit.wc 1) hs
  have hz (i : {i // P i}) : (V i.val).wide = (U i.val).wide := by
    change min 1 (w i.val - s i.val * 1)=1
    have h0 : s i.val<w i.val := i.property
    omega
  have hU' i : (U i).Fits (p i+w i) := by simpa only [mul_one,U] using
    (quay_fits (p i) 1 (j i) (w i) (hb' i))
  have hy' (i : {i // P i}) : p i.val+s i.val<e i.val :=
    (Nat.add_lt_add_left i.property _).trans_le (hE _)
  have hc' (i : ι) : c i<e i :=
    (hb i).trans_le ((Nat.le_add_right (p i) (w i)).trans (hE i))
  have hl := ((hh.transfer F).riseEntry (draw F (hp.add hs)) (draw F hc) hy').mul
    ((hg.riseEntry hc hj hc').transfer F)
  exact (hV.transfer F).flash (hU.transfer F) (draw F (hp.add hw))
    (fun i => jetty_fits _ _ _ _) (fun i => hU' _) hz (fun i => quay_jet _ _ _ _ (hb' _))
    (hy.transfer F) (Fabric.flat hl)

lemma carve_sand {p : ι→ℕ} (hp : b.Digit p) (hE : ∀ i,p i+w i ≤ e i) :
    b.Engrave (fun i => p i+w i) (fun i => sand (p i) (w i) (h i) (g i)) := by
  refine Engrave.riprap (hp.add hw) (Digit.wc 26) hp (fun i => speck (p i) (w i) (h i) (g i))
    ?_ (fun _ _ _ _ _ _ _ => beats_speck _ _ _ _ _ _ _)
  have A := Feeds.scan b p
  have B := Feeds.scan (b.scan p) fun i => p i.i
  have C := Feeds.scan (Engrave.double b p) fun i => p i.i.i
  have F := (C.next B).next A
  exact carve_speck (hh.transfer F) (hg.transfer F) (hy.transfer F) (draw F hw) (draw F hp)
    (draw (C.next B) (slot hp)) (draw C (slot (draw A hp))) (slot (draw (B.next A) hp))
    (fun i => i.i.hj) (fun i => i.hj) (fun i => hE _)

variable (hk : b.Arch k) (hr : b.Hue r) (hz : ∀ i, r i≠0)
  (hE : ∀ i, 16*2^k i+w i ≤ e i)
include hk hr hz hE

lemma carve_gravel {s c j : ι→ℕ} (hs : b.Digit s) (hc : b.Digit c) (hj : b.Digit j)
    (hb : ∀ i,c i<16) (hb' : ∀ i,j i<16) :
    b.Engrave (fun i => 16*2^k i+w i)
      (fun i => gravel (k i) (r i) (w i) (h i) (g i) (s i) (c i) (j i)) := by
  let B i := 2^k i
  let P i := 16*B i
  let Y i := P i+w i
  let U i := quay (B i) (j i)
  let V i := jetty (P i) (w i) (B i) (s i)
  let Z i := trestle (B i) (j i)
  let K i := barrier (B i) (j i)
  let M i := lockBay (B i) (j i)
  have hP : b.Digit P := (Digit.wc 16).mul hk.span
  have hY := hP.add hw
  have HF : b.Digit fun i => far (B i) (j i) :=
    iteN (Study.lt hj (Digit.wc 8)) ((Digit.wc 8).mul hk.span) (Digit.wc 0)
  have hU : b.Spots U := spot_quay hj hk.span
  have hV : b.Spots V := spot_jetty hP hw hk.span hs
  have hZ : b.Spots Z := ⟨HF,hk.span⟩
  have hK : b.Spots K := ⟨HF.add hk.span,(Digit.wc 2).mul hk.span⟩
  have hM : b.Spots M := ⟨HF.add ((Digit.wc 3).mul hk.span),(Digit.wc 2).mul hk.span⟩
  have A (i : ι) : Wharf (Y i) (U i) (V i) (Z i) (K i) (M i) :=
    wharf _ _ _ _ (hb' i)
  have W (i : ι) : Slips (k i) (U i) (V i) (Z i) (K i) (M i) :=
    slips _ _ _ _
  have ht := hc.mul hk.span
  have hu (i : ι) (d : ℕ) (hd : d < B i) : c i*B i+d<e i := by
    have H := quay_fits 16 (B i) (c i) (w i) (hb i) _ ((quay (B i) (c i)).inside hd)
    exact H.trans_le (hE _)
  have hv (i : ι) (d : ℕ) (hd : d < (V i).wide) : (V i).lo+d<e i :=
    ((A i).fitsV _ ((V i).inside hd)).trans_le (hE _)
  have h1 (x : ι→Line) (hh : b.Fabric e x) :=
    Spots.bore hk hr hz hY hy hU hZ hK hM (fun i => (W i).lw) (fun i => (W i).mw)
      (fun i => (A i).fitsU) (fun i => (A i).fitsZ) (fun i => (A i).fitsL)
      (fun i => (A i).fitsM) (fun i => (A i).lm)
      (fun i => (W i).uw) (fun i => (W i).zw)
      (fun i => (A i).ul) (fun i => (A i).zm) hU.low ht hh hu
  have h2 (x : ι→Line) (hh : b.Fabric e x) :=
    Spots.bore hk hr hz hY hy hZ hV hK hM (fun i => (W i).lw) (fun i => (W i).mw)
      (fun i => (A i).fitsZ) (fun i => (A i).fitsV) (fun i => (A i).fitsL)
      (fun i => (A i).fitsM) (fun i => (A i).lm)
      (fun i => (W i).zw) (fun i => (W i).vw)
      (fun i => (A i).zl) (fun i => (A i).vm) ht hV.low hh hv
  unfold gravel cliff
  exact engrave_cameo (h1 g hg) (h2 h hh) (h1 _ hg.neg) (h2 _ hh.neg)

lemma carve_reef :
    b.Engrave (fun i => 16*2^k i+w i)
      (fun i => reef (k i) (r i) (w i) (h i) (g i)) := by
  let L (_ : ι) := 16
  let S i := 4*(80*k i+348)
  have hS : b.Digit S := (Digit.wc 4).mul (((Digit.wc 80).mul hk.ep).add (Digit.wc 348))
  have hL : b.Digit L := Digit.wc 16
  unfold reef
  refine Engrave.riprap (((Digit.wc 16).mul hk.span).add hw) hS hL
    (fun i => gravel (k i) (r i) (w i) (h i) (g i)) ?_
    (fun _ _ _ _ _ _ _ => beats_gravel _ _ _ _ _ _ _ _)
  have A := Feeds.scan b L
  have B := Feeds.scan (b.scan L) fun i => L i.i
  have C := Feeds.scan (Engrave.double b L) fun i => L i.i.i
  have F := (C.next B).next A
  exact carve_gravel (hh.transfer F) (hg.transfer F) (hy.transfer F) (draw F hw)
    (hk.transfer F) (hr.transfer F) (fun i => hz _) (fun i => hE _)
    (draw (C.next B) (slot hL)) (draw C (slot (draw A hL))) (slot (draw (B.next A) hL))
    (fun i => i.i.hj) (fun i => i.hj)

end
end Bench
end
end PowerSaving.RAM

end OAI
