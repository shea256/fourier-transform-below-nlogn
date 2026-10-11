import OAI.Computability.FourierTransform.IntervalPrograms
import OAI.Computability.FourierTransform.BinaryFFT

namespace OAI

namespace PowerSaving.RAM
open Ty Slant Slant.Stroke Complex
noncomputable section

universe U V
namespace Bench
variable {m : Bool} {ι : Type U} {κ : Type V} {b : Bench m ι} {q : Bench m κ}

/-- exponent with both it and the power of two available in polynomial resources. -/
structure Arch (b : Bench m ι) (e : ι→ℕ) : Prop where
  ep : b.Digit e
  span : b.Digit (fun i => 2^e i)

namespace Arch
lemma transfer {e : κ→ℕ} (h : q.Arch e) {f : ι→κ} (F : b.Feeds q f) :
    b.Arch (fun i => e (f i)) :=
  ⟨draw F h.ep,draw F h.span⟩
variable {e d : ι→ℕ}

lemma fromSmall (h : b.Digit e) (g : Small b.size (fun i => 2^e i)) :
    b.Arch e := ⟨h,h.two g⟩

lemma below (h : b.Arch e) (hh : b.Digit d) (g : ∀ i,d i ≤ e i) :
    b.Arch d :=
  fromSmall hh (h.span.small.mono fun i => Nat.pow_le_pow_right (by omega) (g i))

lemma succ (h : b.Arch e) :
    b.Arch (fun i => e i+1) :=
  ⟨h.ep.add (Digit.wc 1), (h.span.mul (Digit.wc 2)).congr (fun _ => (pow_succ ..).symm)⟩

lemma sub (h : b.Arch e) (g : b.Digit d) :
    b.Arch (fun i => e i-d i) :=
  h.below (h.ep.sub g) fun _ => Nat.sub_le ..
end Arch

section
variable {u : ι→ℂ} {n : ι→ℕ}

lemma powers_fabric (h : b.Hue u) (ha : b.Digit n) :
    b.Fabric n (fun i j => u i ^ j) :=
  (h.transfer (Feeds.scan b n)).exponent (slot ha)

lemma print_fold (hy : b.Hue fun _ => I) (h : b.Hue u)
    (ha : b.Digit n) :
    b.Engrave (fun i => n i+n i) (fun i => foldPair (n i) (u i)) := by
  let F i := initial (n i); let G i := ending (n i)
  have hf : b.Spots F := ⟨Digit.wc 0,ha⟩
  have hg : b.Spots G := ⟨ha,ha⟩
  have hr i := (half_fits (n i)).1
  have hs i := (half_fits (n i)).2
  exact (hf.shade hg Fabric.one (powers_fabric h ha) (ha.add ha) hr hs).stack
    (hf.hinge hg (ha.add ha) hr hs (fun _ => rfl) (fun _ => half_sep _) hy)

lemma print_deal (h : b.Digit n) :
    b.Engrave (fun i => n i+n i) (fun i => Reel.lace (n i+n i) (deal (n i))) := by
  let W i := n i+n i
  have hh := h.add h
  refine Engrave.lace (fun i => deal (n i)) hh ?_ ?_
  · intro i j hj; unfold deal; split <;> omega
  · have hk := slot hh
    have hn := draw (Feeds.scan b W) h
    exact (iteN (Study.lt hk hn) ((Digit.wc 2).mul hk)
      (((Digit.wc 2).mul (hk.sub hn)).add (Digit.wc 1))).run

lemma print_duo (hy : b.Hue fun _ => I) (h : b.Hue u)
    {p : ι→Reel} (g : b.Engrave n p) :
    b.Engrave (fun i => n i+n i) (fun i => duo (n i) (u i) (p i)) :=
  ((print_deal g.width).stack (g.parallel g (fun _ => rfl))).stack
    (print_fold hy h g.width)

end

variable {e : ι→ℕ} {r : ι→ℂ}

private def towerNote (k i : ℕ) (r : ℂ) := r ^ (2^(k-i):ℕ)

private lemma note_change (r : ℂ) (k i : ℕ) (hi : i<k) :
    towerNote k i r = towerNote k (i+1) r ^ 2 := by
  unfold towerNote
  rw [← pow_mul, show k-i=k-(i+1)+1 by omega, pow_succ]

lemma pulse_duration (h : b.Digit e) (r : ι→ℂ) :
    b.Digit (tickCount fun i => pulse (e i) (r i)) :=
  ((Digit.wc 5).mul h).congr (fun _ => (beats_pulse _ _).symm)

lemma print_pulse (hy : b.Hue fun _ => I) (h : b.Arch e) (g : b.Hue r) :
    b.Engrave (fun i => 2^e i) (fun i => pulse (e i) (r i)) := by
  let u i j := towerNote (e i) j (r i)
  let R i (j : ℕ) := pulse j (u i j)
  let Z i (j : ℕ) := film (2^j) (R i j)
  have hf : b.Makes filmTy (fun i => Z i (e i)) := by
    refine loop (t:=filmTy) h.ep Z ?_ ?_
    · have H := (Engrave.rest (b:=b) (Digit.wc 1) (Digit.wc 0)).layers
      exact H.congr (fun i => by simp only [Z,R,pulse,pow_zero])
    · let P := b.climbs e filmTy Z
      have F := Feeds.climbs b e Z -- specify
      have hw : P.Digit During.j := stepi h.ep Z
      have hs : P.Arch During.j := (h.transfer F).below hw (fun i => i.hj.le)
      let d (i : During e) := u i.i (i.j+1)
      have hd : P.Hue d :=
        (g.transfer F).exponent (((h.transfer F).sub (hw.add (Digit.wc 1))).span)
      let p (i : During e) := R i.i i.j
      have ha : P.Engrave (fun i => 2^i.j) p :=
        ⟨fun i => sound_pulse _ _,pulse_duration hw _,hs.span,stepsum (t:=filmTy) b e Z⟩
      -- add one step; equality only on the requested index range
      refine (print_duo (hy.transfer F) hd ha).layers.congr ?_
      intro i
      simp only [Z,R,p,d,pow_succ (2:ℕ),mul_two]
      rw [pulse]
      have hx : u i.i i.j=u i.i (i.j+1)^2 := note_change _ _ _ i.hj
      rw [hx]
  have H : b.Engrave (fun i => 2^e i) (fun i => R i (e i)) :=
    ⟨fun i => sound_pulse _ _,pulse_duration h.ep _,h.span,hf⟩
  refine H.congr (fun _ => rfl) ?_
  intro i; unfold R u towerNote; simp

lemma print_backPulse (hy : b.Hue fun _ => I) (h : b.Arch e)
    (g : b.Hue r) (hg : ∀ i, r i≠0) :
    b.Engrave (fun i => 2^e i) (fun i => backPulse (e i) (r i)) := by
  have hp := print_pulse hy h (g.inv hg)
  have hh := (Hue.casting h.span).inv (by intro i; exact Nat.cast_ne_zero.mpr (by positivity))
  exact hp.stack (Engrave.swatch h.span _ (Fabric.flat hh))

end Bench
end
end PowerSaving.RAM

end OAI
