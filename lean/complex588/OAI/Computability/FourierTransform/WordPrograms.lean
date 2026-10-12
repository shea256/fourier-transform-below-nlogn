import OAI.Computability.FourierTransform.FourierCompilation
import OAI.Computability.FourierTransform.FourierIdentities

namespace OAI

namespace PowerSaving.RAM
open Ty Finset Complex
noncomputable section

universe U V

namespace Bench
variable {m : Bool} {ι : Type U} {κ : Type V} {b : Bench m ι} {q : Bench m κ}

structure Hue (b : Bench m ι) (f : ι→ℂ) : Prop where
  bright : b.Makes sc f
  dull : b.Makes sc (fun i => starRingEnd ℂ (f i))

namespace Hue
variable {f g : ι→ℂ}

lemma congr (h : b.Hue f) (k : ∀ i, f i=g i) : b.Hue g := by rwa [← funext k]

lemma transfer {p : ι→κ} {f : κ→ℂ} (h : q.Hue f) (g : b.Feeds q p) :
    b.Hue (fun i => f (p i)) := ⟨pull g h.bright,pull g h.dull⟩

lemma zero : b.Hue (fun _ => 0) :=
  ⟨Makes.zero,Makes.zero.congr (fun _ => by simp)⟩

lemma one : b.Hue (fun _ => 1) :=
  ⟨Makes.one,Makes.one.congr (fun _ => by simp)⟩

lemma neg (h : b.Hue f) : b.Hue (fun i => -(f i)) :=
  ⟨h.bright.neg,h.dull.neg.congr (fun _ => by simp)⟩

lemma add (h : b.Hue f) (k : b.Hue g) : b.Hue (fun i => f i + g i) :=
  ⟨h.bright.add k.bright,(h.dull.add k.dull).congr (fun _ => by simp)⟩

lemma sub (h : b.Hue f) (k : b.Hue g) : b.Hue (fun i => f i - g i) :=
  ⟨h.bright.sub k.bright,(h.dull.sub k.dull).congr (fun _ => by simp)⟩

lemma mul (h : b.Hue f) (k : b.Hue g) : b.Hue (fun i => f i*g i) :=
  ⟨h.bright.mul k.bright,(h.dull.mul k.dull).congr (fun _ => by simp)⟩

lemma inv (h : b.Hue f) (k : ∀ i, f i ≠ 0) : b.Hue (fun i => (f i)⁻¹) :=
  ⟨h.bright.inv k,(h.dull.inv (by intro i; simpa using k i)).congr (fun _ => by simp)⟩

lemma div (h : b.Hue f) (k : b.Hue g) (hg : ∀ i, g i≠0) :
    b.Hue fun i => f i / g i :=
  (h.mul (k.inv hg)).congr (fun _ => (div_eq_mul_inv _ _).symm)

lemma flip (h : b.Hue f) :
    b.Hue (fun i => starRingEnd ℂ (f i)) :=
  ⟨h.dull,h.bright.congr (fun i => by simp)⟩

lemma letterI (h : b.Makes sc fun _ => I) :
    b.Hue (fun _ => I) := ⟨h,h.neg.congr (fun _ => by simp)⟩

lemma casting {n} (h : b.Digit n) : b.Hue (fun i => (n i:ℂ)) :=
  ⟨Makes.casting h,(Makes.casting h).congr fun _ => by simp⟩

lemma numeral (n : ℕ) : b.Hue (fun _ => (n:ℂ)) := casting (Digit.wc n)

lemma of_root {n : ι→ℕ} (h : b.Makes sc f) (hn : ∀ i, 0<n i)
    (hf : ∀ i, f i ^ n i = 1) : b.Hue f := by
  have hh : ∀ i, f i ≠ 0 := by
    intro i hg
    have hk := hf i
    rw [hg,zero_pow (by have := hn i; omega)] at hk
    exact zero_ne_one hk
  exact ⟨h,(h.inv hh).congr (fun i => (Spectral.conj_of_root (hn i) (hf i)).symm)⟩

lemma exponent (h : b.Hue f) {n} (g : b.Digit n) :
    b.Hue (fun i => f i ^ n i) :=
  ⟨Makes.expZ g h.bright,(Makes.expZ g h.dull).congr fun _ => by simp⟩

lemma fork {P : ι→Prop} [DecidablePred P] (hp : b.Study P)
    (a : (b.scrutin P).Hue (fun i => f i.val))
    (c : (b.scrutin (fun i => ¬P i)).Hue (fun i => g i.val)) :
    b.Hue fun i => if P i then f i else g i :=
  ⟨branchM hp a.bright c.bright,
    (branchM (x:=fun i => starRingEnd ℂ (f i)) (y:=fun i => starRingEnd ℂ (g i)) hp
      a.dull c.dull).congr (fun i => by by_cases hi : P i <;> simp [hi])⟩

variable {n : ι→ℕ}
lemma sum (h : b.Digit n) (x : ι → Line)
    (g : (b.scan n).Hue (fun i => x i.i i.j)) :
    b.Hue (fun i => ∑ j ∈ range (n i), x i j) :=
  ⟨Makes.gridSum h x g.bright,
    (Makes.gridSum h (fun i j => starRingEnd ℂ (x i j)) g.dull).congr
      (fun _ => by simp)⟩

lemma prod (h : b.Digit n) (x : ι → Line)
    (g : (b.scan n).Hue (fun i => x i.i i.j)) :
    b.Hue (fun i => ∏ j ∈ range (n i), x i j) :=
  ⟨Makes.gridProd h x g.bright,
    (Makes.gridProd h (fun i j => starRingEnd ℂ (x i j)) g.dull).congr
      (fun _ => by simp)⟩

end Hue

/- easier lift over a scan on coordinates. -/
def carried (p : ι→κ) (n : κ→ℕ) (i : During fun j => n (p j)) :
    During n := ⟨p i.i,i.j,i.hj⟩

lemma Feeds.carry {p : ι→κ} (h : b.Feeds q p) (n : κ→ℕ) :
    (b.scan (fun i => n (p i))).Feeds (q.scan n) (carried p n) := by
  have E := (Feeds.scan b fun i => n (p i)).next h
  exact Feeds.select E (toppings (t:=w) _ During.j)

def Fabric (b : Bench m ι) (n : ι→ℕ) (x : ι → Line) : Prop :=
  (b.scan n).Hue (fun i => x i.i i.j)

namespace Fabric
variable {n : ι→ℕ} {x y : ι → Line}

lemma bright (h : b.Fabric n x) : (b.scan n).Makes sc (fun i => x i.i i.j) :=
  Hue.bright h
lemma dull (h : b.Fabric n x) :
    (b.scan n).Makes sc (fun i => starRingEnd ℂ (x i.i i.j)) := Hue.dull h

lemma pick (h : b.Fabric n x) {k} (hk : b.Makes w k) (H : ∀ i,k i < n i) :
    b.Hue (fun i => x i (k i)) :=
  Hue.transfer h (show b.Feeds (b.scan n) (fun i => ⟨i,k i,H i⟩) from
    ⟨(prepares b).pair hk,Small.self _⟩)

lemma transfer {n : κ→ℕ} {x : κ→Line} (h : q.Fabric n x) {f} (g : b.Feeds q f) :
    b.Fabric (fun i => n (f i)) (fun i => x (f i)) :=
  Hue.transfer h (g.carry n)

lemma congr (h : b.Fabric n x) (g : ∀ i, x i=y i) : b.Fabric n y := by rwa [← funext g]

lemma zero : b.Fabric n (fun _ _ => 0) := Hue.zero
lemma one : b.Fabric n (fun _ _ => 1) := Hue.one
lemma flat {f} (h : b.Hue f) : b.Fabric n (fun i _ => f i) :=
  h.transfer (Feeds.scan b n)
lemma neg (h : b.Fabric n x) : b.Fabric n (fun i j => -x i j) := Hue.neg h
lemma add (h : b.Fabric n x) (g : b.Fabric n y) :
    b.Fabric n (fun i j => x i j+y i j) := Hue.add h g
lemma sub (h : b.Fabric n x) (g : b.Fabric n y) :
    b.Fabric n (fun i j => x i j-y i j) := Hue.sub h g
lemma mul (h : b.Fabric n x) (g : b.Fabric n y) :
    b.Fabric n (fun i j => x i j*y i j) := Hue.mul h g
lemma inv (h : b.Fabric n x) (k : ∀ i, ∀ j<n i, x i j ≠ 0) :
    b.Fabric n (fun i j => (x i j)⁻¹) := Hue.inv h (fun i => k i.i i.j i.hj)
lemma flip (h : b.Fabric n x) :
    b.Fabric n (fun i j => starRingEnd ℂ (x i j)) := Hue.flip h

lemma supply (h : b.Fabric n x) (hk : b.Digit n) :
    b.Makes (a (p sc sc)) (fun i => Tape.tab (n i) fun j => (x i j,starRingEnd ℂ (x i j))) :=
  tab hk _ (h.bright.pair h.dull)

lemma recover (h : b.Makes (a (p sc sc))
    (fun i => Tape.tab (n i) fun j => (x i j,starRingEnd ℂ (x i j)))) :
    b.Fabric n x := by
  let y := fun (d : During n) (i : ℕ) => (x d.i i,starRingEnd ℂ (x d.i i))
  have K := Makes.pick (b:=b.scan n) (n:=fun d => n d.i) (t:=p sc sc) y
    (pull (Feeds.scan b n) h) (toppings (t:=w) _ During.j) During.hj
  exact ⟨K.fst,K.snd⟩

end Fabric
end Bench
end
end PowerSaving.RAM

end OAI
