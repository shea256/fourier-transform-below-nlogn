import OAI.Computability.FourierTransform.PolynomialPrograms

namespace OAI

/-! Additional composition library for local compilation -- time and all integer words
polynomial in the ambient width. -/
namespace PowerSaving.RAM
open Ty Finset
noncomputable section

universe U V Z

structure Bench (m : Bool) (ι : Type U) where
  size : ι→ℕ
  tray : Ty
  env : ι → T tray

namespace Bench
variable {m : Bool} {ι : Type U} {κ : Type V}

def Makes (b : Bench m ι) (t : Ty) (f : ι → T t) : Prop :=
  PolyCan m b.size b.size b.tray t b.env f

structure Digit (b : Bench m ι) (f : ι→ℕ) : Prop where
  run : b.Makes w f
  small : Small b.size f

def along (b : Bench m ι) (f : κ → ι) : Bench m κ :=
  ⟨fun i => b.size (f i), b.tray, fun i => b.env (f i)⟩

def extend (b : Bench m ι) (t : Ty) (x : ι→T t) : Bench m ι :=
  ⟨b.size,p b.tray t,fun i => (b.env i,x i)⟩

def scrutin (b : Bench m ι) (P : ι→Prop) : Bench m {i // P i} :=
  b.along Subtype.val

def scan (b : Bench m ι) (n : ι→ℕ) : Bench m (During n) :=
  (b.along During.i).extend w During.j

def climbs (b : Bench m ι) (n : ι→ℕ) (t : Ty) (x : ι → ℕ → T t) :
    Bench m (During n) :=
  (b.along During.i).extend (p w t) fun d => (d.j,x d.i d.j)

-- Access another bench. b prepares q's inputs.
structure Feeds (b : Bench m ι) (q : Bench m κ) (f : ι→κ) : Prop where
  inputs : b.Makes q.tray (fun i => q.env (f i))
  size : Small b.size (fun i => q.size (f i))

variable {b : Bench m ι} {q : Bench m κ} {s t : Ty}

namespace Makes

lemma congr {x y : ι→T t} (h : b.Makes t x) (H : ∀ i, x i=y i) :
    b.Makes t y := PolyCan.cong h (fun _ => rfl) H

lemma along {x : ι→T t} (h : b.Makes t x) (f : κ→ι) :
    (b.along f).Makes t (fun i => x (f i)) := PolyCan.reindex h f

lemma pair {x : ι→T s} {y : ι→T t} (h : b.Makes s x) (g : b.Makes t y) :
    b.Makes (p s t) (fun i => (x i,y i)) := PolyCan.pair h g

lemma fst {x : ι→T (p s t)} (h : b.Makes (p s t) x) :
    b.Makes s (fun i => (x i).1) := PolyCan.fst h
lemma snd {x : ι→T (p s t)} (h : b.Makes (p s t) x) :
    b.Makes t (fun i => (x i).2) := PolyCan.snd h

lemma wc (n : ℕ) : b.Makes w (fun _ => n) := PolyCan.wc n

lemma zero {cl} : b.Makes (c cl) (fun _ => 0) := PolyCan.zero
lemma one : b.Makes sc (fun _ => 1) := PolyCan.one
lemma add {cl} {x y : ι→ℂ} (h : b.Makes (c cl) x) (g : b.Makes (c cl) y) :
    b.Makes (c cl) (fun i => x i+y i) := PolyCan.add h g
lemma sub {cl} {x y : ι→ℂ} (h : b.Makes (c cl) x) (g : b.Makes (c cl) y) :
    b.Makes (c cl) (fun i => x i-y i) := PolyCan.sub h g
lemma neg {cl} {x : ι→ℂ} (h : b.Makes (c cl) x) :
    b.Makes (c cl) (fun i => -x i) := (zero.sub h).congr (fun _ => zero_sub _)
lemma mul {cl} {x y : ι→ℂ} (h : b.Makes sc x) (g : b.Makes (c cl) y) :
    b.Makes (c cl) (fun i => x i*y i) := PolyCan.mul h g
lemma inv {x : ι→ℂ} (h : b.Makes sc x) (g : ∀ i, x i ≠ 0) :
    b.Makes sc (fun i => (x i)⁻¹) := PolyCan.inv h g
lemma look {x : ι→Tape (T t)} {n} (h : b.Makes (a t) x) (g : b.Makes w n) :
    b.Makes t (fun i => (x i).look (n i) t.blank) := PolyCan.look h g

end Makes

lemma prepares (b : Bench m ι) : b.Makes b.tray b.env := PolyCan.id

lemma pull {f : ι→κ} (h : b.Feeds q f) {x : κ→T t} (g : q.Makes t x) :
    b.Makes t (fun i => x (f i)) :=
  PolyCan.pipe h.inputs (PolyCan.weaken (PolyCan.reindex g f) h.size h.size)

lemma draw {f : ι→κ} (h : b.Feeds q f) {x} (g : q.Digit x) :
    b.Digit (fun i => x (f i)) :=
  ⟨pull h g.run,(g.small.reindex f).trans h.size⟩

lemma Feeds.along (b : Bench m ι) (f : κ→ι) :
    (b.along f).Feeds b f :=
  ⟨prepares _,Small.self _⟩

lemma toppings (b : Bench m ι) (f : ι→T t) :
    (b.extend t f).Makes t f := PolyCan.second

lemma trayLeft (b : Bench m ι) (f : ι→T t) :
    (b.extend t f).Makes b.tray b.env := PolyCan.first

lemma Feeds.extend (b : Bench m ι) (t : Ty) (f : ι→T t) :
    (b.extend t f).Feeds b id := ⟨trayLeft _ f,Small.self _⟩

lemma Feeds.push {f : ι→κ} (h : b.Feeds q f) (x : κ→T t) (g : b.Makes t (fun i => x (f i))) :
    b.Feeds (q.extend t x) f := ⟨h.inputs.pair g,h.size⟩

lemma Feeds.next {μ : Type Z} {a : Bench m μ} {f : ι→κ} {g : κ→μ}
    (h : b.Feeds q f) (j : q.Feeds a g) :
    b.Feeds a (fun i => g (f i)) :=
  ⟨pull h j.inputs,(j.size.reindex f).trans h.size⟩

lemma enclose {x : ι→T t} {y : ι→T s} (h : b.Makes t x)
    (g : (b.extend t x).Makes s y) : b.Makes s y :=
  PolyCan.bind h g

namespace Digit

variable {x y : ι→ℕ}

lemma wc (n : ℕ) : b.Digit (fun _ => n) := ⟨Makes.wc n,Small.const _ n⟩

lemma congr (h : b.Digit x) (g : ∀ i, x i=y i) : b.Digit y := by rwa [← funext g]

lemma add (h : b.Digit x) (g : b.Digit y) :
    b.Digit (fun i => x i + y i) :=
  ⟨PolyCan.wadd h.run g.run (h.small.add g.small), h.small.add g.small⟩
lemma sub (h : b.Digit x) (g : b.Digit y) :
    b.Digit (fun i => x i-y i) :=
  have hs := h.small.mono (G:=fun i => x i-y i) (fun _ => Nat.sub_le ..)
  ⟨PolyCan.wsub h.run g.run hs, hs⟩
lemma mul (h : b.Digit x) (g : b.Digit y) :
    b.Digit (fun i => x i * y i) :=
  ⟨PolyCan.wmul h.run g.run (h.small.mul g.small), h.small.mul g.small⟩
lemma div (h : b.Digit x) (g : b.Digit y) :
    b.Digit (fun i => x i/y i) :=
  have hs := h.small.mono (G:=fun i => x i/y i) (fun _ => Nat.div_le_self ..)
  ⟨PolyCan.wdiv h.run g.run hs,hs⟩
lemma mod (h : b.Digit x) (g : b.Digit y) :
    b.Digit (fun i => x i%y i) :=
  have hs := h.small.mono (G:=fun i => x i%y i) (fun _ => Nat.mod_le ..)
  ⟨PolyCan.wmod h.run g.run hs,hs⟩
lemma minimum (h : b.Digit x) (g : b.Digit y) :
    b.Digit (fun i => min (x i) (y i)) := by
  refine (h.sub (h.sub g)).congr ?_
  intro i; omega

lemma isLess (h : b.Digit x) (g : b.Digit y) :
    b.Digit (fun i => if x i<y i then 1 else 0) :=
  ⟨PolyCan.wlt h.run g.run,(Small.const b.size 1).mono (fun i => by split <;> omega)⟩

end Digit

namespace Feeds

variable {n : ι→ℕ}

lemma scan (b : Bench m ι) (n : ι→ℕ) : (b.scan n).Feeds b During.i :=
  (Feeds.extend (b.along During.i) w During.j).next (Feeds.along b During.i)

lemma climbs (b : Bench m ι) (n : ι→ℕ) (x : ι → ℕ → T t) :
    (b.climbs n t x).Feeds b During.i :=
  (Feeds.extend (b.along During.i) _ _).next (Feeds.along b During.i)
end Feeds

variable {n : ι→ℕ}
lemma slot (h : b.Digit n) :
    (b.scan n).Digit During.j :=
  ⟨toppings (t:=w) (b.along During.i) During.j,
    (h.small.reindex During.i).mono (fun j : During n => j.hj.le)⟩

lemma tab (h : b.Digit n) (x : ι→ℕ→T t) (g : (b.scan n).Makes t (fun d => x d.i d.j)) :
    b.Makes (a t) (fun i => Tape.tab (n i) (x i)) :=
  PolyCan.tab h.run g h.small h.small

lemma stepi (h : b.Digit n) (x : ι → ℕ → T t) :
    (b.climbs n t x).Digit During.j := ⟨
  (toppings (b.along During.i) (t:=p w t) (fun d : During n => (d.j,x d.i d.j))).fst,
  (slot h).small⟩

lemma stepsum (b : Bench m ι) (n : ι→ℕ) (x : ι → ℕ → T t) :
    (b.climbs n t x).Makes t (fun d => x d.i d.j) :=
  (toppings (b.along During.i) (t:=p w t) (fun d : During n => (d.j,x d.i d.j))).snd

lemma loop (h : b.Digit n) (x : ι → ℕ → T t) (g : b.Makes t (fun i => x i 0))
    (k : (b.climbs n t x).Makes t (fun d => x d.i (d.j+1))) :
    b.Makes t (fun i => x i (n i)) :=
  PolyCan.loop h.run g k h.small h.small

-- scan arbitrary stage by computed index
lemma Feeds.select {n : κ→ℕ} {f : ι → During n}
    (h : b.Feeds q (fun i => (f i).i)) (g : b.Makes w (fun i => (f i).j)) :
    b.Feeds (q.scan n) f := ⟨h.inputs.pair g,h.size⟩

end Bench

end
end PowerSaving.RAM

end OAI
