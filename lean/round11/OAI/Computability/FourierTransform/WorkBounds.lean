import OAI.Computability.FourierTransform.CompilerEnvironment
import OAI.Computability.FourierTransform.IntegerPrograms

namespace OAI

/- Cost-sensitive ambient bench combinators. -/
namespace PowerSaving.RAM
open Ty Finset
noncomputable section

universe U V Z

namespace Bench
variable {m : Bool} {ι : Type U} {κ : Type V} {μ : Type Z}

def Moves (b : Bench m ι) (W : ι→ℕ) (t : Ty) (f : ι→T t) : Prop :=
  Can m b.size b.tray t b.env f W

structure Nick (b : Bench m ι) (f : ι→ℕ) : Prop where
  close : b.Moves (fun _ => 0) w f
  small : Small b.size f

/-- Constant work setup of another environment. -/
structure Instant (b : Bench m ι) (q : Bench m κ) (f : ι→κ) : Prop where
  prep : b.Moves (fun _ => 0) q.tray fun i => q.env (f i)
  covers : Small b.size fun i => q.size (f i)

variable {b : Bench m ι} {q : Bench m κ} {z : Bench m μ} {s t : Ty} {W : ι → ℕ}
  {x y : ι → T t}

namespace Moves

lemma congr (h : b.Moves W t x) (g : ∀ i, x i=y i) :
    b.Moves W t y := by rwa [← funext g]

lemma weaken {P} (h : b.Moves W t x) (g : Dom P W) :
    b.Moves P t x := Can.weaken h g

lemma ease (h : b.Moves (fun _ => 0) t x) (V : ι → ℕ) :
    b.Moves V t x := h.weaken (Dom.const V 0)

lemma wc (n : ℕ) : b.Moves W w fun _ => n := Can.wc n

lemma pair {u : ι → T s} (h : b.Moves W s u) (g : b.Moves W t x) :
    b.Moves W (p s t) fun i => (u i,x i) := Can.pair h g
lemma fst {v : ι → T (p s t)} (h : b.Moves W (p s t) v) :
    b.Moves W s fun i => (v i).1 := Can.fst h
lemma snd {v : ι → T (p s t)} (h : b.Moves W (p s t) v) :
    b.Moves W t fun i => (v i).2 := Can.snd h

lemma len {v : ι→Tape (T t)} (h : b.Moves W (a t) v) (g : Small b.size fun i => (v i).len) :
    b.Moves W w fun i => (v i).len := Can.len h g

lemma pick {n k : ι → ℕ} (x : ι → ℕ → T t)
    (h : b.Moves W (a t) fun i => Tape.tab (n i) (x i)) (g : b.Moves W w k)
    (hh : ∀ i, k i<n i) :
    b.Moves W t fun i => x i (k i) :=
  (Can.look h g).cong (fun _ => rfl) (fun i => by rw [Tape.look_tab,ite_eq_left (hh i)])

lemma transfer {P : κ→ℕ} {x : κ→T t} (h : q.Moves P t x) {f} (g : b.Instant q f) :
    b.Moves (fun i => P (f i)) t fun i => x (f i) :=
  Can.then_do (g.prep.ease _) ((Can.reindex h f).ambient g.covers)

variable {cl : Paint}
lemma zero : b.Moves W (c cl) (fun _ => 0) := Can.zero
lemma one : b.Moves W sc (fun _ => 1) := Can.one
variable {X Y : ι→ℂ}
lemma add (h : b.Moves W (c cl) X) (g : b.Moves W (c cl) Y) :
    b.Moves W (c cl) fun i => X i+Y i := Can.add h g
lemma sub (h : b.Moves W (c cl) X) (g : b.Moves W (c cl) Y) :
    b.Moves W (c cl) fun i => X i-Y i := Can.sub h g
lemma mul (h : b.Moves W sc X) (g : b.Moves W (c cl) Y) :
    b.Moves W (c cl) fun i => X i*Y i := Can.mul h g
lemma inv (h : b.Moves W sc X) (k : ∀ i, X i≠0) :
    b.Moves W sc fun i => (X i)⁻¹ := Can.inv h k

end Moves

namespace Nick
variable {x y : ι→ℕ}
lemma wc (n : ℕ) : b.Nick fun _ => n := ⟨Moves.wc n,Small.const _ n⟩

lemma mov (h : b.Nick x) (W : ι→ℕ) : b.Moves W w x := h.close.ease W

lemma congr (h : b.Nick x) (g : ∀ i, x i=y i) :
    b.Nick y := by rwa [← funext g]

lemma transfer {f} {x : κ→ℕ} (h : q.Nick x) (g : b.Instant q f) :
    b.Nick fun i => x (f i) :=
  ⟨h.close.transfer g,(h.small.reindex _).trans g.covers⟩

lemma add (h : b.Nick x) (g : b.Nick y) : b.Nick fun i => x i+y i :=
  ⟨Can.plus h.close g.close h.small g.small,h.small.add g.small⟩
lemma sub (h : b.Nick x) (g : b.Nick y) : b.Nick fun i => x i-y i :=
  ⟨Can.minus h.close g.close h.small,h.small.sub⟩
lemma mul (h : b.Nick x) (g : b.Nick y) : b.Nick fun i => x i*y i :=
  ⟨Can.times h.close g.close h.small g.small,h.small.mul g.small⟩
lemma div (h : b.Nick x) (g : b.Nick y) : b.Nick fun i => x i/y i :=
  ⟨Can.dvdW h.close g.close h.small,h.small.div⟩
lemma residue (h : b.Nick x) (g : b.Nick y) : b.Nick fun i => x i%y i :=
  ⟨Can.modW h.close g.close h.small,h.small.mod⟩
lemma digit (h : b.Nick x) : b.Digit x :=
  ⟨PolyCan.of_can h.close (Small.const _ _),h.small⟩
end Nick

lemma envNow (b : Bench m ι) : b.Moves W b.tray b.env := Can.id
lemma cherry (b : Bench m ι) (x : ι→T t) : (b.extend t x).Moves W t x := Can.second
lemma pie (b : Bench m ι) (x : ι→T t) : (b.extend t x).Moves W b.tray b.env :=
  Can.first
lemma caseM {v : ι→T s} (h : b.Moves W t x) (g : (b.extend t x).Moves W s v) :
    b.Moves W s v := Can.bind h g

namespace Instant
variable {f : ι→κ}

lemma next (h : b.Instant q f) {p : κ→μ} (g : q.Instant z p) :
    b.Instant z fun i => p (f i) :=
  ⟨g.prep.transfer h,(g.covers.reindex _).trans h.covers⟩
lemma extend (b : Bench m ι) (x : ι→T t) : (b.extend t x).Instant b id :=
  ⟨pie b x,Small.self _⟩
lemma along (b : Bench m ι) (f : κ→ι) : (b.along f).Instant b f :=
  ⟨envNow (b.along f),Small.self _⟩
lemma identity (b : Bench m ι) : b.Instant b id :=
  ⟨envNow b,Small.self _⟩
lemma scan (b : Bench m ι) (n : ι→ℕ) : (b.scan n).Instant b During.i :=
  (Instant.extend _ (t:=w) (During.j (n:=n))).next (Instant.along b During.i)
lemma climbs (b : Bench m ι) (n : ι→ℕ) (x : ι → ℕ → T t) :
    (b.climbs n t x).Instant b During.i :=
  (Instant.extend _ (t:=p w t) (fun i : During n => (i.j,x i.i i.j))).next (Instant.along b During.i)
lemma supply (h : b.Instant q f) (x : κ→T t)
    (hx : b.Moves (fun _ => 0) t (fun i => x (f i))) :
    b.Instant (q.extend t x) f := ⟨h.prep.pair hx,h.covers⟩
lemma select {n : κ→ℕ} {f : ι→During n} (h : b.Instant q (fun i => (f i).i))
    (g : b.Moves (fun _ => 0) w (fun i => (f i).j)) :
    b.Instant (q.scan n) f := ⟨h.prep.pair g,h.covers⟩
end Instant

lemma chop {n : ι→ℕ} (h : b.Nick n) :
    (b.scan n).Nick During.j :=
  ⟨cherry (t:=w) _ During.j,
    (h.small.reindex During.i).mono (fun d : During n => d.hj.le)⟩

lemma stride {n : ι→ℕ} (h : b.Nick n) (x : ι → ℕ → T t) :
    (b.climbs n t x).Nick During.j :=
  ⟨(cherry (W:=fun _ => 0) _ (t:=p w t) (fun d : During n => (d.j,x d.i d.j))).fst,
    (chop h).small⟩
lemma tokenNow (b : Bench m ι) (n : ι→ℕ) (x : ι → ℕ → T t) :
    (b.climbs n t x).Moves (fun _ => 0) t (fun i => x i.i i.j) :=
  (cherry (t:=p w t) (W:=fun _ => 0) _ (fun d : During n => (d.j,x d.i d.j))).snd

variable {n : ι→ℕ} {u : ι → ℕ → ℕ}

theorem arrayM (h : b.Nick n) (f : ι→ℕ→T t)
    (hs : (b.scan n).Moves (fun d => u d.i d.j) t (fun d => f d.i d.j)) :
    b.Moves (fun i => n i + ∑ j ∈ range (n i), u i j) (a t)
      (fun i => Tape.tab (n i) (f i)) := by
  have hh := Can.tab (v:=f) (uB:=u) h.close hs h.small
  simpa only [Nat.zero_add,Moves] using hh

theorem arrayNow (h : b.Nick n) (f : ι→ℕ→T t)
    (hs : (b.scan n).Moves (fun _ => 0) t (fun d => f d.i d.j)) :
    b.Moves n (a t) (fun i => Tape.tab (n i) (f i)) := by
  simpa only [Nat.add_zero,sum_const_zero] using arrayM (u:=fun _ _ => 0) h f hs

theorem scatterNow (h : b.Nick n) (f : ι → ℕ → ℕ × T t)
    (hs : (b.scan n).Moves (fun _ => 0) (p w t) (fun d => f d.i d.j)) :
    b.Moves n (a t) (fun i => Tape.sow (n i) (n i) t.blank (f i)) := by
  have H := Can.sow (v:=f) (uB:=fun _ _ => 0) h.close h.close hs h.small h.small
  simp only [Nat.add_zero,Nat.zero_add,sum_const_zero] at H
  exact H.weaken ((Dom.self n).add (Dom.self n))

theorem repeatM (h : b.Nick n) (f : ι → ℕ → T t)
    (hb : b.Moves (fun _ => 0) t fun i => f i 0)
    (hh : (b.climbs n t f).Moves (fun d => u d.i d.j) t fun d => f d.i (d.j+1)) :
    b.Moves (fun i => n i+∑ j ∈ range (n i), u i j) t fun i => f i (n i) := by
  have H := Can.loop (v:=f) (uB:=u) h.close hb hh h.small
  simpa only [Nat.add_zero,Nat.zero_add,Moves] using H

theorem inspectz (h : b.Nick n)
    (hg : (b.along (Subtype.val (p:=fun i => n i = 0))).Moves
      (fun i => W i.val) t (fun i => x i.val))
    (hj : (b.along (Subtype.val (p:=fun i => n i ≠ 0))).Moves
      (fun i => W i.val) t (fun i => x i.val)) :
    b.Moves W t x := Can.testz (h.mov W) hg hj

end Bench

end
end PowerSaving.RAM

end OAI
