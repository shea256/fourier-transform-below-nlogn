import OAI.Computability.FourierTransform.PolynomialBounds

namespace OAI

/-! Compositional proofs of operation/word bounds. -/
namespace PowerSaving.RAM
open Ty Finset

universe U V

/-- Parameters for one uniform open code guarantee. When doing recursion proofs the
  index i can range over arbitrary environments including call bounds. -/
structure Bank (r : Port) (ι : Type U) where
  B : ι → ℕ
  ext : ι → ℕ             -- additional bound allowed on words of external calls
  use : ι → Handler r

variable {ι : Type U} {r : Port}

def Bank.cap (b : Bank r ι) (d : ℕ) (i : ι) : ℕ :=
  max ((b.B i+2)^d) (b.ext i)

theorem Bank.cm (b : Bank r ι) {d e} (h : d ≤ e) (i : ι) : b.cap d i ≤ b.cap e i :=
  max_le_max (Small.pow_mono_degree _ h) le_rfl

def Bank.closed {ι : Type U} (B : ι → ℕ) : Bank none ι := ⟨B, fun _ => 0, fun _ => ()⟩

def Bank.comap {ι : Type U} {κ : Type V} (b : Bank r ι) (f : κ → ι) : Bank r κ :=
  ⟨fun i => b.B (f i), fun i => b.ext (f i), fun i => b.use (f i)⟩

/-- The charge Z is additive work allowed (used in body proofs for calls).
  Unlike the budget W it does not get an implicit constant multiplier. -/
def Able {r} {ι : Type U} (m : Bool) (b : Bank r ι) (s t)
    (x : ι → T s) (y : ι → T t) (W Z : ι → ℕ) : Prop :=
  ∃ (f : Code m r s t) (C d : ℕ), ∀ i,
    (f.run (b.use i) (x i)).OK (y i) (C*(W i+1)+Z i) (b.cap d i)

/-- Ordinary closed computation guarantee. -/
abbrev Can {ι : Type U} (m : Bool) (B : ι → ℕ) (s t)
    (x : ι → T s) (y : ι → T t) (W : ι → ℕ) : Prop :=
  Able m (Bank.closed B) s t x y W (fun _ => 0)

namespace Able
variable {ι : Type U} {κ : Type V}
  {m : Bool} {r : Port} {b : Bank r ι} {s t u : Ty}
  {x : ι → T s} {y : ι → T t} {z : ι → T u}
  {W Z W' Z' : ι → ℕ}

theorem reindex (h : Able m b s t x y W Z) (f : κ → ι) :
    Able m (b.comap f) s t (fun i => x (f i)) (fun i => y (f i))
      (fun i => W (f i)) (fun i => Z (f i)) :=
  let ⟨pr,d,e,hp⟩ := h
  ⟨pr,d,e,fun i => hp (f i)⟩

theorem cong (h : Able m b s t x y W Z) {x' y'} (hx : ∀ i, x i = x' i)
    (hy : ∀ i, y i = y' i) : Able m b s t x' y' W Z := by
  rwa [funext hx, funext hy] at h

theorem weaken (h : Able m b s t x y W Z) (hW : Dom W' W)
    (hZ : ∀ i, Z i ≤ Z' i) : Able m b s t x y W' Z' := by
  obtain ⟨f,C,d,h⟩ := h
  obtain ⟨D,hW⟩ := hW
  exact ⟨f,C*D,d, fun i => (h i).mono
    (Nat.add_le_add (by simpa [mul_assoc] using Nat.mul_le_mul_left C (hW i)) (hZ i)) le_rfl⟩

theorem mono (h : Able m b s t x y W Z) (hW : ∀ i, W i ≤ W' i)
    (hZ : ∀ i, Z i ≤ Z' i) : Able m b s t x y W' Z' :=
  h.weaken (Dom.of_le hW) hZ

/-- Change word budget. -/
theorem rebank {b' : Bank r ι} (h : Able m b s t x y W Z)
    (hB : Small b'.B b.B) (hH : ∀ i, b.ext i ≤ b'.ext i) (hU : b.use = b'.use) :
    Able m b' s t x y W Z := by
  obtain ⟨f,C,d,h⟩ := h
  obtain ⟨e,he⟩ := (hB.add (Small.const _ 2)).pow d
  refine ⟨f,C,e,fun i => ?_⟩
  rw [← hU]
  exact (h i).mono le_rfl (max_le_max (he i) (hH i))

private theorem combine_time (C D w v y z : ℕ) :
    (C*(w+1)+y)+(D*(v+1)+z)+1 ≤ (C+D+1)*(w+v+1)+(y+z) := by
  simp only [mul_add, add_mul, one_mul, mul_one]
  omega

theorem comp (h : Able m b s t x y W Z) (g : Able m b t u y z W' Z') :
    Able m b s u x z (fun i => W i + W' i) (fun i => Z i + Z' i) := by
  obtain ⟨f,C,d,hf⟩ := h
  obtain ⟨j,D,e,hj⟩ := g
  refine ⟨.comp f j, C+D+1, max d e, fun i => ?_⟩
  rw [Code.run]
  have h := (hf i).mono le_rfl (b.cm (le_max_left d e) i)
  have g := (hj i).mono le_rfl (b.cm (le_max_right d e) i)
  exact ((h.pass g).pay (Nat.zero_le _)).mono (combine_time _ _ _ _ _ _) le_rfl

theorem comp_keep (h : Able m b s t x y W Z) (g : Able m b t u y z W Z') :
    Able m b s u x z W (fun i => Z i + Z' i) :=
  (h.comp g).weaken ((Dom.self W).add (Dom.self W)) (fun _ => le_rfl)

theorem fork (h : Able m b s t x y W Z) (g : Able m b s u x z W' Z') :
    Able m b s (p t u) x (fun i => (y i,z i)) (fun i => W i+W' i) (fun i => Z i+Z' i) := by
  obtain ⟨f,C,d,hf⟩ := h
  obtain ⟨j,D,e,hj⟩ := g
  refine ⟨.fork f j, C+D+1, max d e, fun i => ?_⟩
  rw [Code.run]
  have h := (hf i).mono le_rfl (b.cm (le_max_left d e) i)
  have g := (hj i).mono le_rfl (b.cm (le_max_right d e) i)
  refine (h.pass (g.pass (Bill.one_ok (y i,z i) _))).mono ?_ le_rfl
  simpa [add_assoc] using combine_time C D (W i) (W' i) (Z i) (Z' i)

theorem fork_keep (h : Able m b s t x y W Z) (g : Able m b s u x z W Z') :
    Able m b s (p t u) x (fun i => (y i,z i)) W (fun i => Z i+Z' i) :=
  (h.fork g).weaken ((Dom.self W).add (Dom.self W)) (fun _ => le_rfl)

theorem use_call {b : Bank (some (s,t)) ι}
    (h : ∀ i, (b.use i (x i)).OK (y i) (Z i) (b.ext i)) :
    Able m b s t x y (fun _ => 0) Z := by
  refine ⟨.call,1,1, fun i => ?_⟩
  rw [Code.run]
  exact ((h i).pay (Nat.zero_le _)).mono (by simp [add_comm]) (le_max_right _ _)

/-- Bring in a closed program; charges its work normally. -/
theorem of_can (h : Can m b.B s t x y W) :
    Able m b s t x y W (fun _ => 0) := by
  obtain ⟨f,C,d,h⟩ := h
  refine ⟨.importClosed f,C+1,d,fun i => ?_⟩
  rw [Code.run]
  refine ((h i).pay (Nat.zero_le _)).mono ?_ ?_
  · dsimp
    rw [add_mul]
    omega
  · exact max_le_max le_rfl (Nat.zero_le _)

/-- One primitive, with whatever polynomial word bound its result takes. -/
theorem atom_small (f : Atom m s t) {P : ι → ℕ} (hP : Small b.B P)
    (h : ∀ i, (f.run (x i)).OK (y i) 1 (P i)) :
    Able m b s t x y W Z := by
  obtain ⟨d,hd⟩ := hP
  refine ⟨.atom f,1,d,fun i => ?_⟩
  rw [Code.run]
  exact (h i).mono (by omega) ((hd i).trans (le_max_left _ _))

theorem atom_one (f : Atom m s t) (h : ∀ i, f.run (x i) = Bill.one (y i)) :
    Able m b s t x y W Z :=
  atom_small f (Small.const b.B 0) (fun i => by rw [h]; apply Bill.one_ok)

theorem id : Able m b s s x x W Z :=
  atom_one .id (fun _ => rfl)

theorem first {v : ι → T (p s t)} : Able m b (p s t) s v (fun i => (v i).1) W Z :=
  atom_one .fst (fun _ => rfl)

theorem second {v : ι → T (p s t)} : Able m b (p s t) t v (fun i => (v i).2) W Z :=
  atom_one .snd (fun _ => rfl)

theorem fst {v : ι → T (p t u)} (h : Able m b s (p t u) x v W Z) :
    Able m b s t x (fun i => (v i).1) W Z :=
  h.comp_keep (first (Z:=fun _ => 0))

theorem snd {v : ι → T (p t u)} (h : Able m b s (p t u) x v W Z) :
    Able m b s u x (fun i => (v i).2) W Z :=
  h.comp_keep (second (Z:=fun _ => 0))

/-- let-bind an expression, retaining environment. -/
theorem save (h : Able m b s t x y W Z)
    (g : Able m b (p s t) u (fun i => (x i,y i)) z W' Z') :
    Able m b s u x z (fun i => W i + W' i) (fun i => Z i + Z' i) := by
  have hh := id (m:=m) (W:=W) (Z:=fun _ => 0) |>.fork_keep h
  simpa using hh.comp g

theorem save_keep (h : Able m b s t x y W Z)
    (g : Able m b (p s t) u (fun i => (x i,y i)) z W Z') :
    Able m b s u x z W (fun i => Z i + Z' i) :=
  (h.save g).weaken ((Dom.self W).add (Dom.self W)) (fun _ => le_rfl)

end Able
end PowerSaving.RAM

end OAI
