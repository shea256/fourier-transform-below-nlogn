import OAI.Computability.FourierTransform.DisjointIntervals

namespace OAI

namespace PowerSaving.Slant
open Reel Stroke Zone Spectral
noncomputable section

def initial (n : ℕ) : Zone := ⟨0,n⟩
def ending (n : ℕ) : Zone := ⟨n,n⟩

lemma half_fits (n : ℕ) : (initial n).Fits (n+n) ∧ (ending n).Fits (n+n) :=
  ⟨fits_of _ _ (by change 0+n ≤ _; omega),fits_of _ _ le_rfl⟩
lemma half_sep (n : ℕ) : (initial n).Sep (ending n) :=
  sep_of _ _ (by change 0+n ≤ n; omega)

def deal (n i : ℕ) := if i<n then 2*i else 2*(i-n)+1

def foldPair (n : ℕ) (u : ℂ) : Reel :=
  (shade (initial n) (ending n) (fun _ => 1) (fun i => u^i)).stack
    (hinge (initial n) (ending n))

def duo (n : ℕ) (u : ℂ) (r : Reel) : Reel :=
  ((lace (n+n) (deal n)).stack (parallel n r r)).stack (foldPair n u)

def pulse : ℕ → ℂ → Reel
  | 0,_ => wait 0
  | d+1,u => duo (2^d) u (pulse d (u^2))

lemma sound_foldPair (n : ℕ) (u : ℂ) : (foldPair n u).Sound (n+n) :=
  ((sound_shade (half_fits n).1 (half_fits n).2).stack
    (sound_hinge (half_fits n).1 (half_fits n).2 rfl (half_sep n)))

lemma sound_duo (n : ℕ) (u : ℂ) (r : Reel) (h : r.Sound n) :
    (duo n u r).Sound (n+n) :=
  ((sound_lace (n+n) (deal n) (by
    intro i hi
    unfold deal
    split <;> omega)).stack (h.parallel h rfl)).stack (sound_foldPair n u)

lemma sound_pulse (d : ℕ) (u : ℂ) : (pulse d u).Sound (2^d) := by
  induction d generalizing u with
  | zero => exact sound_wait 0 _
  | succ d ih =>
    rw [pulse, pow_succ (2:ℕ) d, mul_two]
    exact sound_duo _ u _ (ih _)

lemma beats_duo (n : ℕ) (u : ℂ) (r : Reel) : (duo n u r).beats=r.beats+5 := by
  change 1+r.beats+(1+3)=_
  omega

lemma beats_pulse (d : ℕ) (u : ℂ) : (pulse d u).beats=5*d := by
  induction d generalizing u with
  | zero => rfl
  | succ d ih =>
    rw [pulse, beats_duo,ih]; omega

def Flows (r : Reel) (n : ℕ) (f : Line→Line) : Prop :=
  ∀ x, ∀ i<n, r.go x i=f x i

lemma go_foldPair (n : ℕ) (u : ℂ) (x : Line) (i : ℕ) (h : i<n) :
    let z := (foldPair n u).go x
    z i = x i + u^i*x (n+i) ∧
    z (n+i) = x i - u^i*x (n+i) := by
  have hh := ((twins_shade (u:=initial n) (v:=ending n) rfl (half_sep n) (fun _ => 1)
    (fun i => u^i)).stack (twins_hinge rfl (half_sep n))).acts x i h
  simpa [foldPair,twinsAt,Zone.peek,drift,initial,ending,
    Prod.mk.injEq] using hh

lemma flows_duo (n : ℕ) (u : ℂ) (r : Reel) (hn : 0<n)
    (hu : IsPrimitiveRoot u (n+n)) (h : r.Sound n) (hf : Flows r n (freq n (u^2))) :
    Flows (duo n u r) (n+n) (freq (n+n) u) := by
  intro x
  let y := (lace (n+n) (deal n)).go x
  let z := (parallel n r r).go y
  have A (i : ℕ) (hi : i<n) : y i=x (2*i) := by
    rw [show y=(lace (n+n) (deal n)).go x from rfl,go_lace _ _ _ _ (by omega),
      deal,ite_eq_left hi]
  have B (i : ℕ) (hi : i<n) : drift n y i=x (2*i+1) := by
    unfold drift y
    rw [go_lace _ _ _ _ (by omega),deal]
    simp
  have U (i : ℕ) (hi : i<n) : z i=freq n (u^2) (fun j => x (2*j)) i := by
    unfold z
    rw [parallel_left n r r h y i hi,hf y i hi, freq_congr (y:=fun j => x (2*j)) A]
  have V (i : ℕ) (hi : i<n) : z (n+i)=freq n (u^2) (fun j => x (2*j+1)) i := by
    change drift n ((parallel n r r).go y) i=_
    rw [parallel_right n r r rfl,hf _ i hi,freq_congr B]
  intro i hi
  simp only [duo,go_stack]
  change (foldPair n u).go z i=_
  rcases lt_or_ge i n with hg|hg
  · rw [(go_foldPair n u z i hg).1, U i hg,V i hg,freq_eo]
  · obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hg
    have HH : j<n := by omega
    rw [(go_foldPair n u z j HH).2,U j HH,V j HH,freq_eo' hn hu]

lemma flows_pulse (d : ℕ) (u : ℂ) (h : IsPrimitiveRoot u (2^d)) :
    Flows (pulse d u) (2^d) (freq (2^d) u) := by
  induction d generalizing u with
  | zero =>
    intro x i hi
    simp at hi
    simp [pulse,freq,hi]
  | succ d ih =>
    rw [pulse,pow_succ (2:ℕ) d,mul_two]
    rw [pow_succ,mul_two] at h
    exact flows_duo _ u _ (by positivity) h (sound_pulse d _) (ih _ (even_prim h))

def backPulse (d : ℕ) (u : ℂ) : Reel :=
  (pulse d u⁻¹).stack (swatch (2^d) (fun _ => (((2^d:ℕ):ℂ))⁻¹))

lemma sound_back (d : ℕ) (u : ℂ) : (backPulse d u).Sound (2^d) :=
  (sound_pulse d _).stack (sound_swatch _ _)

lemma beats_back (d : ℕ) (u : ℂ) : (backPulse d u).beats=5*d+1 := by
  change (pulse d u⁻¹).beats+1=_
  rw [beats_pulse]

lemma flows_back (d : ℕ) (u : ℂ) (h : IsPrimitiveRoot u (2^d)) :
    Flows (backPulse d u) (2^d) (fun x i => (((2^d:ℕ):ℂ))⁻¹ * freq (2^d) u⁻¹ x i) := by
  intro x i hi
  rw [backPulse,go_stack,go_swatch _ _ _ _ hi, flows_pulse d _ h.inv _ i hi]

/-- mount at offset and effect only on zone. -/
structure Retrace (r : Reel) (u : Zone) (f : Line→Line) : Prop where
  draws : ∀ x, ∀ i<u.wide, u.peek (r.go x) i=f (u.peek x) i
  waits : ∀ x i, ¬u.has i → r.go x i=x i

lemma atBase_retrace {a : Reel} {z : Zone} {f : Line→Line} (h : a.Sound z.wide)
    (g : Flows a z.wide f) :
    Retrace (atBase z.lo a) z f := by
  refine ⟨fun x i hi => ?_,fun x i hi => ?_⟩
  · unfold Zone.peek drift
    rw [atBase_right]
    exact g _ i hi
  · cases z.boundary hi with
    | inl hp => exact atBase_left z.lo a x i hp
    | inr hp => exact (h.atBase z.lo).still x i hp

lemma retrace_preserve {a : Reel} {u v : Zone} {f : Line→Line} (h : Retrace a u f)
    (g : v.Sep u) (x : Line) (i : ℕ) (hi : i<v.wide) :
    v.peek (a.go x) i=v.peek x i := h.waits x _ (g _ (v.inside hi))

end
end PowerSaving.Slant

end OAI
