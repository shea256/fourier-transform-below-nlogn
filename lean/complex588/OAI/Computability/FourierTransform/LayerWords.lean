import OAI.Computability.FourierTransform.BinaryFrames
import OAI.Computability.FourierTransform.FourierIdentities

namespace OAI

/-! Layer words using the binary kernel copies and scaled-index layers. Exact-width by
a closure property on indices touched (indices outside the width never used and are
identity). Arrays modeled on ℕ. Monomial-slot representation doesn't need a permutation
certificate; it works even for a "gather". -/
namespace PowerSaving.Slant

open Binary Spectral Matrix Finset
noncomputable section

structure Stroke where
  ix : ℕ → ℕ
  dye : Line
  partner : ℕ → ℕ

namespace Stroke

def applyM (u : Stroke) (x : Line) : Line := fun i => u.dye i * x (u.ix i)

def applyC (u : Stroke) (x : Line) : Line := fun i =>
  if u.partner i = i then x i else ca * x i + cb * x (u.partner i)

def send (u : Stroke) (x : Line) := u.applyC (u.applyM x)

structure Sound (u : Stroke) (n : ℕ) : Prop where
  bdix : ∀ i < n, u.ix i < n
  bdp : ∀ i < n, u.partner i < n
  pair : ∀ i, u.partner (u.partner i)=i
  awayix : ∀ i, n ≤ i → u.ix i=i
  awayp : ∀ i, n ≤ i → u.partner i=i
  awayd : ∀ i, n ≤ i → u.dye i=1

namespace Sound
variable {u : Stroke} {n n' : ℕ}

lemma wider (h : u.Sound n) (h' : n ≤ n') : u.Sound n' := by
  refine ⟨fun i hi => ?_, fun i hi => ?_, h.pair, fun i hi => h.awayix i (by omega),
    fun i hi => h.awayp i (by omega), fun i hi => h.awayd i (by omega)⟩
  · rcases lt_or_ge i n with g|g
    · exact (h.bdix i g).trans_le h'
    · rwa [h.awayix i g]
  · rcases lt_or_ge i n with g|g
    · exact (h.bdp i g).trans_le h'
    · rwa [h.awayp i g]

theorem same (h : u.Sound n) (x : Line) (i : ℕ) (hi : n ≤ i) :
    u.send x i=x i := by simp [send,applyC,h.awayp i hi,applyM,h.awayix i hi,h.awayd i hi]

theorem send_congr (h : u.Sound n) {x y : Line} (H : ∀ i<n, x i=y i) :
    ∀ i<n, u.send x i=u.send y i := by
  have g (i : ℕ) (hi : i<n) : u.applyM x i=u.applyM y i :=
    congr_arg (u.dye i * ·) (H _ (h.bdix i hi))
  intro i hi
  simp only [send,applyC, g i hi,g _ (h.bdp i hi)]

end Sound

def unmark : Stroke := ⟨id,fun _ => 1,id⟩

@[simp] theorem send_unmark (x : Line) : unmark.send x=x := by ext i; simp [send,unmark,applyC,applyM]

theorem sound_unmark (n : ℕ) : unmark.Sound n :=
  ⟨fun _ hi => hi, fun _ hi => hi,fun _ => rfl,fun _ _ => rfl,fun _ _ => rfl,fun _ _ => rfl⟩

/-- A scaled lookup; used for monomial slots. -/
def plain (n : ℕ) (l : ℕ→ℕ) (d : Line) : Stroke :=
  ⟨fun i => if i < n then l i else i, fun i => if i < n then d i else 1, id⟩

theorem plain_sound (n : ℕ) (l : ℕ→ℕ) (d : Line)
    (h : ∀ i<n, l i<n) : (plain n l d).Sound n := by
  refine ⟨fun i hi => ?_,fun i hi => hi,fun i => rfl,fun i hi => ?_,
    fun i hi => rfl,fun i hi => ?_⟩ <;> simp [plain, hi, h, Nat.not_lt.mpr]

theorem plain_send (n : ℕ) (l : ℕ→ℕ) (d : Line) (x : Line) (i : ℕ) :
    (plain n l d).send x i=if i<n then d i*x (l i) else x i := by
  by_cases h : i<n <;> simp [send,plain,applyM,applyC,h]

-- parallel sum
def beside (p : ℕ) (u v : Stroke) : Stroke where
  ix i := if i<p then u.ix i else p+v.ix (i-p)
  dye i := if i<p then u.dye i else v.dye (i-p)
  partner i := if i<p then u.partner i else p+v.partner (i-p)

theorem Sound.beside {p q : ℕ} {u v : Stroke} (hu : u.Sound p) (hv : v.Sound q) :
    (Stroke.beside p u v).Sound (p+q) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i => ?_, fun i hi => ?_,
    fun i hi => ?_, fun i hi => ?_⟩
  · unfold Stroke.beside; dsimp; split
    · rename_i h
      have := hu.bdix i h
      omega
    · have := hv.bdix (i-p) (by omega)
      omega
  · unfold Stroke.beside; dsimp; split
    · rename_i h
      have := hu.bdp i h
      omega
    · have := hv.bdp (i-p) (by omega)
      omega
  · by_cases h : i<p
    · simp only [Stroke.beside,h,↓reduceIte, hu.bdp i h, hu.pair]
    · have HH := hv.pair (i-p)
      simp [Stroke.beside,h,HH,Nat.not_lt.mpr]
      omega
  · simp only [Stroke.beside, ite_eq_right (show ¬i<p by omega),
      hv.awayix _ (show q ≤ i-p by omega)]
    omega
  · simp only [Stroke.beside, ite_eq_right (show ¬i<p by omega),
      hv.awayp _ (show q ≤ i-p by omega)]
    omega
  · simp only [Stroke.beside, ite_eq_right (show ¬i<p by omega),
      hv.awayd _ (show q ≤ i-p by omega)]

def drift (p : ℕ) (x : Line) : Line := fun i => x (p+i)

theorem beside_left (p : ℕ) (u v : Stroke) (hu : u.Sound p) (x : Line)
    (i : ℕ) (hi : i<p) : (beside p u v).send x i=u.send x i := by
  simp only [send,applyM,applyC,beside,ite_eq_left hi,ite_eq_left (hu.bdp i hi)]

theorem beside_right (p : ℕ) (u v : Stroke) (x : Line) :
    drift p ((beside p u v).send x)=v.send (drift p x) := by
  ext i
  simp [send,applyC,applyM,beside,drift,Nat.not_lt.mpr]

end Stroke

open Stroke

/-- Array of strokes; slots read for t < beats. -/
structure Reel where
  beats : ℕ
  atBeat : ℕ → Stroke

namespace Reel

def reach (p : Reel) (x : Line) : ℕ → Line
  | 0 => x
  | t+1 => (p.atBeat t).send (reach p x t)

def go (p : Reel) (x : Line) := p.reach x p.beats

def Sound (p : Reel) (n : ℕ) : Prop := ∀ t<p.beats, (p.atBeat t).Sound n

namespace Sound

variable {u : Reel} {n n' : ℕ}

lemma wider (h : u.Sound n) (g : n ≤ n') : u.Sound n' :=
  fun t ht => (h t ht).wider g

theorem still (h : u.Sound n) (x : Line) (i : ℕ) (hi : n ≤ i) :
    u.go x i=x i := by
  have H (t : ℕ) (ht : t ≤ u.beats) :
      u.reach x t i=x i := by
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [reach,(h t (by omega)).same _ i hi, ih (by omega)]
  exact H u.beats le_rfl

theorem go_congr (h : u.Sound n) {x y : Line} (H : ∀ i<n, x i=y i) :
    ∀ i<n, u.go x i=u.go y i := by
  have G (t : ℕ) (ht : t ≤ u.beats) :
      ∀ i<n, u.reach x t i=u.reach y t i := by
    induction t with
    | zero => exact H
    | succ t ih => exact (h t (by omega)).send_congr (ih (by omega))
  exact G _ le_rfl

end Sound

def wait (d : ℕ) : Reel := ⟨d,fun _ => unmark⟩

@[simp] theorem go_wait (d : ℕ) (x : Line) : (wait d).go x=x := by
  have H (t : ℕ) : (wait d).reach x t=x := by
    induction t <;> simp_all [reach,wait]
  exact H _

theorem sound_wait (d n : ℕ) : (wait d).Sound n := fun _ _ => sound_unmark n

def tick (s : Stroke) : Reel := ⟨1,fun _ => s⟩

@[simp] theorem go_tick (s : Stroke) (x : Line) :
    (tick s).go x=s.send x := rfl

lemma sound_tick {n : ℕ} {s : Stroke} (h : s.Sound n) : (tick s).Sound n := fun _ _ => h

/-- Stack layer sequences, a performed first. -/
def stack (a b : Reel) : Reel :=
  ⟨a.beats+b.beats,fun i => if i<a.beats then a.atBeat i else b.atBeat (i-a.beats)⟩

@[simp] lemma go_stack (a b : Reel) (x : Line) :
    (a.stack b).go x=b.go (a.go x) := by
  have H (t : ℕ) (ht : t ≤ a.beats) :
      (a.stack b).reach x t=a.reach x t := by
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [reach,reach,ih (by omega)]
      simp only [stack,ite_eq_left (show t<a.beats by omega)]
  have G (t : ℕ) :
      (a.stack b).reach x (a.beats+t)=b.reach (a.go x) t := by
    induction t with
    | zero => simpa [go,reach] using H _ le_rfl
    | succ t ih =>
      rw [← add_assoc,reach,reach,ih]
      simp [stack]
  exact G b.beats

lemma Sound.stack {n : ℕ} {a b : Reel} (h : a.Sound n) (g : b.Sound n) :
    (a.stack b).Sound n := by
  intro t ht
  change t<a.beats+b.beats at ht
  unfold Reel.stack; dsimp; split
  · rename_i H; exact h t H
  · exact g _ (by omega)

/-- zip in parallel; used with matching lengths. -/
def parallel (p : ℕ) (a b : Reel) : Reel :=
  ⟨a.beats, fun i => beside p (a.atBeat i) (b.atBeat i)⟩

theorem Sound.parallel {p q : ℕ} {a b : Reel} (h : a.Sound p) (g : b.Sound q)
    (hl : a.beats=b.beats) :
    (Reel.parallel p a b).Sound (p+q) :=
  fun i hi => (h i hi).beside (g i (hl ▸ (by exact hi)))

theorem parallel_left (p : ℕ) (a b : Reel) (h : a.Sound p)
    (x : Line) : ∀ i<p, (parallel p a b).go x i=a.go x i := by
  have H (t : ℕ) (ht : t ≤ a.beats) :
      ∀ i<p, (parallel p a b).reach x t i=a.reach x t i := by
    induction t with
    | zero => intros; rfl
    | succ t ih =>
      intro i hi
      have g := h t (by omega)
      exact (beside_left p _ (b.atBeat t) g _ i hi).trans (g.send_congr (ih (by omega)) i hi)
  exact H a.beats le_rfl

theorem parallel_right (p : ℕ) (a b : Reel) (hl : a.beats=b.beats) (x : Line) :
    drift p ((parallel p a b).go x)=b.go (drift p x) := by
  have H (t : ℕ) : drift p ((parallel p a b).reach x t)=b.reach (drift p x) t := by
    induction t with
    | zero => rfl
    | succ t ih =>
      exact (beside_right p _ _ _).trans (congr_arg ((b.atBeat t).send) ih)
  change drift p ((parallel p a b).reach x a.beats)=_
  rw [H,hl]; rfl

/-- Use at offset p. -/
def atBase (p : ℕ) (a : Reel) : Reel := parallel p (wait a.beats) a

lemma Sound.atBase {q : ℕ} {a : Reel} (h : a.Sound q) (p : ℕ) :
    (Reel.atBase p a).Sound (p+q) :=
  (sound_wait _ _).parallel h rfl

lemma atBase_left (p : ℕ) (a : Reel) (x : Line) (i : ℕ) (hi : i<p) :
    (atBase p a).go x i=x i := by
  rw [atBase,parallel_left p _ a (sound_wait a.beats p) x i hi,go_wait]

lemma atBase_right (p : ℕ) (a : Reel) (x : Line) (i : ℕ) :
    (atBase p a).go x (p+i)=a.go (drift p x) i :=
  congr_fun (parallel_right p (wait a.beats) a rfl x) i

-- layer singleton builders
def swatch (n : ℕ) (d : Line) : Reel :=
  tick (Stroke.plain n id d)

def lace (n : ℕ) (q : ℕ→ℕ) : Reel :=
  tick (Stroke.plain n q (fun _ => 1))

lemma sound_swatch (n : ℕ) (d : Line) : (swatch n d).Sound n :=
  sound_tick (Stroke.plain_sound n _ _ fun _ hi => hi)

lemma go_swatch (n : ℕ) (d : Line) (x : Line) (i : ℕ) (hi : i<n) :
    (swatch n d).go x i=d i*x i := by
  rw [swatch,go_tick, plain_send,ite_eq_left hi]; rfl

lemma sound_lace (n : ℕ) (q : ℕ→ℕ) (h : ∀ i<n, q i<n) : (lace n q).Sound n :=
  sound_tick (Stroke.plain_sound n q _ h)

lemma go_lace (n : ℕ) (q : ℕ→ℕ) (x : Line) (i : ℕ) (hi : i<n) :
    (lace n q).go x i=x (q i) := by
  rw [lace,go_tick, plain_send,ite_eq_left hi,one_mul]

end Reel

end
end PowerSaving.Slant

end OAI
