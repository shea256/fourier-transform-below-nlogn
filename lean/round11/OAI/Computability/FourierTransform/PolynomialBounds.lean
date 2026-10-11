import OAI.Computability.FourierTransform.Cost

namespace OAI

/-! Uniform elementary bound helpers (natural envelopes; later compare to the real bounds). -/
namespace PowerSaving.RAM
open Finset

universe u v

/-- Pointwise polynomial bound with absolute constants. The bound relevant to word sizes
  will use n as B. Local computations may also have polynomial *work* in a different B. -/
def Small {ι : Type u} (B F : ι → ℕ) : Prop := ∃ d : ℕ, ∀ i, F i ≤ (B i+2)^d

namespace Small
variable {ι : Type u} {κ : Type v} {B C F G : ι → ℕ}

theorem const (B : ι → ℕ) (n : ℕ) : Small B (fun _ => n) := by
  refine ⟨n, fun i => ?_⟩
  have hh : n < 2^n := Nat.lt_two_pow_self
  exact hh.le.trans (Nat.pow_le_pow_left (by omega) _)

theorem self (B : ι → ℕ) : Small B B := ⟨1, by simp⟩

theorem reindex (h : Small B F) (f : κ → ι) : Small (fun j => B (f j)) (fun j => F (f j)) :=
  let ⟨d, hd⟩ := h
  ⟨d, fun j => hd (f j)⟩

theorem mono (h : Small B F) (hh : ∀ i, G i ≤ F i) : Small B G :=
  let ⟨d, hd⟩ := h
  ⟨d, fun i => (hh i).trans (hd i)⟩

theorem mul (h : Small B F) (g : Small B G) : Small B (fun i => F i * G i) := by
  obtain ⟨d,hd⟩ := h
  obtain ⟨e,he⟩ := g
  exact ⟨d+e, fun i => by simpa [pow_add] using Nat.mul_le_mul (hd i) (he i)⟩

theorem pow_mono_degree (b : ℕ) {d e : ℕ} (h : d ≤ e) :
    (b+2)^d ≤ (b+2)^e :=
  Nat.pow_le_pow_right (by omega) h

theorem add (h : Small B F) (g : Small B G) : Small B (fun i => F i + G i) := by
  obtain ⟨d,hd⟩ := h
  obtain ⟨e,he⟩ := g
  refine ⟨d+e+1, fun i => ?_⟩
  have a := (hd i).trans (pow_mono_degree _ (Nat.le_add_right d e))
  have b := (he i).trans (pow_mono_degree _ (Nat.le_add_left e d))
  rw [pow_succ]
  calc
    F i + G i ≤ ((B i+2)^(d+e))*2 := by omega
    _ ≤ _ := Nat.mul_le_mul_left _ (by omega)

theorem max (h : Small B F) (g : Small B G) :
    Small B (fun i => Max.max (F i) (G i)) :=
  (h.add g).mono (fun i => by omega)

theorem pow (h : Small B F) (n : ℕ) : Small B (fun i => (F i)^n) := by
  induction n with
  | zero => simpa using Small.const B 1
  | succ n ih => simpa [pow_succ] using ih.mul h

theorem trans (h : Small B F) (g : Small C B) : Small C F := by
  obtain ⟨d,hd⟩ := h
  exact ((g.add (Small.const C 2)).pow d).mono hd

end Small

/-- Least data needed for a "big-O with +1" natural work budget convenience. -/
def Dom {ι : Type u} (W F : ι → ℕ) : Prop :=
  ∃ C : ℕ, ∀ i, F i+1 ≤ C*(W i+1)

namespace Dom
variable {ι : Type u} {W F G : ι → ℕ}

theorem of_le (h : ∀ i, F i ≤ W i) : Dom W F :=
  ⟨1, fun i => by simpa using Nat.add_le_add_right (h i) 1⟩

theorem self (W : ι → ℕ) : Dom W W := of_le (fun _ => le_rfl)

theorem const (W : ι → ℕ) (n : ℕ) : Dom W (fun _ => n) := by
  refine ⟨n+1, ?_⟩
  intro i
  simp [mul_add]

theorem add (a : Dom W F) (b : Dom W G) : Dom W (fun i => F i + G i) := by
  obtain ⟨d,hd⟩ := a
  obtain ⟨e,he⟩ := b
  refine ⟨d+e, fun i => ?_⟩
  specialize hd i
  specialize he i
  dsimp
  rw [add_mul]
  omega

theorem trans (a : Dom W F) (b : Dom F G) : Dom W G := by
  obtain ⟨d,hd⟩ := a
  obtain ⟨e,he⟩ := b
  exact ⟨e*d, fun i => (he i).trans (by simpa [mul_assoc] using Nat.mul_le_mul_left e (hd i))⟩

end Dom
end PowerSaving.RAM

end OAI
