import OAI.Computability.FourierTransform.TensorIndexing

namespace OAI

/-! Prefix computation and tensor gather. -/
namespace PowerSaving.Grove
open Slant Finset
noncomputable section

/-- Run state updates in order, with natural prefix addressing.
For step: parameters (axis, old prefix, extension digit, previous state). -/
def climb {α : Type*} (r : Axes) (x : α)
    (step : ℕ → ℕ → ℕ → α → α) : ℕ → ℕ → α
  | 0 => fun _ => x
  | l+1 => fun i => step l (i/r l) (i%r l) (climb r x step l (i/r l))

def survey (r : Axes) (u : ℕ → Stroke) : ℕ → ℕ → ℕ × ℂ :=
  climb r (0,1) fun i _ a s => (s.1*r i+(u i).ix a,s.2*(u i).dye a)

lemma survey_lt (r : Axes) (l : ℕ) (u : ℕ → Stroke) (h : Splits r l)
    (g : ∀ i<l, (u i).Sound (r i)) :
    ∀ j<extent r l, (survey r u l j).1<extent r l := by
  induction l with
  | zero => intro i hi; change 0<1; omega
  | succ l ih =>
    intro j hj
    exact h.join_lt (ih (h.cut (by omega)) (fun i hi => g i (by omega)) _
      (h.div_lt hj)) ((g l (by omega)).bdix _ (h.mod_lt j))

lemma canopy_survey (r : Axes) (l : ℕ) (u : ℕ → Stroke) (h : Splits r l)
    (g : ∀ i<l, (u i).Sound (r i)) :
    ∀ i<extent r l, ∀ j<extent r l,
      canopy r (fun t => leafM (u t)) l i j =
      if j=(survey r u l i).1 then (survey r u l i).2 else 0 := by
  induction l with
  | zero =>
    intro i hi j hj
    change j<1 at hj
    have h : j=0 := by omega
    simp [survey,climb,h,canopy]
  | succ l ih =>
    intro i hi j hj
    let v := survey r u l (i/r l)
    let b := (u l).ix (i%r l)
    have hb : b < r l := (g l (by omega)).bdix _ (h.mod_lt i)
    have H : j=v.1*r l+b ↔ j/r l=v.1 ∧ j%r l=b := by
      constructor
      · intro h; rw [h,chops _ _ _ hb,chips _ _ _ hb]; exact ⟨rfl,rfl⟩
      · rintro ⟨A,B⟩; rw [← A,← B]; exact (joined ..).symm
    change canopy r _ l _ _ * leafM (u l) _ _ =
      if j=v.1*r l+b then v.2 * (u l).dye (i%r l) else 0
    rw [ih (h.cut (by omega)) (fun i hi => g i (by omega)) _ (h.div_lt hi) _
      (h.div_lt hj)]
    change (if j/r l=v.1 then v.2 else 0) *
      (if j%r l=b then _ else 0) = if j=v.1*r l+b then _ else _
    by_cases A : j/r l=v.1 <;> by_cases B : j%r l=b <;> simp [H,A,B]

theorem graft_survey (r : Axes) (l : ℕ) (u : ℕ → Stroke) (h : Splits r l)
    (g : ∀ i<l, (u i).Sound (r i)) (x : Line) (j : ℕ) (hj : j<extent r l) :
    graft (extent r l) (canopy r (fun t => leafM (u t)) l) x j =
    (survey r u l j).2 * x (survey r u l j).1 := by
  let t := survey r u l j
  have ht := survey_lt r l u h g j hj
  change ∑ i ∈ range _, _ = t.2*x t.1
  rw [sum_eq_single t.1]
  · rw [canopy_survey r l u h g j hj _ ht, ite_eq_left rfl]
  · intro b hb hg
    rw [canopy_survey r l u h g j hj _ (mem_range.mp hb), ite_eq_right hg, zero_mul]
  · intro hh; exact absurd (mem_range.mpr ht) hh

end
end PowerSaving.Grove

end OAI
