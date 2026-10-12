import Work.Reframe.Basic

/-!
# (key: reframe) Frame algebra for shared helper sets

`SS.frameM M = wrap (fun x => lum (M *ᵥ x))` is the frame matrix of the projector `M`
(`frame A s = frameM (A.mat s)`, `SS.frame_eq`).  All frame matrices are diagonal in the Walsh
basis, hence commute.

* `frameM_add`       `Pᵀ * Q = 0 → frameM (P + Q) = frameM P * frameM Q`
                     (frame of an orthogonal sum; no basis needed);
* `frameM_comm`, `frameM_one` (`= kernel α`), `SS.frameM_zero` (`= 1`, already there);
* `unframeM`, `frameM_unframeM`, `unframeM_frameM`   explicit two-sided inverse;
* `reD Q A = unframeM Q * frameM A`   the re-framing matrix of a helper slot whose invocation
                     has base `Q` and which has absorbed `A`;
* `frameM_reD`       `frameM Q * reD Q A = frameM A`;
* `frameM_add_reD`   `frameM (Q + W) * reD Q A = frameM (W + A)` when `Q ⟂ W`, `W ⟂ A`;
* in ONE orthonormal basis: `OBase.mat_union`, `OBase.mat_orth`, `OBase.mat_transpose`,
  `frame_mul_unframe` (`frame B (q ∪ w) * (unframe B q * Z) = frame B w * Z`).

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace CB
open Binary Matrix Finset RAM SS
noncomputable section

section
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- adjointness of `mulVec` for the dot product (square case). -/
lemma dot_mulVec_adj (M : Matrix α α F) (x y : Space α) :
    dot (M *ᵥ x) y = dot x (Mᵀ *ᵥ y) := by
  change ∑ i, (∑ j, M i j * x j) * y i = ∑ j, x j * (∑ i, M i j * y i)
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma dot_mulVec_orth (P Q : Matrix α α F) (h : Pᵀ * Q = 0) (x : Space α) :
    dot (P *ᵥ x) (Q *ᵥ x) = 0 := by
  rw [dot_mulVec_adj, Matrix.mulVec_mulVec, h, Matrix.zero_mulVec, dot_zero_right]

/-- **Frame of an orthogonal sum of projectors.** -/
theorem frameM_add (P Q : Matrix α α F) (h : Pᵀ * Q = 0) :
    frameM (P + Q) = frameM P * frameM Q := by
  unfold frameM
  rw [wrap_mul]
  congr 1
  funext x
  rw [Matrix.add_mulVec, lum_add, dot_mulVec_orth P Q h x]
  simp [sign]

lemma frameM_comm (P Q : Matrix α α F) : frameM P * frameM Q = frameM Q * frameM P :=
  wrap_comm _ _

lemma frameM_one : frameM (1 : Matrix α α F) = kernel α := by
  unfold frameM
  have h : (fun x : Space α => lum ((1 : Matrix α α F) *ᵥ x)) = lum := by
    funext x; rw [Matrix.one_mulVec]
  rw [h, wrap_lum]

/-- explicit inverse of a frame matrix. -/
def unframeM (M : Matrix α α F) : CMat α := wrap fun x => (lum (M *ᵥ x))⁻¹

lemma frameM_unframeM (M : Matrix α α F) : frameM M * unframeM M = 1 := by
  unfold frameM unframeM
  rw [wrap_mul]
  have h : (fun x : Space α => lum (M *ᵥ x) * (lum (M *ᵥ x))⁻¹) = fun _ => 1 := by
    funext x; exact mul_inv_cancel₀ (lum_nonzero _)
  rw [h, wrap_one]

lemma unframeM_frameM (M : Matrix α α F) : unframeM M * frameM M = 1 :=
  mul_eq_one_comm.mp (frameM_unframeM M)

lemma unframeM_comm (P Q : Matrix α α F) : unframeM P * frameM Q = frameM Q * unframeM P :=
  wrap_comm _ _

/-- **The re-framing matrix of a helper slot**: its invocation has base `Q`, the slot has
absorbed `A` in earlier invocations. -/
def reD (Q A : Matrix α α F) : CMat α := unframeM Q * frameM A

lemma frameM_reD (Q A : Matrix α α F) : frameM Q * reD Q A = frameM A := by
  unfold reD
  rw [← Matrix.mul_assoc, frameM_unframeM, Matrix.one_mul]

/-- after the invocation the slot has absorbed the window `W` as well. -/
theorem frameM_add_reD (Q W A : Matrix α α F) (hQW : Qᵀ * W = 0) (hWA : Wᵀ * A = 0) :
    frameM (Q + W) * reD Q A = frameM (W + A) := by
  rw [frameM_add Q W hQW, frameM_comm Q W, Matrix.mul_assoc, frameM_reD, frameM_add W A hWA]

/-! ### inside one orthonormal basis -/

lemma _root_.OAI.PowerSaving.Binary.OBase.mat_union (A : OBase α) (s t : Finset α)
    (h : Disjoint s t) : A.mat (s ∪ t) = A.mat s + A.mat t := by
  ext i j
  simp only [OBase.mat, Matrix.add_apply]
  exact Finset.sum_union h

lemma _root_.OAI.PowerSaving.Binary.OBase.mat_transpose (A : OBase α) (s : Finset α) :
    (A.mat s)ᵀ = A.mat s := by
  ext i j
  simp only [OBase.mat, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- projectors of disjoint index sets of one basis are orthogonal. -/
lemma _root_.OAI.PowerSaving.Binary.OBase.mat_orth (A : OBase α) (s t : Finset α)
    (h : Disjoint s t) : (A.mat s)ᵀ * A.mat t = 0 := by
  rw [OBase.mat_transpose]
  ext i j
  simp only [Matrix.mul_apply, OBase.mat, Matrix.zero_apply, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro a ha
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro b hb
  have hab : a ≠ b := fun e => Finset.disjoint_left.mp h ha (e ▸ hb)
  have h0 : ∑ l, A.v a l * A.v b l = 0 := by
    have := A.rows a b
    rwa [if_neg hab] at this
  calc ∑ l, A.v a i * A.v a l * (A.v b l * A.v b j)
      = A.v a i * A.v b j * ∑ l, A.v a l * A.v b l := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        ring
    _ = 0 := by rw [h0, mul_zero]

/-- the same statements with index sets: base `q`, window `w` (disjoint), any `Z` on the
right. -/
lemma frame_mul_unframe (B : OBase α) (q w : Finset α) (h : Disjoint q w) (Z : CMat α) :
    frame B (q ∪ w) * (unframe B q * Z) = frame B w * Z := by
  rw [frame_union B q w h, frame, frame, wrap_comm, ← frame, ← frame, Matrix.mul_assoc,
    ← Matrix.mul_assoc (frame B q), unframe_right, Matrix.one_mul]

end
end
end CB
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.CB.frameM_add
#print axioms OAI.PowerSaving.CB.frameM_add_reD
#print axioms OAI.PowerSaving.Binary.OBase.mat_orth
#print axioms OAI.PowerSaving.CB.frame_mul_unframe
