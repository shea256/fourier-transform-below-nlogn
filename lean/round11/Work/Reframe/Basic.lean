import Work.Combine.XInvocation

/-!
# (key: reframe) Re-framing an exact block route

`XRoute S T g c` (`Work.BlockApply.Exact`) is semantic: ONE proper block word, correct for every
input array.  Therefore the word may be started from `S r * D r` instead of `S r`, for ARBITRARY
matrices `D r`, as long as the scalar network `g` commutes with `D`.  Same word, same price for
every price list.  This is the block version of `Route.reframe` / `GPath.reframe`
(`checks/wht6/shared/helper-sharing/Reframe.lean`, `ReframeG.lean`).

* `XRoute.reframe`            the lemma;
* `point_actPoint_commD`      the commutation hypothesis for one rational gate matrix
                              (every nonzero entry joins two roles with the same `D`);
* `XRoute.reframe_actPoint`   re-framing a route whose scalar network is one gate matrix;
* `XStep.mul_right`, `XReach.mul_right`
                              the one-role version: a block move of one role does not care what
                              stands to the right of the frame matrix.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace RAM
open Binary Matrix Finset
noncomputable section

section
variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

theorem multiAct_mulR (f : ℕ) (S D : ρ → CMat α) (x : Data α ρ f) :
    multiAct f (fun r => S r * D r) x = multiAct f S (multiAct f D x) := by
  funext r
  show matAct f (S r * D r) (x r) = matAct f (S r) (matAct f (D r) (x r))
  rw [matAct_mul]

/-- **Re-framing an exact block route.**  Same word, same price for every price list. -/
theorem XRoute.reframe {S T : ρ → CMat α} {g : (ρ→ℂ) → (ρ→ℂ)} {c : (ℕ → ℝ) → ℝ}
    (D : ρ → CMat α) (h : XRoute S T g c)
    (hg : ∀ (f : ℕ) (x : Data α ρ f), point f g (multiAct f D x) = multiAct f D (point f g x)) :
    XRoute (fun r => S r * D r) (fun r => T r * D r) g c := by
  obtain ⟨w, hw, hc, hwalk⟩ := h
  refine ⟨w, hw, hc, fun f x => ?_⟩
  have h1 := multiAct_mulR f S D x
  have h2 := multiAct_mulR f T D (point f g x)
  rw [h1, hwalk, hg, h2]

/-- The commutation hypothesis for a point gate: every nonzero entry joins roles with equal
`D`. -/
theorem point_actPoint_commD (G : Matrix ρ ρ ℚ) (D : ρ → CMat α)
    (hD : ∀ i j, G i j ≠ 0 → D i = D j) (f : ℕ) (x : Data α ρ f) :
    point f (actPoint G) (multiAct f D x) = multiAct f D (point f (actPoint G) x) := by
  funext r i
  change ∑ j, (G r j:ℂ) * (∑ a, digitProd (fun _ : Fin f => D j) i a * x j a)
     = ∑ a, digitProd (fun _ : Fin f => D r) i a * (∑ j, (G r j:ℂ) * x j a)
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro j _
  by_cases gh : G r j = 0
  · simp [gh]
  · rw [hD r j gh]
    ac_rfl

/-- Re-framing a route whose scalar network is one rational matrix. -/
theorem XRoute.reframe_actPoint {S T : ρ → CMat α} {G : Matrix ρ ρ ℚ} {c : (ℕ → ℝ) → ℝ}
    (D : ρ → CMat α) (h : XRoute S T (actPoint G) c) (hD : ∀ i j, G i j ≠ 0 → D i = D j) :
    XRoute (fun r => S r * D r) (fun r => T r * D r) (actPoint G) c :=
  XRoute.reframe D h (point_actPoint_commD G D hD)

/-- linearity of the action of a matrix on one array. -/
lemma matAct_add (f : ℕ) (M : CMat α) (x y : Sky α f → ℂ) :
    matAct f M (x + y) = matAct f M x + matAct f M y := by
  unfold matAct; rw [Matrix.mulVec_add]

lemma matAct_sub (f : ℕ) (M : CMat α) (x y : Sky α f → ℂ) :
    matAct f M (x - y) = matAct f M x - matAct f M y := by
  unfold matAct; rw [Matrix.mulVec_sub]

lemma matAct_zero' (f : ℕ) (M : CMat α) : matAct f M (0 : Sky α f → ℂ) = 0 := by
  unfold matAct; rw [Matrix.mulVec_zero]

end
end
end RAM

namespace Binary
open Matrix Finset
section
variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

/-- a block word on one role acts on the LEFT of its matrix: any right factor is carried
along. -/
theorem XStep.mul_right {l : ρ} {M N : CMat α} {c : (ℕ → ℝ) → ℝ} (h : XStep l M N c)
    (D : CMat α) : XStep l (M * D) (N * D) c := by
  obtain ⟨w, U, hw, hc, hU, hwalk⟩ := h
  exact ⟨w, U, hw, hc, by rw [← Matrix.mul_assoc, hU], hwalk⟩

end
end Binary

namespace CB
open Binary Matrix Finset RAM
section
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- a block move of one role, with an arbitrary right factor. -/
theorem XReach.mul_right {A B : CMat α} {c : (ℕ → ℝ) → ℝ} (h : XReach A B c) (D : CMat α) :
    XReach (A * D) (B * D) c :=
  fun ρ _ _ l => (h ρ l).mul_right D

end
end CB
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.RAM.XRoute.reframe
#print axioms OAI.PowerSaving.RAM.XRoute.reframe_actPoint
#print axioms OAI.PowerSaving.CB.XReach.mul_right
