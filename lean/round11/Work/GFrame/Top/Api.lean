import Work.GFrame.Top.Menu
import Work.Reframe.Basic

/-!
# GFrame, top (key: eng-integrate): API parity of `GRoute` with `XRoute`, for the network copy

The bridged network (`Work/Reframe/Shared.lean`, `Work/Bridge/{Inv,Net,Cert}.lean`,
`Work/BridgeGeom/{Stage,Net}.lean`) uses, besides what ENGINE and LABELS already provide
(`GRoute.refl/cast/trans/gate/on_role/shifts/lift/parallel/liveKernel/reframe`), the following
combinators of the old calculus.  They are provided here under the same names with
`X ↦ G`, so that the network files can be copied by renaming:

    XReach            ↦ GReach             (def; = `Reach (gcalc α)`)
    XReach.refl/cast/trans/mul_right        ↦ GReach.refl/cast/trans/mul_right
    XReach.of_subset/down_subset, XMap.climb ↦ GReach.ofX applied to the old statement
    XStep.mul_right   ↦ GStep.mul_right
    XRoute.castg      ↦ GRoute.castg
    XRoute.reach_all  ↦ GRoute.reach_all
    XRoute.reframe_actPoint ↦ GRoute.reframe_actPoint

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.GF
open Binary Matrix Finset RAM CB
noncomputable section
section
variable {α : Type} [Fintype α] [DecidableEq α] {ρ : Type} [Fintype ρ] [DecidableEq ρ]

/-- a generalised word on one role acts on the LEFT of its matrix: any right factor is carried
along. -/
theorem GStep.mul_right {l : ρ} {M N : CMat α} {c : (ℕ → ℝ) → ℝ} (h : GStep l M N c)
    (D : CMat α) : GStep l (M * D) (N * D) c := by
  obtain ⟨w, U, hw, hc, hU, hwalk⟩ := h
  exact ⟨w, U, hw, hc, by rw [← Matrix.mul_assoc, hU], hwalk⟩

/-- On any role, the frame matrix `A` is carried to `B` by a generalised word of price `c`
(the analogue of `CB.XReach`). -/
def GReach (A B : CMat α) (c : (ℕ → ℝ) → ℝ) : Prop :=
  ∀ (ρ : Type) [Fintype ρ] [DecidableEq ρ] (l : ρ), GStep l A B c

namespace GReach
variable {A B C : CMat α} {c c' : (ℕ → ℝ) → ℝ}

theorem refl (A : CMat α) : GReach A A (fun _ => 0) := fun ρ _ _ l => GStep.refl l A

theorem cast (h : GReach A B c) (hc : ∀ φ, c φ = c' φ) : GReach A B c' :=
  fun ρ _ _ l => (h ρ l).cast hc

theorem trans (h : GReach A B c) (g : GReach B C c') : GReach A C (fun φ => c φ + c' φ) :=
  fun ρ _ _ l => (h ρ l).trans (g ρ l)

/-- every old one-role move (`XMap.climb`, `XReach.of_subset`, ...) is a generalised one. -/
theorem ofX (h : XReach A B c) : GReach A B c := fun ρ _ _ l => GStep.ofX (h ρ l)

theorem mul_right (h : GReach A B c) (D : CMat α) : GReach (A * D) (B * D) c :=
  fun ρ _ _ l => (h ρ l).mul_right D

/-- `GReach` is the `Reach` of the generalised calculus (what a schedule move asks for). -/
theorem toReach (h : GReach A B c) : Reach (gcalc α) A B c := h

theorem ofReach (h : Reach (gcalc α) A B c) : GReach A B c := h

end GReach

namespace GRoute

/-- rewrite the scalar map of an exact route. -/
theorem castg {S T : ρ → CMat α} {g g' : (ρ→ℂ) → (ρ→ℂ)} {c : (ℕ → ℝ) → ℝ}
    (h : GRoute S T g c) (hg : g = g') : GRoute S T g' c := hg ▸ h

/-- Every role moves by its own generalised word; prices add. -/
theorem reach_all (S T : ρ → CMat α) (c : ρ → (ℕ → ℝ) → ℝ)
    (h : ∀ r, GReach (S r) (T r) (c r)) :
    GRoute S T id (fun φ => ∑ r, c r φ) := by
  have hh (J : Finset ρ) :
      GRoute S (fun r => if r ∈ J then T r else S r) id (fun φ => ∑ r ∈ J, c r φ) := by
    induction J using Finset.induction_on with
    | empty =>
      have e0 : (fun r => if r ∈ (∅ : Finset ρ) then T r else S r) = S := by
        funext r; simp
      rw [e0]
      exact GRoute.refl.cast (fun φ => by simp)
    | insert l J hl ih =>
      have hsl : (if l ∈ J then T l else S l) = S l := by simp [hl]
      have step : GStep l (if l ∈ J then T l else S l) (T l) (c l) := by
        rw [hsl]; exact h l ρ l
      have b := GRoute.on_role (fun r => if r ∈ J then T r else S r) l (T l) step
      have hupd : Function.update (fun r => if r ∈ J then T r else S r) l (T l) =
          fun r => if r ∈ insert l J then T r else S r := by
        funext r
        by_cases hr : r = l
        · subst hr; simp
        · simp [Function.update_of_ne hr, Finset.mem_insert, hr]
      rw [hupd] at b
      exact (ih.trans b).cast (fun φ => by rw [Finset.sum_insert hl, add_comm])
  have H := hh Finset.univ
  have e1 : (fun r => if r ∈ (Finset.univ : Finset ρ) then T r else S r) = T := by
    funext r; simp
  rw [e1] at H
  exact H

/-- Re-framing a route whose scalar network is one rational matrix. -/
theorem reframe_actPoint {S T : ρ → CMat α} {G : Matrix ρ ρ ℚ} {c : (ℕ → ℝ) → ℝ}
    (D : ρ → CMat α) (h : GRoute S T (actPoint G) c) (hD : ∀ i j, G i j ≠ 0 → D i = D j) :
    GRoute (fun r => S r * D r) (fun r => T r * D r) (actPoint G) c :=
  GRoute.reframe D h (point_actPoint_commD G D hD)

end GRoute
end
end
end PowerSaving.GF
end OAI

#print axioms OAI.PowerSaving.GF.GStep.mul_right
#print axioms OAI.PowerSaving.GF.GReach.ofX
#print axioms OAI.PowerSaving.GF.GReach.mul_right
#print axioms OAI.PowerSaving.GF.GRoute.reach_all
#print axioms OAI.PowerSaving.GF.GRoute.reframe_actPoint
