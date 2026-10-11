import Work.GFrame.Top.Api
import Work.Reframe.SNet

/-!
# GFrame, top (key: eng-integrate): a stage of generalised invocations

`gsstage`: the generalised copy of `RF.sstage` (`Work/Reframe/SNet.lean`): every invocation `d`
of a stage runs a Box route of the GENERALISED engine with the same scalar map and the same
price; ONE parallel composition over `Γ`.  It is stated for arbitrary frame matrices `S`, `U`
(no frame map, no label type), so it serves stage A and stage B alike; it is the first brick of
the network copy (`Work/Bridge/{Inv,Net,Cert}.lean` with `XRoute ↦ GRoute`).

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.GF
open Binary Matrix Finset RAM SS CB RF
noncomputable section
section
variable {T Sl C α Γ : Type} [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] [Fintype α] [DecidableEq α]
  [Fintype Γ] [DecidableEq Γ]

/-- **A stage of generalised routes** (as `RF.sstage`). -/
theorem gsstage (εX : T → Γ ≃ Γ) (εS : Γ ≃ Γ) {S U : SRole Γ T Sl C → CMat α}
    {G : (SRole Γ T Sl C → ℂ) → (SRole Γ T Sl C → ℂ)}
    {h : (Box T Sl C → ℂ) → (Box T Sl C → ℂ)} {cost : (ℕ → ℝ) → ℝ}
    (q : ∀ d, GRoute (S ∘ sem εX εS d) (U ∘ sem εX εS d) h cost)
    (hin : ∀ d x, (G x) ∘ sem εX εS d = h (x ∘ sem εX εS d)) :
    GRoute S U G (fun φ => (Fintype.card Γ : ℝ) * cost φ) := by
  have key := GRoute.parallel (ρ := Box T Sl C) (σ := SRole Γ T Sl C) (J := Γ)
    (e := fun d => sem εX εS d) (fun d d' hd x => sem_dis εX εS d d' hd x)
    (S := S) (T := U) (d := fun _ => cost) (g := G) (h := fun _ => h) q hin
    (fun x r hr => by
      obtain ⟨d, hd⟩ := scovered εX εS r
      exact absurd hd (hr d))
    (fun r hr => by
      obtain ⟨d, hd⟩ := scovered εX εS r
      exact absurd hd (hr d))
  refine key.cast (fun φ => ?_)
  simp

end
end
end PowerSaving.GF
end OAI

#print axioms OAI.PowerSaving.GF.gsstage
