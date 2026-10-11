import Work.GFrame.Labels.All
import Work.GFrame.Engine.Group

/-!
# GFrame, top (key: eng-integrate): schedule -> exact route -> certificate -> engine

The generalised replacement of the chain `CR.sched_route -> XRoute -> XRoute.liveKernel ->
engine_program_group_list`:

    GSchedOkR (gcalc α) Φ lab l            a legal schedule over ANY label system `Φ`
      --gsched_groute_R (LABELS)-->  GRoute  an exact route of the generalised engine
      --GCert.ofRoute (ENGINE)-->    GCert   a scratch certificate with the exact price
      --engine_program_ggroup_list (ENGINE)-->  the program and its time bound.

* `KernelSched Φ lab l e`   what a schedule must do besides being legal: start on invertible
                            frames, leave the live coordinates alone, end on `kernel * start`;
* `gcert_of_sched`          legal + `KernelSched`  =>  `GCert α e (rcost · (gschedRanks l))`;
* `RAM.engine_program_gsched`      the RAM program, numeric hypothesis UNCHANGED
                                   (that of `engine_program_group_list`, verbatim);
* `BlockWHT.wht_main_of_gsched`    the Walsh-Hadamard program and its time bound.

A move of a schedule is ANY one-role step of the generalised engine (`Reach`): a block along
any independent directions, a free adapter, a nested step between arbitrary subspaces
(degenerate ones included), an alternating residual.  See `Top/Menu.lean`.  A gate needs
IDENTICAL frame matrices.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving

namespace GF
open Binary Matrix Finset RAM CB
noncomputable section
section
variable {α 𝓛 ρ σ : Type} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

/-- **What a schedule must do to be a kernel certificate** on the live roles `e`:
`inv`  every role starts on an invertible frame matrix;
`fix`  when the scratch roles hold zero, the scalar network of the schedule returns the live
       coordinates unchanged;
`ker`  every live role ends on `kernel α * (its starting frame)`. -/
structure KernelSched (Φ : 𝓛 → CMat α) (lab : ρ → 𝓛) (l : List (GSt 𝓛 ρ)) (e : σ → ρ) :
    Prop where
  inv : ∀ r, ∃ Ψ : CMat α, Φ (lab r) * Ψ = 1
  fix : ∀ x : ρ → ℂ, (∀ s, (∀ t, e t ≠ s) → x s = 0) → ∀ t, gschedAct l x (e t) = x (e t)
  ker : ∀ t, Φ (gschedOut lab l (e t)) = kernel α * Φ (lab (e t))

/-- **A legal schedule that is a kernel on the live roles is a generalised certificate**, at
the exact price `rcost φ (gschedRanks l)`: one block per paid rank, nothing for gates and
free adapters. -/
theorem gcert_of_sched (Φ : 𝓛 → CMat α) (l : List (GSt 𝓛 ρ)) (lab : ρ → 𝓛)
    (h : GSchedOkR (gcalc α) Φ lab l) (e : σ → ρ) (hK : KernelSched Φ lab l e) :
    GCert α e (fun φ => rcost φ (gschedRanks l)) := by
  choose Ψ hΨ using hK.inv
  exact GCert.ofRoute e (fun r => Φ (lab r)) Ψ (fun r => Φ (gschedOut lab l r)) hΨ
    (gschedAct l) _ (gsched_groute_R Φ l lab h) hK.fix hK.ker

/-- the same from an exact route of the generalised engine (for networks that assemble their
route with `GRoute.lift`, `GRoute.parallel`, `GRoute.trans`). -/
theorem gcert_of_groute (e : σ → ρ) (S T : ρ → CMat α) (g : (ρ → ℂ) → (ρ → ℂ))
    (c : (ℕ → ℝ) → ℝ) (h : GRoute S T g c) (hS : ∀ r, ∃ Ψ : CMat α, S r * Ψ = 1)
    (hg : ∀ x : ρ → ℂ, (∀ s, (∀ t, e t ≠ s) → x s = 0) → ∀ t, g x (e t) = x (e t))
    (hT : ∀ t, T (e t) = kernel α * S (e t)) : GCert α e c := by
  choose Ψ hΨ using hS
  exact GCert.ofRoute e S Ψ T hΨ g c h hg hT

end
end
end GF

namespace RAM
open Binary Matrix Ty Finset FoldRate GF CB
universe V

/-- **THE ASSEMBLED THEOREM.**  A legal schedule of the generalised label calculus that is a
kernel on `G * W` live roles, whose block ranks are `G` copies of the block list `U`, gives the
program of the block engine with the time bound `2^k * envelope z k`; the numeric hypothesis
`hnum` is that of `engine_program_group_list`, verbatim. -/
theorem engine_program_gsched {α ρ σ 𝓛 : Type} [Fintype α] [DecidableEq α] [Fintype ρ]
    [DecidableEq ρ] [Fintype σ] [DecidableEq σ]
    (u : ℕ) (hα : Fintype.card α = u) (hu : 3 ≤ u)
    (Φ : 𝓛 → CMat α) (l : List (GSt 𝓛 ρ)) (lab : ρ → 𝓛)
    (h : GSchedOkR (gcalc α) Φ lab l)
    (e : σ → ρ) (he : Function.Injective e) (hK : KernelSched Φ lab l e)
    (G W : ℕ) (hG : 1 ≤ G) (hW : 1 ≤ W) (hσ : Fintype.card σ = G * W)
    (U : List (ℕ × ℕ)) (hc : ∀ φ, rcost φ (gschedRanks l) = (G:ℝ) * listCost φ U)
    (s : ℕ) (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hnum : ((2:ℝ)^s - 1) * BlockAccounting.moment u z U
        + (W:ℝ) * (BlockAccounting.T u z (u - 1) 1 + BlockAccounting.T u z 1 1)
        < (2:ℝ)^s * (W:ℝ))
    (cl : Paint) (m : Bool) {ι : Type V} (k : ι→ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*envelope z (k i)) :=
  engine_program_ggroup_list u hα hu e he G W hG hW hσ _ (gcert_of_sched Φ l lab h e hK)
    U hc s z hz hz1 hnum cl m k v

/-- the same from an exact generalised route (network form). -/
theorem engine_program_groute {α ρ σ : Type} [Fintype α] [DecidableEq α] [Fintype ρ]
    [DecidableEq ρ] [Fintype σ] [DecidableEq σ]
    (u : ℕ) (hα : Fintype.card α = u) (hu : 3 ≤ u)
    (e : σ → ρ) (he : Function.Injective e) (S T : ρ → CMat α) (g : (ρ → ℂ) → (ρ → ℂ))
    (c : (ℕ → ℝ) → ℝ) (h : GRoute S T g c) (hS : ∀ r, ∃ Ψ : CMat α, S r * Ψ = 1)
    (hg : ∀ x : ρ → ℂ, (∀ s, (∀ t, e t ≠ s) → x s = 0) → ∀ t, g x (e t) = x (e t))
    (hT : ∀ t, T (e t) = kernel α * S (e t))
    (G W : ℕ) (hG : 1 ≤ G) (hW : 1 ≤ W) (hσ : Fintype.card σ = G * W)
    (U : List (ℕ × ℕ)) (hc : ∀ φ, c φ = (G:ℝ) * listCost φ U)
    (s : ℕ) (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hnum : ((2:ℝ)^s - 1) * BlockAccounting.moment u z U
        + (W:ℝ) * (BlockAccounting.T u z (u - 1) 1 + BlockAccounting.T u z 1 1)
        < (2:ℝ)^s * (W:ℝ))
    (cl : Paint) (m : Bool) {ι : Type V} (k : ι→ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*envelope z (k i)) :=
  engine_program_ggroup_list u hα hu e he G W hG hW hσ c (gcert_of_groute e S T g c h hS hg hT)
    U hc s z hz hz1 hnum cl m k v

end RAM

namespace BlockWHT
open RAM Binary FoldRate GF CB

/-- **Walsh-Hadamard transform from a legal schedule of the generalised label calculus**:
a program and the time bound `WHTTimeBoundsAt z`, under the unchanged numeric hypothesis. -/
theorem wht_main_of_gsched {α ρ σ 𝓛 : Type} [Fintype α] [DecidableEq α] [Fintype ρ]
    [DecidableEq ρ] [Fintype σ] [DecidableEq σ]
    (u : ℕ) (hα : Fintype.card α = u) (hu : 3 ≤ u)
    (Φ : 𝓛 → CMat α) (l : List (GSt 𝓛 ρ)) (lab : ρ → 𝓛)
    (h : GSchedOkR (gcalc α) Φ lab l)
    (e : σ → ρ) (he : Function.Injective e) (hK : KernelSched Φ lab l e)
    (G W : ℕ) (hG : 1 ≤ G) (hW : 1 ≤ W) (hσ : Fintype.card σ = G * W)
    (U : List (ℕ × ℕ)) (hc : ∀ φ, rcost φ (gschedRanks l) = (G:ℝ) * listCost φ U)
    (s : ℕ) (z : ℝ) (hz : 0 ≤ z) (hz1 : z < 1)
    (hnum : ((2:ℝ)^s - 1) * BlockAccounting.moment u z U
        + (W:ℝ) * (BlockAccounting.T u z (u - 1) 1 + BlockAccounting.T u z 1 1)
        < (2:ℝ)^s * (W:ℝ)) :
    ∃ solve W', WHT.WHTProgram solve W' ∧ WHTTimeBoundsAt z W' :=
  wht_main_of_ggroup_list u hα hu e he G W hG hW hσ _ (gcert_of_sched Φ l lab h e hK)
    U hc s z hz hz1 hnum

end BlockWHT
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.GF.gcert_of_sched
#print axioms OAI.PowerSaving.GF.gcert_of_groute
#print axioms OAI.PowerSaving.RAM.engine_program_gsched
#print axioms OAI.PowerSaving.RAM.engine_program_groute
#print axioms OAI.PowerSaving.BlockWHT.wht_main_of_gsched
