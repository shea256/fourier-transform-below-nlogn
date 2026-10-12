import Work.Bridge401.Gates
import Work.GCert.Chain.Stage

/-!
# (key: bridge-401) Routes of one stage of a run (`GRoute`)

Credits: the entrance gauges and the residual banks are Dugongue's (CrocSwap/integer-mult-bounds PR #401); the bank
patterns are Lydakis's (#275); the compressed nine-stage layout is jacklightChen's (#377); the bridged word B_K is
DaysSky's (#363); B_2, the engine, the stage geometry and the E8 unit are Jacob Sussman's (wht-power-saving-lean,
Apache-2.0).  Written by w-newsums/gen401/gen401.py (from gen377.py).  Copy of `GX.gblift1`, `GX.gblift2` (Work/GCert/Chain/Stage.lean): stage `l` runs on pair `p(l)` of the
run's replica; the slot `q` of the invocation `g` uses the bank `(g, u q)` (`u` injective); the other pairs and the
other banks keep their matrices.
No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace OAI
namespace PowerSaving
namespace GX
open Binary Matrix Finset RAM SS CB RF BR GF
noncomputable section

section Lift
variable {Γ T Sl C α : Type} {nb : ℕ} [Fintype α] [DecidableEq α]
  [Fintype Γ] [DecidableEq Γ] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]

/-- **A route of stage 0 of a run** (pair 1, bank family 0). -/
theorem gbliftQ0 (u : Sl → Fin nb) (hu : Function.Injective u) (O2X O2Y O3X O3Y O4X O4Y : Γ → T → CMat α)
    (ZS ZU : Γ → Fin nb → CMat α)
    {SX SY UX UY : Γ → T → CMat α} {SS US : Γ → Sl → CMat α} {SC UC : Γ → C → CMat α}
    {h : (SRole Γ T Sl C → ℂ) → (SRole Γ T Sl C → ℂ)} {c : (ℕ → ℝ) → ℝ}
    (q : GRoute (mkS SX SY SS SC) (mkS UX UY US UC) h c)
    (hS : ∀ g q, ZS g (u q) = SS g q) (hU : ∀ g q, ZU g (u q) = US g q)
    (hZ : ∀ g b, (∀ q, u q ≠ b) → ZS g b = ZU g b)
    (hh : ∀ y g q, h y (jS (g,q)) = y (jS (g,q))) :
    GRoute (mkR4 SX SY O2X O2Y O3X O3Y O4X O4Y ZS SC) (mkR4 UX UY O2X O2Y O3X O3Y O4X O4Y ZU UC) (liftQ0 u h) c := by
  refine GRoute.lift (emQ0 (Γ := Γ) (T := T) (C := C) u hu) (h := h) ?_
    (fun x => ?_) (fun x i hi => ?_) (fun i hi => ?_)
  · have e1 : mkR4 SX SY O2X O2Y O3X O3Y O4X O4Y ZS SC ∘ (emQ0 (Γ := Γ) (T := T) (C := C) u hu)
        = mkS SX SY SS SC := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · rfl
      · rfl
      · exact hS g q
      · rfl
    have e2 : mkR4 UX UY O2X O2Y O3X O3Y O4X O4Y ZU UC ∘ (emQ0 (Γ := Γ) (T := T) (C := C) u hu)
        = mkS UX UY US UC := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · rfl
      · rfl
      · exact hU g q
      · rfl
    rw [e1, e2]
    exact q
  · funext r
    rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
    · rfl
    · rfl
    · exact (hh (x ∘ emQ0 (Γ := Γ) (T := T) (C := C) u hu) g q).symm
    · rfl
  · rcases i with ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
    · exact absurd ((cover_iff _ _).mpr ⟨jX (g,t), rfl⟩) hi
    · exact absurd ((cover_iff _ _).mpr ⟨jY (g,t), rfl⟩) hi
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact absurd ((cover_iff _ _).mpr ⟨jC (g,c), rfl⟩) hi
  · rcases i with ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
    · exact absurd ((cover_iff _ _).mpr ⟨jX (g,t), rfl⟩) hi
    · exact absurd ((cover_iff _ _).mpr ⟨jY (g,t), rfl⟩) hi
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · by_cases hb : ∃ q, u q = b
      · obtain ⟨q, rfl⟩ := hb
        exact absurd ((cover_iff _ _).mpr ⟨jS (g,q), rfl⟩) hi
      · push_neg at hb
        exact hZ g b hb
    · exact absurd ((cover_iff _ _).mpr ⟨jC (g,c), rfl⟩) hi

/-- **A route of stage 1 of a run** (pair 1, bank family 1). -/
theorem gbliftQ1 (u : Sl → Fin nb) (hu : Function.Injective u) (O2X O2Y O3X O3Y O4X O4Y : Γ → T → CMat α)
    (ZS ZU : Γ → Fin nb → CMat α)
    {SX SY UX UY : Γ → T → CMat α} {SS US : Γ → Sl → CMat α} {SC UC : Γ → C → CMat α}
    {h : (SRole Γ T Sl C → ℂ) → (SRole Γ T Sl C → ℂ)} {c : (ℕ → ℝ) → ℝ}
    (q : GRoute (mkS SX SY SS SC) (mkS UX UY US UC) h c)
    (hS : ∀ g q, ZS g (u q) = SS g q) (hU : ∀ g q, ZU g (u q) = US g q)
    (hZ : ∀ g b, (∀ q, u q ≠ b) → ZS g b = ZU g b)
    (hh : ∀ y g q, h y (jS (g,q)) = y (jS (g,q))) :
    GRoute (mkR4 SX SY O2X O2Y O3X O3Y O4X O4Y ZS SC) (mkR4 UX UY O2X O2Y O3X O3Y O4X O4Y ZU UC) (liftQ1 u h) c := by
  refine GRoute.lift (emQ1 (Γ := Γ) (T := T) (C := C) u hu) (h := h) ?_
    (fun x => ?_) (fun x i hi => ?_) (fun i hi => ?_)
  · have e1 : mkR4 SX SY O2X O2Y O3X O3Y O4X O4Y ZS SC ∘ (emQ1 (Γ := Γ) (T := T) (C := C) u hu)
        = mkS SX SY SS SC := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · rfl
      · rfl
      · exact hS g q
      · rfl
    have e2 : mkR4 UX UY O2X O2Y O3X O3Y O4X O4Y ZU UC ∘ (emQ1 (Γ := Γ) (T := T) (C := C) u hu)
        = mkS UX UY US UC := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · rfl
      · rfl
      · exact hU g q
      · rfl
    rw [e1, e2]
    exact q
  · funext r
    rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
    · rfl
    · rfl
    · exact (hh (x ∘ emQ1 (Γ := Γ) (T := T) (C := C) u hu) g q).symm
    · rfl
  · rcases i with ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
    · exact absurd ((cover_iff _ _).mpr ⟨jX (g,t), rfl⟩) hi
    · exact absurd ((cover_iff _ _).mpr ⟨jY (g,t), rfl⟩) hi
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact absurd ((cover_iff _ _).mpr ⟨jC (g,c), rfl⟩) hi
  · rcases i with ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
    · exact absurd ((cover_iff _ _).mpr ⟨jX (g,t), rfl⟩) hi
    · exact absurd ((cover_iff _ _).mpr ⟨jY (g,t), rfl⟩) hi
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · by_cases hb : ∃ q, u q = b
      · obtain ⟨q, rfl⟩ := hb
        exact absurd ((cover_iff _ _).mpr ⟨jS (g,q), rfl⟩) hi
      · push_neg at hb
        exact hZ g b hb
    · exact absurd ((cover_iff _ _).mpr ⟨jC (g,c), rfl⟩) hi

/-- **A route of stage 2 of a run** (pair 1, bank family 2). -/
theorem gbliftQ2 (u : Sl → Fin nb) (hu : Function.Injective u) (O2X O2Y O3X O3Y O4X O4Y : Γ → T → CMat α)
    (ZS ZU : Γ → Fin nb → CMat α)
    {SX SY UX UY : Γ → T → CMat α} {SS US : Γ → Sl → CMat α} {SC UC : Γ → C → CMat α}
    {h : (SRole Γ T Sl C → ℂ) → (SRole Γ T Sl C → ℂ)} {c : (ℕ → ℝ) → ℝ}
    (q : GRoute (mkS SX SY SS SC) (mkS UX UY US UC) h c)
    (hS : ∀ g q, ZS g (u q) = SS g q) (hU : ∀ g q, ZU g (u q) = US g q)
    (hZ : ∀ g b, (∀ q, u q ≠ b) → ZS g b = ZU g b)
    (hh : ∀ y g q, h y (jS (g,q)) = y (jS (g,q))) :
    GRoute (mkR4 SX SY O2X O2Y O3X O3Y O4X O4Y ZS SC) (mkR4 UX UY O2X O2Y O3X O3Y O4X O4Y ZU UC) (liftQ2 u h) c := by
  refine GRoute.lift (emQ2 (Γ := Γ) (T := T) (C := C) u hu) (h := h) ?_
    (fun x => ?_) (fun x i hi => ?_) (fun i hi => ?_)
  · have e1 : mkR4 SX SY O2X O2Y O3X O3Y O4X O4Y ZS SC ∘ (emQ2 (Γ := Γ) (T := T) (C := C) u hu)
        = mkS SX SY SS SC := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · rfl
      · rfl
      · exact hS g q
      · rfl
    have e2 : mkR4 UX UY O2X O2Y O3X O3Y O4X O4Y ZU UC ∘ (emQ2 (Γ := Γ) (T := T) (C := C) u hu)
        = mkS UX UY US UC := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · rfl
      · rfl
      · exact hU g q
      · rfl
    rw [e1, e2]
    exact q
  · funext r
    rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
    · rfl
    · rfl
    · exact (hh (x ∘ emQ2 (Γ := Γ) (T := T) (C := C) u hu) g q).symm
    · rfl
  · rcases i with ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
    · exact absurd ((cover_iff _ _).mpr ⟨jX (g,t), rfl⟩) hi
    · exact absurd ((cover_iff _ _).mpr ⟨jY (g,t), rfl⟩) hi
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact absurd ((cover_iff _ _).mpr ⟨jC (g,c), rfl⟩) hi
  · rcases i with ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
    · exact absurd ((cover_iff _ _).mpr ⟨jX (g,t), rfl⟩) hi
    · exact absurd ((cover_iff _ _).mpr ⟨jY (g,t), rfl⟩) hi
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · by_cases hb : ∃ q, u q = b
      · obtain ⟨q, rfl⟩ := hb
        exact absurd ((cover_iff _ _).mpr ⟨jS (g,q), rfl⟩) hi
      · push_neg at hb
        exact hZ g b hb
    · exact absurd ((cover_iff _ _).mpr ⟨jC (g,c), rfl⟩) hi

/-- **A route of stage 3 of a run** (pair 2, bank family 3). -/
theorem gbliftQ3 (u : Sl → Fin nb) (hu : Function.Injective u) (O1X O1Y O3X O3Y O4X O4Y : Γ → T → CMat α)
    (ZS ZU : Γ → Fin nb → CMat α)
    {SX SY UX UY : Γ → T → CMat α} {SS US : Γ → Sl → CMat α} {SC UC : Γ → C → CMat α}
    {h : (SRole Γ T Sl C → ℂ) → (SRole Γ T Sl C → ℂ)} {c : (ℕ → ℝ) → ℝ}
    (q : GRoute (mkS SX SY SS SC) (mkS UX UY US UC) h c)
    (hS : ∀ g q, ZS g (u q) = SS g q) (hU : ∀ g q, ZU g (u q) = US g q)
    (hZ : ∀ g b, (∀ q, u q ≠ b) → ZS g b = ZU g b)
    (hh : ∀ y g q, h y (jS (g,q)) = y (jS (g,q))) :
    GRoute (mkR4 O1X O1Y SX SY O3X O3Y O4X O4Y ZS SC) (mkR4 O1X O1Y UX UY O3X O3Y O4X O4Y ZU UC) (liftQ3 u h) c := by
  refine GRoute.lift (emQ3 (Γ := Γ) (T := T) (C := C) u hu) (h := h) ?_
    (fun x => ?_) (fun x i hi => ?_) (fun i hi => ?_)
  · have e1 : mkR4 O1X O1Y SX SY O3X O3Y O4X O4Y ZS SC ∘ (emQ3 (Γ := Γ) (T := T) (C := C) u hu)
        = mkS SX SY SS SC := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · rfl
      · rfl
      · exact hS g q
      · rfl
    have e2 : mkR4 O1X O1Y UX UY O3X O3Y O4X O4Y ZU UC ∘ (emQ3 (Γ := Γ) (T := T) (C := C) u hu)
        = mkS UX UY US UC := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · rfl
      · rfl
      · exact hU g q
      · rfl
    rw [e1, e2]
    exact q
  · funext r
    rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
    · rfl
    · rfl
    · exact (hh (x ∘ emQ3 (Γ := Γ) (T := T) (C := C) u hu) g q).symm
    · rfl
  · rcases i with ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
    · rfl
    · rfl
    · exact absurd ((cover_iff _ _).mpr ⟨jX (g,t), rfl⟩) hi
    · exact absurd ((cover_iff _ _).mpr ⟨jY (g,t), rfl⟩) hi
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact absurd ((cover_iff _ _).mpr ⟨jC (g,c), rfl⟩) hi
  · rcases i with ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
    · rfl
    · rfl
    · exact absurd ((cover_iff _ _).mpr ⟨jX (g,t), rfl⟩) hi
    · exact absurd ((cover_iff _ _).mpr ⟨jY (g,t), rfl⟩) hi
    · rfl
    · rfl
    · rfl
    · rfl
    · by_cases hb : ∃ q, u q = b
      · obtain ⟨q, rfl⟩ := hb
        exact absurd ((cover_iff _ _).mpr ⟨jS (g,q), rfl⟩) hi
      · push_neg at hb
        exact hZ g b hb
    · exact absurd ((cover_iff _ _).mpr ⟨jC (g,c), rfl⟩) hi

/-- **A route of stage 4 of a run** (pair 2, bank family 4). -/
theorem gbliftQ4 (u : Sl → Fin nb) (hu : Function.Injective u) (O1X O1Y O3X O3Y O4X O4Y : Γ → T → CMat α)
    (ZS ZU : Γ → Fin nb → CMat α)
    {SX SY UX UY : Γ → T → CMat α} {SS US : Γ → Sl → CMat α} {SC UC : Γ → C → CMat α}
    {h : (SRole Γ T Sl C → ℂ) → (SRole Γ T Sl C → ℂ)} {c : (ℕ → ℝ) → ℝ}
    (q : GRoute (mkS SX SY SS SC) (mkS UX UY US UC) h c)
    (hS : ∀ g q, ZS g (u q) = SS g q) (hU : ∀ g q, ZU g (u q) = US g q)
    (hZ : ∀ g b, (∀ q, u q ≠ b) → ZS g b = ZU g b)
    (hh : ∀ y g q, h y (jS (g,q)) = y (jS (g,q))) :
    GRoute (mkR4 O1X O1Y SX SY O3X O3Y O4X O4Y ZS SC) (mkR4 O1X O1Y UX UY O3X O3Y O4X O4Y ZU UC) (liftQ4 u h) c := by
  refine GRoute.lift (emQ4 (Γ := Γ) (T := T) (C := C) u hu) (h := h) ?_
    (fun x => ?_) (fun x i hi => ?_) (fun i hi => ?_)
  · have e1 : mkR4 O1X O1Y SX SY O3X O3Y O4X O4Y ZS SC ∘ (emQ4 (Γ := Γ) (T := T) (C := C) u hu)
        = mkS SX SY SS SC := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · rfl
      · rfl
      · exact hS g q
      · rfl
    have e2 : mkR4 O1X O1Y UX UY O3X O3Y O4X O4Y ZU UC ∘ (emQ4 (Γ := Γ) (T := T) (C := C) u hu)
        = mkS UX UY US UC := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · rfl
      · rfl
      · exact hU g q
      · rfl
    rw [e1, e2]
    exact q
  · funext r
    rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
    · rfl
    · rfl
    · exact (hh (x ∘ emQ4 (Γ := Γ) (T := T) (C := C) u hu) g q).symm
    · rfl
  · rcases i with ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
    · rfl
    · rfl
    · exact absurd ((cover_iff _ _).mpr ⟨jX (g,t), rfl⟩) hi
    · exact absurd ((cover_iff _ _).mpr ⟨jY (g,t), rfl⟩) hi
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact absurd ((cover_iff _ _).mpr ⟨jC (g,c), rfl⟩) hi
  · rcases i with ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
    · rfl
    · rfl
    · exact absurd ((cover_iff _ _).mpr ⟨jX (g,t), rfl⟩) hi
    · exact absurd ((cover_iff _ _).mpr ⟨jY (g,t), rfl⟩) hi
    · rfl
    · rfl
    · rfl
    · rfl
    · by_cases hb : ∃ q, u q = b
      · obtain ⟨q, rfl⟩ := hb
        exact absurd ((cover_iff _ _).mpr ⟨jS (g,q), rfl⟩) hi
      · push_neg at hb
        exact hZ g b hb
    · exact absurd ((cover_iff _ _).mpr ⟨jC (g,c), rfl⟩) hi

/-- **A route of stage 5 of a run** (pair 3, bank family 5). -/
theorem gbliftQ5 (u : Sl → Fin nb) (hu : Function.Injective u) (O1X O1Y O2X O2Y O4X O4Y : Γ → T → CMat α)
    (ZS ZU : Γ → Fin nb → CMat α)
    {SX SY UX UY : Γ → T → CMat α} {SS US : Γ → Sl → CMat α} {SC UC : Γ → C → CMat α}
    {h : (SRole Γ T Sl C → ℂ) → (SRole Γ T Sl C → ℂ)} {c : (ℕ → ℝ) → ℝ}
    (q : GRoute (mkS SX SY SS SC) (mkS UX UY US UC) h c)
    (hS : ∀ g q, ZS g (u q) = SS g q) (hU : ∀ g q, ZU g (u q) = US g q)
    (hZ : ∀ g b, (∀ q, u q ≠ b) → ZS g b = ZU g b)
    (hh : ∀ y g q, h y (jS (g,q)) = y (jS (g,q))) :
    GRoute (mkR4 O1X O1Y O2X O2Y SX SY O4X O4Y ZS SC) (mkR4 O1X O1Y O2X O2Y UX UY O4X O4Y ZU UC) (liftQ5 u h) c := by
  refine GRoute.lift (emQ5 (Γ := Γ) (T := T) (C := C) u hu) (h := h) ?_
    (fun x => ?_) (fun x i hi => ?_) (fun i hi => ?_)
  · have e1 : mkR4 O1X O1Y O2X O2Y SX SY O4X O4Y ZS SC ∘ (emQ5 (Γ := Γ) (T := T) (C := C) u hu)
        = mkS SX SY SS SC := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · rfl
      · rfl
      · exact hS g q
      · rfl
    have e2 : mkR4 O1X O1Y O2X O2Y UX UY O4X O4Y ZU UC ∘ (emQ5 (Γ := Γ) (T := T) (C := C) u hu)
        = mkS UX UY US UC := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · rfl
      · rfl
      · exact hU g q
      · rfl
    rw [e1, e2]
    exact q
  · funext r
    rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
    · rfl
    · rfl
    · exact (hh (x ∘ emQ5 (Γ := Γ) (T := T) (C := C) u hu) g q).symm
    · rfl
  · rcases i with ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
    · rfl
    · rfl
    · rfl
    · rfl
    · exact absurd ((cover_iff _ _).mpr ⟨jX (g,t), rfl⟩) hi
    · exact absurd ((cover_iff _ _).mpr ⟨jY (g,t), rfl⟩) hi
    · rfl
    · rfl
    · rfl
    · exact absurd ((cover_iff _ _).mpr ⟨jC (g,c), rfl⟩) hi
  · rcases i with ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
    · rfl
    · rfl
    · rfl
    · rfl
    · exact absurd ((cover_iff _ _).mpr ⟨jX (g,t), rfl⟩) hi
    · exact absurd ((cover_iff _ _).mpr ⟨jY (g,t), rfl⟩) hi
    · rfl
    · rfl
    · by_cases hb : ∃ q, u q = b
      · obtain ⟨q, rfl⟩ := hb
        exact absurd ((cover_iff _ _).mpr ⟨jS (g,q), rfl⟩) hi
      · push_neg at hb
        exact hZ g b hb
    · exact absurd ((cover_iff _ _).mpr ⟨jC (g,c), rfl⟩) hi

/-- **A route of stage 6 of a run** (pair 3, bank family 6). -/
theorem gbliftQ6 (u : Sl → Fin nb) (hu : Function.Injective u) (O1X O1Y O2X O2Y O4X O4Y : Γ → T → CMat α)
    (ZS ZU : Γ → Fin nb → CMat α)
    {SX SY UX UY : Γ → T → CMat α} {SS US : Γ → Sl → CMat α} {SC UC : Γ → C → CMat α}
    {h : (SRole Γ T Sl C → ℂ) → (SRole Γ T Sl C → ℂ)} {c : (ℕ → ℝ) → ℝ}
    (q : GRoute (mkS SX SY SS SC) (mkS UX UY US UC) h c)
    (hS : ∀ g q, ZS g (u q) = SS g q) (hU : ∀ g q, ZU g (u q) = US g q)
    (hZ : ∀ g b, (∀ q, u q ≠ b) → ZS g b = ZU g b)
    (hh : ∀ y g q, h y (jS (g,q)) = y (jS (g,q))) :
    GRoute (mkR4 O1X O1Y O2X O2Y SX SY O4X O4Y ZS SC) (mkR4 O1X O1Y O2X O2Y UX UY O4X O4Y ZU UC) (liftQ6 u h) c := by
  refine GRoute.lift (emQ6 (Γ := Γ) (T := T) (C := C) u hu) (h := h) ?_
    (fun x => ?_) (fun x i hi => ?_) (fun i hi => ?_)
  · have e1 : mkR4 O1X O1Y O2X O2Y SX SY O4X O4Y ZS SC ∘ (emQ6 (Γ := Γ) (T := T) (C := C) u hu)
        = mkS SX SY SS SC := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · rfl
      · rfl
      · exact hS g q
      · rfl
    have e2 : mkR4 O1X O1Y O2X O2Y UX UY O4X O4Y ZU UC ∘ (emQ6 (Γ := Γ) (T := T) (C := C) u hu)
        = mkS UX UY US UC := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · rfl
      · rfl
      · exact hU g q
      · rfl
    rw [e1, e2]
    exact q
  · funext r
    rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
    · rfl
    · rfl
    · exact (hh (x ∘ emQ6 (Γ := Γ) (T := T) (C := C) u hu) g q).symm
    · rfl
  · rcases i with ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
    · rfl
    · rfl
    · rfl
    · rfl
    · exact absurd ((cover_iff _ _).mpr ⟨jX (g,t), rfl⟩) hi
    · exact absurd ((cover_iff _ _).mpr ⟨jY (g,t), rfl⟩) hi
    · rfl
    · rfl
    · rfl
    · exact absurd ((cover_iff _ _).mpr ⟨jC (g,c), rfl⟩) hi
  · rcases i with ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
    · rfl
    · rfl
    · rfl
    · rfl
    · exact absurd ((cover_iff _ _).mpr ⟨jX (g,t), rfl⟩) hi
    · exact absurd ((cover_iff _ _).mpr ⟨jY (g,t), rfl⟩) hi
    · rfl
    · rfl
    · by_cases hb : ∃ q, u q = b
      · obtain ⟨q, rfl⟩ := hb
        exact absurd ((cover_iff _ _).mpr ⟨jS (g,q), rfl⟩) hi
      · push_neg at hb
        exact hZ g b hb
    · exact absurd ((cover_iff _ _).mpr ⟨jC (g,c), rfl⟩) hi

/-- **A route of stage 7 of a run** (pair 4, bank family 7). -/
theorem gbliftQ7 (u : Sl → Fin nb) (hu : Function.Injective u) (O1X O1Y O2X O2Y O3X O3Y : Γ → T → CMat α)
    (ZS ZU : Γ → Fin nb → CMat α)
    {SX SY UX UY : Γ → T → CMat α} {SS US : Γ → Sl → CMat α} {SC UC : Γ → C → CMat α}
    {h : (SRole Γ T Sl C → ℂ) → (SRole Γ T Sl C → ℂ)} {c : (ℕ → ℝ) → ℝ}
    (q : GRoute (mkS SX SY SS SC) (mkS UX UY US UC) h c)
    (hS : ∀ g q, ZS g (u q) = SS g q) (hU : ∀ g q, ZU g (u q) = US g q)
    (hZ : ∀ g b, (∀ q, u q ≠ b) → ZS g b = ZU g b)
    (hh : ∀ y g q, h y (jS (g,q)) = y (jS (g,q))) :
    GRoute (mkR4 O1X O1Y O2X O2Y O3X O3Y SX SY ZS SC) (mkR4 O1X O1Y O2X O2Y O3X O3Y UX UY ZU UC) (liftQ7 u h) c := by
  refine GRoute.lift (emQ7 (Γ := Γ) (T := T) (C := C) u hu) (h := h) ?_
    (fun x => ?_) (fun x i hi => ?_) (fun i hi => ?_)
  · have e1 : mkR4 O1X O1Y O2X O2Y O3X O3Y SX SY ZS SC ∘ (emQ7 (Γ := Γ) (T := T) (C := C) u hu)
        = mkS SX SY SS SC := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · rfl
      · rfl
      · exact hS g q
      · rfl
    have e2 : mkR4 O1X O1Y O2X O2Y O3X O3Y UX UY ZU UC ∘ (emQ7 (Γ := Γ) (T := T) (C := C) u hu)
        = mkS UX UY US UC := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · rfl
      · rfl
      · exact hU g q
      · rfl
    rw [e1, e2]
    exact q
  · funext r
    rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
    · rfl
    · rfl
    · exact (hh (x ∘ emQ7 (Γ := Γ) (T := T) (C := C) u hu) g q).symm
    · rfl
  · rcases i with ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact absurd ((cover_iff _ _).mpr ⟨jX (g,t), rfl⟩) hi
    · exact absurd ((cover_iff _ _).mpr ⟨jY (g,t), rfl⟩) hi
    · rfl
    · exact absurd ((cover_iff _ _).mpr ⟨jC (g,c), rfl⟩) hi
  · rcases i with ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact absurd ((cover_iff _ _).mpr ⟨jX (g,t), rfl⟩) hi
    · exact absurd ((cover_iff _ _).mpr ⟨jY (g,t), rfl⟩) hi
    · by_cases hb : ∃ q, u q = b
      · obtain ⟨q, rfl⟩ := hb
        exact absurd ((cover_iff _ _).mpr ⟨jS (g,q), rfl⟩) hi
      · push_neg at hb
        exact hZ g b hb
    · exact absurd ((cover_iff _ _).mpr ⟨jC (g,c), rfl⟩) hi

/-- **A route of stage 8 of a run** (pair 4, bank family 8). -/
theorem gbliftQ8 (u : Sl → Fin nb) (hu : Function.Injective u) (O1X O1Y O2X O2Y O3X O3Y : Γ → T → CMat α)
    (ZS ZU : Γ → Fin nb → CMat α)
    {SX SY UX UY : Γ → T → CMat α} {SS US : Γ → Sl → CMat α} {SC UC : Γ → C → CMat α}
    {h : (SRole Γ T Sl C → ℂ) → (SRole Γ T Sl C → ℂ)} {c : (ℕ → ℝ) → ℝ}
    (q : GRoute (mkS SX SY SS SC) (mkS UX UY US UC) h c)
    (hS : ∀ g q, ZS g (u q) = SS g q) (hU : ∀ g q, ZU g (u q) = US g q)
    (hZ : ∀ g b, (∀ q, u q ≠ b) → ZS g b = ZU g b)
    (hh : ∀ y g q, h y (jS (g,q)) = y (jS (g,q))) :
    GRoute (mkR4 O1X O1Y O2X O2Y O3X O3Y SX SY ZS SC) (mkR4 O1X O1Y O2X O2Y O3X O3Y UX UY ZU UC) (liftQ8 u h) c := by
  refine GRoute.lift (emQ8 (Γ := Γ) (T := T) (C := C) u hu) (h := h) ?_
    (fun x => ?_) (fun x i hi => ?_) (fun i hi => ?_)
  · have e1 : mkR4 O1X O1Y O2X O2Y O3X O3Y SX SY ZS SC ∘ (emQ8 (Γ := Γ) (T := T) (C := C) u hu)
        = mkS SX SY SS SC := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · rfl
      · rfl
      · exact hS g q
      · rfl
    have e2 : mkR4 O1X O1Y O2X O2Y O3X O3Y UX UY ZU UC ∘ (emQ8 (Γ := Γ) (T := T) (C := C) u hu)
        = mkS UX UY US UC := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · rfl
      · rfl
      · exact hU g q
      · rfl
    rw [e1, e2]
    exact q
  · funext r
    rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
    · rfl
    · rfl
    · exact (hh (x ∘ emQ8 (Γ := Γ) (T := T) (C := C) u hu) g q).symm
    · rfl
  · rcases i with ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact absurd ((cover_iff _ _).mpr ⟨jX (g,t), rfl⟩) hi
    · exact absurd ((cover_iff _ _).mpr ⟨jY (g,t), rfl⟩) hi
    · rfl
    · exact absurd ((cover_iff _ _).mpr ⟨jC (g,c), rfl⟩) hi
  · rcases i with ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact absurd ((cover_iff _ _).mpr ⟨jX (g,t), rfl⟩) hi
    · exact absurd ((cover_iff _ _).mpr ⟨jY (g,t), rfl⟩) hi
    · by_cases hb : ∃ q, u q = b
      · obtain ⟨q, rfl⟩ := hb
        exact absurd ((cover_iff _ _).mpr ⟨jS (g,q), rfl⟩) hi
      · push_neg at hb
        exact hZ g b hb
    · exact absurd ((cover_iff _ _).mpr ⟨jC (g,c), rfl⟩) hi

end Lift
end
end GX
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.GX.gbliftQ0
#print axioms OAI.PowerSaving.GX.gbliftQ1
#print axioms OAI.PowerSaving.GX.gbliftQ2
#print axioms OAI.PowerSaving.GX.gbliftQ3
#print axioms OAI.PowerSaving.GX.gbliftQ4
#print axioms OAI.PowerSaving.GX.gbliftQ5
#print axioms OAI.PowerSaving.GX.gbliftQ6
#print axioms OAI.PowerSaving.GX.gbliftQ7
#print axioms OAI.PowerSaving.GX.gbliftQ8
