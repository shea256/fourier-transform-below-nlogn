import Work.Bridge401.GNetDef

/-!
# (key: bridge-401) The stages, idle climbs and gate layers of one run of the compressed nine-stage word

Credits: the entrance gauges and the residual banks are Dugongue's (CrocSwap/integer-mult-bounds PR #401); the bank
patterns are Lydakis's (#275); the compressed nine-stage layout is jacklightChen's (#377); the bridged word B_K is
DaysSky's (#363); B_2, the engine, the stage geometry and the E8 unit are Jacob Sussman's (wht-power-saving-lean,
Apache-2.0).  Written by w-newsums/gen401/gen401.py (from gen377.py).  Copy of Work/GCert/Chain/NetStage.lean (via genk), generic in the run `ρ`.  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace OAI
namespace PowerSaving
namespace GX
open Binary Matrix Finset RAM SS CB RF BR GF
noncomputable section

section Net
variable {H T Sl C α Γ : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] [Fintype α] [DecidableEq α]
  [Fintype Γ] [DecidableEq Γ]
variable {nb : ℕ} (N : G401 H T Sl C α Γ nb)

/-- the free bank adapters before stage 0 of run `ρ` (`bank_adapt`): every bank from `Zb` to `Zp`. -/
lemma G401.adapt0 (ρ : Fin 8) :
    GRoute (N.S0 ρ) (N.S1 ρ) id (fun _ => 0) := by
  have H1 := GRoute.reach_all (N.S0 ρ) (N.S1 ρ) (fun _ _ => 0) (by
      rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact N.hP0 ρ g b
      · exact GReach.refl _)
  exact H1.cast (fun φ => by simp)

/-- stage 0 of run `ρ`: forward on pair 1; the slot `q` of `g` on the bank `(g, use ρ 0 q)`. -/
lemma G401.stage0 (ρ : Fin 8) :
    GRoute (N.S1 ρ) (N.S2 ρ) (liftQ0 (Γ := Γ) (T := T) (C := C) (N.use ρ 0) GF)
      (fun φ => (Fintype.card Γ : ℝ) * N.I.cost φ) := by
  have h := gistageE_fwd N.I (bid Γ T) N.G0 N.N0 N.Wn0 N.hN0 N.hW0
    (fun g q => N.Zp (9 * ρ.val + 0) g (N.use ρ 0 q)) (cOne Γ C α) (cOne Γ C α)
  have h' : GRoute (bIn N.I.tv (bid Γ T) (fun d => (N.G0 d).Xm)
        (fun g q => N.Zp (9 * ρ.val + 0) g (N.use ρ 0 q)) (cOne Γ C α))
      (mkS N.xi1 N.yi1 (fun g q => N.Zb (9 * ρ.val + 1) g (N.use ρ 0 q)) (cOne Γ C α)) GF
      (fun φ => (Fintype.card Γ : ℝ) * N.I.cost φ) := by
    have e : bOut N.I.tv (bid Γ T) (fun d => (N.G0 d).Xm)
        (fun g q => N.Wn0 g q * N.Zp (9 * ρ.val + 0) g (N.use ρ 0 q)) (cOne Γ C α)
        = mkS N.xi1 N.yi1 (fun g q => N.Zb (9 * ρ.val + 1) g (N.use ρ 0 q)) (cOne Γ C α) := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · exact N.x01 g t
      · exact N.y01 g t
      · exact N.hZ0 ρ g q
      · rfl
    rw [← e]
    exact h
  exact gbliftQ0 (N.use ρ 0) (N.hinj ρ 0) N.xi0 N.yi0 N.xi0 N.yi0 N.xi0 N.yi0 (fun g b => N.Zp (9 * ρ.val + 0) g b)
    (fun g b => N.Zb (9 * ρ.val + 1) g b) h'
    (fun g q => rfl) (fun g q => rfl) (fun g b hb => (N.hZn0 ρ g b hb).symm) (fun _ _ _ => rfl)

/-- the free bank adapters before stage 1 of run `ρ` (`bank_adapt`): every bank from `Zb` to `Zp`. -/
lemma G401.adapt1 (ρ : Fin 8) :
    GRoute (N.S2 ρ) (N.S3 ρ) id (fun _ => 0) := by
  have H1 := GRoute.reach_all (N.S2 ρ) (N.S3 ρ) (fun _ _ => 0) (by
      rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact N.hP1 ρ g b
      · exact GReach.refl _)
  exact H1.cast (fun φ => by simp)

/-- stage 1 of run `ρ`: backward on pair 1; the slot `q` of `g` on the bank `(g, use ρ 1 q)`. -/
lemma G401.stage1 (ρ : Fin 8) :
    GRoute (N.S3 ρ) (N.S4 ρ) (liftQ1 (Γ := Γ) (T := T) (C := C) (N.use ρ 1) GB)
      (fun φ => (Fintype.card Γ : ℝ) * N.I.cost φ) := by
  have h := gistageE_bwd N.I N.r1 N.G1 N.N1 N.Wn1 N.hN1 N.hW1
    (fun g q => N.Zp (9 * ρ.val + 1) g (N.use ρ 1 q)) (cOne Γ C α) (cOne Γ C α)
  have h' : GRoute (bIn N.I.tv N.r1 (fun d => (N.G1 d).Xm)
        (fun g q => N.Zp (9 * ρ.val + 1) g (N.use ρ 1 q)) (cOne Γ C α))
      (mkS N.xi2 N.yi2 (fun g q => N.Zb (9 * ρ.val + 2) g (N.use ρ 1 q)) (cOne Γ C α)) GB
      (fun φ => (Fintype.card Γ : ℝ) * N.I.cost φ) := by
    have e : bOut N.I.tv N.r1 (fun d => (N.G1 d).Xm)
        (fun g q => N.Wn1 g q * N.Zp (9 * ρ.val + 1) g (N.use ρ 1 q)) (cOne Γ C α)
        = mkS N.xi2 N.yi2 (fun g q => N.Zb (9 * ρ.val + 2) g (N.use ρ 1 q)) (cOne Γ C α) := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · exact N.x12 g t
      · exact N.y12 g t
      · exact N.hZ1 ρ g q
      · rfl
    rw [← e]
    exact h
  exact gbliftQ1 (N.use ρ 1) (N.hinj ρ 1) N.xi0 N.yi0 N.xi0 N.yi0 N.xi0 N.yi0 (fun g b => N.Zp (9 * ρ.val + 1) g b)
    (fun g b => N.Zb (9 * ρ.val + 2) g b) h'
    (fun g q => rfl) (fun g q => rfl) (fun g b hb => (N.hZn1 ρ g b hb).symm) (fun _ _ _ => rfl)

/-- first idle climb of pair 2 (ONE block per role), to the frames of pair 1 after stage 1. -/
lemma G401.climbA2 (ρ : Fin 8) :
    XRoute (N.S4 ρ) (N.S5 ρ) id (fun φ => (Fintype.card Γ : ℝ) *
      ((Fintype.card T : ℝ) * (N.caX2 φ + N.caY2 φ))) := by
  have H1 := XRoute.reach_all (N.S4 ρ) (N.S5 ρ)
    (mkR4 (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ => N.caX2) (fun _ _ => N.caY2) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)) (by
      rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
      · exact XReach.refl _
      · exact XReach.refl _
      · show XReach ((N.G0 g).Xm.Φ (tt (N.I.tv t))) ((N.G2 (N.r2 t g)).Xm.Φ (tt (N.I.tv t))) N.caX2
        rw [← N.x12 g t]
        exact N.aX2 g t
      · show XReach ((N.G0 g).Xm.Φ 0) ((N.G2 (N.r2 t g)).Xm.Φ 0) N.caY2
        rw [← N.y12 g t]
        exact N.aY2 g t
      · exact XReach.refl _
      · exact XReach.refl _
      · exact XReach.refl _
      · exact XReach.refl _
      · exact XReach.refl _
      · exact XReach.refl _)
  refine H1.cast (fun φ => ?_)
  simp_rw [mkR4_map (fun c : (ℕ → ℝ) → ℝ => c φ)]
  rw [sum_mkR4]
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_zero, add_zero, zero_add]
  ring

/-- gate layer A of pair 2 in run `ρ`: twins have equal frames. -/
lemma G401.gateA2 (ρ : Fin 8) : XRoute (N.S5 ρ) (N.S5 ρ) (gscQ pABQ_2 kAQ_2) (fun _ => 0) := by
  refine gateP pABQ_2 kAQ_2 (N.S5 ρ) ?_
  rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩) hk
  · rfl
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · rfl
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim

/-- the free bank adapters before stage 2 of run `ρ` (`bank_adapt`): every bank from `Zb` to `Zp`. -/
lemma G401.adapt2 (ρ : Fin 8) :
    GRoute (N.S5 ρ) (N.S6 ρ) id (fun _ => 0) := by
  have H1 := GRoute.reach_all (N.S5 ρ) (N.S6 ρ) (fun _ _ => 0) (by
      rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact N.hP2 ρ g b
      · exact GReach.refl _)
  exact H1.cast (fun φ => by simp)

/-- stage 2 of run `ρ`: forward on pair 1; the slot `q` of `g` on the bank `(g, use ρ 2 q)`. -/
lemma G401.stage2 (ρ : Fin 8) :
    GRoute (N.S6 ρ) (N.S7 ρ) (liftQ2 (Γ := Γ) (T := T) (C := C) (N.use ρ 2) GF)
      (fun φ => (Fintype.card Γ : ℝ) * N.I.cost φ) := by
  have h := gistageE_fwd N.I N.r2 N.G2 N.N2 N.Wn2 N.hN2 N.hW2
    (fun g q => N.Zp (9 * ρ.val + 2) g (N.use ρ 2 q)) (cOne Γ C α) (cOne Γ C α)
  have h' : GRoute (bIn N.I.tv N.r2 (fun d => (N.G2 d).Xm)
        (fun g q => N.Zp (9 * ρ.val + 2) g (N.use ρ 2 q)) (cOne Γ C α))
      (mkS N.xo2 N.yo2 (fun g q => N.Zb (9 * ρ.val + 3) g (N.use ρ 2 q)) (cOne Γ C α)) GF
      (fun φ => (Fintype.card Γ : ℝ) * N.I.cost φ) := by
    have e : bOut N.I.tv N.r2 (fun d => (N.G2 d).Xm)
        (fun g q => N.Wn2 g q * N.Zp (9 * ρ.val + 2) g (N.use ρ 2 q)) (cOne Γ C α)
        = mkS N.xo2 N.yo2 (fun g q => N.Zb (9 * ρ.val + 3) g (N.use ρ 2 q)) (cOne Γ C α) := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · rfl
      · rfl
      · exact N.hZ2 ρ g q
      · rfl
    rw [← e]
    exact h
  exact gbliftQ2 (N.use ρ 2) (N.hinj ρ 2) N.xi2 N.yi2 N.xi0 N.yi0 N.xi0 N.yi0 (fun g b => N.Zp (9 * ρ.val + 2) g b)
    (fun g b => N.Zb (9 * ρ.val + 3) g b) h'
    (fun g q => rfl) (fun g q => rfl) (fun g b hb => (N.hZn2 ρ g b hb).symm) (fun _ _ _ => rfl)

/-- second idle climb of pair 2: the window of stage 2, ONE block of rank `card H - 1` per role. -/
lemma G401.climbB2 (ρ : Fin 8) :
    XRoute (N.S7 ρ) (N.S8 ρ) id (fun φ => (Fintype.card Γ : ℝ) *
      ((Fintype.card T : ℝ) * (2 * bcost φ (Fintype.card H - 1)))) := by
  have H1 := XRoute.reach_all (N.S7 ρ) (N.S8 ρ)
    (mkR4 (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ => (fun φ => bcost φ (Fintype.card H - 1))) (fun _ _ => (fun φ => bcost φ (Fintype.card H - 1))) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)) (by
      rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
      · exact XReach.refl _
      · exact XReach.refl _
      · show XReach ((N.G2 (N.r2 t g)).Xm.Φ (tt (N.I.tv t))) ((N.G3 (N.r3 t g)).Xm.Φ (tt (N.I.tv t)))
          (fun φ => bcost φ (Fintype.card H - 1))
        rw [← N.x23 g t]
        exact GInvE.climbX N.I (N.G2 (N.r2 t g)).Xm t
      · show XReach ((N.G2 (N.r2 t g)).Xm.Φ 0) ((N.G3 (N.r3 t g)).Xm.Φ 0)
          (fun φ => bcost φ (Fintype.card H - 1))
        rw [← N.y23 g t]
        exact GInvE.climbY N.I (N.G2 (N.r2 t g)).Xm t
      · exact XReach.refl _
      · exact XReach.refl _
      · exact XReach.refl _
      · exact XReach.refl _
      · exact XReach.refl _
      · exact XReach.refl _)
  refine H1.cast (fun φ => ?_)
  simp_rw [mkR4_map (fun c : (ℕ → ℝ) → ℝ => c φ)]
  rw [sum_mkR4]
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_zero, add_zero, zero_add]
  ring

/-- gate layer B of pair 2 in run `ρ`: twins have equal frames. -/
lemma G401.gateB2 (ρ : Fin 8) : XRoute (N.S8 ρ) (N.S8 ρ) (gscQ pABQ_2 kBQ_2) (fun _ => 0) := by
  refine gateP pABQ_2 kBQ_2 (N.S8 ρ) ?_
  rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩) hk
  · exact N.x23 g t
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (N.y23 g t).symm
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim

/-- the free bank adapters before stage 3 of run `ρ` (`bank_adapt`): every bank from `Zb` to `Zp`. -/
lemma G401.adapt3 (ρ : Fin 8) :
    GRoute (N.S8 ρ) (N.S9 ρ) id (fun _ => 0) := by
  have H1 := GRoute.reach_all (N.S8 ρ) (N.S9 ρ) (fun _ _ => 0) (by
      rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact N.hP3 ρ g b
      · exact GReach.refl _)
  exact H1.cast (fun φ => by simp)

/-- stage 3 of run `ρ`: backward on pair 2; the slot `q` of `g` on the bank `(g, use ρ 3 q)`. -/
lemma G401.stage3 (ρ : Fin 8) :
    GRoute (N.S9 ρ) (N.S10 ρ) (liftQ3 (Γ := Γ) (T := T) (C := C) (N.use ρ 3) GB)
      (fun φ => (Fintype.card Γ : ℝ) * N.I.cost φ) := by
  have h := gistageE_bwd N.I N.r3 N.G3 N.N3 N.Wn3 N.hN3 N.hW3
    (fun g q => N.Zp (9 * ρ.val + 3) g (N.use ρ 3 q)) (cOne Γ C α) (cOne Γ C α)
  have h' : GRoute (bIn N.I.tv N.r3 (fun d => (N.G3 d).Xm)
        (fun g q => N.Zp (9 * ρ.val + 3) g (N.use ρ 3 q)) (cOne Γ C α))
      (mkS N.xi4 N.yi4 (fun g q => N.Zb (9 * ρ.val + 4) g (N.use ρ 3 q)) (cOne Γ C α)) GB
      (fun φ => (Fintype.card Γ : ℝ) * N.I.cost φ) := by
    have e : bOut N.I.tv N.r3 (fun d => (N.G3 d).Xm)
        (fun g q => N.Wn3 g q * N.Zp (9 * ρ.val + 3) g (N.use ρ 3 q)) (cOne Γ C α)
        = mkS N.xi4 N.yi4 (fun g q => N.Zb (9 * ρ.val + 4) g (N.use ρ 3 q)) (cOne Γ C α) := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · exact N.x34 g t
      · exact N.y34 g t
      · exact N.hZ3 ρ g q
      · rfl
    rw [← e]
    exact h
  exact gbliftQ3 (N.use ρ 3) (N.hinj ρ 3) N.xo2 N.yo2 N.xi0 N.yi0 N.xi0 N.yi0 (fun g b => N.Zp (9 * ρ.val + 3) g b)
    (fun g b => N.Zb (9 * ρ.val + 4) g b) h'
    (fun g q => rfl) (fun g q => rfl) (fun g b hb => (N.hZn3 ρ g b hb).symm) (fun _ _ _ => rfl)

/-- first idle climb of pair 3 (ONE block per role), to the frames of pair 2 after stage 3. -/
lemma G401.climbA3 (ρ : Fin 8) :
    XRoute (N.S10 ρ) (N.S11 ρ) id (fun φ => (Fintype.card Γ : ℝ) *
      ((Fintype.card T : ℝ) * (N.caX3 φ + N.caY3 φ))) := by
  have H1 := XRoute.reach_all (N.S10 ρ) (N.S11 ρ)
    (mkR4 (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ => N.caX3) (fun _ _ => N.caY3) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)) (by
      rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
      · exact XReach.refl _
      · exact XReach.refl _
      · exact XReach.refl _
      · exact XReach.refl _
      · show XReach ((N.G0 g).Xm.Φ (tt (N.I.tv t))) ((N.G4 (N.r4 t g)).Xm.Φ (tt (N.I.tv t))) N.caX3
        rw [← N.x34 g t]
        exact N.aX3 g t
      · show XReach ((N.G0 g).Xm.Φ 0) ((N.G4 (N.r4 t g)).Xm.Φ 0) N.caY3
        rw [← N.y34 g t]
        exact N.aY3 g t
      · exact XReach.refl _
      · exact XReach.refl _
      · exact XReach.refl _
      · exact XReach.refl _)
  refine H1.cast (fun φ => ?_)
  simp_rw [mkR4_map (fun c : (ℕ → ℝ) → ℝ => c φ)]
  rw [sum_mkR4]
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_zero, add_zero, zero_add]
  ring

/-- gate layer A of pair 3 in run `ρ`: twins have equal frames. -/
lemma G401.gateA3 (ρ : Fin 8) : XRoute (N.S11 ρ) (N.S11 ρ) (gscQ pABQ_3 kAQ_3) (fun _ => 0) := by
  refine gateP pABQ_3 kAQ_3 (N.S11 ρ) ?_
  rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩) hk
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · rfl
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · rfl
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim

/-- the free bank adapters before stage 4 of run `ρ` (`bank_adapt`): every bank from `Zb` to `Zp`. -/
lemma G401.adapt4 (ρ : Fin 8) :
    GRoute (N.S11 ρ) (N.S12 ρ) id (fun _ => 0) := by
  have H1 := GRoute.reach_all (N.S11 ρ) (N.S12 ρ) (fun _ _ => 0) (by
      rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact N.hP4 ρ g b
      · exact GReach.refl _)
  exact H1.cast (fun φ => by simp)

/-- stage 4 of run `ρ`: forward on pair 2; the slot `q` of `g` on the bank `(g, use ρ 4 q)`. -/
lemma G401.stage4 (ρ : Fin 8) :
    GRoute (N.S12 ρ) (N.S13 ρ) (liftQ4 (Γ := Γ) (T := T) (C := C) (N.use ρ 4) GF)
      (fun φ => (Fintype.card Γ : ℝ) * N.I.cost φ) := by
  have h := gistageE_fwd N.I N.r4 N.G4 N.N4 N.Wn4 N.hN4 N.hW4
    (fun g q => N.Zp (9 * ρ.val + 4) g (N.use ρ 4 q)) (cOne Γ C α) (cOne Γ C α)
  have h' : GRoute (bIn N.I.tv N.r4 (fun d => (N.G4 d).Xm)
        (fun g q => N.Zp (9 * ρ.val + 4) g (N.use ρ 4 q)) (cOne Γ C α))
      (mkS N.xo4 N.yo4 (fun g q => N.Zb (9 * ρ.val + 5) g (N.use ρ 4 q)) (cOne Γ C α)) GF
      (fun φ => (Fintype.card Γ : ℝ) * N.I.cost φ) := by
    have e : bOut N.I.tv N.r4 (fun d => (N.G4 d).Xm)
        (fun g q => N.Wn4 g q * N.Zp (9 * ρ.val + 4) g (N.use ρ 4 q)) (cOne Γ C α)
        = mkS N.xo4 N.yo4 (fun g q => N.Zb (9 * ρ.val + 5) g (N.use ρ 4 q)) (cOne Γ C α) := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · rfl
      · rfl
      · exact N.hZ4 ρ g q
      · rfl
    rw [← e]
    exact h
  exact gbliftQ4 (N.use ρ 4) (N.hinj ρ 4) N.xo2 N.yo2 N.xi4 N.yi4 N.xi0 N.yi0 (fun g b => N.Zp (9 * ρ.val + 4) g b)
    (fun g b => N.Zb (9 * ρ.val + 5) g b) h'
    (fun g q => rfl) (fun g q => rfl) (fun g b hb => (N.hZn4 ρ g b hb).symm) (fun _ _ _ => rfl)

/-- second idle climb of pair 3: the window of stage 4, ONE block of rank `card H - 1` per role. -/
lemma G401.climbB3 (ρ : Fin 8) :
    XRoute (N.S13 ρ) (N.S14 ρ) id (fun φ => (Fintype.card Γ : ℝ) *
      ((Fintype.card T : ℝ) * (2 * bcost φ (Fintype.card H - 1)))) := by
  have H1 := XRoute.reach_all (N.S13 ρ) (N.S14 ρ)
    (mkR4 (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ => (fun φ => bcost φ (Fintype.card H - 1))) (fun _ _ => (fun φ => bcost φ (Fintype.card H - 1))) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0)) (by
      rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
      · exact XReach.refl _
      · exact XReach.refl _
      · exact XReach.refl _
      · exact XReach.refl _
      · show XReach ((N.G4 (N.r4 t g)).Xm.Φ (tt (N.I.tv t))) ((N.G5 (N.r5 t g)).Xm.Φ (tt (N.I.tv t)))
          (fun φ => bcost φ (Fintype.card H - 1))
        rw [← N.x45 g t]
        exact GInvE.climbX N.I (N.G4 (N.r4 t g)).Xm t
      · show XReach ((N.G4 (N.r4 t g)).Xm.Φ 0) ((N.G5 (N.r5 t g)).Xm.Φ 0)
          (fun φ => bcost φ (Fintype.card H - 1))
        rw [← N.y45 g t]
        exact GInvE.climbY N.I (N.G4 (N.r4 t g)).Xm t
      · exact XReach.refl _
      · exact XReach.refl _
      · exact XReach.refl _
      · exact XReach.refl _)
  refine H1.cast (fun φ => ?_)
  simp_rw [mkR4_map (fun c : (ℕ → ℝ) → ℝ => c φ)]
  rw [sum_mkR4]
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_zero, add_zero, zero_add]
  ring

/-- gate layer B of pair 3 in run `ρ`: twins have equal frames. -/
lemma G401.gateB3 (ρ : Fin 8) : XRoute (N.S14 ρ) (N.S14 ρ) (gscQ pABQ_3 kBQ_3) (fun _ => 0) := by
  refine gateP pABQ_3 kBQ_3 (N.S14 ρ) ?_
  rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩) hk
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact N.x45 g t
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (N.y45 g t).symm
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim

/-- the free bank adapters before stage 5 of run `ρ` (`bank_adapt`): every bank from `Zb` to `Zp`. -/
lemma G401.adapt5 (ρ : Fin 8) :
    GRoute (N.S14 ρ) (N.S15 ρ) id (fun _ => 0) := by
  have H1 := GRoute.reach_all (N.S14 ρ) (N.S15 ρ) (fun _ _ => 0) (by
      rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact N.hP5 ρ g b
      · exact GReach.refl _)
  exact H1.cast (fun φ => by simp)

/-- stage 5 of run `ρ`: backward on pair 3; the slot `q` of `g` on the bank `(g, use ρ 5 q)`. -/
lemma G401.stage5 (ρ : Fin 8) :
    GRoute (N.S15 ρ) (N.S16 ρ) (liftQ5 (Γ := Γ) (T := T) (C := C) (N.use ρ 5) GB)
      (fun φ => (Fintype.card Γ : ℝ) * N.I.cost φ) := by
  have h := gistageE_bwd N.I N.r5 N.G5 N.N5 N.Wn5 N.hN5 N.hW5
    (fun g q => N.Zp (9 * ρ.val + 5) g (N.use ρ 5 q)) (cOne Γ C α) (cOne Γ C α)
  have h' : GRoute (bIn N.I.tv N.r5 (fun d => (N.G5 d).Xm)
        (fun g q => N.Zp (9 * ρ.val + 5) g (N.use ρ 5 q)) (cOne Γ C α))
      (mkS N.xi6 N.yi6 (fun g q => N.Zb (9 * ρ.val + 6) g (N.use ρ 5 q)) (cOne Γ C α)) GB
      (fun φ => (Fintype.card Γ : ℝ) * N.I.cost φ) := by
    have e : bOut N.I.tv N.r5 (fun d => (N.G5 d).Xm)
        (fun g q => N.Wn5 g q * N.Zp (9 * ρ.val + 5) g (N.use ρ 5 q)) (cOne Γ C α)
        = mkS N.xi6 N.yi6 (fun g q => N.Zb (9 * ρ.val + 6) g (N.use ρ 5 q)) (cOne Γ C α) := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · exact N.x56 g t
      · exact N.y56 g t
      · exact N.hZ5 ρ g q
      · rfl
    rw [← e]
    exact h
  exact gbliftQ5 (N.use ρ 5) (N.hinj ρ 5) N.xo2 N.yo2 N.xo4 N.yo4 N.xi0 N.yi0 (fun g b => N.Zp (9 * ρ.val + 5) g b)
    (fun g b => N.Zb (9 * ρ.val + 6) g b) h'
    (fun g q => rfl) (fun g q => rfl) (fun g b hb => (N.hZn5 ρ g b hb).symm) (fun _ _ _ => rfl)

/-- first idle climb of pair 4 (ONE block per role), to the frames of pair 3 after stage 5. -/
lemma G401.climbA4 (ρ : Fin 8) :
    XRoute (N.S16 ρ) (N.S17 ρ) id (fun φ => (Fintype.card Γ : ℝ) *
      ((Fintype.card T : ℝ) * (N.caX4 φ + N.caY4 φ))) := by
  have H1 := XRoute.reach_all (N.S16 ρ) (N.S17 ρ)
    (mkR4 (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ => N.caX4) (fun _ _ => N.caY4) (fun _ _ _ => 0) (fun _ _ _ => 0)) (by
      rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
      · exact XReach.refl _
      · exact XReach.refl _
      · exact XReach.refl _
      · exact XReach.refl _
      · exact XReach.refl _
      · exact XReach.refl _
      · show XReach ((N.G0 g).Xm.Φ (tt (N.I.tv t))) ((N.G6 (N.r6 t g)).Xm.Φ (tt (N.I.tv t))) N.caX4
        rw [← N.x56 g t]
        exact N.aX4 g t
      · show XReach ((N.G0 g).Xm.Φ 0) ((N.G6 (N.r6 t g)).Xm.Φ 0) N.caY4
        rw [← N.y56 g t]
        exact N.aY4 g t
      · exact XReach.refl _
      · exact XReach.refl _)
  refine H1.cast (fun φ => ?_)
  simp_rw [mkR4_map (fun c : (ℕ → ℝ) → ℝ => c φ)]
  rw [sum_mkR4]
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_zero, add_zero, zero_add]
  ring

/-- gate layer A of pair 4 in run `ρ`: twins have equal frames. -/
lemma G401.gateA4 (ρ : Fin 8) : XRoute (N.S17 ρ) (N.S17 ρ) (gscQ pABQ_4 kAQ_4) (fun _ => 0) := by
  refine gateP pABQ_4 kAQ_4 (N.S17 ρ) ?_
  rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩) hk
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · rfl
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · rfl
  · exact (hk rfl).elim
  · exact (hk rfl).elim

/-- the free bank adapters before stage 6 of run `ρ` (`bank_adapt`): every bank from `Zb` to `Zp`. -/
lemma G401.adapt6 (ρ : Fin 8) :
    GRoute (N.S17 ρ) (N.S18 ρ) id (fun _ => 0) := by
  have H1 := GRoute.reach_all (N.S17 ρ) (N.S18 ρ) (fun _ _ => 0) (by
      rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact N.hP6 ρ g b
      · exact GReach.refl _)
  exact H1.cast (fun φ => by simp)

/-- stage 6 of run `ρ`: forward on pair 3; the slot `q` of `g` on the bank `(g, use ρ 6 q)`. -/
lemma G401.stage6 (ρ : Fin 8) :
    GRoute (N.S18 ρ) (N.S19 ρ) (liftQ6 (Γ := Γ) (T := T) (C := C) (N.use ρ 6) GF)
      (fun φ => (Fintype.card Γ : ℝ) * N.I.cost φ) := by
  have h := gistageE_fwd N.I N.r6 N.G6 N.N6 N.Wn6 N.hN6 N.hW6
    (fun g q => N.Zp (9 * ρ.val + 6) g (N.use ρ 6 q)) (cOne Γ C α) (cOne Γ C α)
  have h' : GRoute (bIn N.I.tv N.r6 (fun d => (N.G6 d).Xm)
        (fun g q => N.Zp (9 * ρ.val + 6) g (N.use ρ 6 q)) (cOne Γ C α))
      (mkS N.xo6 N.yo6 (fun g q => N.Zb (9 * ρ.val + 7) g (N.use ρ 6 q)) (cOne Γ C α)) GF
      (fun φ => (Fintype.card Γ : ℝ) * N.I.cost φ) := by
    have e : bOut N.I.tv N.r6 (fun d => (N.G6 d).Xm)
        (fun g q => N.Wn6 g q * N.Zp (9 * ρ.val + 6) g (N.use ρ 6 q)) (cOne Γ C α)
        = mkS N.xo6 N.yo6 (fun g q => N.Zb (9 * ρ.val + 7) g (N.use ρ 6 q)) (cOne Γ C α) := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · rfl
      · rfl
      · exact N.hZ6 ρ g q
      · rfl
    rw [← e]
    exact h
  exact gbliftQ6 (N.use ρ 6) (N.hinj ρ 6) N.xo2 N.yo2 N.xo4 N.yo4 N.xi6 N.yi6 (fun g b => N.Zp (9 * ρ.val + 6) g b)
    (fun g b => N.Zb (9 * ρ.val + 7) g b) h'
    (fun g q => rfl) (fun g q => rfl) (fun g b hb => (N.hZn6 ρ g b hb).symm) (fun _ _ _ => rfl)

/-- second idle climb of pair 4: the window of stage 6, ONE block of rank `card H - 1` per role. -/
lemma G401.climbB4 (ρ : Fin 8) :
    XRoute (N.S19 ρ) (N.S20 ρ) id (fun φ => (Fintype.card Γ : ℝ) *
      ((Fintype.card T : ℝ) * (2 * bcost φ (Fintype.card H - 1)))) := by
  have H1 := XRoute.reach_all (N.S19 ρ) (N.S20 ρ)
    (mkR4 (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ => (fun φ => bcost φ (Fintype.card H - 1))) (fun _ _ => (fun φ => bcost φ (Fintype.card H - 1))) (fun _ _ _ => 0) (fun _ _ _ => 0)) (by
      rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
      · exact XReach.refl _
      · exact XReach.refl _
      · exact XReach.refl _
      · exact XReach.refl _
      · exact XReach.refl _
      · exact XReach.refl _
      · show XReach ((N.G6 (N.r6 t g)).Xm.Φ (tt (N.I.tv t))) ((N.G7 (N.r7 t g)).Xm.Φ (tt (N.I.tv t)))
          (fun φ => bcost φ (Fintype.card H - 1))
        rw [← N.x67 g t]
        exact GInvE.climbX N.I (N.G6 (N.r6 t g)).Xm t
      · show XReach ((N.G6 (N.r6 t g)).Xm.Φ 0) ((N.G7 (N.r7 t g)).Xm.Φ 0)
          (fun φ => bcost φ (Fintype.card H - 1))
        rw [← N.y67 g t]
        exact GInvE.climbY N.I (N.G6 (N.r6 t g)).Xm t
      · exact XReach.refl _
      · exact XReach.refl _)
  refine H1.cast (fun φ => ?_)
  simp_rw [mkR4_map (fun c : (ℕ → ℝ) → ℝ => c φ)]
  rw [sum_mkR4]
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_zero, add_zero, zero_add]
  ring

/-- gate layer B of pair 4 in run `ρ`: twins have equal frames. -/
lemma G401.gateB4 (ρ : Fin 8) : XRoute (N.S20 ρ) (N.S20 ρ) (gscQ pABQ_4 kBQ_4) (fun _ => 0) := by
  refine gateP pABQ_4 kBQ_4 (N.S20 ρ) ?_
  rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩) hk
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact N.x67 g t
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (N.y67 g t).symm
  · exact (hk rfl).elim
  · exact (hk rfl).elim

/-- the free bank adapters before stage 7 of run `ρ` (`bank_adapt`): every bank from `Zb` to `Zp`. -/
lemma G401.adapt7 (ρ : Fin 8) :
    GRoute (N.S20 ρ) (N.S21 ρ) id (fun _ => 0) := by
  have H1 := GRoute.reach_all (N.S20 ρ) (N.S21 ρ) (fun _ _ => 0) (by
      rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact N.hP7 ρ g b
      · exact GReach.refl _)
  exact H1.cast (fun φ => by simp)

/-- stage 7 of run `ρ`: backward on pair 4; the slot `q` of `g` on the bank `(g, use ρ 7 q)`. -/
lemma G401.stage7 (ρ : Fin 8) :
    GRoute (N.S21 ρ) (N.S22 ρ) (liftQ7 (Γ := Γ) (T := T) (C := C) (N.use ρ 7) GB)
      (fun φ => (Fintype.card Γ : ℝ) * N.I.cost φ) := by
  have h := gistageE_bwd N.I N.r7 N.G7 N.N7 N.Wn7 N.hN7 N.hW7
    (fun g q => N.Zp (9 * ρ.val + 7) g (N.use ρ 7 q)) (cOne Γ C α) (cOne Γ C α)
  have h' : GRoute (bIn N.I.tv N.r7 (fun d => (N.G7 d).Xm)
        (fun g q => N.Zp (9 * ρ.val + 7) g (N.use ρ 7 q)) (cOne Γ C α))
      (mkS N.xi8 N.yi8 (fun g q => N.Zb (9 * ρ.val + 8) g (N.use ρ 7 q)) (cOne Γ C α)) GB
      (fun φ => (Fintype.card Γ : ℝ) * N.I.cost φ) := by
    have e : bOut N.I.tv N.r7 (fun d => (N.G7 d).Xm)
        (fun g q => N.Wn7 g q * N.Zp (9 * ρ.val + 7) g (N.use ρ 7 q)) (cOne Γ C α)
        = mkS N.xi8 N.yi8 (fun g q => N.Zb (9 * ρ.val + 8) g (N.use ρ 7 q)) (cOne Γ C α) := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · exact N.x78 g t
      · exact N.y78 g t
      · exact N.hZ7 ρ g q
      · rfl
    rw [← e]
    exact h
  exact gbliftQ7 (N.use ρ 7) (N.hinj ρ 7) N.xo2 N.yo2 N.xo4 N.yo4 N.xo6 N.yo6 (fun g b => N.Zp (9 * ρ.val + 7) g b)
    (fun g b => N.Zb (9 * ρ.val + 8) g b) h'
    (fun g q => rfl) (fun g q => rfl) (fun g b hb => (N.hZn7 ρ g b hb).symm) (fun _ _ _ => rfl)

/-- the free bank adapters before stage 8 of run `ρ` (`bank_adapt`): every bank from `Zb` to `Zp`. -/
lemma G401.adapt8 (ρ : Fin 8) :
    GRoute (N.S22 ρ) (N.S23 ρ) id (fun _ => 0) := by
  have H1 := GRoute.reach_all (N.S22 ρ) (N.S23 ρ) (fun _ _ => 0) (by
      rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact GReach.refl _
      · exact N.hP8 ρ g b
      · exact GReach.refl _)
  exact H1.cast (fun φ => by simp)

/-- stage 8 of run `ρ`: forward on pair 4; the slot `q` of `g` on the bank `(g, use ρ 8 q)`. -/
lemma G401.stage8 (ρ : Fin 8) :
    GRoute (N.S23 ρ) (N.S24 ρ) (liftQ8 (Γ := Γ) (T := T) (C := C) (N.use ρ 8) GF)
      (fun φ => (Fintype.card Γ : ℝ) * N.I.cost φ) := by
  have h := gistageE_fwd N.I N.r8 N.G8 N.N8 N.Wn8 N.hN8 N.hW8
    (fun g q => N.Zp (9 * ρ.val + 8) g (N.use ρ 8 q)) (cOne Γ C α) (cOne Γ C α)
  have h' : GRoute (bIn N.I.tv N.r8 (fun d => (N.G8 d).Xm)
        (fun g q => N.Zp (9 * ρ.val + 8) g (N.use ρ 8 q)) (cOne Γ C α))
      (mkS N.xo8 N.yo8 (fun g q => N.Zb (9 * ρ.val + 9) g (N.use ρ 8 q)) (cOne Γ C α)) GF
      (fun φ => (Fintype.card Γ : ℝ) * N.I.cost φ) := by
    have e : bOut N.I.tv N.r8 (fun d => (N.G8 d).Xm)
        (fun g q => N.Wn8 g q * N.Zp (9 * ρ.val + 8) g (N.use ρ 8 q)) (cOne Γ C α)
        = mkS N.xo8 N.yo8 (fun g q => N.Zb (9 * ρ.val + 9) g (N.use ρ 8 q)) (cOne Γ C α) := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · rfl
      · rfl
      · exact N.hZ8 ρ g q
      · rfl
    rw [← e]
    exact h
  exact gbliftQ8 (N.use ρ 8) (N.hinj ρ 8) N.xo2 N.yo2 N.xo4 N.yo4 N.xo6 N.yo6 (fun g b => N.Zp (9 * ρ.val + 8) g b)
    (fun g b => N.Zb (9 * ρ.val + 9) g b) h'
    (fun g q => rfl) (fun g q => rfl) (fun g b hb => (N.hZn8 ρ g b hb).symm) (fun _ _ _ => rfl)

/-- the final climbs of the replica of run `ρ`: every pair from its frames after its last stage. -/
lemma G401.fin (ρ : Fin 8) :
    XRoute (N.S24 ρ) (N.S25 ρ) id (fun φ => (Fintype.card Γ : ℝ) *
      ((Fintype.card T : ℝ) * ((N.cX1 φ + N.cY1 φ) + (N.cX2 φ + N.cY2 φ) + (N.cX3 φ + N.cY3 φ) + (N.cX4 φ + N.cY4 φ)))) := by
  have H1 := XRoute.reach_all (N.S24 ρ) (N.S25 ρ)
    (mkR4 (fun _ _ => N.cX1) (fun _ _ => N.cY1) (fun _ _ => N.cX2) (fun _ _ => N.cY2) (fun _ _ => N.cX3) (fun _ _ => N.cY3) (fun _ _ => N.cX4) (fun _ _ => N.cY4) (fun _ _ _ => 0) (fun _ _ _ => 0)) (by
      rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩)
      · exact N.fX1 g t
      · exact N.fY1 g t
      · exact N.fX2 g t
      · exact N.fY2 g t
      · exact N.fX3 g t
      · exact N.fY3 g t
      · exact N.fX4 g t
      · exact N.fY4 g t
      · exact XReach.refl _
      · exact XReach.refl _)
  refine H1.cast (fun φ => ?_)
  simp_rw [mkR4_map (fun c : (ℕ → ℝ) → ℝ => c φ)]
  rw [sum_mkR4]
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_zero, add_zero, zero_add]
  ring

/-- gate layer C of pair 4 in run `ρ`: twins have equal frames. -/
lemma G401.gateC4 (ρ : Fin 8) : XRoute (N.S25 ρ) (N.S25 ρ) (gscQ pCQ_4 kCQ_4) (fun _ => 0) := by
  refine gateP pCQ_4 kCQ_4 (N.S25 ρ) ?_
  rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩) hk
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · rfl
  · rfl
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim

/-- gate layer C of pair 3 in run `ρ`: twins have equal frames. -/
lemma G401.gateC3 (ρ : Fin 8) : XRoute (N.S25 ρ) (N.S25 ρ) (gscQ pCQ_3 kCQ_3) (fun _ => 0) := by
  refine gateP pCQ_3 kCQ_3 (N.S25 ρ) ?_
  rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩) hk
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · rfl
  · rfl
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim

/-- gate layer C of pair 2 in run `ρ`: twins have equal frames. -/
lemma G401.gateC2 (ρ : Fin 8) : XRoute (N.S25 ρ) (N.S25 ρ) (gscQ pCQ_2 kCQ_2) (fun _ => 0) := by
  refine gateP pCQ_2 kCQ_2 (N.S25 ρ) ?_
  rintro ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩) hk
  · exact (hk rfl).elim
  · rfl
  · rfl
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · exact (hk rfl).elim

end Net
end
end GX
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.GX.G401.stage0
#print axioms OAI.PowerSaving.GX.G401.stage1
#print axioms OAI.PowerSaving.GX.G401.stage2
#print axioms OAI.PowerSaving.GX.G401.stage3
#print axioms OAI.PowerSaving.GX.G401.stage4
#print axioms OAI.PowerSaving.GX.G401.stage5
#print axioms OAI.PowerSaving.GX.G401.stage6
#print axioms OAI.PowerSaving.GX.G401.stage7
#print axioms OAI.PowerSaving.GX.G401.stage8
#print axioms OAI.PowerSaving.GX.G401.fin
