import Work.Reframe.SNet
import Work.BlockApply.Copies

/-!
# (key: reframe) The folded three-stage network with SHARED helper sets, abstract form

Shared counterpart of `Work.Fold.XFold3` (agent fold-core): cross-stage form of PLAN.md B2.
`Fold3S H T Sl C α Γ` is everything the wiring needs to know about the geometry:

* a block circuit `X` (one invocation);
* block frame maps `M1 M2 M3 : Γ → XMap H α` of the invocations of the three stages;
* bijections `r1 t`, `r2 t` of `Γ`: the bank pair `(g,t)` is served by the invocations `g`
  (stage 1, forward), `r1 t g` (stage 2, backward), `r2 t g` (stage 3, forward);
* bijections `s2`, `s3` of `Γ`: the helper set `g` (one per element of `Γ`, `Sl` slots and `C`
  scratch copies) serves the invocations `g` (stage 1), `s2⁻¹ g` (stage 2), `s3⁻¹ g` (stage 3);
* for stages 2 and 3 an inverse `N_k d` of the frame of the base and the frame `W_k d` of the
  window of every invocation; `sfin`: the three windows of a helper set make up the kernel;
* the frame identities of the bank roles between the stages (`x12 y12 x23 y23`), their final
  climbs, each ONE block (`fX`, `fY`, ranks `eX`, `eY`), and the terminal identity (`term`).

`fold3s_certificate`: a `BCert` (proper block word, `LiveKernel`) whose price, for EVERY price
list, is `card Γ * N.unit φ`,

    N.unit φ = 3 * N.X.cost φ + card T * (bcost φ eX + bcost φ eY).

Live roles: `card Γ * (2 card T + card Sl)` (`RF.card_SLive`).  No helper slot makes any block
outside its three invocations.  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace RF
open Binary Matrix Finset RAM SS CB
noncomputable section

/-- See the file header. -/
structure Fold3S (H T Sl C α Γ : Type) [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
    [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] [Fintype α] [DecidableEq α] where
  X : XCircuit H T Sl C
  M1 : Γ → XMap H α
  M2 : Γ → XMap H α
  M3 : Γ → XMap H α
  r1 : T → Γ ≃ Γ
  r2 : T → Γ ≃ Γ
  s2 : Γ ≃ Γ
  s3 : Γ ≃ Γ
  N2 : Γ → CMat α
  W2 : Γ → CMat α
  N3 : Γ → CMat α
  W3 : Γ → CMat α
  u : Γ → T → Space α
  YF : Γ → T → CMat α
  hm : 2 ≤ Fintype.card α
  eX : ℕ
  eY : ℕ
  inv1 : ∀ g t, ∃ N : CMat α, (M1 g).Φ (tt (X.K.tv t)) * N = 1
  z1 : ∀ g, (M1 g).Φ 0 = 1
  hN2 : ∀ d, (M2 d).Φ 0 * N2 d = 1
  hW2 : ∀ d, (M2 d).Φ 1 = W2 d * (M2 d).Φ 0
  hN3 : ∀ d, (M3 d).Φ 0 * N3 d = 1
  hW3 : ∀ d, (M3 d).Φ 1 = W3 d * (M3 d).Φ 0
  x12 : ∀ g t, (M1 g).Φ 1 = (M2 (r1 t g)).Φ (tt (X.K.tv t))
  y12 : ∀ g t, (M1 g).Φ (1 + tt (X.K.tv t)) = (M2 (r1 t g)).Φ 0
  x23 : ∀ g t, (M2 (r1 t g)).Φ 1 = (M3 (r2 t g)).Φ (tt (X.K.tv t))
  y23 : ∀ g t, (M2 (r1 t g)).Φ (1 + tt (X.K.tv t)) = (M3 (r2 t g)).Φ 0
  sfin : ∀ g, W3 (s3.symm g) * (W2 (s2.symm g) * (M1 g).Φ 1) = kernel α
  fX : ∀ g t, XReach ((M3 (r2 t g)).Φ 1) (kernel α) (fun φ => bcost φ eX)
  fY : ∀ g t, XReach ((M3 (r2 t g)).Φ (1 + tt (X.K.tv t))) (YF g t) (fun φ => bcost φ eY)
  term : ∀ g t, kernel α * (M1 g).Φ (tt (X.K.tv t)) = shift (u g t) * YF g t

section Net
variable {H T Sl C α Γ : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] [Fintype α] [DecidableEq α]
  [Fintype Γ] [DecidableEq Γ]
variable (N : Fold3S H T Sl C α Γ)

/-- price of the blocks of one unit (one element of `Γ`): three invocations and the two final
blocks of every bank pair. -/
def Fold3S.unit (φ : ℕ → ℝ) : ℝ :=
  3 * N.X.cost φ + (Fintype.card T : ℝ) * (bcost φ N.eX + bcost φ N.eY)

/-- the bank index of stage 1: the pair `(g,t)` belongs to the invocation `g`. -/
abbrev rid (Γ T : Type) : T → Γ ≃ Γ := fun _ => Equiv.refl Γ

/-- helper slots after stage 1, after stage 2. -/
def Fold3S.Z1 : Γ → Sl → CMat α := fun g _ => (N.M1 g).Φ 1
def Fold3S.Z2 : Γ → Sl → CMat α := fun g _ => N.W2 (N.s2.symm g) * (N.M1 g).Φ 1

/-- frames at the start; after stage 1; after stage 2; after stage 3. -/
def Fold3S.SA : SRole Γ T Sl C → CMat α :=
  sIn N.X.K (rid Γ T) N.M1 (fun _ _ => 1) (fun _ _ => 1)
def Fold3S.SB : SRole Γ T Sl C → CMat α := sIn N.X.K N.r1 N.M2 N.Z1 (fun _ _ => 1)
def Fold3S.SC : SRole Γ T Sl C → CMat α := sIn N.X.K N.r2 N.M3 N.Z2 (fun _ _ => 1)
def Fold3S.SD : SRole Γ T Sl C → CMat α :=
  sOut N.X.K N.r2 N.M3 (fun g q => N.W3 (N.s3.symm g) * N.Z2 g q) (fun _ _ => 1)

/-- stage 1: forward, every helper set starts at the matrix `1`. -/
lemma Fold3S.stage1_x :
    XRoute N.SA N.SB GF (fun φ => (Fintype.card Γ : ℝ) * N.X.cost φ) := by
  have h := sstage_fwd N.X (rid Γ T) (Equiv.refl Γ) N.M1 (fun _ => 1) (fun g => (N.M1 g).Φ 1)
    (fun d => by rw [N.z1, Matrix.mul_one]) (fun d => by rw [N.z1, Matrix.mul_one])
    (fun _ _ => 1) (fun _ _ => 1) (fun _ _ => 1)
  have e : sOut N.X.K (rid Γ T) N.M1
      (fun g (_ : Sl) => (N.M1 ((Equiv.refl Γ).symm g)).Φ 1 * (1 : CMat α))
      (fun _ (_ : C) => (1 : CMat α)) = N.SB := by
    funext r
    rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
    · exact N.x12 g t
    · exact N.y12 g t
    · show (N.M1 g).Φ 1 * 1 = (N.M1 g).Φ 1
      rw [Matrix.mul_one]
    · rfl
  rw [e] at h
  exact h

/-- stage 2: backward; the helper set `g` serves the invocation `s2⁻¹ g`. -/
lemma Fold3S.stage2_x :
    XRoute N.SB N.SC GB (fun φ => (Fintype.card Γ : ℝ) * N.X.cost φ) := by
  have h := sstage_bwd N.X N.r1 N.s2 N.M2 N.N2 N.W2 N.hN2 N.hW2 N.Z1
    (fun _ _ => 1) (fun _ _ => 1)
  have e : sOut N.X.K N.r1 N.M2 (fun g q => N.W2 (N.s2.symm g) * N.Z1 g q)
      (fun _ (_ : C) => (1 : CMat α)) = N.SC := by
    funext r
    rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
    · exact N.x23 g t
    · exact N.y23 g t
    · rfl
    · rfl
  rw [e] at h
  exact h

/-- stage 3: forward; the helper set `g` serves the invocation `s3⁻¹ g`. -/
lemma Fold3S.stage3_x :
    XRoute N.SC N.SD GF (fun φ => (Fintype.card Γ : ℝ) * N.X.cost φ) :=
  sstage_fwd N.X N.r2 N.s3 N.M3 N.N3 N.W3 N.hN3 N.hW3 N.Z2 (fun _ _ => 1) (fun _ _ => 1)

/-- final frames: the banks after their last climb, the helper slots at the kernel. -/
def Fold3S.SE : SRole Γ T Sl C → CMat α :=
  mkS (fun _ _ => kernel α) (fun g t => N.YF g t) (fun _ _ => kernel α) (fun _ _ => 1)

/-- the last climbs of the banks: ONE block each; the helper slots are already at the kernel. -/
lemma Fold3S.fin_x :
    XRoute N.SD N.SE id (fun φ => (Fintype.card Γ : ℝ) *
      ((Fintype.card T : ℝ) * (bcost φ N.eX + bcost φ N.eY))) := by
  have H1 := XRoute.reach_all N.SD N.SE
    (mkS (fun _ _ φ => bcost φ N.eX) (fun _ _ φ => bcost φ N.eY) (fun _ _ _ => 0)
      (fun _ _ _ => 0)) (by
      rintro (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
      · show XReach ((N.M3 (N.r2 t g)).Φ 1) (kernel α) (fun φ => bcost φ N.eX)
        exact N.fX g t
      · show XReach ((N.M3 (N.r2 t g)).Φ (1 + tt (N.X.K.tv t))) (N.YF g t)
          (fun φ => bcost φ N.eY)
        exact N.fY g t
      · show XReach (N.W3 (N.s3.symm g) * (N.W2 (N.s2.symm g) * (N.M1 g).Φ 1)) (kernel α)
          (fun _ => 0)
        rw [N.sfin g]
        exact XReach.refl _
      · show XReach (1 : CMat α) 1 (fun _ => 0)
        exact XReach.refl _)
  refine H1.cast (fun φ => ?_)
  simp_rw [mkS_map (fun c : (ℕ → ℝ) → ℝ => c φ)]
  rw [sum_mkS]
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_zero, add_zero]
  ring

/-- the free shifts at the end. -/
def Fold3S.corr : SRole Γ T Sl C → Space α :=
  mkS (fun _ _ => 0) (fun g t => N.u g t) (fun _ _ => 0) (fun _ _ => 0)

def Fold3S.SF : SRole Γ T Sl C → CMat α := fun r => shift (N.corr r) * N.SE r

/-- the signed exchange `X := Y`, `Y := -X`. -/
def spull : SRole Γ T Sl C → SRole Γ T Sl C :=
  mkS (fun g t => jY (g,t)) (fun g t => jX (g,t)) (fun g q => jS (g,q)) (fun g c => jC (g,c))

def ssgn : SRole Γ T Sl C → ℚ :=
  mkS (fun _ _ => 1) (fun _ _ => -1) (fun _ _ => 1) (fun _ _ => 1)

def srecM : Matrix (SRole Γ T Sl C) (SRole Γ T Sl C) ℚ :=
  fun i j => if j = spull i then ssgn i else 0

lemma actPoint_srecM (x : SRole Γ T Sl C → ℂ) (i : SRole Γ T Sl C) :
    actPoint srecM x i = (ssgn i : ℂ) * x (spull i) := by
  unfold actPoint
  rw [sum_eq_single (spull i)]
  · simp [srecM]
  · intro j _ hj; simp [srecM, hj]
  · simp

/-- **The scratch certificate of the three-stage network with shared helper sets**, in whole
blocks, with its exact price for every price list. -/
theorem fold3s_certificate :
    BCert α (Sum.inl : SLive Γ T Sl → SRole Γ T Sl C)
      (fun φ => (Fintype.card Γ : ℝ) * N.unit φ) := by
  have R1 := ((N.stage1_x.trans N.stage2_x).trans N.stage3_x).trans N.fin_x
  have R2 : XRoute N.SE N.SF id (fun _ => 0) := XRoute.shifts N.hm N.SE N.corr
  have R3 : XRoute N.SF (fun r => N.SF (spull r)) (actPoint srecM) (fun _ => 0) :=
    XRoute.gate srecM N.SF _ (fun i j h => by
      have hj : j = spull i := by
        by_contra hne
        exact h (by simp [srecM, hne])
      rw [hj])
  have Rt := ((R1.trans R2).trans R3).cast (c' := fun φ => (Fintype.card Γ : ℝ) * N.unit φ)
    (fun φ => by simp only [Fold3S.unit]; ring)
  have hSinv : ∀ r, ∃ M, N.SA r * M = 1 := by
    rintro (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
    · exact N.inv1 g t
    · refine ⟨1, ?_⟩
      show (N.M1 g).Φ 0 * 1 = 1
      rw [N.z1, Matrix.mul_one]
    · exact ⟨1, Matrix.mul_one _⟩
    · exact ⟨1, Matrix.mul_one _⟩
  choose S' hS' using hSinv
  have hT : ∀ l : SLive Γ T Sl, N.SF (spull (Sum.inl l)) = kernel α * N.SA (Sum.inl l) := by
    rintro ((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)
    · show shift (N.u g t) * N.YF g t = kernel α * (N.M1 g).Φ (tt (N.X.K.tv t))
      exact (N.term g t).symm
    · show shift (0 : Space α) * kernel α = kernel α * (N.M1 g).Φ 0
      rw [shift_zero, Matrix.one_mul, N.z1, Matrix.mul_one]
    · show shift (0 : Space α) * kernel α = kernel α * 1
      rw [shift_zero, Matrix.one_mul, Matrix.mul_one]
  have hg : ∀ x : SRole Γ T Sl C → ℂ,
      (∀ s, (∀ l : SLive Γ T Sl, (Sum.inl l : SRole Γ T Sl C) ≠ s) → x s = 0) →
      ∀ l : SLive Γ T Sl,
        (actPoint srecM ∘ (id ∘ (id ∘ (GF ∘ (GB ∘ GF))))) x (Sum.inl l) = x (Sum.inl l) := by
    intro x _ l
    change actPoint srecM (GF (GB (GF x))) (Sum.inl l) = _
    rw [actPoint_srecM]
    rcases l with ((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)
    · show ((1:ℚ):ℂ) * ((x (jY (g,t)) + x (jX (g,t)))
        + (x (jX (g,t)) - (x (jY (g,t)) + x (jX (g,t))))) = x (jX (g,t))
      push_cast
      ring
    · show ((-1:ℚ):ℂ) * (x (jX (g,t)) - (x (jY (g,t)) + x (jX (g,t)))) = x (jY (g,t))
      push_cast
      ring
    · show ((1:ℚ):ℂ) * x (jS (g,q)) = x (jS (g,q))
      push_cast
      ring
  exact XRoute.liveKernel (Sum.inl : SLive Γ T Sl → SRole Γ T Sl C) N.SA S'
    (fun r => N.SF (spull r)) hS' _ _ Rt hg hT

end Net
end
end RF
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.RF.Fold3S.stage1_x
#print axioms OAI.PowerSaving.RF.Fold3S.stage2_x
#print axioms OAI.PowerSaving.RF.Fold3S.stage3_x
#print axioms OAI.PowerSaving.RF.fold3s_certificate
