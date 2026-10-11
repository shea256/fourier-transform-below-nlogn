import Work.Reframe.Shared

/-!
# (key: reframe) One STAGE of a network with SHARED helper sets

Roles of a network in which every element of a finite type `Γ` owns ONE helper set and ONE
set of scratch copies (cross-stage form of PLAN.md B2):

    live     X(g,t), Y(g,t)   bank pairs,   Γ × T each
             S(g,q)           helper slots, Γ × Sl        (shared by all stages)
    scratch  C(g,c)           copies,       Γ × C         (shared by all stages)

A stage is given by bijections `εX t : Γ ≃ Γ` (the invocation `εX t g` serves the bank pair
`(g,t)`) and `εS : Γ ≃ Γ` (the invocation `d` uses the helper set and the copies `εS d`).

* `sem εX εS d`    the roles of the invocation `d` as an embedded `Box T Sl C`;
* `sstage`         every invocation runs the same kind of Box route: ONE `XRoute.parallel`
                   over `Γ`, price `card Γ * cost`;
* `GF`, `GB`       scalar maps of a whole stage: `y += x` resp. `x -= y` on every bank pair,
                   slots untouched, copies erased;
* `sstage_fwd`, `sstage_bwd`
                   a stage of erase-wrapped invocations on dirty helper slots
                   (`xinvocation_fwd_dirty`): the helper set `g` enters with ARBITRARY matrices
                   `Z g q` and leaves with `Wn (εS⁻¹ g) * Z g q`.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace RF
open Binary Matrix Finset RAM SS CB
noncomputable section

abbrev SLive (Γ T Sl : Type) := ((Γ × T) ⊕ (Γ × T)) ⊕ (Γ × Sl)
abbrev SRole (Γ T Sl C : Type) := SLive Γ T Sl ⊕ (Γ × C)

section Roles
variable {Γ T Sl C : Type}

def jX (k : Γ × T) : SRole Γ T Sl C := .inl (.inl (.inl k))
def jY (k : Γ × T) : SRole Γ T Sl C := .inl (.inl (.inr k))
def jS (k : Γ × Sl) : SRole Γ T Sl C := .inl (.inr k)
def jC (k : Γ × C) : SRole Γ T Sl C := .inr k

/-- a function on the roles, block by block. -/
def mkS {β : Type*} (fX fY : Γ → T → β) (fS : Γ → Sl → β) (fC : Γ → C → β) :
    SRole Γ T Sl C → β
  | .inl (.inl (.inl (g,t))) => fX g t
  | .inl (.inl (.inr (g,t))) => fY g t
  | .inl (.inr (g,q)) => fS g q
  | .inr (g,c) => fC g c

lemma mkS_map {β γ : Type*} (h : β → γ) (fX fY : Γ → T → β) (fS : Γ → Sl → β)
    (fC : Γ → C → β) (r : SRole Γ T Sl C) :
    h (mkS fX fY fS fC r) = mkS (fun g t => h (fX g t)) (fun g t => h (fY g t))
      (fun g q => h (fS g q)) (fun g c => h (fC g c)) r := by
  rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩) <;> rfl

lemma sum_mkS [Fintype Γ] [Fintype T] [Fintype Sl] [Fintype C]
    (fX fY : Γ → T → ℝ) (fS : Γ → Sl → ℝ) (fC : Γ → C → ℝ) :
    ∑ r : SRole Γ T Sl C, mkS fX fY fS fC r
      = ∑ g, ∑ t, fX g t + (∑ g, ∑ t, fY g t + (∑ g, ∑ q, fS g q + ∑ g, ∑ c, fC g c)) := by
  simp only [Fintype.sum_sum_type, mkS, Fintype.sum_prod_type]
  ring

lemma card_SLive [Fintype Γ] [Fintype T] [Fintype Sl] :
    Fintype.card (SLive Γ T Sl) = Fintype.card Γ * (2 * Fintype.card T + Fintype.card Sl) := by
  simp only [Fintype.card_sum, Fintype.card_prod]
  ring

/-- where the roles of the invocation `d` sit. -/
def spos (εX : T → Γ ≃ Γ) (εS : Γ ≃ Γ) (d : Γ) : Box T Sl C → SRole Γ T Sl C :=
  stamp (fun t => jX ((εX t).symm d, t)) (fun t => jY ((εX t).symm d, t))
    (fun q => jS (εS d, q)) (fun c => jC (εS d, c))

lemma spos_inj (εX : T → Γ ≃ Γ) (εS : Γ ≃ Γ) {d d' : Γ} {x y : Box T Sl C}
    (h : (spos εX εS d x : SRole Γ T Sl C) = spos εX εS d' y) : d = d' ∧ x = y := by
  rcases x with ((t|t)|(q|c)) <;> rcases y with ((t'|t')|(q'|c')) <;>
    simp only [spos, stamp, jX, jY, jS, jC, Sum.elim_inl, Sum.elim_inr, Sum.inl.injEq,
      Sum.inr.injEq, Prod.mk.injEq, reduceCtorEq] at h
  · obtain ⟨h1, h2⟩ := h; subst h2; exact ⟨(εX t).symm.injective h1, rfl⟩
  · obtain ⟨h1, h2⟩ := h; subst h2; exact ⟨(εX t).symm.injective h1, rfl⟩
  · obtain ⟨h1, h2⟩ := h; subst h2; exact ⟨εS.injective h1, rfl⟩
  · obtain ⟨h1, h2⟩ := h; subst h2; exact ⟨εS.injective h1, rfl⟩

def sem (εX : T → Γ ≃ Γ) (εS : Γ ≃ Γ) (d : Γ) : Box T Sl C ↪ SRole Γ T Sl C :=
  ⟨spos εX εS d, fun _ _ h => (spos_inj εX εS h).2⟩

lemma spos_X (εX : T → Γ ≃ Γ) (εS : Γ ≃ Γ) (g : Γ) (t : T) :
    (spos εX εS (εX t g) (bX t) : SRole Γ T Sl C) = jX (g, t) := by
  show jX ((εX t).symm (εX t g), t) = _
  rw [Equiv.symm_apply_apply]

lemma spos_Y (εX : T → Γ ≃ Γ) (εS : Γ ≃ Γ) (g : Γ) (t : T) :
    (spos εX εS (εX t g) (bY t) : SRole Γ T Sl C) = jY (g, t) := by
  show jY ((εX t).symm (εX t g), t) = _
  rw [Equiv.symm_apply_apply]

lemma spos_S (εX : T → Γ ≃ Γ) (εS : Γ ≃ Γ) (g : Γ) (q : Sl) :
    (spos εX εS (εS.symm g) (bS q) : SRole Γ T Sl C) = jS (g, q) := by
  show jS (εS (εS.symm g), q) = _
  rw [Equiv.apply_symm_apply]

lemma spos_C (εX : T → Γ ≃ Γ) (εS : Γ ≃ Γ) (g : Γ) (c : C) :
    (spos εX εS (εS.symm g) (bC c) : SRole Γ T Sl C) = jC (g, c) := by
  show jC (εS (εS.symm g), c) = _
  rw [Equiv.apply_symm_apply]

/-- scalar map of a forward stage: `y += x` on every bank pair, copies erased. -/
def GF (x : SRole Γ T Sl C → ℂ) : SRole Γ T Sl C → ℂ :=
  mkS (fun g t => x (jX (g,t))) (fun g t => x (jY (g,t)) + x (jX (g,t)))
    (fun g q => x (jS (g,q))) (fun _ _ => 0)

/-- scalar map of a backward stage: `x -= y` on every bank pair, copies erased. -/
def GB (x : SRole Γ T Sl C → ℂ) : SRole Γ T Sl C → ℂ :=
  mkS (fun g t => x (jX (g,t)) - x (jY (g,t))) (fun g t => x (jY (g,t)))
    (fun g q => x (jS (g,q))) (fun _ _ => 0)

variable [DecidableEq Γ] [DecidableEq T] [DecidableEq Sl] [DecidableEq C]
  [Fintype T] [Fintype Sl] [Fintype C]

lemma sem_dis (εX : T → Γ ≃ Γ) (εS : Γ ≃ Γ) (d d' : Γ) (h : d ≠ d') (x : SRole Γ T Sl C) :
    x ∈ covered (sem εX εS d) → x ∉ covered (sem εX εS d') := by
  simp only [cover_iff, not_exists]
  rintro ⟨u, hu⟩ v hv
  exact h (spos_inj εX εS (hu.trans hv.symm)).1

/-- every role belongs to exactly one invocation of a stage. -/
lemma scovered (εX : T → Γ ≃ Γ) (εS : Γ ≃ Γ) (r : SRole Γ T Sl C) :
    ∃ d, r ∈ covered (sem εX εS d) := by
  rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩)
  · exact ⟨εX t g, (cover_iff ..).mpr ⟨bX t, spos_X εX εS g t⟩⟩
  · exact ⟨εX t g, (cover_iff ..).mpr ⟨bY t, spos_Y εX εS g t⟩⟩
  · exact ⟨εS.symm g, (cover_iff ..).mpr ⟨bS q, spos_S εX εS g q⟩⟩
  · exact ⟨εS.symm g, (cover_iff ..).mpr ⟨bC c, spos_C εX εS g c⟩⟩

end Roles

section Stage
variable {H T Sl C α Γ : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] [Fintype α] [DecidableEq α]
  [Fintype Γ] [DecidableEq Γ]

/-- **A stage**: every invocation `d` runs a Box route with the same scalar map and the same
price; ONE parallel composition over `Γ`. -/
theorem sstage (εX : T → Γ ≃ Γ) (εS : Γ ≃ Γ) {S U : SRole Γ T Sl C → CMat α}
    {G : (SRole Γ T Sl C → ℂ) → (SRole Γ T Sl C → ℂ)}
    {h : (Box T Sl C → ℂ) → (Box T Sl C → ℂ)} {cost : (ℕ → ℝ) → ℝ}
    (q : ∀ d, XRoute (S ∘ sem εX εS d) (U ∘ sem εX εS d) h cost)
    (hin : ∀ d x, (G x) ∘ sem εX εS d = h (x ∘ sem εX εS d)) :
    XRoute S U G (fun φ => (Fintype.card Γ : ℝ) * cost φ) := by
  have key := XRoute.parallel (ρ := Box T Sl C) (σ := SRole Γ T Sl C) (J := Γ)
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

/-- frames at the START of a stage: the bank pair `(g,t)` at the invocation `εX t g`, the
helper set `g` at the matrices `Z g`, the copies at `c g`. -/
def sIn (K : Circuit H T Sl C) (εX : T → Γ ≃ Γ) (M : Γ → XMap H α) (Z : Γ → Sl → CMat α)
    (c : Γ → C → CMat α) : SRole Γ T Sl C → CMat α :=
  mkS (fun g t => (M (εX t g)).Φ (tt (K.tv t))) (fun g t => (M (εX t g)).Φ 0) Z c

/-- frames at the END of a stage. -/
def sOut (K : Circuit H T Sl C) (εX : T → Γ ≃ Γ) (M : Γ → XMap H α) (Z : Γ → Sl → CMat α)
    (c : Γ → C → CMat α) : SRole Γ T Sl C → CMat α :=
  mkS (fun g t => (M (εX t g)).Φ 1) (fun g t => (M (εX t g)).Φ (1 + tt (K.tv t))) Z c

lemma sIn_sem (K : Circuit H T Sl C) (εX : T → Γ ≃ Γ) (εS : Γ ≃ Γ) (M : Γ → XMap H α)
    (Z : Γ → Sl → CMat α) (c : Γ → C → CMat α) (d : Γ) :
    sIn K εX M Z c ∘ sem εX εS d = xin (M d) K (fun q => Z (εS d) q) (fun k => c (εS d) k) := by
  funext b
  rcases b with ((t|t)|(q|k))
  · show (M (εX t ((εX t).symm d))).Φ (tt (K.tv t)) = (M d).Φ (tt (K.tv t))
    rw [Equiv.apply_symm_apply]
  · show (M (εX t ((εX t).symm d))).Φ 0 = (M d).Φ 0
    rw [Equiv.apply_symm_apply]
  · rfl
  · rfl

lemma sOut_sem (K : Circuit H T Sl C) (εX : T → Γ ≃ Γ) (εS : Γ ≃ Γ) (M : Γ → XMap H α)
    (Z : Γ → Sl → CMat α) (c : Γ → C → CMat α) (d : Γ) :
    sOut K εX M Z c ∘ sem εX εS d = xout (M d) K (fun q => Z (εS d) q) (fun k => c (εS d) k) := by
  funext b
  rcases b with ((t|t)|(q|k))
  · show (M (εX t ((εX t).symm d))).Φ 1 = (M d).Φ 1
    rw [Equiv.apply_symm_apply]
  · show (M (εX t ((εX t).symm d))).Φ (1 + tt (K.tv t)) = (M d).Φ (1 + tt (K.tv t))
    rw [Equiv.apply_symm_apply]
  · rfl
  · rfl

variable (X : XCircuit H T Sl C)

/-- **A forward stage on shared helper sets.**  The invocation `d` has the frame map `M d`,
an inverse `N0 d` of the frame of its base and the frame `Wn d` of its window; it serves the
bank pairs `(g,t)` with `εX t g = d` and uses the helper set and the copies `εS d`.  The helper
set `g` enters with ARBITRARY matrices `Z g q` and leaves with `Wn (εS⁻¹ g) * Z g q`; the
copies enter and leave with arbitrary matrices. -/
theorem sstage_fwd (εX : T → Γ ≃ Γ) (εS : Γ ≃ Γ) (M : Γ → XMap H α) (N0 Wn : Γ → CMat α)
    (hN : ∀ d, (M d).Φ 0 * N0 d = 1) (hW : ∀ d, (M d).Φ 1 = Wn d * (M d).Φ 0)
    (Z : Γ → Sl → CMat α) (c0 c1 : Γ → C → CMat α) :
    XRoute (sIn X.K εX M Z c0) (sOut X.K εX M (fun g q => Wn (εS.symm g) * Z g q) c1)
      GF (fun φ => (Fintype.card Γ : ℝ) * X.cost φ) := by
  refine sstage εX εS (h := shearF) (cost := X.cost) (fun d => ?_) (fun d x => ?_)
  · rw [sIn_sem, sOut_sem]
    exact xinvocation_fwd_dirty X (M d) (N0 d) (Wn (εS.symm (εS d))) (hN d)
      (by rw [Equiv.symm_apply_apply]; exact hW d) _ _ _
  · funext b
    rcases b with ((t|t)|(q|k)) <;> rfl

/-- **A backward stage on shared helper sets.** -/
theorem sstage_bwd (εX : T → Γ ≃ Γ) (εS : Γ ≃ Γ) (M : Γ → XMap H α) (N0 Wn : Γ → CMat α)
    (hN : ∀ d, (M d).Φ 0 * N0 d = 1) (hW : ∀ d, (M d).Φ 1 = Wn d * (M d).Φ 0)
    (Z : Γ → Sl → CMat α) (c0 c1 : Γ → C → CMat α) :
    XRoute (sIn X.K εX M Z c0) (sOut X.K εX M (fun g q => Wn (εS.symm g) * Z g q) c1)
      GB (fun φ => (Fintype.card Γ : ℝ) * X.cost φ) := by
  refine sstage εX εS (h := shearB) (cost := X.cost) (fun d => ?_) (fun d x => ?_)
  · rw [sIn_sem, sOut_sem]
    exact xinvocation_bwd_dirty X (M d) (N0 d) (Wn (εS.symm (εS d))) (hN d)
      (by rw [Equiv.symm_apply_apply]; exact hW d) _ _ _
  · funext b
    rcases b with ((t|t)|(q|k)) <;> rfl

end Stage
end
end RF
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.RF.sstage
#print axioms OAI.PowerSaving.RF.sstage_fwd
#print axioms OAI.PowerSaving.RF.sstage_bwd
