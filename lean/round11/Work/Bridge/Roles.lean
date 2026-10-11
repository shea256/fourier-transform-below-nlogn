import Work.Reframe.SNet
import Work.BlockApply.Copies

/-!
# (key: bridge-net) Roles of the BRIDGED word: TWO bank pairs per class

Every class `(g,t) : Γ × T` owns two bank pairs (twins: same line), every `g : Γ` one helper
set and one set of scratch copies:

    live     X1(g,t), Y1(g,t), X2(g,t), Y2(g,t)     Γ × T each
             S(g,q)                                  Γ × Sl
    scratch  C(g,c)                                  Γ × C

* `BLive`, `BRole`, constructors `kX1 kY1 kX2 kY2 kS kC`, block-wise functions `mkB`;
* `em1`, `em2`: the one-pair roles `RF.SRole` (pair, helper set, copies) embedded as pair 1
  resp. pair 2 of the bridged roles;
* `blift1`, `blift2`: a route on the one-pair roles is a route on the bridged roles in which
  the other pair is untouched (`XRoute.lift`);
* `gateP`: a layer of free gates `x i += k i * x (p i)` between roles with equal frames.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace BR
open Binary Matrix Finset RAM SS CB RF
noncomputable section

abbrev BLive (Γ T Sl : Type) := (((Γ × T) ⊕ (Γ × T)) ⊕ ((Γ × T) ⊕ (Γ × T))) ⊕ (Γ × Sl)
abbrev BRole (Γ T Sl C : Type) := BLive Γ T Sl ⊕ (Γ × C)

/-! Instances by hand: the default search for `DecidableEq` exceeds its size limit on these
types, and explicit instances keep the instance terms small.  The two stepping stones are
`local` to this section, so that they do not change the instances found for the one-pair
roles `RF.SRole`. -/
section Inst

set_option synthInstance.maxSize 4096 in
local instance bpairDec {A B : Type} [DecidableEq A] [DecidableEq B] :
    DecidableEq ((A × B) ⊕ (A × B)) := inferInstance

set_option synthInstance.maxSize 4096 in
local instance bquadDec {A B : Type} [DecidableEq A] [DecidableEq B] :
    DecidableEq (((A × B) ⊕ (A × B)) ⊕ ((A × B) ⊕ (A × B))) := inferInstance

set_option synthInstance.maxSize 4096 in
instance bliveDec {Γ T Sl : Type} [DecidableEq Γ] [DecidableEq T] [DecidableEq Sl] :
    DecidableEq (BLive Γ T Sl) := inferInstance

set_option synthInstance.maxSize 4096 in
instance broleDec {Γ T Sl C : Type} [DecidableEq Γ] [DecidableEq T] [DecidableEq Sl]
    [DecidableEq C] : DecidableEq (BRole Γ T Sl C) := inferInstance

end Inst

instance bliveFin {Γ T Sl : Type} [Fintype Γ] [Fintype T] [Fintype Sl] :
    Fintype (BLive Γ T Sl) := inferInstance
instance broleFin {Γ T Sl C : Type} [Fintype Γ] [Fintype T] [Fintype Sl] [Fintype C] :
    Fintype (BRole Γ T Sl C) := inferInstance

section Roles
variable {Γ T Sl C : Type}

def kX1 (k : Γ × T) : BRole Γ T Sl C := .inl (.inl (.inl (.inl k)))
def kY1 (k : Γ × T) : BRole Γ T Sl C := .inl (.inl (.inl (.inr k)))
def kX2 (k : Γ × T) : BRole Γ T Sl C := .inl (.inl (.inr (.inl k)))
def kY2 (k : Γ × T) : BRole Γ T Sl C := .inl (.inl (.inr (.inr k)))
def kS (k : Γ × Sl) : BRole Γ T Sl C := .inl (.inr k)
def kC (k : Γ × C) : BRole Γ T Sl C := .inr k

/-- a function on the roles, block by block. -/
def mkB {β : Type*} (fX1 fY1 fX2 fY2 : Γ → T → β) (fS : Γ → Sl → β) (fC : Γ → C → β) :
    BRole Γ T Sl C → β
  | .inl (.inl (.inl (.inl (g,t)))) => fX1 g t
  | .inl (.inl (.inl (.inr (g,t)))) => fY1 g t
  | .inl (.inl (.inr (.inl (g,t)))) => fX2 g t
  | .inl (.inl (.inr (.inr (g,t)))) => fY2 g t
  | .inl (.inr (g,q)) => fS g q
  | .inr (g,c) => fC g c

lemma mkB_map {β γ : Type*} (h : β → γ) (fX1 fY1 fX2 fY2 : Γ → T → β) (fS : Γ → Sl → β)
    (fC : Γ → C → β) (r : BRole Γ T Sl C) :
    h (mkB fX1 fY1 fX2 fY2 fS fC r) = mkB (fun g t => h (fX1 g t)) (fun g t => h (fY1 g t))
      (fun g t => h (fX2 g t)) (fun g t => h (fY2 g t))
      (fun g q => h (fS g q)) (fun g c => h (fC g c)) r := by
  rcases r with ((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|⟨g,q⟩)|⟨g,c⟩) <;> rfl

lemma sum_mkB [Fintype Γ] [Fintype T] [Fintype Sl] [Fintype C]
    (fX1 fY1 fX2 fY2 : Γ → T → ℝ) (fS : Γ → Sl → ℝ) (fC : Γ → C → ℝ) :
    ∑ r : BRole Γ T Sl C, mkB fX1 fY1 fX2 fY2 fS fC r
      = ∑ g, ∑ t, fX1 g t + ∑ g, ∑ t, fY1 g t + ∑ g, ∑ t, fX2 g t + ∑ g, ∑ t, fY2 g t
        + ∑ g, ∑ q, fS g q + ∑ g, ∑ c, fC g c := by
  simp only [Fintype.sum_sum_type, mkB, Fintype.sum_prod_type]
  ring

/-- live roles of the bridged word: four bank roles per class, one helper set per `g`. -/
lemma card_BLive [Fintype Γ] [Fintype T] [Fintype Sl] :
    Fintype.card (BLive Γ T Sl) = Fintype.card Γ * (4 * Fintype.card T + Fintype.card Sl) := by
  simp only [Fintype.card_sum, Fintype.card_prod]
  ring

/-- the one-pair roles as PAIR 1 of the bridged roles. -/
def pos1 : SRole Γ T Sl C → BRole Γ T Sl C :=
  mkS (fun g t => kX1 (g,t)) (fun g t => kY1 (g,t)) (fun g q => kS (g,q)) (fun g c => kC (g,c))

/-- the one-pair roles as PAIR 2 of the bridged roles. -/
def pos2 : SRole Γ T Sl C → BRole Γ T Sl C :=
  mkS (fun g t => kX2 (g,t)) (fun g t => kY2 (g,t)) (fun g q => kS (g,q)) (fun g c => kC (g,c))

lemma pos1_inj : Function.Injective (pos1 : SRole Γ T Sl C → BRole Γ T Sl C) := by
  rintro (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩) (((⟨g',t'⟩|⟨g',t'⟩)|⟨g',q'⟩)|⟨g',c'⟩) h <;>
    simp only [pos1, mkS, kX1, kY1, kS, kC, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq,
      reduceCtorEq] at h <;>
    (obtain ⟨h1, h2⟩ := h; subst h1; subst h2; rfl)

lemma pos2_inj : Function.Injective (pos2 : SRole Γ T Sl C → BRole Γ T Sl C) := by
  rintro (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩) (((⟨g',t'⟩|⟨g',t'⟩)|⟨g',q'⟩)|⟨g',c'⟩) h <;>
    simp only [pos2, mkS, kX2, kY2, kS, kC, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq,
      reduceCtorEq] at h <;>
    (obtain ⟨h1, h2⟩ := h; subst h1; subst h2; rfl)

def em1 : SRole Γ T Sl C ↪ BRole Γ T Sl C := ⟨pos1, pos1_inj⟩
def em2 : SRole Γ T Sl C ↪ BRole Γ T Sl C := ⟨pos2, pos2_inj⟩

/-- scalar map of a route on pair 1: pair 2 untouched. -/
def lift1 (h : (SRole Γ T Sl C → ℂ) → (SRole Γ T Sl C → ℂ)) (x : BRole Γ T Sl C → ℂ) :
    BRole Γ T Sl C → ℂ :=
  mkB (fun g t => h (x ∘ pos1) (jX (g,t))) (fun g t => h (x ∘ pos1) (jY (g,t)))
    (fun g t => x (kX2 (g,t))) (fun g t => x (kY2 (g,t)))
    (fun g q => h (x ∘ pos1) (jS (g,q))) (fun g c => h (x ∘ pos1) (jC (g,c)))

/-- scalar map of a route on pair 2: pair 1 untouched. -/
def lift2 (h : (SRole Γ T Sl C → ℂ) → (SRole Γ T Sl C → ℂ)) (x : BRole Γ T Sl C → ℂ) :
    BRole Γ T Sl C → ℂ :=
  mkB (fun g t => x (kX1 (g,t))) (fun g t => x (kY1 (g,t)))
    (fun g t => h (x ∘ pos2) (jX (g,t))) (fun g t => h (x ∘ pos2) (jY (g,t)))
    (fun g q => h (x ∘ pos2) (jS (g,q))) (fun g c => h (x ∘ pos2) (jC (g,c)))

end Roles

section Lift
variable {Γ T Sl C α : Type} [Fintype α] [DecidableEq α]
  [Fintype Γ] [DecidableEq Γ] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]

/-- **A route on pair 1.**  A route on the one-pair roles, run on the pairs `(X1,Y1)`, the
helper sets and the copies; the pairs `(X2,Y2)` keep their matrices `PX`, `PY` and their
contents. -/
theorem blift1 {SX SY UX UY : Γ → T → CMat α} (PX PY : Γ → T → CMat α)
    {SS US : Γ → Sl → CMat α} {SC UC : Γ → C → CMat α}
    {h : (SRole Γ T Sl C → ℂ) → (SRole Γ T Sl C → ℂ)} {c : (ℕ → ℝ) → ℝ}
    (q : XRoute (mkS SX SY SS SC) (mkS UX UY US UC) h c) :
    XRoute (mkB SX SY PX PY SS SC) (mkB UX UY PX PY US UC) (lift1 h) c := by
  refine XRoute.lift (em1 (Γ := Γ) (T := T) (Sl := Sl) (C := C)) (h := h) ?_
    (fun x => ?_) (fun x i hi => ?_) (fun i hi => ?_)
  · have e1 : mkB SX SY PX PY SS SC ∘ (em1 (Γ := Γ) (T := T) (Sl := Sl) (C := C))
        = mkS SX SY SS SC := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩) <;> rfl
    have e2 : mkB UX UY PX PY US UC ∘ (em1 (Γ := Γ) (T := T) (Sl := Sl) (C := C))
        = mkS UX UY US UC := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩) <;> rfl
    rw [e1, e2]
    exact q
  · funext r
    rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩) <;> rfl
  · rcases i with ((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|⟨g,q⟩)|⟨g,c⟩)
    · exact absurd ((cover_iff _ _).mpr ⟨jX (g,t), rfl⟩) hi
    · exact absurd ((cover_iff _ _).mpr ⟨jY (g,t), rfl⟩) hi
    · rfl
    · rfl
    · exact absurd ((cover_iff _ _).mpr ⟨jS (g,q), rfl⟩) hi
    · exact absurd ((cover_iff _ _).mpr ⟨jC (g,c), rfl⟩) hi
  · rcases i with ((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|⟨g,q⟩)|⟨g,c⟩)
    · exact absurd ((cover_iff _ _).mpr ⟨jX (g,t), rfl⟩) hi
    · exact absurd ((cover_iff _ _).mpr ⟨jY (g,t), rfl⟩) hi
    · rfl
    · rfl
    · exact absurd ((cover_iff _ _).mpr ⟨jS (g,q), rfl⟩) hi
    · exact absurd ((cover_iff _ _).mpr ⟨jC (g,c), rfl⟩) hi

/-- **A route on pair 2**; the pairs `(X1,Y1)` keep their matrices and their contents. -/
theorem blift2 (PX PY : Γ → T → CMat α) {SX SY UX UY : Γ → T → CMat α}
    {SS US : Γ → Sl → CMat α} {SC UC : Γ → C → CMat α}
    {h : (SRole Γ T Sl C → ℂ) → (SRole Γ T Sl C → ℂ)} {c : (ℕ → ℝ) → ℝ}
    (q : XRoute (mkS SX SY SS SC) (mkS UX UY US UC) h c) :
    XRoute (mkB PX PY SX SY SS SC) (mkB PX PY UX UY US UC) (lift2 h) c := by
  refine XRoute.lift (em2 (Γ := Γ) (T := T) (Sl := Sl) (C := C)) (h := h) ?_
    (fun x => ?_) (fun x i hi => ?_) (fun i hi => ?_)
  · have e1 : mkB PX PY SX SY SS SC ∘ (em2 (Γ := Γ) (T := T) (Sl := Sl) (C := C))
        = mkS SX SY SS SC := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩) <;> rfl
    have e2 : mkB PX PY UX UY US UC ∘ (em2 (Γ := Γ) (T := T) (Sl := Sl) (C := C))
        = mkS UX UY US UC := by
      funext r
      rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩) <;> rfl
    rw [e1, e2]
    exact q
  · funext r
    rcases r with (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩) <;> rfl
  · rcases i with ((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|⟨g,q⟩)|⟨g,c⟩)
    · rfl
    · rfl
    · exact absurd ((cover_iff _ _).mpr ⟨jX (g,t), rfl⟩) hi
    · exact absurd ((cover_iff _ _).mpr ⟨jY (g,t), rfl⟩) hi
    · exact absurd ((cover_iff _ _).mpr ⟨jS (g,q), rfl⟩) hi
    · exact absurd ((cover_iff _ _).mpr ⟨jC (g,c), rfl⟩) hi
  · rcases i with ((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|⟨g,q⟩)|⟨g,c⟩)
    · rfl
    · rfl
    · exact absurd ((cover_iff _ _).mpr ⟨jX (g,t), rfl⟩) hi
    · exact absurd ((cover_iff _ _).mpr ⟨jY (g,t), rfl⟩) hi
    · exact absurd ((cover_iff _ _).mpr ⟨jS (g,q), rfl⟩) hi
    · exact absurd ((cover_iff _ _).mpr ⟨jC (g,c), rfl⟩) hi

end Lift

section Gate
variable {α ρ : Type} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

/-- matrix of a layer of gates: every role `i` receives `k i` times the role `p i`. -/
def gateM (p : ρ → ρ) (k : ρ → ℚ) : Matrix ρ ρ ℚ :=
  fun i j => (if j = i then 1 else 0) + (if j = p i then k i else 0)

lemma actPoint_gateM (p : ρ → ρ) (k : ρ → ℚ) (x : ρ → ℂ) (i : ρ) :
    actPoint (gateM p k) x i = x i + (k i : ℂ) * x (p i) := by
  unfold actPoint gateM
  simp only [Rat.cast_add, add_mul, Finset.sum_add_distrib]
  congr 1
  · rw [sum_eq_single i]
    · simp
    · intro j _ hj; simp [hj]
    · simp
  · rw [sum_eq_single (p i)]
    · simp
    · intro j _ hj; simp [hj]
    · simp

/-- **A layer of free gates between roles with equal frames**: no block, no frame moves. -/
theorem gateP (p : ρ → ρ) (k : ρ → ℚ) (S : ρ → CMat α) (h : ∀ i, k i ≠ 0 → S i = S (p i)) :
    XRoute S S (fun x i => x i + (k i : ℂ) * x (p i)) (fun _ => 0) := by
  refine (XRoute.gate (gateM p k) S S (fun i j hne => ?_)).castg
    (funext fun x => funext fun i => actPoint_gateM p k x i)
  by_cases hj : j = i
  · rw [hj]
  · by_cases hp : j = p i
    · subst hp
      refine h i (fun hk => hne ?_)
      simp [gateM, hj, hk]
    · exact absurd (by simp [gateM, hj, hp]) hne

end Gate
end
end BR
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.BR.blift1
#print axioms OAI.PowerSaving.BR.blift2
#print axioms OAI.PowerSaving.BR.gateP
