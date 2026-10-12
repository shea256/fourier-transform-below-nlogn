import Work.Bridge.Roles

/-!
# (key: bridge-401) Roles of the compressed nine-stage word (PR #377), replica-outer runs

Credits: the entrance gauges and the residual banks are Dugongue's (CrocSwap/integer-mult-bounds PR #401); the bank
patterns are Lydakis's (#275); the compressed nine-stage layout is jacklightChen's (#377); the bridged word B_K is
DaysSky's (#363); B_2, the engine, the stage geometry and the E8 unit are Jacob Sussman's (wht-power-saving-lean,
Apache-2.0).  Written by w-newsums/gen401/gen401.py (from gen377.py).

* `BDat4 Γ T`: the data of ONE replica, 4 bank pairs `X_p`, `Y_p` per class `(g,t)` (as `BLiveK4` of B_4);
* `BRun4 Γ T nb C`: the roles of ONE run: the data of its replica, the 9 bank families `Γ × (Fin 9 × Sl)`
  (stage `l` uses the family `l`), the copies `Γ × C`;
* `BLive401 Γ T nb`, `BRole401 Γ T nb C`: all 8 replicas, the 9 bank families, the copies;
* `posR<l>`: the one-pair roles as the roles of stage `l` of a run; `liftR<l>`: the scalar map of such a stage;
* `runPos4 ρ`: the roles of a run as the roles of replica `ρ`; `liftRun4 ρ`: the scalar map of run `ρ`.
No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace OAI
namespace PowerSaving
namespace GX
open Binary Matrix Finset RAM SS CB RF
noncomputable section

abbrev BDat4 (Γ T : Type) := (((((Γ × T) ⊕ (Γ × T)) ⊕ ((Γ × T) ⊕ (Γ × T))) ⊕ ((Γ × T) ⊕ (Γ × T))) ⊕ ((Γ × T) ⊕ (Γ × T)))
abbrev BRunL4 (Γ T : Type) (nb : ℕ) := BDat4 Γ T ⊕ (Γ × Fin nb)
abbrev BRun4 (Γ T : Type) (nb : ℕ) (C : Type) := BRunL4 Γ T nb ⊕ (Γ × C)
abbrev BLive401 (Γ T : Type) (nb : ℕ) := (Fin 8 × BDat4 Γ T) ⊕ (Γ × Fin nb)
abbrev BRole401 (Γ T : Type) (nb : ℕ) (C : Type) := BLive401 Γ T nb ⊕ (Γ × C)

section Inst
set_option synthInstance.maxSize 4096 in
local instance b401step0Dec {A B : Type} [DecidableEq A] [DecidableEq B] :
    DecidableEq ((A × B) ⊕ (A × B)) := inferInstance
set_option synthInstance.maxSize 4096 in
local instance b401step1Dec {A B : Type} [DecidableEq A] [DecidableEq B] :
    DecidableEq (((A × B) ⊕ (A × B)) ⊕ ((A × B) ⊕ (A × B))) := inferInstance
set_option synthInstance.maxSize 4096 in
local instance b401step2Dec {A B : Type} [DecidableEq A] [DecidableEq B] :
    DecidableEq ((((A × B) ⊕ (A × B)) ⊕ ((A × B) ⊕ (A × B))) ⊕ ((A × B) ⊕ (A × B))) := inferInstance
set_option synthInstance.maxSize 4096 in
local instance b401step3Dec {A B : Type} [DecidableEq A] [DecidableEq B] :
    DecidableEq (((((A × B) ⊕ (A × B)) ⊕ ((A × B) ⊕ (A × B))) ⊕ ((A × B) ⊕ (A × B))) ⊕ ((A × B) ⊕ (A × B))) := inferInstance
set_option synthInstance.maxSize 4096 in
instance b401datDec {Γ T : Type} [DecidableEq Γ] [DecidableEq T] : DecidableEq (BDat4 Γ T) := inferInstance

set_option synthInstance.maxSize 4096 in
instance b401runDec {Γ T C : Type} {nb : ℕ} [DecidableEq Γ] [DecidableEq T] [DecidableEq C] :
    DecidableEq (BRun4 Γ T nb C) := inferInstance

set_option synthInstance.maxSize 4096 in
instance b401liveDec {Γ T : Type} {nb : ℕ} [DecidableEq Γ] [DecidableEq T] :
    DecidableEq (BLive401 Γ T nb) := inferInstance

set_option synthInstance.maxSize 4096 in
instance b401roleDec {Γ T C : Type} {nb : ℕ} [DecidableEq Γ] [DecidableEq T] [DecidableEq C] :
    DecidableEq (BRole401 Γ T nb C) := inferInstance

end Inst

instance b401datFin {Γ T : Type} [Fintype Γ] [Fintype T] : Fintype (BDat4 Γ T) := inferInstance
instance b401runFin {Γ T C : Type} {nb : ℕ} [Fintype Γ] [Fintype T] [Fintype C] :
    Fintype (BRun4 Γ T nb C) := inferInstance
instance b401liveFin {Γ T : Type} {nb : ℕ} [Fintype Γ] [Fintype T] :
    Fintype (BLive401 Γ T nb) := inferInstance
instance b401roleFin {Γ T C : Type} {nb : ℕ} [Fintype Γ] [Fintype T] [Fintype C] :
    Fintype (BRole401 Γ T nb C) := inferInstance

section Roles
variable {Γ T Sl C : Type} {nb : ℕ}

def dqX1 (k : Γ × T) : BDat4 Γ T := Sum.inl (Sum.inl (Sum.inl (Sum.inl (k))))
def dqY1 (k : Γ × T) : BDat4 Γ T := Sum.inl (Sum.inl (Sum.inl (Sum.inr (k))))
def dqX2 (k : Γ × T) : BDat4 Γ T := Sum.inl (Sum.inl (Sum.inr (Sum.inl (k))))
def dqY2 (k : Γ × T) : BDat4 Γ T := Sum.inl (Sum.inl (Sum.inr (Sum.inr (k))))
def dqX3 (k : Γ × T) : BDat4 Γ T := Sum.inl (Sum.inr (Sum.inl (k)))
def dqY3 (k : Γ × T) : BDat4 Γ T := Sum.inl (Sum.inr (Sum.inr (k)))
def dqX4 (k : Γ × T) : BDat4 Γ T := Sum.inr (Sum.inl (k))
def dqY4 (k : Γ × T) : BDat4 Γ T := Sum.inr (Sum.inr (k))
def rqX1 (k : Γ × T) : BRun4 Γ T nb C := Sum.inl (Sum.inl (dqX1 k))
def rqY1 (k : Γ × T) : BRun4 Γ T nb C := Sum.inl (Sum.inl (dqY1 k))
def rqX2 (k : Γ × T) : BRun4 Γ T nb C := Sum.inl (Sum.inl (dqX2 k))
def rqY2 (k : Γ × T) : BRun4 Γ T nb C := Sum.inl (Sum.inl (dqY2 k))
def rqX3 (k : Γ × T) : BRun4 Γ T nb C := Sum.inl (Sum.inl (dqX3 k))
def rqY3 (k : Γ × T) : BRun4 Γ T nb C := Sum.inl (Sum.inl (dqY3 k))
def rqX4 (k : Γ × T) : BRun4 Γ T nb C := Sum.inl (Sum.inl (dqX4 k))
def rqY4 (k : Γ × T) : BRun4 Γ T nb C := Sum.inl (Sum.inl (dqY4 k))
def rqS (k : Γ × Fin nb) : BRun4 Γ T nb C := Sum.inl (Sum.inr k)
def rqC (k : Γ × C) : BRun4 Γ T nb C := Sum.inr k

/-- a function on the data of one replica, block by block. -/
def mkD4 {β : Type*} (fX1 fY1 fX2 fY2 fX3 fY3 fX4 fY4 : Γ → T → β) : BDat4 Γ T → β
  | .inl (.inl (.inl (.inl (g,t)))) => fX1 g t
  | .inl (.inl (.inl (.inr (g,t)))) => fY1 g t
  | .inl (.inl (.inr (.inl (g,t)))) => fX2 g t
  | .inl (.inl (.inr (.inr (g,t)))) => fY2 g t
  | .inl (.inr (.inl (g,t))) => fX3 g t
  | .inl (.inr (.inr (g,t))) => fY3 g t
  | .inr (.inl (g,t)) => fX4 g t
  | .inr (.inr (g,t)) => fY4 g t

/-- a function on the roles of a run. -/
def mkR4 {β : Type*} (fX1 fY1 fX2 fY2 fX3 fY3 fX4 fY4 : Γ → T → β) (fS : Γ → Fin nb → β) (fC : Γ → C → β) :
    BRun4 Γ T nb C → β
  | .inl (.inl d) => mkD4 fX1 fY1 fX2 fY2 fX3 fY3 fX4 fY4 d
  | .inl (.inr (g, b)) => fS g b
  | .inr (g, c) => fC g c

/-- a function on all roles. -/
def mk401 {β : Type*} (fD : Fin 8 → BDat4 Γ T → β) (fS : Γ → Fin nb → β) (fC : Γ → C → β) :
    BRole401 Γ T nb C → β
  | .inl (.inl (ρ, d)) => fD ρ d
  | .inl (.inr (g, b)) => fS g b
  | .inr (g, c) => fC g c

lemma mkD4_map {β γ : Type*} (h : β → γ) (fX1 fY1 fX2 fY2 fX3 fY3 fX4 fY4 : Γ → T → β) (d : BDat4 Γ T) :
    h (mkD4 fX1 fY1 fX2 fY2 fX3 fY3 fX4 fY4 d) = mkD4 (fun g t => h (fX1 g t)) (fun g t => h (fY1 g t)) (fun g t => h (fX2 g t)) (fun g t => h (fY2 g t)) (fun g t => h (fX3 g t)) (fun g t => h (fY3 g t)) (fun g t => h (fX4 g t)) (fun g t => h (fY4 g t)) d := by
  rcases d with ((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩)) <;> rfl

lemma mkR4_map {β γ : Type*} (h : β → γ) (fX1 fY1 fX2 fY2 fX3 fY3 fX4 fY4 : Γ → T → β)
    (fS : Γ → Fin nb → β) (fC : Γ → C → β) (r : BRun4 Γ T nb C) :
    h (mkR4 fX1 fY1 fX2 fY2 fX3 fY3 fX4 fY4 fS fC r) = mkR4 (fun g t => h (fX1 g t)) (fun g t => h (fY1 g t)) (fun g t => h (fX2 g t)) (fun g t => h (fY2 g t)) (fun g t => h (fX3 g t)) (fun g t => h (fY3 g t)) (fun g t => h (fX4 g t)) (fun g t => h (fY4 g t))
      (fun g b => h (fS g b)) (fun g c => h (fC g c)) r := by
  rcases r with ((((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)|⟨g,c⟩) <;> rfl

lemma mk401_map {β γ : Type*} (h : β → γ) (fD : Fin 8 → BDat4 Γ T → β) (fS : Γ → Fin nb → β)
    (fC : Γ → C → β) (r : BRole401 Γ T nb C) :
    h (mk401 fD fS fC r) = mk401 (fun ρ d => h (fD ρ d)) (fun g b => h (fS g b)) (fun g c => h (fC g c)) r := by
  rcases r with ((⟨ρ,d⟩|⟨g,b⟩)|⟨g,c⟩) <;> rfl

lemma sum_mkD4 [Fintype Γ] [Fintype T] (fX1 fY1 fX2 fY2 fX3 fY3 fX4 fY4 : Γ → T → ℝ) :
    ∑ d : BDat4 Γ T, mkD4 fX1 fY1 fX2 fY2 fX3 fY3 fX4 fY4 d = ∑ g, ∑ t, fX1 g t + ∑ g, ∑ t, fY1 g t + ∑ g, ∑ t, fX2 g t + ∑ g, ∑ t, fY2 g t + ∑ g, ∑ t, fX3 g t + ∑ g, ∑ t, fY3 g t + ∑ g, ∑ t, fX4 g t + ∑ g, ∑ t, fY4 g t := by
  simp only [Fintype.sum_sum_type, mkD4, Fintype.sum_prod_type]
  ring

lemma sum_mkR4 [Fintype Γ] [Fintype T] [Fintype C]
    (fX1 fY1 fX2 fY2 fX3 fY3 fX4 fY4 : Γ → T → ℝ) (fS : Γ → Fin nb → ℝ) (fC : Γ → C → ℝ) :
    ∑ r : BRun4 Γ T nb C, mkR4 fX1 fY1 fX2 fY2 fX3 fY3 fX4 fY4 fS fC r
      = ∑ g, ∑ t, fX1 g t + ∑ g, ∑ t, fY1 g t + ∑ g, ∑ t, fX2 g t + ∑ g, ∑ t, fY2 g t + ∑ g, ∑ t, fX3 g t + ∑ g, ∑ t, fY3 g t + ∑ g, ∑ t, fX4 g t + ∑ g, ∑ t, fY4 g t + ∑ g, ∑ b, fS g b + ∑ g, ∑ c, fC g c := by
  simp only [Fintype.sum_sum_type, mkR4, mkD4, Fintype.sum_prod_type]
  ring

lemma sum_mk401 [Fintype Γ] [Fintype T] [Fintype C]
    (fD : Fin 8 → BDat4 Γ T → ℝ) (fS : Γ → Fin nb → ℝ) (fC : Γ → C → ℝ) :
    ∑ r : BRole401 Γ T nb C, mk401 fD fS fC r
      = ∑ ρ, ∑ d, fD ρ d + ∑ g, ∑ b, fS g b + ∑ g, ∑ c, fC g c := by
  simp only [Fintype.sum_sum_type, mk401, Fintype.sum_prod_type]

/-- live roles of the #401 word: 8 replicas of 8 data roles per class, `nb` banks per `g`. -/
lemma card_BLive401 [Fintype Γ] [Fintype T] :
    Fintype.card (BLive401 Γ T nb) = Fintype.card Γ * (64 * Fintype.card T + nb) := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  ring

/-- the one-pair roles as the roles of STAGE 0 of a run: pair 1, bank family 0. -/
def posQ0 (u : Sl → Fin nb) : SRole Γ T Sl C → BRun4 Γ T nb C :=
  mkS (fun g t => rqX1 (g,t)) (fun g t => rqY1 (g,t)) (fun g q => rqS (g, u q)) (fun g c => rqC (g,c))

lemma posQ0_inj {u : Sl → Fin nb} (hu : Function.Injective u) :
    Function.Injective (posQ0 u : SRole Γ T Sl C → BRun4 Γ T nb C) := by
  rintro (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩) (((⟨g',t'⟩|⟨g',t'⟩)|⟨g',q'⟩)|⟨g',c'⟩) h <;>
    simp only [posQ0, mkS, rqX1, rqY1, dqX1, dqY1, rqS, rqC, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq,
      reduceCtorEq, eq_self_iff_true, true_and, and_true] at h <;>
    (obtain ⟨h1, h2⟩ := h; subst h1; first | (subst h2; rfl) | rw [hu h2])

def emQ0 (u : Sl → Fin nb) (hu : Function.Injective u) : SRole Γ T Sl C ↪ BRun4 Γ T nb C :=
  ⟨posQ0 u, posQ0_inj hu⟩

/-- the one-pair roles as the roles of STAGE 1 of a run: pair 1, bank family 1. -/
def posQ1 (u : Sl → Fin nb) : SRole Γ T Sl C → BRun4 Γ T nb C :=
  mkS (fun g t => rqX1 (g,t)) (fun g t => rqY1 (g,t)) (fun g q => rqS (g, u q)) (fun g c => rqC (g,c))

lemma posQ1_inj {u : Sl → Fin nb} (hu : Function.Injective u) :
    Function.Injective (posQ1 u : SRole Γ T Sl C → BRun4 Γ T nb C) := by
  rintro (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩) (((⟨g',t'⟩|⟨g',t'⟩)|⟨g',q'⟩)|⟨g',c'⟩) h <;>
    simp only [posQ1, mkS, rqX1, rqY1, dqX1, dqY1, rqS, rqC, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq,
      reduceCtorEq, eq_self_iff_true, true_and, and_true] at h <;>
    (obtain ⟨h1, h2⟩ := h; subst h1; first | (subst h2; rfl) | rw [hu h2])

def emQ1 (u : Sl → Fin nb) (hu : Function.Injective u) : SRole Γ T Sl C ↪ BRun4 Γ T nb C :=
  ⟨posQ1 u, posQ1_inj hu⟩

/-- the one-pair roles as the roles of STAGE 2 of a run: pair 1, bank family 2. -/
def posQ2 (u : Sl → Fin nb) : SRole Γ T Sl C → BRun4 Γ T nb C :=
  mkS (fun g t => rqX1 (g,t)) (fun g t => rqY1 (g,t)) (fun g q => rqS (g, u q)) (fun g c => rqC (g,c))

lemma posQ2_inj {u : Sl → Fin nb} (hu : Function.Injective u) :
    Function.Injective (posQ2 u : SRole Γ T Sl C → BRun4 Γ T nb C) := by
  rintro (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩) (((⟨g',t'⟩|⟨g',t'⟩)|⟨g',q'⟩)|⟨g',c'⟩) h <;>
    simp only [posQ2, mkS, rqX1, rqY1, dqX1, dqY1, rqS, rqC, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq,
      reduceCtorEq, eq_self_iff_true, true_and, and_true] at h <;>
    (obtain ⟨h1, h2⟩ := h; subst h1; first | (subst h2; rfl) | rw [hu h2])

def emQ2 (u : Sl → Fin nb) (hu : Function.Injective u) : SRole Γ T Sl C ↪ BRun4 Γ T nb C :=
  ⟨posQ2 u, posQ2_inj hu⟩

/-- the one-pair roles as the roles of STAGE 3 of a run: pair 2, bank family 3. -/
def posQ3 (u : Sl → Fin nb) : SRole Γ T Sl C → BRun4 Γ T nb C :=
  mkS (fun g t => rqX2 (g,t)) (fun g t => rqY2 (g,t)) (fun g q => rqS (g, u q)) (fun g c => rqC (g,c))

lemma posQ3_inj {u : Sl → Fin nb} (hu : Function.Injective u) :
    Function.Injective (posQ3 u : SRole Γ T Sl C → BRun4 Γ T nb C) := by
  rintro (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩) (((⟨g',t'⟩|⟨g',t'⟩)|⟨g',q'⟩)|⟨g',c'⟩) h <;>
    simp only [posQ3, mkS, rqX2, rqY2, dqX2, dqY2, rqS, rqC, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq,
      reduceCtorEq, eq_self_iff_true, true_and, and_true] at h <;>
    (obtain ⟨h1, h2⟩ := h; subst h1; first | (subst h2; rfl) | rw [hu h2])

def emQ3 (u : Sl → Fin nb) (hu : Function.Injective u) : SRole Γ T Sl C ↪ BRun4 Γ T nb C :=
  ⟨posQ3 u, posQ3_inj hu⟩

/-- the one-pair roles as the roles of STAGE 4 of a run: pair 2, bank family 4. -/
def posQ4 (u : Sl → Fin nb) : SRole Γ T Sl C → BRun4 Γ T nb C :=
  mkS (fun g t => rqX2 (g,t)) (fun g t => rqY2 (g,t)) (fun g q => rqS (g, u q)) (fun g c => rqC (g,c))

lemma posQ4_inj {u : Sl → Fin nb} (hu : Function.Injective u) :
    Function.Injective (posQ4 u : SRole Γ T Sl C → BRun4 Γ T nb C) := by
  rintro (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩) (((⟨g',t'⟩|⟨g',t'⟩)|⟨g',q'⟩)|⟨g',c'⟩) h <;>
    simp only [posQ4, mkS, rqX2, rqY2, dqX2, dqY2, rqS, rqC, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq,
      reduceCtorEq, eq_self_iff_true, true_and, and_true] at h <;>
    (obtain ⟨h1, h2⟩ := h; subst h1; first | (subst h2; rfl) | rw [hu h2])

def emQ4 (u : Sl → Fin nb) (hu : Function.Injective u) : SRole Γ T Sl C ↪ BRun4 Γ T nb C :=
  ⟨posQ4 u, posQ4_inj hu⟩

/-- the one-pair roles as the roles of STAGE 5 of a run: pair 3, bank family 5. -/
def posQ5 (u : Sl → Fin nb) : SRole Γ T Sl C → BRun4 Γ T nb C :=
  mkS (fun g t => rqX3 (g,t)) (fun g t => rqY3 (g,t)) (fun g q => rqS (g, u q)) (fun g c => rqC (g,c))

lemma posQ5_inj {u : Sl → Fin nb} (hu : Function.Injective u) :
    Function.Injective (posQ5 u : SRole Γ T Sl C → BRun4 Γ T nb C) := by
  rintro (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩) (((⟨g',t'⟩|⟨g',t'⟩)|⟨g',q'⟩)|⟨g',c'⟩) h <;>
    simp only [posQ5, mkS, rqX3, rqY3, dqX3, dqY3, rqS, rqC, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq,
      reduceCtorEq, eq_self_iff_true, true_and, and_true] at h <;>
    (obtain ⟨h1, h2⟩ := h; subst h1; first | (subst h2; rfl) | rw [hu h2])

def emQ5 (u : Sl → Fin nb) (hu : Function.Injective u) : SRole Γ T Sl C ↪ BRun4 Γ T nb C :=
  ⟨posQ5 u, posQ5_inj hu⟩

/-- the one-pair roles as the roles of STAGE 6 of a run: pair 3, bank family 6. -/
def posQ6 (u : Sl → Fin nb) : SRole Γ T Sl C → BRun4 Γ T nb C :=
  mkS (fun g t => rqX3 (g,t)) (fun g t => rqY3 (g,t)) (fun g q => rqS (g, u q)) (fun g c => rqC (g,c))

lemma posQ6_inj {u : Sl → Fin nb} (hu : Function.Injective u) :
    Function.Injective (posQ6 u : SRole Γ T Sl C → BRun4 Γ T nb C) := by
  rintro (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩) (((⟨g',t'⟩|⟨g',t'⟩)|⟨g',q'⟩)|⟨g',c'⟩) h <;>
    simp only [posQ6, mkS, rqX3, rqY3, dqX3, dqY3, rqS, rqC, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq,
      reduceCtorEq, eq_self_iff_true, true_and, and_true] at h <;>
    (obtain ⟨h1, h2⟩ := h; subst h1; first | (subst h2; rfl) | rw [hu h2])

def emQ6 (u : Sl → Fin nb) (hu : Function.Injective u) : SRole Γ T Sl C ↪ BRun4 Γ T nb C :=
  ⟨posQ6 u, posQ6_inj hu⟩

/-- the one-pair roles as the roles of STAGE 7 of a run: pair 4, bank family 7. -/
def posQ7 (u : Sl → Fin nb) : SRole Γ T Sl C → BRun4 Γ T nb C :=
  mkS (fun g t => rqX4 (g,t)) (fun g t => rqY4 (g,t)) (fun g q => rqS (g, u q)) (fun g c => rqC (g,c))

lemma posQ7_inj {u : Sl → Fin nb} (hu : Function.Injective u) :
    Function.Injective (posQ7 u : SRole Γ T Sl C → BRun4 Γ T nb C) := by
  rintro (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩) (((⟨g',t'⟩|⟨g',t'⟩)|⟨g',q'⟩)|⟨g',c'⟩) h <;>
    simp only [posQ7, mkS, rqX4, rqY4, dqX4, dqY4, rqS, rqC, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq,
      reduceCtorEq, eq_self_iff_true, true_and, and_true] at h <;>
    (obtain ⟨h1, h2⟩ := h; subst h1; first | (subst h2; rfl) | rw [hu h2])

def emQ7 (u : Sl → Fin nb) (hu : Function.Injective u) : SRole Γ T Sl C ↪ BRun4 Γ T nb C :=
  ⟨posQ7 u, posQ7_inj hu⟩

/-- the one-pair roles as the roles of STAGE 8 of a run: pair 4, bank family 8. -/
def posQ8 (u : Sl → Fin nb) : SRole Γ T Sl C → BRun4 Γ T nb C :=
  mkS (fun g t => rqX4 (g,t)) (fun g t => rqY4 (g,t)) (fun g q => rqS (g, u q)) (fun g c => rqC (g,c))

lemma posQ8_inj {u : Sl → Fin nb} (hu : Function.Injective u) :
    Function.Injective (posQ8 u : SRole Γ T Sl C → BRun4 Γ T nb C) := by
  rintro (((⟨g,t⟩|⟨g,t⟩)|⟨g,q⟩)|⟨g,c⟩) (((⟨g',t'⟩|⟨g',t'⟩)|⟨g',q'⟩)|⟨g',c'⟩) h <;>
    simp only [posQ8, mkS, rqX4, rqY4, dqX4, dqY4, rqS, rqC, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq,
      reduceCtorEq, eq_self_iff_true, true_and, and_true] at h <;>
    (obtain ⟨h1, h2⟩ := h; subst h1; first | (subst h2; rfl) | rw [hu h2])

def emQ8 (u : Sl → Fin nb) (hu : Function.Injective u) : SRole Γ T Sl C ↪ BRun4 Γ T nb C :=
  ⟨posQ8 u, posQ8_inj hu⟩

/-- scalar map of stage 0 on a run: pair 1 moves, the banks keep their contents. -/
def liftQ0 (u : Sl → Fin nb) (h : (SRole Γ T Sl C → ℂ) → (SRole Γ T Sl C → ℂ)) (x : BRun4 Γ T nb C → ℂ) :
    BRun4 Γ T nb C → ℂ :=
  mkR4 (fun g t => h (x ∘ posQ0 u) (jX (g,t))) (fun g t => h (x ∘ posQ0 u) (jY (g,t))) (fun g t => x (rqX2 (g,t))) (fun g t => x (rqY2 (g,t))) (fun g t => x (rqX3 (g,t))) (fun g t => x (rqY3 (g,t))) (fun g t => x (rqX4 (g,t))) (fun g t => x (rqY4 (g,t))) (fun g b => x (rqS (g,b))) (fun g c => h (x ∘ posQ0 u) (jC (g,c)))

/-- scalar map of stage 1 on a run: pair 1 moves, the banks keep their contents. -/
def liftQ1 (u : Sl → Fin nb) (h : (SRole Γ T Sl C → ℂ) → (SRole Γ T Sl C → ℂ)) (x : BRun4 Γ T nb C → ℂ) :
    BRun4 Γ T nb C → ℂ :=
  mkR4 (fun g t => h (x ∘ posQ1 u) (jX (g,t))) (fun g t => h (x ∘ posQ1 u) (jY (g,t))) (fun g t => x (rqX2 (g,t))) (fun g t => x (rqY2 (g,t))) (fun g t => x (rqX3 (g,t))) (fun g t => x (rqY3 (g,t))) (fun g t => x (rqX4 (g,t))) (fun g t => x (rqY4 (g,t))) (fun g b => x (rqS (g,b))) (fun g c => h (x ∘ posQ1 u) (jC (g,c)))

/-- scalar map of stage 2 on a run: pair 1 moves, the banks keep their contents. -/
def liftQ2 (u : Sl → Fin nb) (h : (SRole Γ T Sl C → ℂ) → (SRole Γ T Sl C → ℂ)) (x : BRun4 Γ T nb C → ℂ) :
    BRun4 Γ T nb C → ℂ :=
  mkR4 (fun g t => h (x ∘ posQ2 u) (jX (g,t))) (fun g t => h (x ∘ posQ2 u) (jY (g,t))) (fun g t => x (rqX2 (g,t))) (fun g t => x (rqY2 (g,t))) (fun g t => x (rqX3 (g,t))) (fun g t => x (rqY3 (g,t))) (fun g t => x (rqX4 (g,t))) (fun g t => x (rqY4 (g,t))) (fun g b => x (rqS (g,b))) (fun g c => h (x ∘ posQ2 u) (jC (g,c)))

/-- scalar map of stage 3 on a run: pair 2 moves, the banks keep their contents. -/
def liftQ3 (u : Sl → Fin nb) (h : (SRole Γ T Sl C → ℂ) → (SRole Γ T Sl C → ℂ)) (x : BRun4 Γ T nb C → ℂ) :
    BRun4 Γ T nb C → ℂ :=
  mkR4 (fun g t => x (rqX1 (g,t))) (fun g t => x (rqY1 (g,t))) (fun g t => h (x ∘ posQ3 u) (jX (g,t))) (fun g t => h (x ∘ posQ3 u) (jY (g,t))) (fun g t => x (rqX3 (g,t))) (fun g t => x (rqY3 (g,t))) (fun g t => x (rqX4 (g,t))) (fun g t => x (rqY4 (g,t))) (fun g b => x (rqS (g,b))) (fun g c => h (x ∘ posQ3 u) (jC (g,c)))

/-- scalar map of stage 4 on a run: pair 2 moves, the banks keep their contents. -/
def liftQ4 (u : Sl → Fin nb) (h : (SRole Γ T Sl C → ℂ) → (SRole Γ T Sl C → ℂ)) (x : BRun4 Γ T nb C → ℂ) :
    BRun4 Γ T nb C → ℂ :=
  mkR4 (fun g t => x (rqX1 (g,t))) (fun g t => x (rqY1 (g,t))) (fun g t => h (x ∘ posQ4 u) (jX (g,t))) (fun g t => h (x ∘ posQ4 u) (jY (g,t))) (fun g t => x (rqX3 (g,t))) (fun g t => x (rqY3 (g,t))) (fun g t => x (rqX4 (g,t))) (fun g t => x (rqY4 (g,t))) (fun g b => x (rqS (g,b))) (fun g c => h (x ∘ posQ4 u) (jC (g,c)))

/-- scalar map of stage 5 on a run: pair 3 moves, the banks keep their contents. -/
def liftQ5 (u : Sl → Fin nb) (h : (SRole Γ T Sl C → ℂ) → (SRole Γ T Sl C → ℂ)) (x : BRun4 Γ T nb C → ℂ) :
    BRun4 Γ T nb C → ℂ :=
  mkR4 (fun g t => x (rqX1 (g,t))) (fun g t => x (rqY1 (g,t))) (fun g t => x (rqX2 (g,t))) (fun g t => x (rqY2 (g,t))) (fun g t => h (x ∘ posQ5 u) (jX (g,t))) (fun g t => h (x ∘ posQ5 u) (jY (g,t))) (fun g t => x (rqX4 (g,t))) (fun g t => x (rqY4 (g,t))) (fun g b => x (rqS (g,b))) (fun g c => h (x ∘ posQ5 u) (jC (g,c)))

/-- scalar map of stage 6 on a run: pair 3 moves, the banks keep their contents. -/
def liftQ6 (u : Sl → Fin nb) (h : (SRole Γ T Sl C → ℂ) → (SRole Γ T Sl C → ℂ)) (x : BRun4 Γ T nb C → ℂ) :
    BRun4 Γ T nb C → ℂ :=
  mkR4 (fun g t => x (rqX1 (g,t))) (fun g t => x (rqY1 (g,t))) (fun g t => x (rqX2 (g,t))) (fun g t => x (rqY2 (g,t))) (fun g t => h (x ∘ posQ6 u) (jX (g,t))) (fun g t => h (x ∘ posQ6 u) (jY (g,t))) (fun g t => x (rqX4 (g,t))) (fun g t => x (rqY4 (g,t))) (fun g b => x (rqS (g,b))) (fun g c => h (x ∘ posQ6 u) (jC (g,c)))

/-- scalar map of stage 7 on a run: pair 4 moves, the banks keep their contents. -/
def liftQ7 (u : Sl → Fin nb) (h : (SRole Γ T Sl C → ℂ) → (SRole Γ T Sl C → ℂ)) (x : BRun4 Γ T nb C → ℂ) :
    BRun4 Γ T nb C → ℂ :=
  mkR4 (fun g t => x (rqX1 (g,t))) (fun g t => x (rqY1 (g,t))) (fun g t => x (rqX2 (g,t))) (fun g t => x (rqY2 (g,t))) (fun g t => x (rqX3 (g,t))) (fun g t => x (rqY3 (g,t))) (fun g t => h (x ∘ posQ7 u) (jX (g,t))) (fun g t => h (x ∘ posQ7 u) (jY (g,t))) (fun g b => x (rqS (g,b))) (fun g c => h (x ∘ posQ7 u) (jC (g,c)))

/-- scalar map of stage 8 on a run: pair 4 moves, the banks keep their contents. -/
def liftQ8 (u : Sl → Fin nb) (h : (SRole Γ T Sl C → ℂ) → (SRole Γ T Sl C → ℂ)) (x : BRun4 Γ T nb C → ℂ) :
    BRun4 Γ T nb C → ℂ :=
  mkR4 (fun g t => x (rqX1 (g,t))) (fun g t => x (rqY1 (g,t))) (fun g t => x (rqX2 (g,t))) (fun g t => x (rqY2 (g,t))) (fun g t => x (rqX3 (g,t))) (fun g t => x (rqY3 (g,t))) (fun g t => h (x ∘ posQ8 u) (jX (g,t))) (fun g t => h (x ∘ posQ8 u) (jY (g,t))) (fun g b => x (rqS (g,b))) (fun g c => h (x ∘ posQ8 u) (jC (g,c)))

/-- the roles of a run as the roles of replica `ρ`. -/
def runPos4 (ρ : Fin 8) : BRun4 Γ T nb C → BRole401 Γ T nb C
  | .inl (.inl d) => .inl (.inl (ρ, d))
  | .inl (.inr s) => .inl (.inr s)
  | .inr c => .inr c

lemma runPos4_inj (ρ : Fin 8) : Function.Injective (runPos4 ρ : BRun4 Γ T nb C → BRole401 Γ T nb C) := by
  intro a b h
  rcases a with ((d|s)|c) <;> rcases b with ((d'|s')|c') <;> simp_all [runPos4]

def emRun4 (ρ : Fin 8) : BRun4 Γ T nb C ↪ BRole401 Γ T nb C := ⟨runPos4 ρ, runPos4_inj ρ⟩

/-- scalar map of run `ρ`: replica `ρ` and the banks move by `h`, the other replicas keep their contents. -/
def liftRun4 (ρ : Fin 8) (h : (BRun4 Γ T nb C → ℂ) → (BRun4 Γ T nb C → ℂ)) (x : BRole401 Γ T nb C → ℂ) :
    BRole401 Γ T nb C → ℂ
  | .inl (.inl (ρ', d)) => if ρ' = ρ then h (x ∘ runPos4 ρ) (.inl (.inl d)) else x (.inl (.inl (ρ', d)))
  | .inl (.inr s) => h (x ∘ runPos4 ρ) (.inl (.inr s))
  | .inr c => h (x ∘ runPos4 ρ) (.inr c)

lemma liftRun4_self (ρ : Fin 8) (h : (BRun4 Γ T nb C → ℂ) → (BRun4 Γ T nb C → ℂ)) (x : BRole401 Γ T nb C → ℂ)
    (d : BDat4 Γ T) : liftRun4 ρ h x (.inl (.inl (ρ, d))) = h (x ∘ runPos4 ρ) (.inl (.inl d)) :=
  if_pos rfl

/-- the roles run `ρ` reads: its replica and the banks. -/
def inA4 (ρ : Fin 8) : BRole401 Γ T nb C → Prop
  | .inl (.inl (ρ', _)) => ρ' = ρ
  | .inl (.inr _) => True
  | .inr _ => False

/-- the bank roles. -/
def isBk4 : BRole401 Γ T nb C → Prop
  | .inl (.inl _) => False
  | .inl (.inr _) => True
  | .inr _ => False

end Roles
end
end GX
end PowerSaving
end OAI
