import Work.SharedSumStructured.Invocation

/-!
# (key: shared-sum-structured) The two-stage network for an ARBITRARY helper circuit

Input: a `Circuit H T Sl C` (one invocation), an orthonormal basis of `H` through every input
vector, and a number `pad` of idle roles.  Output (`network_certificate`): a word on
`α = H × H` with

* live roles  `X(a,b)`, `Y(a,b)` (`a b : T`), the helper slots of the `2 |T|` invocations
  (stage 1: second triple fixed, forward; stage 2: first triple fixed, backward) and `pad`
  idle roles;
* scratch roles: the copies of every invocation and one endpoint copy `Z(a,b)` per bank pair;
* `LiveKernel` (kernel on every live role whenever the scratch roles start at zero);
* `tally + |T|^2 = (number of live roles) * |H|^2 + 2 |T| * (sum of the copy dimensions)`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace SS
open Binary Matrix Finset RAM
noncomputable section

/-- one invocation certificate, bases through the input vectors, padding. -/
structure NetData (H T Sl C : Type) [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
    [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] where
  K : Circuit H T Sl C
  base : T → OBase H
  piv : T → H
  hbase : ∀ t, K.tv t = (base t).v (piv t)
  pad : ℕ

abbrev Key (T : Type) := T × T
abbrev Live (T Sl : Type) (P : ℕ) := (Key T ⊕ Key T) ⊕ ((Bool × T × Sl) ⊕ Fin P)
abbrev Scr (T C : Type) := (Bool × T × C) ⊕ Key T
abbrev Role (T Sl C : Type) (P : ℕ) := Live T Sl P ⊕ Scr T C

instance liveDec {T Sl : Type} [DecidableEq T] [DecidableEq Sl] (P : ℕ) :
    DecidableEq (Live T Sl P) := inferInstance
instance scrDec {T C : Type} [DecidableEq T] [DecidableEq C] : DecidableEq (Scr T C) :=
  inferInstance
instance roleDec {T Sl C : Type} [DecidableEq T] [DecidableEq Sl] [DecidableEq C] (P : ℕ) :
    DecidableEq (Role T Sl C P) := inferInstance
instance liveFin {T Sl : Type} [Fintype T] [Fintype Sl] (P : ℕ) : Fintype (Live T Sl P) :=
  inferInstance
instance scrFin {T C : Type} [Fintype T] [Fintype C] : Fintype (Scr T C) := inferInstance
instance roleFin {T Sl C : Type} [Fintype T] [Fintype Sl] [Fintype C] (P : ℕ) :
    Fintype (Role T Sl C P) := inferInstance

section Roles
variable {T Sl C : Type} {P : ℕ}

def iX (k : Key T) : Role T Sl C P := .inl (.inl (.inl k))
def iY (k : Key T) : Role T Sl C P := .inl (.inl (.inr k))
def iS (p : Bool × T × Sl) : Role T Sl C P := .inl (.inr (.inl p))
def iI (i : Fin P) : Role T Sl C P := .inl (.inr (.inr i))
def iC (p : Bool × T × C) : Role T Sl C P := .inr (.inl p)
def iZ (k : Key T) : Role T Sl C P := .inr (.inr k)

lemma iX_inj : Function.Injective (iX : Key T → Role T Sl C P) := fun _ _ h => by
  simpa [iX] using h
lemma iY_inj : Function.Injective (iY : Key T → Role T Sl C P) := fun _ _ h => by
  simpa [iY] using h
lemma iZ_inj : Function.Injective (iZ : Key T → Role T Sl C P) := fun _ _ h => by
  simpa [iZ] using h

/-- a function on the roles, block by block. -/
def mkState {β : Type*} (fX fY : Key T → β) (fS : Bool → T → Sl → β) (fI : Fin P → β)
    (fC : Bool → T → C → β) (fZ : Key T → β) : Role T Sl C P → β
  | .inl (.inl (.inl k)) => fX k
  | .inl (.inl (.inr k)) => fY k
  | .inl (.inr (.inl (b,r,q))) => fS b r q
  | .inl (.inr (.inr i)) => fI i
  | .inr (.inl (b,r,c)) => fC b r c
  | .inr (.inr k) => fZ k

lemma mkState_map {β γ : Type*} (g : β → γ) (fX fY : Key T → β) (fS : Bool → T → Sl → β)
    (fI : Fin P → β) (fC : Bool → T → C → β) (fZ : Key T → β) (r : Role T Sl C P) :
    g (mkState fX fY fS fI fC fZ r) = mkState (fun k => g (fX k)) (fun k => g (fY k))
      (fun b r q => g (fS b r q)) (fun i => g (fI i)) (fun b r c => g (fC b r c))
      (fun k => g (fZ k)) r := by
  rcases r with (((k|k)|(⟨b,r,q⟩|i))|(⟨b,r,c⟩|k)) <;> rfl

variable [Fintype T] [Fintype Sl] [Fintype C]

lemma sum_mkState (fX fY : Key T → ℕ) (fS : Bool → T → Sl → ℕ) (fI : Fin P → ℕ)
    (fC : Bool → T → C → ℕ) (fZ : Key T → ℕ) :
    ∑ r : Role T Sl C P, mkState fX fY fS fI fC fZ r
      = ∑ k, fX k + ∑ k, fY k + (∑ r, ∑ q, fS true r q + ∑ r, ∑ q, fS false r q) + ∑ i, fI i
        + (∑ r, ∑ c, fC true r c + ∑ r, ∑ c, fC false r c) + ∑ k, fZ k := by
  simp only [Fintype.sum_sum_type, mkState, Fintype.sum_prod_type, Fintype.sum_bool]
  ring

lemma fmass_mkState {α : Type*} (fX fY : Key T → Fr α) (fS : Bool → T → Sl → Fr α)
    (fI : Fin P → Fr α) (fC : Bool → T → C → Fr α) (fZ : Key T → Fr α) :
    fmass (mkState fX fY fS fI fC fZ : Role T Sl C P → Fr α)
      = ∑ k, (fX k).d + ∑ k, (fY k).d
        + (∑ r, ∑ q, (fS true r q).d + ∑ r, ∑ q, (fS false r q).d) + ∑ i, (fI i).d
        + (∑ r, ∑ c, (fC true r c).d + ∑ r, ∑ c, (fC false r c).d) + ∑ k, (fZ k).d := by
  unfold fmass
  simp_rw [mkState_map (fun x : Fr α => x.d)]
  exact sum_mkState _ _ _ _ _ _

/-- where the roles of the invocation with fixed SECOND triple `r` sit (stage 1). -/
def pos1 (r : T) : Box T Sl C → Role T Sl C P :=
  stamp (fun t => iX (t,r)) (fun t => iY (t,r)) (fun q => iS (false,r,q)) (fun c => iC (false,r,c))

/-- where the roles of the invocation with fixed FIRST triple `r` sit (stage 2). -/
def pos2 (r : T) : Box T Sl C → Role T Sl C P :=
  stamp (fun t => iX (r,t)) (fun t => iY (r,t)) (fun q => iS (true,r,q)) (fun c => iC (true,r,c))

lemma pos1_inj {r r' : T} {x y : Box T Sl C}
    (h : (pos1 r x : Role T Sl C P) = pos1 r' y) : r = r' ∧ x = y := by
  rcases x with ((t|t)|(q|c)) <;> rcases y with ((t'|t')|(q'|c')) <;>
    simp [pos1, stamp, iX, iY, iS, iC] at h <;>
    (obtain ⟨h1, h2⟩ := h; subst h1; subst h2; exact ⟨rfl, rfl⟩)

lemma pos2_inj {r r' : T} {x y : Box T Sl C}
    (h : (pos2 r x : Role T Sl C P) = pos2 r' y) : r = r' ∧ x = y := by
  rcases x with ((t|t)|(q|c)) <;> rcases y with ((t'|t')|(q'|c')) <;>
    simp [pos2, stamp, iX, iY, iS, iC] at h <;>
    (obtain ⟨h1, h2⟩ := h; subst h1; subst h2; exact ⟨rfl, rfl⟩)

def e1 (r : T) : Box T Sl C ↪ Role T Sl C P := ⟨pos1 r, fun _ _ h => (pos1_inj h).2⟩
def e2 (r : T) : Box T Sl C ↪ Role T Sl C P := ⟨pos2 r, fun _ _ h => (pos2_inj h).2⟩

variable [DecidableEq T] [DecidableEq Sl] [DecidableEq C]

lemma e1_dis (r r' : T) (h : r ≠ r') (x : Role T Sl C P) :
    x ∈ covered (e1 r) → x ∉ covered (e1 r') := by
  simp only [cover_iff, not_exists]
  rintro ⟨u, hu⟩ v hv
  exact h (pos1_inj (hu.trans hv.symm)).1

lemma e2_dis (r r' : T) (h : r ≠ r') (x : Role T Sl C P) :
    x ∈ covered (e2 r) → x ∉ covered (e2 r') := by
  simp only [cover_iff, not_exists]
  rintro ⟨u, hu⟩ v hv
  exact h (pos2_inj (hu.trans hv.symm)).1

end Roles

section Net
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]
variable (D : NetData H T Sl C)

/-- stage-1 frame map of the invocation with second triple `r`. -/
def NetData.F1 (r : T) : FMap H (H × H) := fmap1 (D.base r) (D.piv r)
/-- stage-2 frame map of the invocation with first triple `r`. -/
def NetData.F2 (r : T) : FMap H (H × H) := fmap2 (D.base r) (D.piv r)

/-- nominal dimension of the full two-factor space, written as `h + (h-1) h`. -/
def NetData.mm (_D : NetData H T Sl C) : ℕ :=
  Fintype.card H + (Fintype.card H - 1) * Fintype.card H
/-- total nominal dimension of the copies of one invocation. -/
def NetData.cst : ℕ := ∑ c, (D.K.cen c).d

def NetData.top (D : NetData H T Sl C) : Fr (H × H) := ⟨kernel (H × H), D.mm⟩
def NetData.bot (_D : NetData H T Sl C) : Fr (H × H) := ⟨1, 0⟩

/-- frames at the start. -/
def NetData.S0 : Role T Sl C D.pad → Fr (H × H) := mkState
  (fun k => (D.F1 k.2).lab (lineL (D.K.tv k.1)))
  (fun k => (D.F1 k.2).lab zeroL)
  (fun b r q => cond b D.bot ((D.F1 r).lab zeroL))
  (fun _ => D.bot)
  (fun b r c => cond b ((D.F2 r).lab zeroL) ((D.F1 r).lab (D.K.cen c)))
  (fun k => (D.F2 k.1).lab fullL)

/-- after stage 1. -/
def NetData.S1 : Role T Sl C D.pad → Fr (H × H) := mkState
  (fun k => (D.F1 k.2).lab fullL)
  (fun k => (D.F1 k.2).lab (perpL (D.K.tv k.1)))
  (fun b r q => cond b D.bot ((D.F1 r).lab fullL))
  (fun _ => D.bot)
  (fun b r c => cond b ((D.F2 r).lab zeroL) ((D.F1 r).lab zeroL))
  (fun k => (D.F2 k.1).lab fullL)

/-- after the exterior climbs. -/
def NetData.S2 : Role T Sl C D.pad → Fr (H × H) := mkState
  (fun k => (D.F2 k.1).lab (lineL (D.K.tv k.2)))
  (fun k => (D.F2 k.1).lab zeroL)
  (fun b r q => cond b ((D.F2 r).lab zeroL) D.top)
  (fun _ => D.top)
  (fun b r c => cond b ((D.F2 r).lab zeroL) ((D.F1 r).lab zeroL))
  (fun k => (D.F2 k.1).lab fullL)

/-- after stage 2. -/
def NetData.S3 : Role T Sl C D.pad → Fr (H × H) := mkState
  (fun k => (D.F2 k.1).lab fullL)
  (fun k => (D.F2 k.1).lab (perpL (D.K.tv k.2)))
  (fun b r q => cond b ((D.F2 r).lab fullL) D.top)
  (fun _ => D.top)
  (fun b r c => cond b ((D.F2 r).lab (D.K.cen c)) ((D.F1 r).lab zeroL))
  (fun k => (D.F2 k.1).lab fullL)

/-- after the endpoint copies have come down one line. -/
def NetData.S4 : Role T Sl C D.pad → Fr (H × H) := mkState
  (fun k => (D.F2 k.1).lab fullL)
  (fun k => (D.F2 k.1).lab (perpL (D.K.tv k.2)))
  (fun b r q => cond b ((D.F2 r).lab fullL) D.top)
  (fun _ => D.top)
  (fun b r c => cond b ((D.F2 r).lab (D.K.cen c)) ((D.F1 r).lab zeroL))
  (fun k => (D.F2 k.1).lab (perpL (D.K.tv k.2)))

/-- scalar map of stage 1: the forward invocation on every block `pos1 r`. -/
def NetData.stage1 (x : Role T Sl C D.pad → ℂ) : Role T Sl C D.pad → ℂ := mkState
  (fun k => D.K.fwd (x ∘ pos1 k.2) (bX k.1))
  (fun k => D.K.fwd (x ∘ pos1 k.2) (bY k.1))
  (fun b r q => cond b (x (iS (true,r,q))) (D.K.fwd (x ∘ pos1 r) (bS q)))
  (fun i => x (iI i))
  (fun b r c => cond b (x (iC (true,r,c))) (D.K.fwd (x ∘ pos1 r) (bC c)))
  (fun k => x (iZ k))

/-- scalar map of stage 2: the backward invocation on every block `pos2 r`. -/
def NetData.stage2 (x : Role T Sl C D.pad → ℂ) : Role T Sl C D.pad → ℂ := mkState
  (fun k => D.K.bwd (x ∘ pos2 k.1) (bX k.2))
  (fun k => D.K.bwd (x ∘ pos2 k.1) (bY k.2))
  (fun b r q => cond b (D.K.bwd (x ∘ pos2 r) (bS q)) (x (iS (false,r,q))))
  (fun i => x (iI i))
  (fun b r c => cond b (D.K.bwd (x ∘ pos2 r) (bC c)) (x (iC (false,r,c))))
  (fun k => x (iZ k))

lemma NetData.stage1_path :
    GPath D.S0 D.S1 D.stage1 (Fintype.card T * D.cst) := by
  have key := GPath.parallel (ρ := Box T Sl C) (σ := Role T Sl C D.pad) (J := T)
    (e := fun r => e1 r) (fun r r' h x => e1_dis r r' h x)
    (s := D.S0) (t := D.S1) (d := fun _ => D.cst) (g := D.stage1) (h := fun _ => D.K.fwd)
    (fun r => by
      have e0 : D.S0 ∘ (e1 r) = st (D.F1 r) (fun t => lineL (D.K.tv t)) (fun _ => zeroL)
          (fun _ => zeroL) D.K.cen := by
        funext b; rcases b with ((t|t)|(q|c)) <;> rfl
      have e1' : D.S1 ∘ (e1 r) = st (D.F1 r) (fun _ => fullL) (fun t => perpL (D.K.tv t))
          (fun _ => fullL) (fun _ => zeroL) := by
        funext b; rcases b with ((t|t)|(q|c)) <;> rfl
      rw [e0, e1']
      exact invocation_fwd D.K (D.F1 r))
    (fun r x => by funext b; rcases b with ((t|t)|(q|c)) <;> rfl)
    (fun x role hr => by
      rcases role with (((⟨a,b⟩|⟨a,b⟩)|(⟨b,r,q⟩|i))|(⟨b,r,c⟩|k))
      · exact absurd ((cover_iff ..).mpr ⟨bX a, rfl⟩) (hr b)
      · exact absurd ((cover_iff ..).mpr ⟨bY a, rfl⟩) (hr b)
      · cases b
        · exact absurd ((cover_iff ..).mpr ⟨bS q, rfl⟩) (hr r)
        · rfl
      · rfl
      · cases b
        · exact absurd ((cover_iff ..).mpr ⟨bC c, rfl⟩) (hr r)
        · rfl
      · rfl)
    (fun role hr => by
      rcases role with (((⟨a,b⟩|⟨a,b⟩)|(⟨b,r,q⟩|i))|(⟨b,r,c⟩|k))
      · exact absurd ((cover_iff ..).mpr ⟨bX a, rfl⟩) (hr b)
      · exact absurd ((cover_iff ..).mpr ⟨bY a, rfl⟩) (hr b)
      · cases b
        · exact absurd ((cover_iff ..).mpr ⟨bS q, rfl⟩) (hr r)
        · simp only [NetData.S0, NetData.S1, mkState, cond_true]
      · simp only [NetData.S0, NetData.S1, mkState]
      · cases b
        · exact absurd ((cover_iff ..).mpr ⟨bC c, rfl⟩) (hr r)
        · simp only [NetData.S0, NetData.S1, mkState, cond_true]
      · simp only [NetData.S0, NetData.S1, mkState])
  refine key.cast rfl ?_
  simp

lemma NetData.stage2_path :
    GPath D.S2 D.S3 D.stage2 0 := by
  have key := GPath.parallel (ρ := Box T Sl C) (σ := Role T Sl C D.pad) (J := T)
    (e := fun r => e2 r) (fun r r' h x => e2_dis r r' h x)
    (s := D.S2) (t := D.S3) (d := fun _ => 0) (g := D.stage2) (h := fun _ => D.K.bwd)
    (fun r => by
      have e0 : D.S2 ∘ (e2 r) = st (D.F2 r) (fun t => lineL (D.K.tv t)) (fun _ => zeroL)
          (fun _ => zeroL) (fun _ => zeroL) := by
        funext b; rcases b with ((t|t)|(q|c)) <;> rfl
      have e1' : D.S3 ∘ (e2 r) = st (D.F2 r) (fun _ => fullL) (fun t => perpL (D.K.tv t))
          (fun _ => fullL) D.K.cen := by
        funext b; rcases b with ((t|t)|(q|c)) <;> rfl
      rw [e0, e1']
      exact invocation_bwd D.K (D.F2 r))
    (fun r x => by funext b; rcases b with ((t|t)|(q|c)) <;> rfl)
    (fun x role hr => by
      rcases role with (((⟨a,b⟩|⟨a,b⟩)|(⟨b,r,q⟩|i))|(⟨b,r,c⟩|k))
      · exact absurd ((cover_iff ..).mpr ⟨bX b, rfl⟩) (hr a)
      · exact absurd ((cover_iff ..).mpr ⟨bY b, rfl⟩) (hr a)
      · cases b
        · rfl
        · exact absurd ((cover_iff ..).mpr ⟨bS q, rfl⟩) (hr r)
      · rfl
      · cases b
        · rfl
        · exact absurd ((cover_iff ..).mpr ⟨bC c, rfl⟩) (hr r)
      · rfl)
    (fun role hr => by
      rcases role with (((⟨a,b⟩|⟨a,b⟩)|(⟨b,r,q⟩|i))|(⟨b,r,c⟩|k))
      · exact absurd ((cover_iff ..).mpr ⟨bX b, rfl⟩) (hr a)
      · exact absurd ((cover_iff ..).mpr ⟨bY b, rfl⟩) (hr a)
      · cases b
        · simp only [NetData.S2, NetData.S3, mkState, cond_false]
        · exact absurd ((cover_iff ..).mpr ⟨bS q, rfl⟩) (hr r)
      · simp only [NetData.S2, NetData.S3, mkState]
      · cases b
        · simp only [NetData.S2, NetData.S3, mkState, cond_false]
        · exact absurd ((cover_iff ..).mpr ⟨bC c, rfl⟩) (hr r)
      · simp only [NetData.S2, NetData.S3, mkState])
  refine key.cast rfl ?_
  simp

lemma hh_sq (n : ℕ) : n * n = n + (n - 1) * n := by
  cases n with
  | zero => rfl
  | succ k => simp only [Nat.add_sub_cancel]; ring

/-- the exterior climbs between the two stages. -/
lemma NetData.ext_path : GPath D.S1 D.S2 id 0 := by
  apply GPath.climb_all
  have hsq := hh_sq (Fintype.card H)
  rintro (((⟨a,b⟩|⟨a,b⟩)|(⟨b,r,q⟩|i))|(⟨b,r,c⟩|k))
  · simp only [NetData.S1, NetData.S2, mkState, NetData.F1, NetData.F2, FMap.lab, fmap1, fmap2,
      fullL, lineL]
    obtain ⟨n, hr, hn⟩ := reach_X (D.base a) (D.base b) (D.piv a) (D.piv b)
    refine ⟨n, ?_, ?_⟩
    · rw [D.hbase b]; exact hr
    · omega
  · simp only [NetData.S1, NetData.S2, mkState, NetData.F1, NetData.F2, FMap.lab, fmap1, fmap2,
      perpL, zeroL]
    obtain ⟨n, hr, hn⟩ := reach_Y (D.base a) (D.base b) (D.piv a) (D.piv b)
    refine ⟨n, ?_, ?_⟩
    · rw [D.hbase a]; exact hr
    · omega
  · cases b
    · simp only [NetData.S1, NetData.S2, mkState, cond_false, NetData.F1, FMap.lab, fmap1,
        fullL, NetData.top, NetData.mm]
      obtain ⟨n, hr, hn⟩ := reach_S1 (D.base r) (D.piv r)
      exact ⟨n, hr, by omega⟩
    · simp only [NetData.S1, NetData.S2, mkState, cond_true, NetData.F2, FMap.lab, fmap2,
        zeroL, NetData.bot]
      obtain ⟨n, hr, hn⟩ := reach_S2 (D.base r) (D.piv r)
      exact ⟨n, hr, by omega⟩
  · simp only [NetData.S1, NetData.S2, mkState, NetData.top, NetData.bot, NetData.mm]
    obtain ⟨n, hr, hn⟩ := reach_idle (H := H)
    exact ⟨n, hr, by omega⟩
  · simp only [NetData.S1, NetData.S2, mkState]
    exact ⟨0, Reach.refl _, rfl⟩
  · simp only [NetData.S1, NetData.S2, mkState]
    exact ⟨0, Reach.refl _, rfl⟩

/-- endpoint, first gate: `Z += X` (both at the full frame). -/
def NetData.endA (x : Role T Sl C D.pad → ℂ) : Role T Sl C D.pad → ℂ :=
  addBlk iZ (ap (1 : Matrix (Key T) (Key T) ℚ) (x ∘ iX)) x
/-- endpoint, second gate: `Y += Z` (both one line below the full frame). -/
def NetData.endB (x : Role T Sl C D.pad → ℂ) : Role T Sl C D.pad → ℂ :=
  addBlk iY (ap (1 : Matrix (Key T) (Key T) ℚ) (x ∘ iZ)) x

lemma NetData.endA_path : GPath D.S3 D.S3 D.endA 0 :=
  gate_shear iZ iX iX_inj 1 (fun a b h => by
    have hab : a = b := by
      by_contra hne
      exact h (Matrix.one_apply_ne hne)
    subst hab
    simp only [NetData.S3, mkState, iZ, iX])

lemma NetData.endB_path : GPath D.S4 D.S4 D.endB 0 :=
  gate_shear iY iZ iZ_inj 1 (fun a b h => by
    have hab : a = b := by
      by_contra hne
      exact h (Matrix.one_apply_ne hne)
    subst hab
    simp only [NetData.S4, mkState, iZ, iY])

/-- the endpoint copies come down one line: one loss per bank pair. -/
lemma NetData.down_path : GPath D.S3 D.S4 id (Fintype.card T * Fintype.card T) := by
  have H := GPath.move_all D.S3 D.S4
    (mkState (fun _ => 0) (fun _ => 0) (fun _ _ _ => 0) (fun _ => 0) (fun _ _ _ => 0)
      (fun _ => 1)) (by
      rintro (((⟨a,b⟩|⟨a,b⟩)|(⟨b,r,q⟩|i))|(⟨b,r,c⟩|⟨a,b⟩))
      · simp only [NetData.S3, NetData.S4, mkState]
        exact Or.inl ⟨0, Reach.refl _, rfl, trivial⟩
      · simp only [NetData.S3, NetData.S4, mkState]
        exact Or.inl ⟨0, Reach.refl _, rfl, trivial⟩
      · simp only [NetData.S3, NetData.S4, mkState]
        exact Or.inl ⟨0, Reach.refl _, rfl, trivial⟩
      · simp only [NetData.S3, NetData.S4, mkState]
        exact Or.inl ⟨0, Reach.refl _, rfl, trivial⟩
      · simp only [NetData.S3, NetData.S4, mkState]
        exact Or.inl ⟨0, Reach.refl _, rfl, trivial⟩
      · simp only [NetData.S3, NetData.S4, mkState, NetData.F2, FMap.lab, fmap2, fullL, perpL]
        refine Or.inr ⟨1, ?_, ?_, rfl⟩
        · rw [D.hbase b, Phi2_full]
          exact reach_end (D.base a) (D.base b) (D.piv a) (D.piv b)
        · have h1 := card_pos_of_base (D.base a) (D.piv a)
          omega)
  refine H.cast rfl ?_
  rw [sum_mkState]
  simp

/-- scalar map of the whole network before the final exchange. -/
def NetData.Gtot : (Role T Sl C D.pad → ℂ) → (Role T Sl C D.pad → ℂ) :=
  D.endB ∘ (id ∘ (D.endA ∘ (D.stage2 ∘ (id ∘ D.stage1))))

lemma NetData.total_path :
    GPath D.S0 D.S4 D.Gtot (Fintype.card T * D.cst + Fintype.card T * Fintype.card T) := by
  have h := ((((D.stage1_path.trans D.ext_path).trans D.stage2_path).trans D.endA_path).trans
    D.down_path).trans D.endB_path
  exact h.cast rfl (by omega)

end Net
end
end SS
end PowerSaving
end OAI
