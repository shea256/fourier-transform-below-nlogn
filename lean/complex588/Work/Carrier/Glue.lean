import Work.Carrier.Scat

/-!
# (key: carrier-thm) From the live roles to all roles of an invocation (scratch copies)

* `upE : L3 T Sl ↪ Box T Sl C`, `glue u c`, `liveAct h`: the live roles inside `Box`;
* `lift_live`: an exact route on the live roles is an exact route on `Box`, the copies keeping
  ANY frame matrices `c`;
* `copies_descend`, `copies_climb`: every copy moves between its label and 0, ONE block each;
* `gateS ia ib M`: the scalar map of a block shear (`xgate_shear`);
* `scat_glue`, `scat_glueT`: on zero copies, `c += Cc s ; y += Jr c` acts on the live roles as
  `scatM (Jr * Cc)`, and `c += Jrᵀ y ; s -= Ccᵀ c` as the transpose of `scatMi (Jr * Cc)`;
* `glue_shearF`, `glue_shearB`: the two shears, back on `Box`.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace CR
open Binary Matrix Finset RAM SS CB BR
noncomputable section

section Glue
variable {T Sl C : Type} [Fintype T] [DecidableEq T] [Fintype Sl] [DecidableEq Sl]
  [Fintype C] [DecidableEq C]

/-- the live roles inside the roles of an invocation. -/
def upE : L3 T Sl ↪ Box T Sl C :=
  ⟨Sum.map id Sum.inl, Sum.map_injective.mpr ⟨Function.injective_id, Sum.inl_injective⟩⟩

/-- a function on the roles of an invocation, from its live part and its copies. -/
def glue {β : Type*} (u : L3 T Sl → β) (c : C → β) : Box T Sl C → β :=
  Sum.elim (fun b => u (Sum.inl b)) (Sum.elim (fun q => u (Sum.inr q)) c)

/-- a scalar map of the live roles acting on all roles (the copies untouched). -/
def liveAct (h : (L3 T Sl → ℂ) → (L3 T Sl → ℂ)) (z : Box T Sl C → ℂ) : Box T Sl C → ℂ :=
  glue (h (z ∘ upE)) (z ∘ bC)

/-- scalar map of a block shear `role (ia a) += ∑_b M a b * role (ib b)`. -/
def gateS {A B : Type} [Fintype A] [Fintype B] (ia : A → Box T Sl C) (ib : B → Box T Sl C)
    (M : Matrix A B ℚ) (z : Box T Sl C → ℂ) : Box T Sl C → ℂ :=
  addBlk ia (ap M (z ∘ ib)) z

lemma glue_up {β : Type*} (u : L3 T Sl → β) (c : C → β) :
    glue u c ∘ (upE : L3 T Sl ↪ Box T Sl C) = u := by
  funext r
  rcases r with (b|q) <;> rfl

lemma glue_bC {β : Type*} (u : L3 T Sl → β) (c : C → β) : glue u c ∘ bC = c := rfl

lemma erase_glue (z : Box T Sl C → ℂ) : eraseC z = glue (z ∘ upE) (fun _ => 0) := by
  funext i
  rcases i with ((t|t)|(q|k)) <;> rfl

lemma erase_of_glue (v : L3 T Sl → ℂ) (c : C → ℂ) :
    eraseC (glue v c) = glue v (fun _ => 0) := by
  funext i
  rcases i with ((t|t)|(q|k)) <;> rfl

variable {α : Type} [Fintype α] [DecidableEq α]

/-- **An exact route on the live roles is an exact route on all roles**; the copies keep any
frame matrices `c`. -/
theorem lift_live {S S' : L3 T Sl → CMat α} (c : C → CMat α)
    {h : (L3 T Sl → ℂ) → (L3 T Sl → ℂ)} {cost : (ℕ → ℝ) → ℝ} (q : XRoute S S' h cost) :
    XRoute (glue S c) (glue S' c) (liveAct h) cost := by
  refine XRoute.lift upE (S := glue S c) (T := glue S' c) (h := h) ?_ ?_ ?_ ?_
  · rw [glue_up, glue_up]
    exact q
  · intro x
    exact glue_up _ _
  · intro x i hi
    rcases i with (b|(q'|k))
    · exact absurd ((cover_iff ..).mpr ⟨Sum.inl b, rfl⟩) hi
    · exact absurd ((cover_iff ..).mpr ⟨Sum.inr q', rfl⟩) hi
    · rfl
  · intro i hi
    rcases i with (b|(q'|k))
    · exact absurd ((cover_iff ..).mpr ⟨Sum.inl b, rfl⟩) hi
    · exact absurd ((cover_iff ..).mpr ⟨Sum.inr q', rfl⟩) hi
    · rfl

variable {H : Type} [Fintype H] [DecidableEq H]

/-- every copy comes down from its label to 0: ONE block of rank `(cen k).d` each. -/
theorem copies_descend (Xm : XMap H α) (S : L3 T Sl → CMat α) (cen : C → Lbl H)
    (kc : ∀ k, Climb zeroL (cen k)) :
    XRoute (glue S (fun k => Xm.Φ (cen k).P)) (glue S (fun _ : C => Xm.Φ 0)) id
      (fun φ => ∑ k, bcost φ (cen k).d) := by
  have H0 := XRoute.reach_all (glue S (fun k => Xm.Φ (cen k).P)) (glue S (fun _ : C => Xm.Φ 0))
    (fun r φ => Sum.elim (fun _ => (0:ℝ))
      (Sum.elim (fun _ => (0:ℝ)) (fun k => bcost φ (cen k).d)) r) (by
      rintro (b|(q|k))
      · exact XReach.refl _
      · exact XReach.refl _
      · exact (Xm.descend (kc k)).cast (fun φ => by first | rfl | simp [zeroL]))
  refine H0.cast (fun φ => ?_)
  first
    | (simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.sum_const_zero,
        zero_add, add_zero]; done)
    | simp [Fintype.sum_sum_type]

/-- every copy climbs from 0 to its label: ONE block of rank `(cen k).d` each. -/
theorem copies_climb (Xm : XMap H α) (S : L3 T Sl → CMat α) (cen : C → Lbl H)
    (kc : ∀ k, Climb zeroL (cen k)) :
    XRoute (glue S (fun _ : C => Xm.Φ 0)) (glue S (fun k => Xm.Φ (cen k).P)) id
      (fun φ => ∑ k, bcost φ (cen k).d) := by
  have H0 := XRoute.reach_all (glue S (fun _ : C => Xm.Φ 0)) (glue S (fun k => Xm.Φ (cen k).P))
    (fun r φ => Sum.elim (fun _ => (0:ℝ))
      (Sum.elim (fun _ => (0:ℝ)) (fun k => bcost φ (cen k).d)) r) (by
      rintro (b|(q|k))
      · exact XReach.refl _
      · exact XReach.refl _
      · exact (Xm.climb (kc k)).cast (fun φ => by first | rfl | simp [zeroL]))
  refine H0.cast (fun φ => ?_)
  first
    | (simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.sum_const_zero,
        zero_add, add_zero]; done)
    | simp [Fintype.sum_sum_type]

/-- on zero copies, `c += Cc s ; y += Jr c` is the scatter `scatM (Jr * Cc)` of the live
roles. -/
lemma scat_glue (Jr : Matrix T C ℚ) (Cc : Matrix C Sl ℚ) (z : Box T Sl C → ℂ)
    (hc : z ∘ bC = 0) :
    gateS bY bC Jr (gateS bC bS Cc z) ∘ (upE : L3 T Sl ↪ Box T Sl C)
      = actPoint (scatM (Jr * Cc)) (z ∘ upE) := by
  have hX : gateS bY bC Jr (gateS bC bS Cc z) ∘ bX = z ∘ bX := by
    simp only [gateS, aY_X, aC_X]
  have hY : gateS bY bC Jr (gateS bC bS Cc z) ∘ bY = z ∘ bY + ap (Jr * Cc) (z ∘ bS) := by
    simp only [gateS, aY_Y, aC_Y, aC_C, aC_S, hc, zero_add, ap_mul]
  have hS : gateS bY bC Jr (gateS bC bS Cc z) ∘ bS = z ∘ bS := by
    simp only [gateS, aY_S, aC_S]
  unfold scatM
  rw [act_scat]
  funext r
  rcases r with ((t|S)|q)
  · show gateS bY bC Jr (gateS bC bS Cc z) (bX t) = z (bX t) + 0
    rw [add_zero]
    exact congrFun hX t
  · exact congrFun hY S
  · show gateS bY bC Jr (gateS bC bS Cc z) (bS q) = z (bS q) + 0
    rw [add_zero]
    exact congrFun hS q

/-- on zero copies, `c += Jrᵀ y ; s -= Ccᵀ c` is the transposed inverse scatter of the live
roles. -/
lemma scat_glueT (Jr : Matrix T C ℚ) (Cc : Matrix C Sl ℚ) (z : Box T Sl C → ℂ)
    (hc : z ∘ bC = 0) :
    gateS bS bC (-Ccᵀ) (gateS bC bY Jrᵀ z) ∘ (upE : L3 T Sl ↪ Box T Sl C)
      = actPoint ((scatMi (Jr * Cc))ᵀ) (z ∘ upE) := by
  have hX : gateS bS bC (-Ccᵀ) (gateS bC bY Jrᵀ z) ∘ bX = z ∘ bX := by
    simp only [gateS, aS_X, aC_X]
  have hY : gateS bS bC (-Ccᵀ) (gateS bC bY Jrᵀ z) ∘ bY = z ∘ bY := by
    simp only [gateS, aS_Y, aC_Y]
  have hS : gateS bS bC (-Ccᵀ) (gateS bC bY Jrᵀ z) ∘ bS
      = z ∘ bS + -(ap (Jr * Cc)ᵀ (z ∘ bY)) := by
    simp only [gateS, aS_S, aC_S, aC_C, aC_Y, hc, zero_add, ap_mneg, Matrix.transpose_mul, ap_mul]
  unfold scatMi
  rw [act_scatT]
  funext r
  rcases r with ((t|S)|q)
  · show gateS bS bC (-Ccᵀ) (gateS bC bY Jrᵀ z) (bX t) = z (bX t) - 0
    rw [sub_zero]
    exact congrFun hX t
  · show gateS bS bC (-Ccᵀ) (gateS bC bY Jrᵀ z) (bY S) = z (bY S) - 0
    rw [sub_zero]
    exact congrFun hY S
  · have h := congrFun hS q
    rw [sub_eq_add_neg]
    exact h

/-- the forward shear of the live roles, with zero copies, is `shearF`. -/
lemma glue_shearF (z : Box T Sl C → ℂ) :
    glue (fun i => (z ∘ (upE : L3 T Sl ↪ Box T Sl C)) i +
      Sum.elim (Sum.elim (fun _ => 0) (fun S => (z ∘ (upE : L3 T Sl ↪ Box T Sl C))
        (Sum.inl (Sum.inl S)))) (fun _ => 0) i) (fun _ => 0) = shearF z := by
  funext i
  rcases i with ((t|t)|(q|k))
  · show z (bX t) + 0 = z (bX t)
    rw [add_zero]
  · rfl
  · show z (bS q) + 0 = z (bS q)
    rw [add_zero]
  · rfl

/-- the backward shear of the live roles, with zero copies, is `shearB`. -/
lemma glue_shearB (z : Box T Sl C → ℂ) :
    glue (fun i => (z ∘ (upE : L3 T Sl ↪ Box T Sl C)) i -
      Sum.elim (Sum.elim (fun t => (z ∘ (upE : L3 T Sl ↪ Box T Sl C))
        (Sum.inl (Sum.inr t))) (fun _ => 0)) (fun _ => 0) i) (fun _ => 0) = shearB z := by
  funext i
  rcases i with ((t|t)|(q|k))
  · rfl
  · show z (bY t) - 0 = z (bY t)
    rw [sub_zero]
  · show z (bS q) - 0 = z (bS q)
    rw [sub_zero]
  · rfl

end Glue
end
end CR
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.CR.lift_live
#print axioms OAI.PowerSaving.CR.scat_glue
#print axioms OAI.PowerSaving.CR.scat_glueT
