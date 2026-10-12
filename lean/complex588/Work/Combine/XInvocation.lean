import Work.Combine.XG
import Work.SharedSumStructured.Invocation

/-!
# (key: combine) One invocation of the two-stage network, in WHOLE BLOCKS

Block version of `Work.SharedSumStructured.Invocation`.  An `XCircuit` is a `Circuit` of the
structured development together with

* single climbs (ONE orthonormal basis each) for the banks and the copies (`kx`, `ky`, `kc`);
* the four phases of the helper slots as exact block routes, for EVERY block frame map:
  loading `0 → φ4` (`p4`), the addition circuit `φ4 → φ5` (`p5`, for `L` and for the transposed
  inverse), the pieces `φ5 → φ7` (`p7`), the completion `φ7 → full` (`pF`), each with the list
  of the ranks of its blocks (`r4`, `r5`, `r7`, `rF`).

`xinvocation_fwd` / `xinvocation_bwd`: the forward and the backward invocation as exact block
routes with the SAME scalar maps `Circuit.fwd` / `Circuit.bwd` as in the structured development
(so `Circuit.fwd_live`, `Circuit.bwd_live` apply unchanged) and the price

    X.cost φ = rcost φ r4 + rcost φ r5 + rcost φ r7 + rcost φ rF
               + ∑ copies, bcost φ (dimension of the copy) + 2 |T| bcost φ (h - 1).

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace CB
open Binary Matrix Finset RAM SS
noncomputable section

section Shear
variable {ρ A B : Type} [Fintype ρ] [DecidableEq ρ] [Fintype A] [Fintype B]
variable {α : Type} [Fintype α] [DecidableEq α]

/-- a shear gate is legal when every nonzero entry joins two roles with the same frame. -/
lemma xgate_shear {S : ρ → CMat α} (ia : A → ρ) (ib : B → ρ) (hib : Function.Injective ib)
    (M : Matrix A B ℚ) (cond : ∀ a b, M a b ≠ 0 → S (ia a) = S (ib b)) :
    XRoute S S (fun z => addBlk ia (ap M (z ∘ ib)) z) (fun _ => 0) := by
  have h := XRoute.gate (α := α) (shearM ia ib M) S S (fun i j hij => by
    by_cases e : i = j
    · subst e; rfl
    · obtain ⟨a, b, rfl, rfl, hM⟩ := shearM_offdiag e hij
      exact cond a b hM)
  exact h.castg (funext fun z => actPoint_shearM ia ib hib M z)

end Shear

section Invocation
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]
variable {α : Type} [Fintype α] [DecidableEq α]

/-- frame matrices of the roles of an invocation, from single-factor labels. -/
def xst (Xm : XMap H α) (x y : T → Lbl H) (s : Sl → Lbl H) (c : C → Lbl H) :
    Box T Sl C → CMat α := fun b => Xm.Φ (stamp x y s c b).P

lemma xst_gate (Xm : XMap H α) {x y : T → Lbl H} {s : Sl → Lbl H} {c : C → Lbl H}
    {A B : Type} [Fintype A] [Fintype B] (ia : A → Box T Sl C) (ib : B → Box T Sl C)
    (hib : Function.Injective ib) (M : Matrix A B ℚ)
    (cond : ∀ a b, M a b ≠ 0 → stamp x y s c (ia a) = stamp x y s c (ib b)) :
    XRoute (xst Xm x y s c) (xst Xm x y s c) (fun z => addBlk ia (ap M (z ∘ ib)) z)
      (fun _ => 0) :=
  xgate_shear ia ib hib M (fun a b h => by simp only [xst]; rw [cond a b h])

lemma xst_wide (Xm : XMap H α) {x y : T → Lbl H} {s : Sl → Lbl H} {c : C → Lbl H}
    (M : Matrix Sl Sl ℚ) (hs : ∀ q q', s q = s q') :
    XRoute (xst Xm x y s c) (xst Xm x y s c) (onS (actPoint M)) (fun _ => 0) := by
  have h := XRoute.gate (α := α) (wide eS M) (xst Xm x y s c) (xst Xm x y s c) (fun i j hij => by
    by_cases e : i = j
    · subst e; rfl
    · obtain ⟨q, q', rfl, rfl⟩ := wide_offdiag M e hij
      change Xm.Φ (s q).P = Xm.Φ (s q').P
      rw [hs q q'])
  exact h.castg (funext fun z => wide_onS M z)

/-- banks and copies move, each role by its own block word; the slots stay. -/
lemma xst_move (Xm : XMap H α) {x x' y y' : T → Lbl H} (s : Sl → Lbl H) {c c' : C → Lbl H}
    {cx cy : T → (ℕ → ℝ) → ℝ} {cc : C → (ℕ → ℝ) → ℝ}
    (hx : ∀ t, XReach (Xm.Φ (x t).P) (Xm.Φ (x' t).P) (cx t))
    (hy : ∀ t, XReach (Xm.Φ (y t).P) (Xm.Φ (y' t).P) (cy t))
    (hc : ∀ k, XReach (Xm.Φ (c k).P) (Xm.Φ (c' k).P) (cc k)) :
    XRoute (xst Xm x y s c) (xst Xm x' y' s c') id
      (fun φ => ∑ t, cx t φ + ∑ t, cy t φ + ∑ k, cc k φ) := by
  have H := XRoute.reach_all (xst Xm x y s c) (xst Xm x' y' s c')
    (stamp cx cy (fun _ _ => 0) cc) (by
      rintro ((t|t)|(q|k))
      · exact hx t
      · exact hy t
      · exact XReach.refl _
      · exact hc k)
  refine H.cast (fun φ => ?_)
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp [stamp]

/-- a route on the slots alone with a scalar map `g` on the slot block. -/
lemma xst_slots (Xm : XMap H α) (x y : T → Lbl H) (c : C → Lbl H) {s s' : Sl → Lbl H}
    {g : (Sl → ℂ) → (Sl → ℂ)} {cost : (ℕ → ℝ) → ℝ}
    (h : XRoute (fun q => Xm.Φ (s q).P) (fun q => Xm.Φ (s' q).P) g cost) :
    XRoute (xst Xm x y s c) (xst Xm x y s' c) (onS g) cost := by
  refine XRoute.lift eS (S := xst Xm x y s c) (T := xst Xm x y s' c) (h := g) h
    (fun z => rfl) ?_ ?_
  · intro z i hi
    rcases i with ((t|t)|(q|k))
    · rfl
    · rfl
    · exact absurd ((cover_iff ..).mpr ⟨q, rfl⟩) hi
    · rfl
  · intro i hi
    rcases i with ((t|t)|(q|k))
    · rfl
    · rfl
    · exact absurd ((cover_iff ..).mpr ⟨q, rfl⟩) hi
    · rfl

/-- a route on the slots alone without gates. -/
lemma xst_slots_id (Xm : XMap H α) (x y : T → Lbl H) (c : C → Lbl H) {s s' : Sl → Lbl H}
    {cost : (ℕ → ℝ) → ℝ}
    (h : XRoute (fun q => Xm.Φ (s q).P) (fun q => Xm.Φ (s' q).P) id cost) :
    XRoute (xst Xm x y s c) (xst Xm x y s' c) id cost := by
  refine XRoute.lift eS (S := xst Xm x y s c) (T := xst Xm x y s' c) (h := id) h
    (fun z => rfl) (fun z i _ => rfl) ?_
  intro i hi
  rcases i with ((t|t)|(q|k))
  · rfl
  · rfl
  · exact absurd ((cover_iff ..).mpr ⟨q, rfl⟩) hi
  · rfl

end Invocation

/-- **The certificate of one invocation, in block form.**  See the file header. -/
structure XCircuit (H T Sl C : Type) [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
    [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] where
  K : Circuit H T Sl C
  kx : ∀ t, Climb (lineL (K.tv t)) fullL
  ky : ∀ t, Climb zeroL (perpL (K.tv t))
  kc : ∀ c, Climb zeroL (K.cen c)
  r4 : List ℕ
  r5 : List ℕ
  r7 : List ℕ
  rF : List ℕ
  p4 : ∀ {α : Type} [Fintype α] [DecidableEq α] (Xm : XMap H α),
    XRoute (fun _ : Sl => Xm.Φ 0) (fun q => Xm.Φ (K.φ4 q).P) id (fun φ => rcost φ r4)
  p5 : ∀ {α : Type} [Fintype α] [DecidableEq α] (Xm : XMap H α),
    XRoute (fun q => Xm.Φ (K.φ4 q).P) (fun q => Xm.Φ (K.φ5 q).P) (actPoint K.L)
        (fun φ => rcost φ r5) ∧
    XRoute (fun q => Xm.Φ (K.φ4 q).P) (fun q => Xm.Φ (K.φ5 q).P) (actPoint K.Linvᵀ)
        (fun φ => rcost φ r5)
  p7 : ∀ {α : Type} [Fintype α] [DecidableEq α] (Xm : XMap H α),
    XRoute (fun q => Xm.Φ (K.φ5 q).P) (fun q => Xm.Φ (K.φ7 q).P) id (fun φ => rcost φ r7)
  pF : ∀ {α : Type} [Fintype α] [DecidableEq α] (Xm : XMap H α),
    XRoute (fun q => Xm.Φ (K.φ7 q).P) (fun _ : Sl => Xm.Φ 1) id (fun φ => rcost φ rF)

section Inv2
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]
variable {α : Type} [Fintype α] [DecidableEq α]

/-- price of the blocks of one invocation (forward or backward). -/
def XCircuit.cost (X : XCircuit H T Sl C) (φ : ℕ → ℝ) : ℝ :=
  rcost φ X.r4 + rcost φ X.r5 + rcost φ X.r7 + rcost φ X.rF + (∑ k, bcost φ (X.K.cen k).d)
    + 2 * ((Fintype.card T : ℝ) * bcost φ (Fintype.card H - 1))

variable (X : XCircuit H T Sl C)

/-- **Forward invocation, in blocks.**  Same scalar map as `SS.invocation_fwd`. -/
theorem xinvocation_fwd (Xm : XMap H α) :
    XRoute (xst Xm (fun t => lineL (X.K.tv t)) (fun _ => zeroL) (fun _ => zeroL) X.K.cen)
      (xst Xm (fun _ => fullL) (fun t => perpL (X.K.tv t)) (fun _ => fullL) (fun _ => zeroL))
      X.K.fwd X.cost := by
  have g1 := xst_gate Xm (x := fun t => lineL (X.K.tv t)) (y := fun _ => zeroL)
    (s := fun _ => zeroL) (c := X.K.cen) (bY : T → Box T Sl C) (bS : Sl → Box T Sl C) bS_inj
    (-((X.K.Jr * X.K.Cc + X.K.Jp) * X.K.L)) (fun a b _ => rfl)
  have c4 := xst_slots_id Xm (fun t => lineL (X.K.tv t)) (fun _ => zeroL) X.K.cen
    (s := fun _ => zeroL) (s' := X.K.φ4) (X.p4 Xm)
  have g4 := xst_gate Xm (x := fun t => lineL (X.K.tv t)) (y := fun _ => zeroL)
    (s := X.K.φ4) (c := X.K.cen) (bS : Sl → Box T Sl C) (bX : T → Box T Sl C) bX_inj
    X.K.V (fun a b h => X.K.sV a b h)
  have g5 := xst_slots Xm (fun t => lineL (X.K.tv t)) (fun _ => zeroL) X.K.cen (X.p5 Xm).1
  have g6a := xst_gate Xm (x := fun t => lineL (X.K.tv t)) (y := fun _ => zeroL)
    (s := X.K.φ5) (c := X.K.cen) (bC : C → Box T Sl C) (bS : Sl → Box T Sl C) bS_inj
    X.K.Cc (fun a b h => X.K.sC a b h)
  have d6 := xst_move Xm (x := fun t => lineL (X.K.tv t)) (x' := fun t => lineL (X.K.tv t))
    (y := fun _ => zeroL) (y' := fun _ => zeroL) X.K.φ5 (c := X.K.cen) (c' := fun _ => zeroL)
    (fun _ => XReach.refl _) (fun _ => XReach.refl _) (fun k => Xm.descend (X.kc k))
  have g6b := xst_gate Xm (x := fun t => lineL (X.K.tv t)) (y := fun _ => zeroL)
    (s := X.K.φ5) (c := fun _ => zeroL) (bY : T → Box T Sl C) (bC : C → Box T Sl C) bC_inj
    X.K.Jr (fun a b _ => rfl)
  have c7a := xst_slots_id Xm (fun t => lineL (X.K.tv t)) (fun _ => zeroL)
    (fun (_ : C) => zeroL) (s := X.K.φ5) (s' := X.K.φ7) (X.p7 Xm)
  have c7b := xst_move Xm (x := fun t => lineL (X.K.tv t)) (x' := fun t => lineL (X.K.tv t))
    (y := fun _ => zeroL) (y' := fun t => perpL (X.K.tv t)) X.K.φ7
    (c := fun (_ : C) => zeroL) (c' := fun _ => zeroL)
    (fun _ => XReach.refl _) (fun t => Xm.climb (X.ky t)) (fun _ => XReach.refl _)
  have g7 := xst_gate Xm (x := fun t => lineL (X.K.tv t)) (y := fun t => perpL (X.K.tv t))
    (s := X.K.φ7) (c := fun _ => zeroL) (bY : T → Box T Sl C) (bS : Sl → Box T Sl C) bS_inj
    X.K.Jp (fun a b h => (X.K.sJ a b h).symm)
  have c8a := xst_move Xm (x := fun t => lineL (X.K.tv t)) (x' := fun _ => fullL)
    (y := fun t => perpL (X.K.tv t)) (y' := fun t => perpL (X.K.tv t)) X.K.φ7
    (c := fun (_ : C) => zeroL) (c' := fun _ => zeroL)
    (fun t => Xm.climb (X.kx t)) (fun _ => XReach.refl _) (fun _ => XReach.refl _)
  have c8b := xst_slots_id Xm (fun (_ : T) => fullL) (fun t => perpL (X.K.tv t))
    (fun (_ : C) => zeroL) (s := X.K.φ7) (s' := fun _ => fullL) (X.pF Xm)
  have g8 := xst_wide Xm (x := fun _ => fullL) (y := fun t => perpL (X.K.tv t))
    (s := fun _ => fullL) (c := fun (_ : C) => zeroL) X.K.Linv (fun _ _ => rfl)
  have g9 := xst_gate Xm (x := fun _ => fullL) (y := fun t => perpL (X.K.tv t))
    (s := fun _ => fullL) (c := fun _ => zeroL) (bS : Sl → Box T Sl C) (bX : T → Box T Sl C)
    bX_inj (-X.K.V) (fun a b _ => rfl)
  have tot := ((((((((((((g1.trans c4).trans g4).trans g5).trans g6a).trans d6).trans g6b).trans
    c7a).trans c7b).trans g7).trans c8a).trans c8b).trans g8).trans g9
  refine (tot.castg (g' := X.K.fwd) rfl).cast (fun φ => ?_)
  simp only [XCircuit.cost, zeroL, perpL, lineL, fullL, Nat.sub_zero, sum_const, card_univ,
    nsmul_eq_mul, zero_add, add_zero, mul_zero]
  ring

/-- **Backward invocation, in blocks.**  Same scalar map as `SS.invocation_bwd`. -/
theorem xinvocation_bwd (Xm : XMap H α) :
    XRoute (xst Xm (fun t => lineL (X.K.tv t)) (fun _ => zeroL) (fun _ => zeroL) (fun _ => zeroL))
      (xst Xm (fun _ => fullL) (fun t => perpL (X.K.tv t)) (fun _ => fullL) X.K.cen)
      X.K.bwd X.cost := by
  have g1 := xst_gate Xm (x := fun t => lineL (X.K.tv t)) (y := fun _ => zeroL)
    (s := fun _ => zeroL) (c := fun _ => zeroL) (bS : Sl → Box T Sl C) (bY : T → Box T Sl C)
    bY_inj (((X.K.Jr * X.K.Cc + X.K.Jp) * X.K.L)ᵀ) (fun a b _ => rfl)
  have c4 := xst_slots_id Xm (fun t => lineL (X.K.tv t)) (fun _ => zeroL)
    (fun (_ : C) => zeroL) (s := fun _ => zeroL) (s' := X.K.φ4) (X.p4 Xm)
  have g4 := xst_gate Xm (x := fun t => lineL (X.K.tv t)) (y := fun _ => zeroL)
    (s := X.K.φ4) (c := fun _ => zeroL) (bX : T → Box T Sl C) (bS : Sl → Box T Sl C) bS_inj
    (-X.K.Vᵀ) (fun a b h => (X.K.sV b a (ne_of_negT X.K.V h)).symm)
  have g5 := xst_slots Xm (fun t => lineL (X.K.tv t)) (fun _ => zeroL) (fun (_ : C) => zeroL)
    (X.p5 Xm).2
  have g6a := xst_gate Xm (x := fun t => lineL (X.K.tv t)) (y := fun _ => zeroL)
    (s := X.K.φ5) (c := fun _ => zeroL) (bC : C → Box T Sl C) (bY : T → Box T Sl C) bY_inj
    X.K.Jrᵀ (fun a b _ => rfl)
  have c6 := xst_move Xm (x := fun t => lineL (X.K.tv t)) (x' := fun t => lineL (X.K.tv t))
    (y := fun _ => zeroL) (y' := fun _ => zeroL) X.K.φ5 (c := fun _ => zeroL) (c' := X.K.cen)
    (fun _ => XReach.refl _) (fun _ => XReach.refl _) (fun k => Xm.climb (X.kc k))
  have g6b := xst_gate Xm (x := fun t => lineL (X.K.tv t)) (y := fun _ => zeroL)
    (s := X.K.φ5) (c := X.K.cen) (bS : Sl → Box T Sl C) (bC : C → Box T Sl C) bC_inj
    (-X.K.Ccᵀ) (fun a b h => (X.K.sC b a (ne_of_negT X.K.Cc h)).symm)
  have c7a := xst_slots_id Xm (fun t => lineL (X.K.tv t)) (fun _ => zeroL)
    X.K.cen (s := X.K.φ5) (s' := X.K.φ7) (X.p7 Xm)
  have c7b := xst_move Xm (x := fun t => lineL (X.K.tv t)) (x' := fun t => lineL (X.K.tv t))
    (y := fun _ => zeroL) (y' := fun t => perpL (X.K.tv t)) X.K.φ7
    (c := X.K.cen) (c' := X.K.cen)
    (fun _ => XReach.refl _) (fun t => Xm.climb (X.ky t)) (fun _ => XReach.refl _)
  have g7 := xst_gate Xm (x := fun t => lineL (X.K.tv t)) (y := fun t => perpL (X.K.tv t))
    (s := X.K.φ7) (c := X.K.cen) (bS : Sl → Box T Sl C) (bY : T → Box T Sl C) bY_inj
    (-X.K.Jpᵀ) (fun a b h => X.K.sJ b a (ne_of_negT X.K.Jp h))
  have c8a := xst_move Xm (x := fun t => lineL (X.K.tv t)) (x' := fun _ => fullL)
    (y := fun t => perpL (X.K.tv t)) (y' := fun t => perpL (X.K.tv t)) X.K.φ7
    (c := X.K.cen) (c' := X.K.cen)
    (fun t => Xm.climb (X.kx t)) (fun _ => XReach.refl _) (fun _ => XReach.refl _)
  have c8b := xst_slots_id Xm (fun (_ : T) => fullL) (fun t => perpL (X.K.tv t))
    X.K.cen (s := X.K.φ7) (s' := fun _ => fullL) (X.pF Xm)
  have g8 := xst_wide Xm (x := fun _ => fullL) (y := fun t => perpL (X.K.tv t))
    (s := fun _ => fullL) (c := X.K.cen) X.K.Lᵀ (fun _ _ => rfl)
  have g9 := xst_gate Xm (x := fun _ => fullL) (y := fun t => perpL (X.K.tv t))
    (s := fun _ => fullL) (c := X.K.cen) (bX : T → Box T Sl C) (bS : Sl → Box T Sl C)
    bS_inj X.K.Vᵀ (fun a b _ => rfl)
  have tot := ((((((((((((g1.trans c4).trans g4).trans g5).trans g6a).trans c6).trans g6b).trans
    c7a).trans c7b).trans g7).trans c8a).trans c8b).trans g8).trans g9
  refine (tot.castg (g' := X.K.bwd) rfl).cast (fun φ => ?_)
  simp only [XCircuit.cost, zeroL, perpL, lineL, fullL, Nat.sub_zero, sum_const, card_univ,
    nsmul_eq_mul, zero_add, add_zero, mul_zero]
  ring

end Inv2
end
end CB
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.CB.xinvocation_fwd
#print axioms OAI.PowerSaving.CB.xinvocation_bwd
