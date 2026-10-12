import Work.Gauge.Defs

/-!
# (key: gauge-401) THE GAUGED INVOCATION THEOREM: `GLab.inv : GInvE`

DFT Bridge3, 2026-10-11.  Jacob Sussman's `Lab.inv` (`Work/GCert/Chain/InvThm.lean`, Apache-2.0) with entrance
labels (Dugongue, PR #401).  Changes to Jacob's forward word:

    erase | (free) ungauged slots to the old frame of 0 | y -= K s | free adapters to the labels (a gauged slot is
    already at its entrance label) | ... as Jacob ... | free adapters to the old frames | slots := ... | (free) slots
    to the full label in the base of their entrance | erase

The gate `y -= K s` reads only ungauged slots, by the E7 fact `GScal.hE`.  `gdirtyE` reframes per slot.  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace GX
open Binary Matrix Finset RAM SS CB BR CR GF RF
noncomputable section

section Win
variable {H α : Type} [Fintype H] [DecidableEq H] [Fintype α] [DecidableEq α]
namespace GWin
variable (W : GWin H α)

/-- ANY label of dimension 0 to the old frame of 0 (free). -/
theorem zeroB (U : SLbl H) (hd : U.dim = 0) :
    GReach (W.X.Φ U) (W.Xm.Φ 0) (fun _ => 0) := by
  rw [← mat_empty (OBase.canonical H)]
  refine W.toOld _ ∅ U (fun x => (insub_iff_of_card (coordPerm (OBase.canonical H)) U.G ∅ U.s
    (fun y hy => ?_) (by rw [Finset.card_empty]; exact hd.symm) x).symm)
  rw [coord_empty _ y hy]
  exact insub_zero _ _

/-- the old frame of 1 to ANY label of full dimension (free). -/
theorem topN (U : SLbl H) (hd : U.dim = Fintype.card H) :
    GReach (W.Xm.Φ 1) (W.X.Φ U) (fun _ => 0) := by
  have hU : U.s = univ := Finset.eq_univ_of_card U.s hd
  rw [← OBase.mat_univ (OBase.canonical H)]
  exact W.toNew _ univ U (fun x =>
    ⟨fun _ k hk => absurd (Finset.mem_univ k) hk,
     fun _ k hk => absurd (by rw [hU]; exact Finset.mem_univ k) hk⟩)

end GWin
end Win

section Dirt
variable {T Sl : Type} [Fintype T] [DecidableEq T] [Fintype Sl] [DecidableEq Sl]

lemma g1_apply_ne (M : Matrix (L3 T Sl) (L3 T Sl) ℚ) {i j : L3 T Sl} (e : i ≠ j) :
    g1 M i j = -(iY i * M i j * (1 - iX j - iY j)) := by
  simp only [g1, PX, PY, Matrix.sub_apply, Matrix.one_apply_ne e, Matrix.mul_sub, Matrix.mul_one,
    Matrix.mul_diagonal, Matrix.diagonal_mul]
  ring

lemma g1i_apply_ne (M : Matrix (L3 T Sl) (L3 T Sl) ℚ) {i j : L3 T Sl} (e : i ≠ j) :
    g1i M i j = iY i * M i j * (1 - iX j - iY j) := by
  simp only [g1i, PX, PY, Matrix.add_apply, Matrix.one_apply_ne e, Matrix.mul_sub, Matrix.mul_one,
    Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  ring

lemma off_ys {M : Matrix (L3 T Sl) (L3 T Sl) ℚ} {i j : L3 T Sl}
    (h : iY i * M i j * (1 - iX j - iY j) ≠ 0) : ∃ t q, i = lY t ∧ j = lS q ∧ M (lY t) (lS q) ≠ 0 := by
  rcases i with ((t|t)|q) <;> rcases j with ((t'|t')|q') <;> simp [iX, iY] at h
  exact ⟨t, q', rfl, rfl, h⟩

/-- an off-diagonal entry of `g1 M` joins a y row and a slot column. -/
lemma g1_off {M : Matrix (L3 T Sl) (L3 T Sl) ℚ} {i j : L3 T Sl} (h : g1 M i j ≠ 0) (e : i ≠ j) :
    ∃ t q, i = lY t ∧ j = lS q ∧ M (lY t) (lS q) ≠ 0 := by
  rw [g1_apply_ne M e, neg_ne_zero] at h
  exact off_ys h

lemma g1i_off {M : Matrix (L3 T Sl) (L3 T Sl) ℚ} {i j : L3 T Sl} (h : g1i M i j ≠ 0) (e : i ≠ j) :
    ∃ t q, i = lY t ∧ j = lS q ∧ M (lY t) (lS q) ≠ 0 := by
  rw [g1i_apply_ne M e] at h
  exact off_ys h

end Dirt

section Dirty
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]
variable {α : Type} [Fintype α] [DecidableEq α]

/-- **From clean frames to DIRTY helper slots, per slot** (Jacob's `gdirty_of_erased` with a start frame `E q`
and an end frame `F q` per slot). -/
theorem gdirtyE (Xm : XMap H α) (tv : T → Space H)
    {g : (Box T Sl C → ℂ) → (Box T Sl C → ℂ)} {cost : (ℕ → ℝ) → ℝ}
    (E F N Wn : Sl → CMat α) (hN : ∀ q, E q * N q = 1) (hW : ∀ q, F q = Wn q * E q)
    (Z : Sl → CMat α) (c0 c1 : C → CMat α)
    (h : GRoute (iin Xm tv E c0) (iout Xm tv F c1) g cost)
    (hcomm : ∀ (f : ℕ) (x : Data α (Box T Sl C) f),
      point f g (multiAct f (stamp (fun _ : T => (1 : CMat α)) (fun _ : T => (1 : CMat α))
          (fun q => N q * Z q) (fun _ : C => (1 : CMat α))) x)
        = multiAct f (stamp (fun _ : T => (1 : CMat α)) (fun _ : T => (1 : CMat α))
          (fun q => N q * Z q) (fun _ : C => (1 : CMat α))) (point f g x)) :
    GRoute (iin Xm tv Z c0) (iout Xm tv (fun q => Wn q * Z q) c1) g cost := by
  have h' := GRoute.reframe
    (stamp (fun _ : T => (1 : CMat α)) (fun _ : T => (1 : CMat α)) (fun q => N q * Z q)
      (fun _ : C => (1 : CMat α))) h hcomm
  have e0 : iin Xm tv Z c0 = fun r => iin Xm tv E c0 r *
      stamp (fun _ : T => (1 : CMat α)) (fun _ : T => (1 : CMat α)) (fun q => N q * Z q)
        (fun _ : C => (1 : CMat α)) r := by
    funext r
    rcases r with ((t|t)|(q|k))
    · show Xm.Φ (tt (tv t)) = Xm.Φ (tt (tv t)) * 1
      rw [Matrix.mul_one]
    · show Xm.Φ 0 = Xm.Φ 0 * 1
      rw [Matrix.mul_one]
    · show Z q = E q * (N q * Z q)
      rw [← Matrix.mul_assoc, hN, Matrix.one_mul]
    · show c0 k = c0 k * 1
      rw [Matrix.mul_one]
  have e1 : iout Xm tv (fun q => Wn q * Z q) c1 = fun r => iout Xm tv F c1 r *
      stamp (fun _ : T => (1 : CMat α)) (fun _ : T => (1 : CMat α)) (fun q => N q * Z q)
        (fun _ : C => (1 : CMat α)) r := by
    funext r
    rcases r with ((t|t)|(q|k))
    · show Xm.Φ 1 = Xm.Φ 1 * 1
      rw [Matrix.mul_one]
    · show Xm.Φ (1 + tt (tv t)) = Xm.Φ (1 + tt (tv t)) * 1
      rw [Matrix.mul_one]
    · show Wn q * Z q = F q * (N q * Z q)
      rw [hW, Matrix.mul_assoc, ← Matrix.mul_assoc (E q), hN, Matrix.one_mul]
    · show c1 k = c1 k * 1
      rw [Matrix.mul_one]
  rw [e0, e1]
  exact h'

end Dirty

section Thm
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]
variable {α : Type} [Fintype α] [DecidableEq α]
variable {S : GScal T Sl C} (L : GLab H S) (W : GWin H α)

/-- live frames at the start: old frames of x and y, entrance frames of the slots. -/
def gst0 (W : GWin H α) (tv : T → Space H) (ent : Sl → SLbl H) : L3 T Sl → CMat α :=
  Sum.elim (Sum.elim (fun t => W.Xm.Φ (tt (tv t))) (fun _ => W.Xm.Φ 0)) (fun q => W.X.Φ (ent q))

/-- live frames for the gate `y -= K s`: the ungauged slots at the old frame of 0. -/
def gst1 (W : GWin H α) (tv : T → Space H) (ent : Sl → SLbl H) (g : Finset Sl) : L3 T Sl → CMat α :=
  Sum.elim (Sum.elim (fun t => W.Xm.Φ (tt (tv t))) (fun _ => W.Xm.Φ 0))
    (fun q => if q ∈ g then W.X.Φ (ent q) else W.Xm.Φ 0)

/-- live frames at the end: old frames of x and y, full labels of the slots. -/
def gen2 (W : GWin H α) (tv : T → Space H) (ent : Sl → SLbl H) : L3 T Sl → CMat α :=
  Sum.elim (Sum.elim (fun _ => W.Xm.Φ 1) (fun t => W.Xm.Φ (1 + tt (tv t)))) (fun q => W.X.Φ (ent q).top)

/-- (free) ungauged slots to the old frame of 0. -/
theorem GLab.pre : GRoute (gst0 W L.tv L.ent) (gst1 W L.tv L.ent S.gauged) id (fun _ => 0) := by
  refine (GRoute.reach_all _ _ (fun _ _ => 0) ?_).cast (fun φ => by simp)
  rintro ((t|t)|q)
  · exact GReach.refl _
  · exact GReach.refl _
  · show GReach (W.X.Φ (L.ent q)) (if q ∈ S.gauged then W.X.Φ (L.ent q) else W.Xm.Φ 0) _
    by_cases hq : q ∈ S.gauged
    · rw [if_pos hq]; exact GReach.refl _
    · rw [if_neg hq]; exact W.zeroB _ (L.hent q hq)

/-- (free) the start frames to the labels of the certificate. -/
theorem GLab.ad0 :
    GRoute (gst1 W L.tv L.ent S.gauged) (fun r => W.X.Φ (L.lab0 r)) id (fun _ => 0) := by
  refine (GRoute.reach_all _ _ (fun _ _ => 0) ?_).cast (fun φ => by simp)
  rintro ((t|t)|q)
  · obtain ⟨p, hp⟩ := L.hgap t
    obtain ⟨A, k, hA⟩ := exists_base_one (L.tv t) (L.hunit t) p hp
    have h := W.line A k (L.lab0 (lX t)) (L.h0x t).1 (by rw [hA]; exact (L.h0x t).2)
    rw [hA] at h
    exact h
  · exact W.zero _ (L.h0y t)
  · show GReach (if q ∈ S.gauged then W.X.Φ (L.ent q) else W.Xm.Φ 0) (W.X.Φ (L.lab0 (lS q))) _
    rw [L.h0s' q]
    by_cases hq : q ∈ S.gauged
    · rw [if_pos hq]; exact GReach.refl _
    · rw [if_neg hq]; exact W.zero _ (L.hent q hq)

/-- (free) the end labels of the certificate to the old frames. -/
theorem GLab.adF :
    GRoute (fun r => W.X.Φ (L.labF r)) (fun r : L3 T Sl => W.Xm.Φ (labE L.tv r)) id
      (fun _ => 0) := by
  refine (GRoute.reach_all _ _ (fun _ _ => 0) ?_).cast (fun φ => by simp)
  rintro ((t|t)|q)
  · exact W.full _ (L.hFx t)
  · obtain ⟨p, hp⟩ := L.hgap t
    obtain ⟨A, k, hA⟩ := exists_base_one (L.tv t) (L.hunit t) p hp
    have h := W.perp A k (L.labF (lY t)) (L.hFy t).1 (by rw [hA]; exact (L.hFy t).2)
    rw [hA] at h
    exact h
  · exact W.full _ (L.hFs q)

/-- (free) slots from the old frame of 1 to the full label in the base of their entrance. -/
theorem GLab.post :
    GRoute (fun r : L3 T Sl => W.Xm.Φ (labE L.tv r)) (gen2 W L.tv L.ent) id (fun _ => 0) := by
  refine (GRoute.reach_all _ _ (fun _ _ => 0) ?_).cast (fun φ => by simp)
  rintro ((t|t)|q)
  · exact GReach.refl _
  · exact GReach.refl _
  · exact W.topN _ (SLbl.top_dim _)

lemma GLab.cfacts (hb : Fintype.card H < Fintype.card α) (k : C) :
    (∀ x, L.z0.Mem x → (L.cen k).Mem x) ∧ L.z0.dim < (L.cen k).dim ∧
    (L.cen k).dim - L.z0.dim < Fintype.card α := by
  refine ⟨fun x hx => ?_, by rw [L.hz0]; exact L.hcen k, ?_⟩
  · rw [mem_dim_zero L.z0 L.hz0 hx]
    exact insub_zero _ _
  · have h1 : (L.cen k).dim ≤ Fintype.card H := Finset.card_le_univ _
    omega

lemma GLab.cdn (k : C) :
    GReach (W.X.Φ (L.cen k)) (W.X.Φ L.z0) (fun φ => bcost φ (L.cen k).dim) := by
  obtain ⟨h0, h1, h2⟩ := L.cfacts W.big k
  have h := (W.X.fmv_sup L.z0 (L.cen k) h0 h1 h2).reach
  have h' : GReach (W.X.Φ (L.cen k)) (W.X.Φ L.z0)
      (fun φ => rcost φ [(L.cen k).dim - L.z0.dim]) := GReach.ofReach h
  exact h'.cast (fun φ => by rw [rcost_single, L.hz0, Nat.sub_zero])

lemma GLab.cupk (k : C) :
    GReach (W.X.Φ L.z0) (W.X.Φ (L.cen k)) (fun φ => bcost φ (L.cen k).dim) := by
  obtain ⟨h0, h1, h2⟩ := L.cfacts W.big k
  have h := (W.X.fmv_sub L.z0 (L.cen k) h0 h1 h2).reach
  have h' : GReach (W.X.Φ L.z0) (W.X.Φ (L.cen k))
      (fun φ => rcost φ [(L.cen k).dim - L.z0.dim]) := GReach.ofReach h
  exact h'.cast (fun φ => by rw [rcost_single, L.hz0, Nat.sub_zero])

theorem GLab.cdown (Sf : L3 T Sl → CMat α) :
    GRoute (glue Sf (fun k => W.X.Φ (L.cen k))) (glue Sf (fun _ : C => W.X.Φ L.z0)) id
      (fun φ => ∑ k, bcost φ (L.cen k).dim) :=
  greach_copies Sf _ _ _ (fun k => L.cdn W k)

theorem GLab.cup (Sf : L3 T Sl → CMat α) :
    GRoute (glue Sf (fun _ : C => W.X.Φ L.z0)) (glue Sf (fun k => W.X.Φ (L.cen k))) id
      (fun φ => ∑ k, bcost φ (L.cen k).dim) :=
  greach_copies Sf _ _ _ (fun k => L.cupk W k)

/-- the gate `y -= K s` (or its transposed inverse) is legal on `gst1`: it reads only ungauged slots. -/
lemma GLab.gate_ok {i j : L3 T Sl} (t : T) (q : Sl) (hi : i = lY t) (hj : j = lS q)
    (hM : S.toScal.Mt (lY t) (lS q) ≠ 0) :
    gst1 W L.tv L.ent S.gauged i = gst1 W L.tv L.ent S.gauged j := by
  subst hi; subst hj
  have hq : q ∉ S.gauged := fun hq => hM (S.hE q hq t)
  show W.Xm.Φ 0 = if q ∈ S.gauged then W.X.Φ (L.ent q) else W.Xm.Φ 0
  rw [if_neg hq]

/-- **Forward word on clean frames, gauged.** -/
theorem GLab.fwd_erasedE (c0 c1 : C → CMat α) :
    GRoute (iin W.Xm L.tv (fun q => W.X.Φ (L.ent q)) c0)
      (iout W.Xm L.tv (fun q => W.X.Φ (L.ent q).top) c1) shearF L.cost := by
  have a1 : GRoute (gst1 W L.tv L.ent S.gauged) (gst1 W L.tv L.ent S.gauged)
      (actPoint (g1 S.toScal.Mt)) (fun _ => 0) :=
    GRoute.gate (g1 S.toScal.Mt) _ _ (fun i j hij => by
      by_cases e : i = j
      · subst e; rfl
      · obtain ⟨t, q, hi, hj, hM⟩ := g1_off hij e
        exact L.gate_ok W t q hi hj hM)
  have b3 : GRoute (fun r : L3 T Sl => W.Xm.Φ (labE L.tv r))
      (fun r : L3 T Sl => W.Xm.Φ (labE L.tv r))
      (actPoint (g8 S.toScal.Mti)) (fun _ => 0) :=
    GRoute.gate (g8 S.toScal.Mti) _ _ (fun i j hij => by
      by_cases e : i = j
      · subst e; rfl
      · have f := g8_facts S.toScal.hiy
        obtain ⟨h1, h2, h3⟩ := offdiag_s f.1 f.2.1 f.2.2 hij e
        exact end_old W.Xm L.tv i j h1 h2 h3)
  have seg1 : GRoute (gst0 W L.tv L.ent) (fun r => W.X.Φ (L.labA r))
      S.toScal.f1 (fun φ => rcost φ L.rA) :=
    ((((L.pre W).trans a1).trans (L.ad0 W)).trans (L.pA W.X W.big).1).cast (fun φ => by simp)
  have seg2 : GRoute (fun r => W.X.Φ (L.labA r)) (gen2 W L.tv L.ent)
      S.toScal.f2 (fun φ => rcost φ L.rB + rcost φ L.rF) :=
    (((((L.pB W.X W.big).1.trans (L.pF W.X W.big)).trans (L.adF W)).trans b3).trans (L.post W)).cast
      (fun φ => by simp)
  have e0 : GRoute (iin W.Xm L.tv (fun q => W.X.Φ (L.ent q)) c0)
      (glue (gst0 W L.tv L.ent) (fun k => W.X.Φ (L.cen k))) eraseC (fun _ => 0) :=
    GRoute.ofX (xerase (fun t => rfl) (fun t => rfl) (fun q => rfl))
  have L1 := glift_live (fun k => W.X.Φ (L.cen k)) seg1
  have m1 : GRoute (glue (fun r => W.X.Φ (L.labA r)) (fun k => W.X.Φ (L.cen k)))
      (glue (fun r => W.X.Φ (L.labA r)) (fun k => W.X.Φ (L.cen k)))
      (fun z => addBlk bC (ap S.Cc (z ∘ bS)) z) (fun _ => 0) :=
    GRoute.ofX (xgate_shear bC bS bS_inj S.Cc (fun k q h => congrArg W.X.Φ (L.hAc k q h)))
  have m2 := L.cdown W (fun r => W.X.Φ (L.labA r))
  have m3 : GRoute (glue (fun r => W.X.Φ (L.labA r)) (fun _ : C => W.X.Φ L.z0))
      (glue (fun r => W.X.Φ (L.labA r)) (fun _ : C => W.X.Φ L.z0))
      (fun z => addBlk bY (ap S.Jr (z ∘ bC)) z) (fun _ => 0) :=
    GRoute.ofX (xgate_shear bY bC bC_inj S.Jr (fun t k _ => congrArg W.X.Φ (L.hAy t)))
  have L2 := glift_live (fun _ : C => W.X.Φ L.z0) seg2
  have e1 : GRoute (glue (gen2 W L.tv L.ent) (fun _ : C => W.X.Φ L.z0))
      (iout W.Xm L.tv (fun q => W.X.Φ (L.ent q).top) c1) eraseC (fun _ => 0) :=
    GRoute.ofX (xerase (fun t => rfl) (fun t => rfl) (fun q => rfl))
  have tot := (((((e0.trans L1).trans m1).trans m2).trans m3).trans L2).trans e1
  refine (tot.castg (g' := shearF) (funext fun z => S.toScal.fwd_scalar z)).cast (fun φ => ?_)
  simp only [GLab.cost, zero_add, add_zero]
  ring

/-- **Backward word on clean frames, gauged.** -/
theorem GLab.bwd_erasedE (c0 c1 : C → CMat α) :
    GRoute (iin W.Xm L.tv (fun q => W.X.Φ (L.ent q)) c0)
      (iout W.Xm L.tv (fun q => W.X.Φ (L.ent q).top) c1) shearB L.cost := by
  have a1 : GRoute (gst1 W L.tv L.ent S.gauged) (gst1 W L.tv L.ent S.gauged)
      (actPoint (g1i S.toScal.Mt)ᵀ) (fun _ => 0) :=
    GRoute.gate (g1i S.toScal.Mt)ᵀ _ _ (fun i j hij => by
      by_cases e : i = j
      · subst e; rfl
      · have hij' : g1i S.toScal.Mt j i ≠ 0 := hij
        obtain ⟨t, q, hj, hi, hM⟩ := g1i_off hij' (Ne.symm e)
        exact (L.gate_ok W t q hj hi hM).symm)
  have b3 : GRoute (fun r : L3 T Sl => W.Xm.Φ (labE L.tv r))
      (fun r : L3 T Sl => W.Xm.Φ (labE L.tv r))
      (actPoint (h8 S.toScal.Mt)ᵀ) (fun _ => 0) :=
    GRoute.gate (h8 S.toScal.Mt)ᵀ _ _ (fun i j hij => by
      by_cases e : i = j
      · subst e; rfl
      · have hij' : h8 S.toScal.Mt j i ≠ 0 := hij
        have f := h8_facts S.toScal.hmy
        obtain ⟨h1, h2, h3⟩ := offdiag_s f.1 f.2.1 f.2.2 hij' (Ne.symm e)
        exact (end_old W.Xm L.tv j i h1 h2 h3).symm)
  have seg1 : GRoute (gst0 W L.tv L.ent) (fun r => W.X.Φ (L.labA r))
      S.toScal.b1 (fun φ => rcost φ L.rA) :=
    ((((L.pre W).trans a1).trans (L.ad0 W)).trans (L.pA W.X W.big).2).cast (fun φ => by simp)
  have seg2 : GRoute (fun r => W.X.Φ (L.labA r)) (gen2 W L.tv L.ent)
      S.toScal.b2 (fun φ => rcost φ L.rB + rcost φ L.rF) :=
    (((((L.pB W.X W.big).2.trans (L.pF W.X W.big)).trans (L.adF W)).trans b3).trans (L.post W)).cast
      (fun φ => by simp)
  have e0 : GRoute (iin W.Xm L.tv (fun q => W.X.Φ (L.ent q)) c0)
      (glue (gst0 W L.tv L.ent) (fun _ : C => W.X.Φ L.z0)) eraseC (fun _ => 0) :=
    GRoute.ofX (xerase (fun t => rfl) (fun t => rfl) (fun q => rfl))
  have L1 := glift_live (fun _ : C => W.X.Φ L.z0) seg1
  have m1 : GRoute (glue (fun r => W.X.Φ (L.labA r)) (fun _ : C => W.X.Φ L.z0))
      (glue (fun r => W.X.Φ (L.labA r)) (fun _ : C => W.X.Φ L.z0))
      (fun z => addBlk bC (ap S.Jrᵀ (z ∘ bY)) z) (fun _ => 0) :=
    GRoute.ofX (xgate_shear bC bY bY_inj S.Jrᵀ (fun k t _ => (congrArg W.X.Φ (L.hAy t)).symm))
  have m2 := L.cup W (fun r => W.X.Φ (L.labA r))
  have m3 : GRoute (glue (fun r => W.X.Φ (L.labA r)) (fun k => W.X.Φ (L.cen k)))
      (glue (fun r => W.X.Φ (L.labA r)) (fun k => W.X.Φ (L.cen k)))
      (fun z => addBlk bS (ap (-S.Ccᵀ) (z ∘ bC)) z) (fun _ => 0) :=
    GRoute.ofX (xgate_shear bS bC bC_inj (-S.Ccᵀ)
      (fun q k h => (congrArg W.X.Φ (L.hAc k q (ne_of_negT S.Cc h))).symm))
  have L2 := glift_live (fun k => W.X.Φ (L.cen k)) seg2
  have e1 : GRoute (glue (gen2 W L.tv L.ent) (fun k => W.X.Φ (L.cen k)))
      (iout W.Xm L.tv (fun q => W.X.Φ (L.ent q).top) c1) eraseC (fun _ => 0) :=
    GRoute.ofX (xerase (fun t => rfl) (fun t => rfl) (fun q => rfl))
  have tot := (((((e0.trans L1).trans m1).trans m2).trans m3).trans L2).trans e1
  refine (tot.castg (g' := shearB) (funext fun z => S.toScal.bwd_scalar z)).cast (fun φ => ?_)
  simp only [GLab.cost, zero_add, add_zero]
  ring

/-- **THE GAUGED INVOCATION THEOREM.**  The two halves of a gauged certificate are a gauged invocation package,
with the price `L.cost`. -/
def GLab.inv : GInvE H T Sl C where
  tv := L.tv
  hunit := L.hunit
  hgap := L.hgap
  cost := L.cost
  ent := L.ent
  fwd := fun W N Wn hN hW Z c0 c1 =>
    gdirtyE W.Xm L.tv _ _ N Wn hN hW Z c0 c1 (L.fwd_erasedE W c0 c1)
      (shearF_comm (fun _ => 1) (fun q => N q * Z q) (fun _ => 1))
  bwd := fun W N Wn hN hW Z c0 c1 =>
    gdirtyE W.Xm L.tv _ _ N Wn hN hW Z c0 c1 (L.bwd_erasedE W c0 c1)
      (shearB_comm (fun _ => 1) (fun q => N q * Z q) (fun _ => 1))

@[simp] lemma GLab.inv_cost (φ : ℕ → ℝ) : L.inv.cost φ = L.cost φ := rfl
@[simp] lemma GLab.inv_tv : L.inv.tv = L.tv := rfl
@[simp] lemma GLab.inv_ent : L.inv.ent = L.ent := rfl

end Thm
end
end GX
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.GX.GLab.fwd_erasedE
#print axioms OAI.PowerSaving.GX.GLab.bwd_erasedE
#print axioms OAI.PowerSaving.GX.GLab.inv
