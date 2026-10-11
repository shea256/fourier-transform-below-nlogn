import Work.Combine.XInvocation
import Work.SharedSumStructured.Certificate

/-!
# (key: combine) The two-stage network for an arbitrary helper circuit, in WHOLE BLOCKS

Block version of `Work.SharedSumStructured.Network` and `.Certificate`.  The roles, the frames
`S0 .. S5` and the scalar maps are those of the structured development (`NetData`); only the
word changes: every climb of a role inside one orthonormal basis is ONE block.

`xnetwork_certificate`: for every `XNetData` (a block circuit `XCircuit`, bases through the input
vectors, padding, `2 ≤ |H|`) there is a PROPER block word `w` on `α = H × H` with

* `LiveKernel Sum.inl w.flat` (the scratch-engine certificate of the structured development,
  for the flat word of `w`);
* for EVERY price list `φ`:  `w.costR φ = N.cost φ`, where

      N.cost φ = 2 |T| (price of one invocation)          -- the two stages
               + 2 |T|^2 bcost φ ((h-1)^2)                -- banks X, Y between the stages
               + 2 |T| |Sl| bcost φ ((h-1) h)             -- helper slots outside their invocation
               + pad (φ (m-1) + φ 1)                      -- idle roles, split (m-1)+1
               + |T|^2 φ 1                                -- endpoint copies.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace CB
open Binary Matrix Finset RAM SS
noncomputable section

/-- a block circuit, bases through the input vectors, padding. -/
structure XNetData (H T Sl C : Type) [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
    [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] where
  X : XCircuit H T Sl C
  base : T → OBase H
  piv : T → H
  hbase : ∀ t, X.K.tv t = (base t).v (piv t)
  pad : ℕ
  hH : 2 ≤ Fintype.card H

section Sums
variable {T Sl C : Type} {P : ℕ} [Fintype T] [Fintype Sl] [Fintype C]

lemma sum_mkStateR (fX fY : Key T → ℝ) (fS : Bool → T → Sl → ℝ) (fI : Fin P → ℝ)
    (fC : Bool → T → C → ℝ) (fZ : Key T → ℝ) :
    ∑ r : Role T Sl C P, mkState fX fY fS fI fC fZ r
      = ∑ k, fX k + ∑ k, fY k + (∑ r, ∑ q, fS true r q + ∑ r, ∑ q, fS false r q) + ∑ i, fI i
        + (∑ r, ∑ c, fC true r c + ∑ r, ∑ c, fC false r c) + ∑ k, fZ k := by
  simp only [Fintype.sum_sum_type, mkState, Fintype.sum_prod_type, Fintype.sum_bool]
  ring

end Sums

section Net
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]
variable (N : XNetData H T Sl C)

/-- the network data of the structured development (roles, frames, scalar maps). -/
@[reducible] def XNetData.D : NetData H T Sl C := ⟨N.X.K, N.base, N.piv, N.hbase, N.pad⟩

/-- stage 1: the forward invocation on every block `pos1 r`, in blocks. -/
lemma XNetData.stage1_x :
    XRoute (fun r => (N.D.S0 r).M) (fun r => (N.D.S1 r).M) N.D.stage1
      (fun φ => (Fintype.card T : ℝ) * N.X.cost φ) := by
  have he0 : ∀ role : Role T Sl C N.D.pad, (∀ i : T, role ∉ covered (e1 i)) →
      N.D.S0 role = N.D.S1 role := by
    intro role hr
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
    · simp only [NetData.S0, NetData.S1, mkState]
  have key := XRoute.parallel (ρ := Box T Sl C) (σ := Role T Sl C N.D.pad) (J := T)
    (e := fun r => e1 r) (fun r r' h x => e1_dis r r' h x)
    (S := fun r => (N.D.S0 r).M) (T := fun r => (N.D.S1 r).M) (d := fun _ => N.X.cost)
    (g := N.D.stage1) (h := fun _ => N.X.K.fwd)
    (fun r => by
      have e0 : (fun r => (N.D.S0 r).M) ∘ (e1 r)
          = xst (xmap1 N.hH (N.base r) (N.piv r)) (fun t => lineL (N.X.K.tv t)) (fun _ => zeroL)
            (fun _ => zeroL) N.X.K.cen := by
        funext b; rcases b with ((t|t)|(q|c)) <;> rfl
      have e1' : (fun r => (N.D.S1 r).M) ∘ (e1 r)
          = xst (xmap1 N.hH (N.base r) (N.piv r)) (fun _ => fullL)
            (fun t => perpL (N.X.K.tv t)) (fun _ => fullL) (fun _ => zeroL) := by
        funext b; rcases b with ((t|t)|(q|c)) <;> rfl
      rw [e0, e1']
      exact xinvocation_fwd N.X (xmap1 N.hH (N.base r) (N.piv r)))
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
    (fun role hr => congrArg Fr.M (he0 role hr))
  refine key.cast (fun φ => ?_)
  simp

/-- stage 2: the backward invocation on every block `pos2 r`, in blocks. -/
lemma XNetData.stage2_x :
    XRoute (fun r => (N.D.S2 r).M) (fun r => (N.D.S3 r).M) N.D.stage2
      (fun φ => (Fintype.card T : ℝ) * N.X.cost φ) := by
  have he0 : ∀ role : Role T Sl C N.D.pad, (∀ i : T, role ∉ covered (e2 i)) →
      N.D.S2 role = N.D.S3 role := by
    intro role hr
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
    · simp only [NetData.S2, NetData.S3, mkState]
  have key := XRoute.parallel (ρ := Box T Sl C) (σ := Role T Sl C N.D.pad) (J := T)
    (e := fun r => e2 r) (fun r r' h x => e2_dis r r' h x)
    (S := fun r => (N.D.S2 r).M) (T := fun r => (N.D.S3 r).M) (d := fun _ => N.X.cost)
    (g := N.D.stage2) (h := fun _ => N.X.K.bwd)
    (fun r => by
      have e0 : (fun r => (N.D.S2 r).M) ∘ (e2 r)
          = xst (xmap2 N.hH (N.base r) (N.piv r)) (fun t => lineL (N.X.K.tv t)) (fun _ => zeroL)
            (fun _ => zeroL) (fun _ => zeroL) := by
        funext b; rcases b with ((t|t)|(q|c)) <;> rfl
      have e1' : (fun r => (N.D.S3 r).M) ∘ (e2 r)
          = xst (xmap2 N.hH (N.base r) (N.piv r)) (fun _ => fullL)
            (fun t => perpL (N.X.K.tv t)) (fun _ => fullL) N.X.K.cen := by
        funext b; rcases b with ((t|t)|(q|c)) <;> rfl
      rw [e0, e1']
      exact xinvocation_bwd N.X (xmap2 N.hH (N.base r) (N.piv r)))
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
    (fun role hr => congrArg Fr.M (he0 role hr))
  refine key.cast (fun φ => ?_)
  simp

/-- price of the exterior climbs between the two stages. -/
def XNetData.extCost (φ : ℕ → ℝ) : ℝ :=
  2 * ((Fintype.card T : ℝ) * (Fintype.card T : ℝ) * bcost φ (rkBank H))
    + 2 * ((Fintype.card T : ℝ) * (Fintype.card Sl : ℝ) * bcost φ (rkSlot H))
    + (N.pad : ℝ) * (φ (Fintype.card (H × H) - 1) + φ 1)

/-- the exterior climbs between the two stages: ONE block per bank role and per helper slot,
two blocks `(m-1)+1` per idle role. -/
lemma XNetData.ext_x :
    XRoute (fun r => (N.D.S1 r).M) (fun r => (N.D.S2 r).M) id N.extCost := by
  have H1 := XRoute.reach_all (fun r => (N.D.S1 r).M) (fun r => (N.D.S2 r).M)
    (mkState (fun _ φ => bcost φ (rkBank H)) (fun _ φ => bcost φ (rkBank H))
      (fun _ _ _ φ => bcost φ (rkSlot H)) (fun _ φ => φ (Fintype.card (H × H) - 1) + φ 1)
      (fun _ _ _ _ => 0) (fun _ _ => 0)) (by
      rintro (((⟨a,b⟩|⟨a,b⟩)|(⟨b,r,q⟩|i))|(⟨b,r,c⟩|k))
      · show XReach (Phi1 ((N.base b).v (N.piv b)) 1)
          (Phi2 ((N.base a).v (N.piv a)) (tt (N.X.K.tv b))) (fun φ => bcost φ (rkBank H))
        rw [N.hbase b]
        exact xreach_X N.hH (N.base a) (N.base b) (N.piv a) (N.piv b)
      · show XReach (Phi1 ((N.base b).v (N.piv b)) (1 + tt (N.X.K.tv a)))
          (Phi2 ((N.base a).v (N.piv a)) 0) (fun φ => bcost φ (rkBank H))
        rw [N.hbase a]
        exact xreach_Y N.hH (N.base a) (N.base b) (N.piv a) (N.piv b)
      · cases b
        · show XReach (Phi1 ((N.base r).v (N.piv r)) 1) (kernel (H × H))
            (fun φ => bcost φ (rkSlot H))
          exact xreach_S1 N.hH (N.base r) (N.piv r)
        · show XReach (1 : CMat (H × H)) (Phi2 ((N.base r).v (N.piv r)) 0)
            (fun φ => bcost φ (rkSlot H))
          exact xreach_S2 N.hH (N.base r) (N.piv r)
      · show XReach (1 : CMat (H × H)) (kernel (H × H))
          (fun φ => φ (Fintype.card (H × H) - 1) + φ 1)
        exact xreach_idle N.hH
      · cases b
        · show XReach (Phi1 ((N.base r).v (N.piv r)) 0) (Phi1 ((N.base r).v (N.piv r)) 0)
            (fun _ => 0)
          exact XReach.refl _
        · show XReach (Phi2 ((N.base r).v (N.piv r)) 0) (Phi2 ((N.base r).v (N.piv r)) 0)
            (fun _ => 0)
          exact XReach.refl _
      · show XReach (Phi2 ((N.base k.1).v (N.piv k.1)) 1) (Phi2 ((N.base k.1).v (N.piv k.1)) 1)
          (fun _ => 0)
        exact XReach.refl _)
  refine H1.cast (fun φ => ?_)
  simp_rw [mkState_map (fun c : (ℕ → ℝ) → ℝ => c φ)]
  rw [sum_mkStateR]
  simp only [XNetData.extCost, sum_const, card_univ, Fintype.card_prod, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_mul, mul_zero, add_zero]
  ring

/-- endpoint, first gate: `Z += X` (both at the full frame). -/
lemma XNetData.endA_x :
    XRoute (fun r => (N.D.S3 r).M) (fun r => (N.D.S3 r).M) N.D.endA (fun _ => 0) :=
  xgate_shear iZ iX iX_inj 1 (fun a b h => by
    have hab : a = b := by
      by_contra hne
      exact h (Matrix.one_apply_ne hne)
    subst hab
    rfl)

/-- endpoint, second gate: `Y += Z` (both one line below the full frame). -/
lemma XNetData.endB_x :
    XRoute (fun r => (N.D.S4 r).M) (fun r => (N.D.S4 r).M) N.D.endB (fun _ => 0) :=
  xgate_shear iY iZ iZ_inj 1 (fun a b h => by
    have hab : a = b := by
      by_contra hne
      exact h (Matrix.one_apply_ne hne)
    subst hab
    rfl)

/-- the endpoint copies come down one line: ONE block of rank 1 per bank pair. -/
lemma XNetData.down_x :
    XRoute (fun r => (N.D.S3 r).M) (fun r => (N.D.S4 r).M) id
      (fun φ => (Fintype.card T : ℝ) * (Fintype.card T : ℝ) * φ 1) := by
  have H1 := XRoute.reach_all (fun r => (N.D.S3 r).M) (fun r => (N.D.S4 r).M)
    (mkState (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ _ => 0) (fun _ _ => 0) (fun _ _ _ _ => 0)
      (fun _ φ => φ 1)) (by
      rintro (((⟨a,b⟩|⟨a,b⟩)|(⟨b,r,q⟩|i))|(⟨b,r,c⟩|⟨a,b⟩))
      · show XReach (Phi2 ((N.base a).v (N.piv a)) 1) (Phi2 ((N.base a).v (N.piv a)) 1)
          (fun _ => 0)
        exact XReach.refl _
      · show XReach (Phi2 ((N.base a).v (N.piv a)) (1 + tt (N.X.K.tv b)))
          (Phi2 ((N.base a).v (N.piv a)) (1 + tt (N.X.K.tv b))) (fun _ => 0)
        exact XReach.refl _
      · cases b
        · show XReach (kernel (H × H)) (kernel (H × H)) (fun _ => 0)
          exact XReach.refl _
        · show XReach (Phi2 ((N.base r).v (N.piv r)) 1) (Phi2 ((N.base r).v (N.piv r)) 1)
            (fun _ => 0)
          exact XReach.refl _
      · show XReach (kernel (H × H)) (kernel (H × H)) (fun _ => 0)
        exact XReach.refl _
      · cases b
        · show XReach (Phi1 ((N.base r).v (N.piv r)) 0) (Phi1 ((N.base r).v (N.piv r)) 0)
            (fun _ => 0)
          exact XReach.refl _
        · show XReach (Phi2 ((N.base r).v (N.piv r)) (N.X.K.cen c).P)
            (Phi2 ((N.base r).v (N.piv r)) (N.X.K.cen c).P) (fun _ => 0)
          exact XReach.refl _
      · show XReach (Phi2 ((N.base a).v (N.piv a)) 1)
          (Phi2 ((N.base a).v (N.piv a)) (1 + tt (N.X.K.tv b))) (fun φ => φ 1)
        rw [N.hbase b, Phi2_full]
        exact xreach_end N.hH (N.base a) (N.base b) (N.piv a) (N.piv b))
  refine H1.cast (fun φ => ?_)
  simp_rw [mkState_map (fun c : (ℕ → ℝ) → ℝ => c φ)]
  rw [sum_mkStateR]
  simp only [sum_const, card_univ, Fintype.card_prod, nsmul_eq_mul, Nat.cast_mul, mul_zero,
    add_zero, zero_add, sum_const_zero]

/-- price of the whole network, for a price list `φ`. -/
def XNetData.cost (φ : ℕ → ℝ) : ℝ :=
  2 * ((Fintype.card T : ℝ) * N.X.cost φ) + N.extCost φ
    + (Fintype.card T : ℝ) * (Fintype.card T : ℝ) * φ 1

lemma XNetData.total_x :
    XRoute (fun r => (N.D.S0 r).M) (fun r => (N.D.S4 r).M) N.D.Gtot N.cost := by
  have h := ((((N.stage1_x.trans N.ext_x).trans N.stage2_x).trans N.endA_x).trans
    N.down_x).trans N.endB_x
  refine (h.castg (g' := N.D.Gtot) rfl).cast (fun φ => ?_)
  simp only [XNetData.cost]
  ring

/-- **The scratch certificate of the two-stage network, in whole blocks, with its exact
price for every price list.** -/
theorem xnetwork_certificate :
    ∃ w : BWord (H × H) (Role T Sl C N.D.pad),
      w.Proper (Fintype.card (H × H)) ∧ (∀ φ : ℕ → ℝ, w.costR φ = N.cost φ) ∧
      LiveKernel (Sum.inl : Live T Sl N.D.pad → Role T Sl C N.D.pad) w.flat := by
  have hm := two_le_sq N.hH
  have R1 := N.total_x
  have R2 : XRoute (fun r => (N.D.S4 r).M) N.D.S5 id (fun _ => 0) :=
    XRoute.shifts hm (fun r => (N.D.S4 r).M) N.D.corr
  have R3 : XRoute N.D.S5 (fun r => N.D.S5 (pull r)) (actPoint recM) (fun _ => 0) :=
    XRoute.gate recM N.D.S5 _ (fun i j h => by
      have hj : j = pull i := by
        by_contra hne
        exact h (by simp [recM, hne])
      rw [hj])
  have Rt := ((R1.trans R2).trans R3).cast (c' := N.cost) (fun φ => by ring)
  have hSinv : ∀ r, ∃ M, (N.D.S0 r).M * M = 1 := by
    rintro (((k|k)|(⟨b,r,q⟩|i))|(⟨b,r,c⟩|k))
    · exact Phi1_inv _ _
    · exact Phi1_inv _ _
    · cases b
      · exact Phi1_inv _ _
      · exact ⟨1, Matrix.mul_one _⟩
    · exact ⟨1, Matrix.mul_one _⟩
    · cases b
      · exact Phi1_inv _ _
      · exact Phi2_inv _ _
    · exact Phi2_inv _ _
  choose S' hS' using hSinv
  have hT : ∀ l : Live T Sl N.D.pad, N.D.S5 (pull (Sum.inl l))
      = kernel (H × H) * (N.D.S0 (Sum.inl l)).M := by
    rintro ((⟨a,b⟩|⟨a,b⟩)|(⟨b,r,q⟩|i))
    · simp only [NetData.S5, pull, mkState, iY, NetData.corr, NetData.S4, NetData.S0, FMap.lab,
        NetData.F1, NetData.F2, fmap1, fmap2, perpL, lineL]
      rw [N.hbase a, N.hbase b]
      exact (terminal_X (N.base a) (N.base b) (N.piv a) (N.piv b)).symm
    · simp only [NetData.S5, pull, mkState, iX, NetData.corr, NetData.S4, NetData.S0, FMap.lab,
        NetData.F1, NetData.F2, fmap1, fmap2, fullL, zeroL]
      rw [shift_zero, Matrix.one_mul, Phi2_full, Phi1_zero, Matrix.mul_one]
    · cases b
      · simp only [NetData.S5, pull, mkState, iS, NetData.corr, NetData.S4, NetData.S0, FMap.lab,
          NetData.F1, fmap1, zeroL, Bool.cond_false, NetData.top]
        rw [shift_zero, Matrix.one_mul, Phi1_zero, Matrix.mul_one]
      · simp only [NetData.S5, pull, mkState, iS, NetData.corr, NetData.S4, NetData.S0, FMap.lab,
          NetData.F2, fmap2, fullL, Bool.cond_true, NetData.bot]
        rw [shift_zero, Matrix.one_mul, Phi2_full, Matrix.mul_one]
    · simp only [NetData.S5, pull, mkState, iI, NetData.corr, NetData.S4, NetData.S0,
        NetData.top, NetData.bot]
      rw [shift_zero, Matrix.one_mul, Matrix.mul_one]
  have hg : ∀ x : Role T Sl C N.D.pad → ℂ,
      (∀ s, (∀ l : Live T Sl N.D.pad, (Sum.inl l : Role T Sl C N.D.pad) ≠ s) → x s = 0) →
      ∀ l : Live T Sl N.D.pad,
        (actPoint recM ∘ (id ∘ N.D.Gtot)) x (Sum.inl l) = x (Sum.inl l) := by
    intro x hx l
    obtain ⟨g1, g2, g3, g4⟩ := N.D.Gtot_live x hx
    change actPoint recM (N.D.Gtot x) (Sum.inl l) = _
    rw [actPoint_recM]
    rcases l with ((k|k)|(p|i))
    · change ((1:ℚ):ℂ) * N.D.Gtot x (iY k) = x (iX k)
      rw [g1]; simp
    · change ((-1:ℚ):ℂ) * N.D.Gtot x (iX k) = x (iY k)
      rw [g2]; simp
    · obtain ⟨b,r,q⟩ := p
      change ((1:ℚ):ℂ) * N.D.Gtot x (iS (b,r,q)) = x (iS (b,r,q))
      rw [g3]; simp
    · change ((1:ℚ):ℂ) * N.D.Gtot x (iI i) = x (iI i)
      rw [g4]; simp
  exact XRoute.liveKernel (Sum.inl : Live T Sl N.D.pad → Role T Sl C N.D.pad)
    (fun r => (N.D.S0 r).M) S' (fun r => N.D.S5 (pull r)) hS' _ N.cost Rt hg hT

end Net
end
end CB
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.CB.xnetwork_certificate
