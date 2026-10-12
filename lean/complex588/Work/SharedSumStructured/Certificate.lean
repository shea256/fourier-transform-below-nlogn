import Work.SharedSumStructured.Network

/-!
# (key: shared-sum-structured) From the two-stage network to a scratch certificate and the engine

`network_certificate`: for every `NetData` (an abstract helper circuit, bases, padding) there is a
word `p` on `H × H` with `LiveKernel Sum.inl p` and
`tally p + |T|^2 = (#live roles) * |H|^2 + 2 |T| * cst`  (`cst` = total copy dimension of one
invocation), i.e. `tally = 2^a m - |T| (|T| - 2 cst)` when the live roles number `2^a`.

`engine_of_network`: the conclusion of upstream `hills_program` with envelope `(k+1)^z`
whenever `tally / 2^a < m^z`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace SS
open Binary Matrix Finset RAM
noncomputable section

section Inv
variable {α : Type*} [Fintype α] [DecidableEq α]

lemma frameM_inv (M : Matrix α α F) : ∃ N : CMat α, frameM M * N = 1 := by
  refine ⟨wrap fun x => (lum (M *ᵥ x))⁻¹, ?_⟩
  unfold frameM
  rw [wrap_mul]
  have h : (fun x : Space α => lum (M *ᵥ x) * (lum (M *ᵥ x))⁻¹) = fun _ => 1 := by
    funext x; exact mul_inv_cancel₀ (lum_nonzero _)
  rw [h, wrap_one]

end Inv

section Cert
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]

lemma Phi1_inv (t : Space H) (P : Matrix H H F) : ∃ N, Phi1 t P * N = 1 := frameM_inv _

lemma Phi2_inv (t : Space H) (P : Matrix H H F) : ∃ N, Phi2 t P * N = 1 := by
  obtain ⟨N1, h1⟩ := frameM_inv (kron (tt t) P)
  obtain ⟨N2, h2⟩ := frameM_inv (kron (1 + tt t) (1 : Matrix H H F))
  refine ⟨N2 * N1, ?_⟩
  unfold Phi2 Kmat
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ N2, h2, Matrix.one_mul, h1]

variable (D : NetData H T Sl C)

lemma card_live : Fintype.card (Live T Sl D.pad)
    = 2 * (Fintype.card T * Fintype.card T) + 2 * (Fintype.card T * Fintype.card Sl) + D.pad := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
  ring

lemma NetData.fmass_S0 : fmass D.S0 = Fintype.card T * Fintype.card T
    + Fintype.card T * (Fintype.card C * ((Fintype.card H - 1) * Fintype.card H))
    + Fintype.card T * D.cst + Fintype.card T * Fintype.card T * D.mm := by
  rw [NetData.S0, fmass_mkState]
  simp only [FMap.lab, NetData.F1, NetData.F2, fmap1, fmap2, lineL, zeroL, fullL, NetData.bot,
    cond_true, cond_false, sum_const, card_univ, Fintype.card_prod, smul_eq_mul, add_zero,
    zero_add, mul_zero, NetData.cst, NetData.mm]
  ring

lemma NetData.fmass_S4 : fmass D.S4 = Fintype.card T * Fintype.card T * D.mm
    + Fintype.card T * Fintype.card T * (Fintype.card H - 1 + (Fintype.card H - 1) * Fintype.card H)
    + (Fintype.card T * Fintype.card Sl * D.mm + Fintype.card T * Fintype.card Sl * D.mm)
    + D.pad * D.mm
    + (Fintype.card T * D.cst
        + Fintype.card T * (Fintype.card C * ((Fintype.card H - 1) * Fintype.card H)))
    + Fintype.card T * Fintype.card T * (Fintype.card H - 1 + (Fintype.card H - 1) * Fintype.card H) := by
  rw [NetData.S4, fmass_mkState]
  simp only [FMap.lab, NetData.F1, NetData.F2, fmap1, fmap2, perpL, zeroL, fullL, NetData.top,
    cond_true, cond_false, sum_const, card_univ, Fintype.card_prod, smul_eq_mul, add_zero,
    zero_add, mul_zero, NetData.cst, NetData.mm, sum_add_distrib, Fintype.card_fin]
  ring

lemma tally_arith (c v R P cC off cst y mm : ℕ) (hy : y + 1 = mm)
    (hc : c + (v*v + v*(cC*off) + v*cst + v*v*mm)
      = (v*v*mm + v*v*y + (v*R*mm + v*R*mm) + P*mm + (v*cst + v*(cC*off)) + v*v*y)
        + 2*(v*cst + v*v)) :
    c + v*v = (2*(v*v) + 2*(v*R) + P)*mm + 2*(v*cst) := by
  zify at hc hy ⊢
  linear_combination hc + 2 * (v:ℤ)^2 * hy

/-! ### the final free moves: shifts on the `Y` roles and the signed exchange -/

def NetData.corr : Role T Sl C D.pad → Space (H × H) := mkState
  (fun _ => 0) (fun k => tens (D.K.tv k.1) (D.K.tv k.2)) (fun _ _ _ => 0) (fun _ => 0)
  (fun _ _ _ => 0) (fun _ => 0)

def pull {P : ℕ} : Role T Sl C P → Role T Sl C P := mkState
  (fun k => iY k) (fun k => iX k) (fun b r q => iS (b,r,q)) (fun i => iI i)
  (fun b r c => iC (b,r,c)) (fun k => iZ k)

def sgn {P : ℕ} : Role T Sl C P → ℚ := mkState
  (fun _ => 1) (fun _ => -1) (fun _ _ _ => 1) (fun _ => 1) (fun _ _ _ => 1) (fun _ => 1)

def recM {P : ℕ} : Matrix (Role T Sl C P) (Role T Sl C P) ℚ :=
  fun i j => if j = pull i then sgn i else 0

lemma actPoint_recM {P : ℕ} (x : Role T Sl C P → ℂ) (i : Role T Sl C P) :
    actPoint recM x i = (sgn i : ℂ) * x (pull i) := by
  unfold actPoint
  rw [sum_eq_single (pull i)]
  · simp [recM]
  · intro j _ hj; simp [recM, hj]
  · simp

/-! ### scalar evaluation on the live roles when the scratch roles are zero -/

lemma NetData.stage1_live (x : Role T Sl C D.pad → ℂ) (hC : ∀ r c, x (iC (false,r,c)) = 0) :
    (∀ a b, D.stage1 x (iX (a,b)) = x (iX (a,b))) ∧
    (∀ a b, D.stage1 x (iY (a,b)) = x (iY (a,b)) + x (iX (a,b))) ∧
    (∀ b r q, D.stage1 x (iS (b,r,q)) = x (iS (b,r,q))) := by
  have hc : ∀ b : T, (x ∘ (pos1 b : Box T Sl C → Role T Sl C D.pad)) ∘ bC = 0 := fun b => by
    funext c; exact hC b c
  refine ⟨fun a b => ?_, fun a b => ?_, fun b r q => ?_⟩
  · exact congrFun (D.K.fwd_live (x ∘ pos1 b) (hc b)).1 a
  · exact congrFun (D.K.fwd_live (x ∘ pos1 b) (hc b)).2.1 a
  · cases b
    · exact congrFun (D.K.fwd_live (x ∘ pos1 r) (hc r)).2.2 q
    · rfl

lemma NetData.stage2_live (x : Role T Sl C D.pad → ℂ) (hC : ∀ r c, x (iC (true,r,c)) = 0) :
    (∀ a b, D.stage2 x (iX (a,b)) = x (iX (a,b)) - x (iY (a,b))) ∧
    (∀ a b, D.stage2 x (iY (a,b)) = x (iY (a,b))) ∧
    (∀ b r q, D.stage2 x (iS (b,r,q)) = x (iS (b,r,q))) := by
  have hc : ∀ a : T, (x ∘ (pos2 a : Box T Sl C → Role T Sl C D.pad)) ∘ bC = 0 := fun a => by
    funext c; exact hC a c
  refine ⟨fun a b => ?_, fun a b => ?_, fun b r q => ?_⟩
  · exact congrFun (D.K.bwd_live (x ∘ pos2 a) (hc a)).1 b
  · exact congrFun (D.K.bwd_live (x ∘ pos2 a) (hc a)).2.1 b
  · cases b
    · rfl
    · exact congrFun (D.K.bwd_live (x ∘ pos2 r) (hc r)).2.2 q

lemma NetData.Gtot_live (x : Role T Sl C D.pad → ℂ)
    (hx : ∀ s, (∀ l : Live T Sl D.pad, (Sum.inl l : Role T Sl C D.pad) ≠ s) → x s = 0) :
    (∀ k, D.Gtot x (iY k) = x (iX k)) ∧ (∀ k, D.Gtot x (iX k) = - x (iY k)) ∧
    (∀ p, D.Gtot x (iS p) = x (iS p)) ∧ (∀ i, D.Gtot x (iI i) = x (iI i)) := by
  have hC : ∀ p, x (iC p) = 0 := fun p => hx _ (fun l h => by cases h)
  have hZ : ∀ k, x (iZ k) = 0 := fun k => hx _ (fun l h => by cases h)
  obtain ⟨a1, a2, a3⟩ := D.stage1_live x (fun r c => hC _)
  obtain ⟨b1, b2, b3⟩ := D.stage2_live (D.stage1 x) (fun r c => hC (true, r, c))
  -- the two endpoint gates
  have h3Z : D.endA (D.stage2 (D.stage1 x)) ∘ iZ
      = D.stage2 (D.stage1 x) ∘ iZ + D.stage2 (D.stage1 x) ∘ iX := by
    unfold NetData.endA
    rw [addBlk_same iZ iZ_inj, ap_one]
  have h3X : D.endA (D.stage2 (D.stage1 x)) ∘ iX = D.stage2 (D.stage1 x) ∘ iX :=
    addBlk_other iZ iX (fun a b h => by simp [iX, iZ] at h) _ _
  have h3Y : D.endA (D.stage2 (D.stage1 x)) ∘ iY = D.stage2 (D.stage1 x) ∘ iY :=
    addBlk_other iZ iY (fun a b h => by simp [iY, iZ] at h) _ _
  have h3S : D.endA (D.stage2 (D.stage1 x)) ∘ iS = D.stage2 (D.stage1 x) ∘ iS :=
    addBlk_other iZ iS (fun a b h => by simp [iS, iZ] at h) _ _
  have h3I : D.endA (D.stage2 (D.stage1 x)) ∘ iI = D.stage2 (D.stage1 x) ∘ iI :=
    addBlk_other iZ iI (fun a b h => by simp [iI, iZ] at h) _ _
  have h4Y : D.Gtot x ∘ iY = D.endA (D.stage2 (D.stage1 x)) ∘ iY
      + D.endA (D.stage2 (D.stage1 x)) ∘ iZ := by
    change D.endB (D.endA (D.stage2 (D.stage1 x))) ∘ iY = _
    unfold NetData.endB
    rw [addBlk_same iY iY_inj, ap_one]
  have h4X : D.Gtot x ∘ iX = D.endA (D.stage2 (D.stage1 x)) ∘ iX :=
    addBlk_other iY iX (fun a b h => by simp [iX, iY] at h) _ _
  have h4S : D.Gtot x ∘ iS = D.endA (D.stage2 (D.stage1 x)) ∘ iS :=
    addBlk_other iY iS (fun a b h => by simp [iS, iY] at h) _ _
  have h4I : D.Gtot x ∘ iI = D.endA (D.stage2 (D.stage1 x)) ∘ iI :=
    addBlk_other iY iI (fun a b h => by simp [iI, iY] at h) _ _
  have z2 : ∀ k, D.stage2 (D.stage1 x) (iZ k) = 0 := fun k => hZ k
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨a, b⟩
    have e1 := congrFun h4Y (a,b)
    have e2 := congrFun h3Y (a,b)
    have e3 := congrFun h3Z (a,b)
    simp only [Function.comp_apply, Pi.add_apply] at e1 e2 e3
    rw [e1, e2, e3, z2, b1, b2, a1, a2]
    ring
  · rintro ⟨a, b⟩
    have e1 := congrFun h4X (a,b)
    have e2 := congrFun h3X (a,b)
    simp only [Function.comp_apply] at e1 e2
    rw [e1, e2, b1, a1, a2]
    ring
  · rintro ⟨b, r, q⟩
    have e1 := congrFun h4S (b,r,q)
    have e2 := congrFun h3S (b,r,q)
    simp only [Function.comp_apply] at e1 e2
    rw [e1, e2, b3, a3]
  · intro i
    have e1 := congrFun h4I i
    have e2 := congrFun h3I i
    simp only [Function.comp_apply] at e1 e2
    rw [e1, e2]
    rfl

/-- frames after the final free shifts. -/
def NetData.S5 : Role T Sl C D.pad → CMat (H × H) := fun r => shift (D.corr r) * (D.S4 r).M

/-- **The scratch certificate of the two-stage network with an arbitrary helper circuit.** -/
theorem network_certificate (t0 : T) :
    ∃ p : PWord (H × H) (Role T Sl C D.pad),
      tally p + Fintype.card T * Fintype.card T
        = (2 * (Fintype.card T * Fintype.card T) + 2 * (Fintype.card T * Fintype.card Sl) + D.pad)
            * (Fintype.card H * Fintype.card H) + 2 * (Fintype.card T * D.cst) ∧
      LiveKernel (Sum.inl : Live T Sl D.pad → Role T Sl C D.pad) p := by
  obtain ⟨c, hc, R1⟩ := D.total_path.route
  rw [D.fmass_S0, D.fmass_S4] at hc
  have h1 := card_pos_of_base (D.base t0) (D.piv t0)
  have hy : (Fintype.card H - 1 + (Fintype.card H - 1) * Fintype.card H) + 1 = D.mm := by
    unfold NetData.mm; omega
  have hcount := tally_arith c (Fintype.card T) (Fintype.card Sl) D.pad (Fintype.card C)
    ((Fintype.card H - 1) * Fintype.card H) D.cst _ D.mm hy hc
  obtain ⟨q, hq, hqw⟩ := translateAll (α := H × H) D.corr
  have R2 : Route (fun r => (D.S4 r).M) D.S5 id 0 := ⟨q, hq, fun f x => by
    rw [hqw]
    funext r
    simp only [multiAct, matAct_mul]
    rfl⟩
  have R3 : Route D.S5 (fun r => D.S5 (pull r)) (actPoint recM) 0 :=
    Route.gate recM D.S5 _ (fun i j h => by
      have hj : j = pull i := by
        by_contra hne
        exact h (by simp [recM, hne])
      rw [hj])
  have Rt := (R1.trans R2).trans R3
  have hSinv : ∀ r, ∃ N, (D.S0 r).M * N = 1 := by
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
  have hT : ∀ l : Live T Sl D.pad, D.S5 (pull (Sum.inl l))
      = kernel (H × H) * (D.S0 (Sum.inl l)).M := by
    rintro ((⟨a,b⟩|⟨a,b⟩)|(⟨b,r,q⟩|i))
    · simp only [NetData.S5, pull, mkState, iY, NetData.corr, NetData.S4, NetData.S0, FMap.lab,
        NetData.F1, NetData.F2, fmap1, fmap2, perpL, lineL]
      rw [D.hbase a, D.hbase b]
      exact (terminal_X (D.base a) (D.base b) (D.piv a) (D.piv b)).symm
    · simp only [NetData.S5, pull, mkState, iX, NetData.corr, NetData.S4, NetData.S0, FMap.lab,
        NetData.F1, NetData.F2, fmap1, fmap2, fullL, zeroL]
      rw [shift_zero, Matrix.one_mul, Phi2_full, Phi1_zero, Matrix.mul_one]
    · cases b
      · simp only [NetData.S5, pull, mkState, iS, NetData.corr, NetData.S4, NetData.S0, FMap.lab,
          NetData.F1, fmap1, zeroL, cond_false, NetData.top]
        rw [shift_zero, Matrix.one_mul, Phi1_zero, Matrix.mul_one]
      · simp only [NetData.S5, pull, mkState, iS, NetData.corr, NetData.S4, NetData.S0, FMap.lab,
          NetData.F2, fmap2, fullL, cond_true, NetData.bot]
        rw [shift_zero, Matrix.one_mul, Phi2_full, Matrix.mul_one]
    · simp only [NetData.S5, pull, mkState, iI, NetData.corr, NetData.S4, NetData.S0,
        NetData.top, NetData.bot]
      rw [shift_zero, Matrix.one_mul, Matrix.mul_one]
  have hg : ∀ x : Role T Sl C D.pad → ℂ,
      (∀ s, (∀ l : Live T Sl D.pad, (Sum.inl l : Role T Sl C D.pad) ≠ s) → x s = 0) →
      ∀ l : Live T Sl D.pad, (actPoint recM ∘ (id ∘ D.Gtot)) x (Sum.inl l) = x (Sum.inl l) := by
    intro x hx l
    obtain ⟨g1, g2, g3, g4⟩ := D.Gtot_live x hx
    change actPoint recM (D.Gtot x) (Sum.inl l) = _
    rw [actPoint_recM]
    rcases l with ((k|k)|(p|i))
    · change ((1:ℚ):ℂ) * D.Gtot x (iY k) = x (iX k)
      rw [g1]; simp
    · change ((-1:ℚ):ℂ) * D.Gtot x (iX k) = x (iY k)
      rw [g2]; simp
    · obtain ⟨b,r,q⟩ := p
      change ((1:ℚ):ℂ) * D.Gtot x (iS (b,r,q)) = x (iS (b,r,q))
      rw [g3]; simp
    · change ((1:ℚ):ℂ) * D.Gtot x (iI i) = x (iI i)
      rw [g4]; simp
  obtain ⟨p, hp, hw⟩ := LiveKernel.of_route (Sum.inl : Live T Sl D.pad → Role T Sl C D.pad)
    (fun r => (D.S0 r).M) S' (fun r => D.S5 (pull r)) hS' _ _ Rt hg hT
  refine ⟨p, ?_, hw⟩
  have e : Fintype.card H * Fintype.card H = D.mm := hh_sq _
  rw [hp, e, add_zero, add_zero]
  exact hcount

end Cert

section Engine
open Ty
universe U
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]

/-- **Engine from a two-stage network with an arbitrary helper circuit.**  Same conclusion as
upstream `hills_program` with envelope `(k+1)^z`: it is enough that the live roles number `2^a`
and that the tally `n` of the network (`n + |T|^2 = 2^a |H|^2 + 2 |T| cst`) satisfies
`n / 2^a < (|H|^2)^z`. -/
theorem engine_of_network (D : NetData H T Sl C) (t0 : T) (a : ℕ)
    (hlive : Fintype.card (Live T Sl D.pad) = 2^a)
    (hm : 3 ≤ Fintype.card H * Fintype.card H) (z : ℝ) (hz : 0 ≤ z)
    (hrate : ∀ n : ℕ, n + Fintype.card T * Fintype.card T
        = 2^a * (Fintype.card H * Fintype.card H) + 2 * (Fintype.card T * D.cst) →
      (n:ℝ)/(2:ℝ)^a < ((Fintype.card H * Fintype.card H : ℕ) : ℝ)^z)
    (cl : Paint) (m : Bool) {ι : Type U} (k : ι → ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*envelope z (k i)) := by
  obtain ⟨p, hp, hw⟩ := network_certificate D t0
  rw [← card_live D, hlive] at hp
  exact engine_program_scratch (Fintype.card H * Fintype.card H) a
    (by rw [Fintype.card_prod]) hlive hm Sum.inl Sum.inl_injective p hw z hz (hrate _ hp)
    cl m k v

end Engine
end
end SS
end PowerSaving
end OAI
