import Work.Bridge401.GNetStage

/-!
# (key: bridge-401) The certificate of the nine-stage word with entrance gauges and residual banks (PR #401)

Credits: the entrance gauges and the residual banks are Dugongue's (CrocSwap/integer-mult-bounds PR #401); the bank
patterns are Lydakis's (#275); the compressed nine-stage layout is jacklightChen's (#377); the bridged word B_K is
DaysSky's (#363); B_2, the engine, the stage geometry and the E8 unit are Jacob Sussman's (wht-power-saving-lean,
Apache-2.0).  Written by w-newsums/gen401/gen401.py (from gen377.py).
`G401.run ρ`: the route of run `ρ` on the roles of a run (as genk's B_4 route, with the free bank adapters).
`G401.runFull ρ`: the same on all roles (`GRoute.lift` by `emRun4 ρ`).  `G401.sweep`: the 8 runs
(`GRoute.sweep_const`).  `G401.padR`: ONE padding block of rank `pad b` on every bank.  Then the free shifts and the
signed exchange, and `gcert_of_groute`.  The scalar identity goes through `sweep_data4` / `sweep_bank4` and
`chainQ_eq` with `rw` only.  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace OAI
namespace PowerSaving
namespace GX
open Binary Matrix Finset RAM SS CB RF BR GF
noncomputable section

section Net
variable {H T Sl C α Γ : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] [Fintype α] [DecidableEq α]
  [Fintype Γ] [DecidableEq Γ]
variable {nb : ℕ} (N : G401 H T Sl C α Γ nb)

/-- the whole run `ρ` before the exchange, on the roles of a run. -/
lemma G401.run (ρ : Fin 8) :
    GRoute (N.S0 ρ) (N.S25 ρ) (chainQ (N.use ρ)) (fun φ => (Fintype.card Γ : ℝ) * N.runUnit φ) := by
  have R := ((((((((((((((((((((((((((((((((((N.adapt0 ρ)).trans (N.stage0 ρ)).trans (N.adapt1 ρ)).trans (N.stage1 ρ)).trans (GRoute.ofX (N.climbA2 ρ))).trans (GRoute.ofX (N.gateA2 ρ))).trans (N.adapt2 ρ)).trans (N.stage2 ρ)).trans (GRoute.ofX (N.climbB2 ρ))).trans (GRoute.ofX (N.gateB2 ρ))).trans (N.adapt3 ρ)).trans (N.stage3 ρ)).trans (GRoute.ofX (N.climbA3 ρ))).trans (GRoute.ofX (N.gateA3 ρ))).trans (N.adapt4 ρ)).trans (N.stage4 ρ)).trans (GRoute.ofX (N.climbB3 ρ))).trans (GRoute.ofX (N.gateB3 ρ))).trans (N.adapt5 ρ)).trans (N.stage5 ρ)).trans (GRoute.ofX (N.climbA4 ρ))).trans (GRoute.ofX (N.gateA4 ρ))).trans (N.adapt6 ρ)).trans (N.stage6 ρ)).trans (GRoute.ofX (N.climbB4 ρ))).trans (GRoute.ofX (N.gateB4 ρ))).trans (N.adapt7 ρ)).trans (N.stage7 ρ)).trans (N.adapt8 ρ)).trans (N.stage8 ρ)).trans (GRoute.ofX (N.fin ρ))).trans (GRoute.ofX (N.gateC4 ρ))).trans (GRoute.ofX (N.gateC3 ρ))).trans (GRoute.ofX (N.gateC2 ρ))
  refine R.cast (fun φ => ?_)
  simp only [G401.runUnit]
  ring

/-- run `ρ` on all roles: the other replicas wait (before their run at `InitD`, after it at `FinD`). -/
lemma G401.runFull (ρ : Fin 8) :
    GRoute (N.Sfull ρ.castSucc) (N.Sfull ρ.succ) (liftRun4 ρ (chainQ (N.use ρ)))
      (fun φ => (Fintype.card Γ : ℝ) * N.runUnit φ) := by
  refine GRoute.lift (emRun4 ρ) (h := chainQ (N.use ρ)) ?_ (fun x => ?_) (fun x i hi => ?_) (fun i hi => ?_)
  · have e1 : N.Sfull ρ.castSucc ∘ (emRun4 ρ) = N.S0 ρ := by
      funext r
      rcases r with ((d|⟨g,b⟩)|⟨g,c⟩)
      · exact if_neg (lt_irrefl _)
      · rfl
      · rfl
    have e2 : N.Sfull ρ.succ ∘ (emRun4 ρ) = N.S25 ρ := by
      funext r
      rcases r with ((d|⟨g,b⟩)|⟨g,c⟩)
      · exact if_pos (Nat.lt_succ_self _)
      · have e : 9 * ρ.succ.val = 9 * ρ.val + 9 := by
          rw [Fin.val_succ]
          ring
        show N.Zb (9 * ρ.succ.val) g b = N.Zb (9 * ρ.val + 9) g b
        rw [e]
      · rfl
    rw [e1, e2]
    exact N.run ρ
  · funext r
    rcases r with ((d|⟨g,b⟩)|⟨g,c⟩)
    · exact if_pos rfl
    · rfl
    · rfl
  · rcases i with ((⟨ρ',d⟩|⟨g,b⟩)|⟨g,c⟩)
    · by_cases e : ρ' = ρ
      · subst e
        exact absurd ((cover_iff _ _).mpr ⟨Sum.inl (Sum.inl d), rfl⟩) hi
      · exact if_neg e
    · exact absurd ((cover_iff _ _).mpr ⟨Sum.inl (Sum.inr (g, b)), rfl⟩) hi
    · exact absurd ((cover_iff _ _).mpr ⟨Sum.inr (g, c), rfl⟩) hi
  · rcases i with ((⟨ρ',d⟩|⟨g,b⟩)|⟨g,c⟩)
    · by_cases e : ρ' = ρ
      · subst e
        exact absurd ((cover_iff _ _).mpr ⟨Sum.inl (Sum.inl d), rfl⟩) hi
      · have e' : ρ'.val ≠ ρ.val := fun h => e (Fin.ext h)
        show (if ρ'.val < ρ.castSucc.val then N.FinD d else N.InitD d)
          = (if ρ'.val < ρ.succ.val then N.FinD d else N.InitD d)
        simp only [Fin.val_castSucc, Fin.val_succ]
        split_ifs <;> first | rfl | (exfalso; omega)
    · exact absurd ((cover_iff _ _).mpr ⟨Sum.inl (Sum.inr (g, b)), rfl⟩) hi
    · exact absurd ((cover_iff _ _).mpr ⟨Sum.inr (g, c), rfl⟩) hi

/-- **the 8 runs one after the other.** -/
lemma G401.sweep :
    GRoute (N.Sfull 0) (N.Sfull (Fin.last 8)) (sweepMap (fun ρ : Fin 8 => liftRun4 ρ (chainQ (N.use ρ))))
      (fun φ => ((8 : ℕ) : ℝ) * ((Fintype.card Γ : ℝ) * N.runUnit φ)) :=
  GRoute.sweep_const 8 N.Sfull _ (fun _ φ => (Fintype.card Γ : ℝ) * N.runUnit φ) _ (fun _ _ => rfl)
    (fun ρ => N.runFull ρ)

/-- **the padding blocks**: ONE block of rank `pad b` per bank. -/
lemma G401.padR :
    GRoute (N.Sfull (Fin.last 8)) N.Sfin id
      (fun φ => (Fintype.card Γ : ℝ) * ∑ b, bcost φ (N.pad b)) := by
  have H1 := GRoute.reach_all (N.Sfull (Fin.last 8)) N.Sfin
    (mk401 (fun _ _ _ => 0) (fun _ b φ => bcost φ (N.pad b)) (fun _ _ _ => 0)) (by
      rintro ((⟨ρ',d⟩|⟨g,b⟩)|⟨g,c⟩)
      · have e : N.Sfull (Fin.last 8) (Sum.inl (Sum.inl (ρ', d))) = N.FinD d := if_pos ρ'.isLt
        show GReach (N.Sfull (Fin.last 8) (Sum.inl (Sum.inl (ρ', d)))) (N.FinD d) (fun _ => 0)
        rw [e]
        exact GReach.refl _
      · exact N.bpad g b
      · exact GReach.refl _)
  refine H1.cast (fun φ => ?_)
  simp_rw [mk401_map (fun c : (ℕ → ℝ) → ℝ => c φ)]
  rw [sum_mk401]
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_zero, add_zero, zero_add, Finset.sum_const_zero]

/-- the free shifts at the end. -/
def G401.corr : BRole401 Γ T nb C → Space α :=
  mk401 (fun _ => mkD4 (fun _ _ => 0) (fun g t => N.u g t) (fun _ _ => 0) (fun g t => N.u g t) (fun _ _ => 0) (fun g t => N.u g t) (fun _ _ => 0) (fun g t => N.u g t)) (fun _ _ => 0) (fun _ _ => 0)

def G401.Sz : BRole401 Γ T nb C → CMat α := fun r => shift (N.corr r) * N.Sfin r

/-- **The scratch certificate of the nine-stage word with entrance gauges and residual banks (PR #401)**, in whole
blocks, with its exact price for every price list. -/
theorem g401_certificate :
    GCert α (Sum.inl : BLive401 Γ T nb → BRole401 Γ T nb C)
      (fun φ => (Fintype.card Γ : ℝ) * N.unit φ) := by
  have R1 := N.sweep.trans N.padR
  have R2 : GRoute N.Sfin N.Sz id (fun _ => 0) := GRoute.shifts N.hm N.Sfin N.corr
  have R3 : GRoute N.Sz (fun r => N.Sz (bpull401 r)) (actPoint brec401) (fun _ => 0) :=
    GRoute.gate brec401 N.Sz _ (fun i j h => by
      have hj : j = bpull401 i := by
        by_contra hne
        exact h (by simp [brec401, hne])
      rw [hj])
  have Rt := ((R1.trans R2).trans R3).cast (c' := fun φ => (Fintype.card Γ : ℝ) * N.unit φ)
    (fun φ => by simp only [G401.unit]; push_cast; ring)
  have h0 : ∀ (ρ' : Fin 8) (d : BDat4 Γ T), N.Sfull 0 (Sum.inl (Sum.inl (ρ', d))) = N.InitD d :=
    fun ρ' d => by simp [G401.Sfull, mk401]
  have hS : ∀ r, ∃ M, N.Sfull 0 r * M = 1 := by
    rintro ((⟨ρ',d⟩|⟨g,b⟩)|⟨g,c⟩)
    · rw [h0]
      rcases d with ((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))
      · exact N.inv0 g t
      · refine ⟨1, ?_⟩
        show (N.G0 g).Xm.Φ 0 * 1 = 1
        rw [N.z0, Matrix.mul_one]
      · exact N.inv0 g t
      · refine ⟨1, ?_⟩
        show (N.G0 g).Xm.Φ 0 * 1 = 1
        rw [N.z0, Matrix.mul_one]
      · exact N.inv0 g t
      · refine ⟨1, ?_⟩
        show (N.G0 g).Xm.Φ 0 * 1 = 1
        rw [N.z0, Matrix.mul_one]
      · exact N.inv0 g t
      · refine ⟨1, ?_⟩
        show (N.G0 g).Xm.Φ 0 * 1 = 1
        rw [N.z0, Matrix.mul_one]
    · refine ⟨1, ?_⟩
      show N.Zb 0 g b * 1 = 1
      rw [N.z0b, Matrix.mul_one]
    · exact ⟨1, Matrix.mul_one _⟩
  have hT : ∀ l : BLive401 Γ T nb, N.Sz (bpull401 (Sum.inl l)) = kernel α * N.Sfull 0 (Sum.inl l) := by
    rintro (⟨ρ', d⟩|⟨g,b⟩)
    · rw [h0]
      rcases d with ((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))
      · show shift (N.u g t) * N.YF g t = kernel α * (N.G0 g).Xm.Φ (tt (N.I.tv t))
        exact (N.term g t).symm
      · show shift (0 : Space α) * kernel α = kernel α * (N.G0 g).Xm.Φ 0
        rw [shift_zero, Matrix.one_mul, N.z0, Matrix.mul_one]
      · show shift (N.u g t) * N.YF g t = kernel α * (N.G0 g).Xm.Φ (tt (N.I.tv t))
        exact (N.term g t).symm
      · show shift (0 : Space α) * kernel α = kernel α * (N.G0 g).Xm.Φ 0
        rw [shift_zero, Matrix.one_mul, N.z0, Matrix.mul_one]
      · show shift (N.u g t) * N.YF g t = kernel α * (N.G0 g).Xm.Φ (tt (N.I.tv t))
        exact (N.term g t).symm
      · show shift (0 : Space α) * kernel α = kernel α * (N.G0 g).Xm.Φ 0
        rw [shift_zero, Matrix.one_mul, N.z0, Matrix.mul_one]
      · show shift (N.u g t) * N.YF g t = kernel α * (N.G0 g).Xm.Φ (tt (N.I.tv t))
        exact (N.term g t).symm
      · show shift (0 : Space α) * kernel α = kernel α * (N.G0 g).Xm.Φ 0
        rw [shift_zero, Matrix.one_mul, N.z0, Matrix.mul_one]
    · show shift (0 : Space α) * kernel α = kernel α * N.Zb 0 g b
      rw [shift_zero, Matrix.one_mul, N.z0b, Matrix.mul_one]
  have hg : ∀ x : BRole401 Γ T nb C → ℂ,
      (∀ s, (∀ l : BLive401 Γ T nb, (Sum.inl l : BRole401 Γ T nb C) ≠ s) → x s = 0) →
      ∀ l : BLive401 Γ T nb,
        (actPoint brec401 ∘ (id ∘ (id ∘ sweepMap (fun ρ : Fin 8 => liftRun4 ρ (chainQ (N.use ρ)))))) x (Sum.inl l)
          = x (Sum.inl l) := by
    intro x _ l
    rw [Function.comp_apply, Function.comp_apply, Function.comp_apply, id_eq, id_eq, actPoint_brec401]
    rcases l with (⟨ρ, d⟩|⟨g,b⟩)
    · rcases d with ((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))
      · show ((1:ℚ):ℂ) * sweepMap (fun i : Fin 8 => liftRun4 i (chainQ (N.use i))) x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inl (Sum.inl (Sum.inr ((g,t)))))))) = _
        rw [sweep_data4 N.use, chainQ_eq]
        show ((1:ℚ):ℂ) * x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inl (Sum.inl (Sum.inl ((g,t)))))))) = x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inl (Sum.inl (Sum.inl ((g,t))))))))
        first | (push_cast; ring) | simp
      · show ((-1:ℚ):ℂ) * sweepMap (fun i : Fin 8 => liftRun4 i (chainQ (N.use i))) x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inl (Sum.inl (Sum.inl ((g,t)))))))) = _
        rw [sweep_data4 N.use, chainQ_eq]
        show ((-1:ℚ):ℂ) * (-x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inl (Sum.inl (Sum.inr ((g,t))))))))) = x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inl (Sum.inl (Sum.inr ((g,t))))))))
        first | (push_cast; ring) | simp
      · show ((1:ℚ):ℂ) * sweepMap (fun i : Fin 8 => liftRun4 i (chainQ (N.use i))) x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inl (Sum.inr (Sum.inr ((g,t)))))))) = _
        rw [sweep_data4 N.use, chainQ_eq]
        show ((1:ℚ):ℂ) * x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inl (Sum.inr (Sum.inl ((g,t)))))))) = x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inl (Sum.inr (Sum.inl ((g,t))))))))
        first | (push_cast; ring) | simp
      · show ((-1:ℚ):ℂ) * sweepMap (fun i : Fin 8 => liftRun4 i (chainQ (N.use i))) x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inl (Sum.inr (Sum.inl ((g,t)))))))) = _
        rw [sweep_data4 N.use, chainQ_eq]
        show ((-1:ℚ):ℂ) * (-x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inl (Sum.inr (Sum.inr ((g,t))))))))) = x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inl (Sum.inr (Sum.inr ((g,t))))))))
        first | (push_cast; ring) | simp
      · show ((1:ℚ):ℂ) * sweepMap (fun i : Fin 8 => liftRun4 i (chainQ (N.use i))) x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inr (Sum.inr ((g,t))))))) = _
        rw [sweep_data4 N.use, chainQ_eq]
        show ((1:ℚ):ℂ) * x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inr (Sum.inl ((g,t))))))) = x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inr (Sum.inl ((g,t)))))))
        first | (push_cast; ring) | simp
      · show ((-1:ℚ):ℂ) * sweepMap (fun i : Fin 8 => liftRun4 i (chainQ (N.use i))) x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inr (Sum.inl ((g,t))))))) = _
        rw [sweep_data4 N.use, chainQ_eq]
        show ((-1:ℚ):ℂ) * (-x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inr (Sum.inr ((g,t)))))))) = x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inr (Sum.inr ((g,t)))))))
        first | (push_cast; ring) | simp
      · show ((1:ℚ):ℂ) * sweepMap (fun i : Fin 8 => liftRun4 i (chainQ (N.use i))) x (Sum.inl (Sum.inl (ρ, Sum.inr (Sum.inr ((g,t)))))) = _
        rw [sweep_data4 N.use, chainQ_eq]
        show ((1:ℚ):ℂ) * x (Sum.inl (Sum.inl (ρ, Sum.inr (Sum.inl ((g,t)))))) = x (Sum.inl (Sum.inl (ρ, Sum.inr (Sum.inl ((g,t))))))
        first | (push_cast; ring) | simp
      · show ((-1:ℚ):ℂ) * sweepMap (fun i : Fin 8 => liftRun4 i (chainQ (N.use i))) x (Sum.inl (Sum.inl (ρ, Sum.inr (Sum.inl ((g,t)))))) = _
        rw [sweep_data4 N.use, chainQ_eq]
        show ((-1:ℚ):ℂ) * (-x (Sum.inl (Sum.inl (ρ, Sum.inr (Sum.inr ((g,t))))))) = x (Sum.inl (Sum.inl (ρ, Sum.inr (Sum.inr ((g,t))))))
        first | (push_cast; ring) | simp
    · show ((1:ℚ):ℂ) * sweepMap (fun i : Fin 8 => liftRun4 i (chainQ (N.use i))) x (Sum.inl (Sum.inr (g, b))) = _
      rw [sweep_bank4 N.use]
      first | (push_cast; ring) | simp
  exact gcert_of_groute (Sum.inl : BLive401 Γ T nb → BRole401 Γ T nb C) (N.Sfull 0)
    (fun r => N.Sz (bpull401 r)) _ _ Rt hS hg hT

end Net
end
end GX
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.GX.G401.run
#print axioms OAI.PowerSaving.GX.G401.runFull
#print axioms OAI.PowerSaving.GX.g401_certificate
