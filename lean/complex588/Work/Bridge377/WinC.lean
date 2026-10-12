import Work.GCert.Chain.Win
import Work.BridgeC.Stage

/-!
# (key: bridge-377) The windows of the compressed geometry `LC B H l` (PR #377)

Port of Jacob Sussman's `Work/GCert/Chain/WinB.lean` (wht-power-saving-lean, Apache-2.0) to the label space
`LC B H l = H ⊕ (B × Hp H l)` of `Work.BridgeC` (the compressed nine-stage layout is jacklightChen's,
CrocSwap/integer-mult-bounds PR #377).  `gwinC hB hH d q : GWin H (LC B H l)` with
`(gwinC hB hH d q).Xm = fmapC hB hH d q` (`rfl`).  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace GX
open Binary Matrix Finset RAM SS CB RF BR BC GF
noncomputable section

section
variable {B H : Type} [Fintype B] [DecidableEq B] [Fintype H] [DecidableEq H] {l : H}

lemma blkCT_mulVec (A : OBase H) (z : Space (LC B H l)) (k : LC B H l) :
    ((blkC B l A)ᵀ *ᵥ z) k = Sum.elim (fun i => dot (A.v i) (fun j => z (Sum.inl j)))
      (fun b => z (Sum.inr b)) k := by
  cases k with
  | inl i =>
    simp [blkC, Matrix.fromBlocks_transpose, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      cmat, dot]
  | inr b =>
    simp [blkC, Matrix.fromBlocks_transpose, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Matrix.one_apply]

/-- coordinates of `y` in the basis `d (A ⊕ std)`. -/
lemma dot_colsC (d : Orth (LC B H l)) (A : OBase H) (y : Space (LC B H l)) (k : LC B H l) :
    dot ((ofCols (d.1 * blkC B l A) (mul_orth d.2 (blkC_orth A))).v k) y
      = Sum.elim (fun i => dot (A.v i) (fun j => (d.1ᵀ *ᵥ y) (Sum.inl j)))
          (fun b => (d.1ᵀ *ᵥ y) (Sum.inr b)) k := by
  rw [← blkCT_mulVec A (d.1ᵀ *ᵥ y) k, Matrix.mulVec_mulVec, ← Matrix.transpose_mul]
  rfl

/-- **the old frame and the lifted label name the same subspace of the address space.** -/
theorem insub_old_newC (d : Orth (LC B H l)) (q : Finset (B × Hp H l)) (A : OBase H) (s : Finset H)
    (U : SLbl H) (h : ∀ x, U.Mem x ↔ InSub (coordPerm A) s x) (y : Space (LC B H l)) :
    InSub (coordPerm (ofCols (d.1 * blkC B l A) (mul_orth d.2 (blkC_orth A)))) (JC s q) y ↔
      InSub (conjPerm d.1 d.2 (Orth.orth' d) U.G) (U.s.disjSum q) y := by
  rw [insub_conj, insub_coordPerm]
  have hU := h (fun i => (d.1ᵀ *ᵥ y) (Sum.inl i))
  constructor
  · intro hk
    refine ⟨hU.mpr ((insub_coordPerm A s _).mpr (fun i hi => ?_)), fun b hb => ?_⟩
    · have h1 := hk (Sum.inl i) (fun hm => hi (Finset.inl_mem_disjSum.mp hm))
      rw [dot_colsC] at h1
      exact h1
    · have h1 := hk (Sum.inr b) (fun hm => hb (Finset.inr_mem_disjSum.mp hm))
      rw [dot_colsC] at h1
      exact h1
  · rintro ⟨h1, h2⟩ k hk
    rw [dot_colsC]
    cases k with
    | inl i =>
      exact (insub_coordPerm A s _).mp (hU.mp h1) i
        (fun hm => hk (Finset.inl_mem_disjSum.mpr hm))
    | inr b => exact h2 b (fun hm => hk (Finset.inr_mem_disjSum.mpr hm))

/-- old frame of a coordinate subspace → representative of any label naming it: FREE. -/
theorem old_to_newC (d : Orth (LC B H l)) (q : Finset (B × Hp H l)) (A : OBase H) (s : Finset H)
    (U : SLbl H) (h : ∀ x, U.Mem x ↔ InSub (coordPerm A) s x) :
    GReach (PhiC d q (A.mat s)) ((BXMap.ofConj d.1 d.2 (Orth.orth' d) q).Φ U) (fun _ => 0) := by
  rw [PhiC_eq]
  obtain ⟨N, hN, e⟩ := repChange (LC B H l) _ _ _ _ (insub_old_newC d q A s U h)
  have a : GReach (frame (ofCols (d.1 * blkC B l A) (mul_orth d.2 (blkC_orth A))) (JC s q))
      (core (coordPerm (ofCols (d.1 * blkC B l A) (mul_orth d.2 (blkC_orth A)))) (JC s q))
      (fun φ => rcost φ []) :=
    GReach.ofReach (fmv_old_to_core _ _).reach
  have b : GReach
      (core (coordPerm (ofCols (d.1 * blkC B l A) (mul_orth d.2 (blkC_orth A)))) (JC s q))
      (core (conjPerm d.1 d.2 (Orth.orth' d) U.G) (U.s.disjSum q)) (fun φ => rcost φ []) :=
    GReach.ofReach (fmv_of_free hN e).reach
  exact (a.trans b).cast (fun φ => by simp [rcost])

/-- the same, backwards. -/
theorem new_to_oldC (d : Orth (LC B H l)) (q : Finset (B × Hp H l)) (A : OBase H) (s : Finset H)
    (U : SLbl H) (h : ∀ x, U.Mem x ↔ InSub (coordPerm A) s x) :
    GReach ((BXMap.ofConj d.1 d.2 (Orth.orth' d) q).Φ U) (PhiC d q (A.mat s)) (fun _ => 0) := by
  rw [PhiC_eq]
  obtain ⟨N, hN, e⟩ := repChange (LC B H l) _ _ _ _
    (fun y => (insub_old_newC d q A s U h y).symm)
  have a : GReach (core (conjPerm d.1 d.2 (Orth.orth' d) U.G) (U.s.disjSum q))
      (core (coordPerm (ofCols (d.1 * blkC B l A) (mul_orth d.2 (blkC_orth A)))) (JC s q))
      (fun φ => rcost φ []) :=
    GReach.ofReach (fmv_of_free hN e).reach
  have b : GReach
      (core (coordPerm (ofCols (d.1 * blkC B l A) (mul_orth d.2 (blkC_orth A)))) (JC s q))
      (frame (ofCols (d.1 * blkC B l A) (mul_orth d.2 (blkC_orth A))) (JC s q))
      (fun φ => rcost φ []) :=
    GReach.ofReach (fmv_core_to_old _ _).reach
  exact (a.trans b).cast (fun φ => by simp [rcost])

/-- **The window of a stage of the bridged geometry.** -/
def gwinC (hB : 1 ≤ Fintype.card B) (hH : 2 ≤ Fintype.card H) (d : Orth (LC B H l))
    (q : Finset (B × Hp H l)) : GWin H (LC B H l) where
  Xm := fmapC hB hH d q
  X := BXMap.ofConj d.1 d.2 (Orth.orth' d) q
  big := by
    have h := card_lt_LC (l := l) hB hH (univ : Finset H)
    rwa [Finset.card_univ] at h
  toNew := fun A s U h => old_to_newC d q A s U h
  toOld := fun A s U h => new_to_oldC d q A s U h

@[simp] lemma gwinC_Xm (hB : 1 ≤ Fintype.card B) (hH : 2 ≤ Fintype.card H) (d : Orth (LC B H l))
    (q : Finset (B × Hp H l)) : (gwinC hB hH d q).Xm = fmapC hB hH d q := rfl

end
end
end GX
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.GX.insub_old_newC
#print axioms OAI.PowerSaving.GX.old_to_newC
#print axioms OAI.PowerSaving.GX.new_to_oldC
#print axioms OAI.PowerSaving.GX.gwinC
