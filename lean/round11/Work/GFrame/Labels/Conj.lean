import Work.GFrame.Labels.Embed
import Work.Reframe.Geom3
import Work.BridgeGeom.Blocks

/-!
# GFrame labels, part 10 (key: eng-labels): the frame maps of the bridged geometry are `GXMap`s

Every frame map of the network geometry has the shape `Φ P = frameM (d (P ⊕ Q) dᵀ)` with `d`
orthogonal (`RF.PhiQ` of `Work/Reframe/Geom3.lean`, `BG.PhiB` of `Work/BridgeGeom/Blocks.lean`).
ONE lemma makes all of them Walsh-diagonal frame maps in the sense of `GXMap`:

* `GXMap.ofConj d hd Q`   `Φ P = frameM (d * fromBlocks P 0 0 Q * dᵀ)` for ANY `d` with
                          `dᵀ d = 1` and ANY block `Q`;
* `gxmapQ`, `gxmapB`      the `GXMap`s with `Φ = RF.PhiQ d q`, `Φ = BG.PhiB d q` (`rfl`).

So the geometry needs NO change to consume generalised climbs: wherever it builds an `XMap`
(`fmapQ`, `fmapB`) it can build the `GXMap` instead, and `GXMap.toXMap` returns the old one.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.GF
open Binary Matrix Finset RAM CB SS
noncomputable section

section
variable {H β : Type} [Fintype H] [DecidableEq H] [Fintype β] [DecidableEq β]

lemma mul_vv_mul {κ ν : Type} [Fintype κ] [DecidableEq κ] [Fintype ν] [DecidableEq ν]
    (E : Matrix ν κ F) (a b : Space κ) : E * vv a b * Eᵀ = vv (E *ᵥ a) (E *ᵥ b) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, vv, Matrix.mulVec, dotProduct]
  rw [Finset.sum_mul_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro k _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro l _
  ring

/-- `a ↦ d (a ⊕ 0)`, linear. -/
def conjL (d : Matrix (H ⊕ β) (H ⊕ β) F) : Space H →ₗ[F] Space (H ⊕ β) where
  toFun := fun a => d *ᵥ (Sum.elim a (0 : Space β))
  map_add' := fun a b => by
    rw [← Matrix.mulVec_add]; congr 1; funext x; cases x <;> simp
  map_smul' := fun c a => by
    rw [RingHom.id_apply, ← Matrix.mulVec_smul]; congr 1; funext x; cases x <;> simp

lemma gram_conj (d : Matrix (H ⊕ β) (H ⊕ β) F) (hd : dᵀ * d = 1) (P : Matrix H H F)
    (Q : Matrix β β F) :
    (d * fromBlocks P 0 0 Q * dᵀ)ᵀ * (d * fromBlocks P 0 0 Q * dᵀ)
      = d * fromBlocks (gram P) 0 0 0 * dᵀ + d * fromBlocks 0 0 0 (Qᵀ * Q) * dᵀ := by
  have h1 : (d * fromBlocks P 0 0 Q * dᵀ)ᵀ = d * fromBlocks Pᵀ 0 0 Qᵀ * dᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.fromBlocks_transpose, ← Matrix.mul_assoc]
    simp
  rw [h1]
  have h2 : d * fromBlocks Pᵀ 0 0 Qᵀ * dᵀ * (d * fromBlocks P 0 0 Q * dᵀ)
      = d * (fromBlocks Pᵀ 0 0 Qᵀ * ((dᵀ * d) * fromBlocks P 0 0 Q)) * dᵀ := by
    simp only [Matrix.mul_assoc]
  rw [h2, hd, Matrix.one_mul, Matrix.fromBlocks_multiply, ← Matrix.add_mul, ← Matrix.mul_add,
    Matrix.fromBlocks_add]
  simp [gram]

/-- **Frame map of a conjugated block sum**: `Φ P = frameM (d (P ⊕ Q) dᵀ)`, `d` orthogonal. -/
def GXMap.ofConj (d : Matrix (H ⊕ β) (H ⊕ β) F) (hd : dᵀ * d = 1) (Q : Matrix β β F)
    (hβ : 0 < Fintype.card β) : GXMap H (H ⊕ β) where
  Φ := fun P => frameM (d * fromBlocks P 0 0 Q * dᵀ)
  ph := fun P x => lum ((d * fromBlocks P 0 0 Q * dᵀ) *ᵥ x)
  hΦ := fun P => rfl
  L := fun B => d * fromBlocks B 0 0 0 * dᵀ
  B0 := d * fromBlocks 0 0 0 (Qᵀ * Q) * dᵀ
  quad := fun P => (QPh.of_lum _).congr (gram_conj d hd P Q)
  ι := conjL d
  inj := fun a b h => by
    have h1 : dᵀ *ᵥ (d *ᵥ Sum.elim a (0 : Space β)) = dᵀ *ᵥ (d *ᵥ Sum.elim b (0 : Space β)) :=
      congrArg (fun v => dᵀ *ᵥ v) h
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hd, Matrix.one_mulVec,
      Matrix.one_mulVec] at h1
    funext i
    exact congrFun h1 (Sum.inl i)
  L_add := fun B B' => by
    rw [← Matrix.add_mul, ← Matrix.mul_add, Matrix.fromBlocks_add]; simp
  L_vv := fun a b => by
    have e : fromBlocks (vv a b) 0 0 0
        = vv (Sum.elim a (0 : Space β)) (Sum.elim b (0 : Space β)) := by
      ext i j; rcases i with i|i <;> rcases j with j|j <;> simp [vv]
    rw [e, mul_vv_mul]; rfl
  card := by rw [Fintype.card_sum]; omega

end

section Inst
variable {B H : Type} [Fintype B] [DecidableEq B] [Fintype H] [DecidableEq H]

/-- the frame map `RF.PhiQ d q` of the three-fold geometry as a `GXMap`. -/
def gxmapQ (hH : 1 ≤ Fintype.card H) (d : RF.Orth (RF.L3 H)) (q : Finset (Bool × H)) :
    GXMap H (RF.L3 H) :=
  GXMap.ofConj d.1 d.2 (RF.diagI q) (by rw [Fintype.card_prod, Fintype.card_bool]; omega)

theorem gxmapQ_Φ (hH : 1 ≤ Fintype.card H) (d : RF.Orth (RF.L3 H)) (q : Finset (Bool × H)) :
    (gxmapQ hH d q).Φ = RF.PhiQ d q := rfl

/-- the frame map `BG.PhiB d q` of the bridged geometry as a `GXMap`. -/
def gxmapB (hB : 1 ≤ Fintype.card B) (hH : 1 ≤ Fintype.card H) (d : RF.Orth (BG.LB B H))
    (q : Finset (B × H)) : GXMap H (BG.LB B H) :=
  GXMap.ofConj d.1 d.2 (RF.diagI q) (by rw [Fintype.card_prod]; exact Nat.mul_pos hB hH)

theorem gxmapB_Φ (hB : 1 ≤ Fintype.card B) (hH : 1 ≤ Fintype.card H) (d : RF.Orth (BG.LB B H))
    (q : Finset (B × H)) : (gxmapB hB hH d q).Φ = BG.PhiB d q := rfl

end Inst
end
end PowerSaving.GF
end OAI

#print axioms OAI.PowerSaving.GF.GXMap.ofConj
#print axioms OAI.PowerSaving.GF.gxmapQ_Φ
#print axioms OAI.PowerSaving.GF.gxmapB_Φ
