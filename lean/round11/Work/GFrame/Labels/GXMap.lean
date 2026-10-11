import Work.GFrame.Labels.Quad
import Work.GFrame.Labels.Sched

/-!
# GFrame labels, part 5 (key: eng-labels): STAGE A labels, climbs and frame maps

Labels of stage A are the old ones (`SS.Lbl H`: a matrix `P` over `F_2` and a nominal dimension).
The frame of `P` is a quadratic phase whose polar form is the GRAM matrix `gram P = Pᵀ P`
(`= P` for a projector).  A nested step needs NO orthonormal basis and NO unit vector:

* `GClimbO U V r`  `gram V.P = gram U.P + ∑ z_i z_iᵀ` for `r` linearly independent `z_i`
                   (old `Climb`: the `z_i` are lines of one orthonormal basis);
* `GClimbA U V p`  `gram V.P = gram U.P + ∑ (w_j w'_jᵀ + w'_j w_jᵀ)`: an ALTERNATING residual of
                   rank `2p` with symplectic data `w, w'` (no unit vector at all);
* `GMv ar U V rs`  one move: stay, up or down, of either kind, with the block ranks it pays;
* `AltAt K ar`     the engine `K` performs an alternating residual of rank `2p` at the block
                   ranks `ar p` (`[2p]`: one twisted block; `[2p,1]`: old engine);
* `GXMap H α`      a Walsh-diagonal frame map: `Φ P = wrap (ph P)`, `ph P` a quadratic phase
                   whose polar form is a linear lift of `gram P`;
* `GXMap.orth`, `GXMap.alt`, `GXMap.mv`   every climb is an `FMv` of ANY engine: ONE block of
                   rank `r` (orthonormal type), `ar p` (alternating).

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.GF
open Binary Matrix Finset RAM CB SS
noncomputable section

section
variable {H α : Type} [Fintype H] [DecidableEq H] [Fintype α] [DecidableEq α]

/-- Gram matrix of a label matrix: the polar form of its frame (`= P` for a projector). -/
def gram (P : Matrix H H F) : Matrix H H F := Pᵀ * P

lemma add_add_cancel_F (B S : Matrix H H F) : B + S + S = B := by
  ext i j; simp [add_assoc]

/-- the relation "the polar forms differ by `S`" is symmetric (characteristic 2). -/
lemma rel_symm {B B' S : Matrix H H F} (h : B' = B + S) : B = B' + S := by
  rw [h, add_add_cancel_F]

/-- nested step, residual `∑ z_i z_iᵀ` along `r` linearly independent vectors. -/
def GClimbO (U V : Lbl H) (r : ℕ) : Prop :=
  ∃ z : Fin r → Space H, LinearIndependent F z ∧
    gram V.P = gram U.P + ∑ i, tt (z i) ∧ V.d = U.d + r

/-- nested step, ALTERNATING residual of rank `2p` with symplectic data `w, w'`. -/
def GClimbA (U V : Lbl H) (p : ℕ) : Prop :=
  ∃ w w' : Fin p → Space H, LinearIndependent F (Sum.elim w w') ∧ 1 ≤ p ∧
    gram V.P = gram U.P + ∑ j, (vv (w j) (w' j) + vv (w' j) (w j)) ∧ V.d = U.d + 2 * p

/-- one move of one role, with the block ranks it pays when an alternating residual of rank
`2p` pays `ar p`. -/
inductive GMv (ar : ℕ → List ℕ) : Lbl H → Lbl H → List ℕ → Prop
  | stay (U : Lbl H) : GMv ar U U [0]
  | up {U V : Lbl H} {r : ℕ} : GClimbO U V r → GMv ar U V [r]
  | down {U V : Lbl H} {r : ℕ} : GClimbO U V r → GMv ar V U [r]
  | aup {U V : Lbl H} {p : ℕ} : GClimbA U V p → GMv ar U V (ar p)
  | adown {U V : Lbl H} {p : ℕ} : GClimbA U V p → GMv ar V U (ar p)

/-- the engine `K` performs an alternating residual of rank `2p` at the block ranks `ar p`. -/
def AltAt (K : Calc α) (ar : ℕ → List ℕ) : Prop :=
  ∀ {p : ℕ} (w w' : Fin p → Space α), LinearIndependent F (Sum.elim w w') → 1 ≤ p →
    2 * p < Fintype.card α → ∀ M : CMat α, FMv K M (altMat w w' * M) (ar p)

/-- **A Walsh-diagonal frame map** (stage A): `Φ P = wrap (ph P)` where `ph P` is a quadratic
phase with polar form `L (gram P) + B0`, `L` additive with `L (a bᵀ) = (ι a) (ι b)ᵀ` for an
injective linear `ι`, and the label space is smaller than the address space. -/
structure GXMap (H α : Type) [Fintype H] [DecidableEq H] [Fintype α] [DecidableEq α] where
  Φ : Matrix H H F → CMat α
  ph : Matrix H H F → Space α → ℂ
  hΦ : ∀ P, Φ P = wrap (ph P)
  L : Matrix H H F → Matrix α α F
  B0 : Matrix α α F
  quad : ∀ P, QPh (ph P) (L (gram P) + B0)
  ι : Space H →ₗ[F] Space α
  inj : Function.Injective ι
  L_add : ∀ B B', L (B + B') = L B + L B'
  L_vv : ∀ a b : Space H, L (vv a b) = vv (ι a) (ι b)
  card : Fintype.card H < Fintype.card α

namespace GXMap
variable (X : GXMap H α)

lemma L_zero : X.L 0 = 0 := by
  have h := X.L_add 0 0
  rw [add_zero] at h
  exact add_left_cancel (a := X.L 0) (by rw [add_zero]; exact h.symm)

lemma L_sum {κ : Type} (s : Finset κ) (B : κ → Matrix H H F) :
    X.L (∑ i ∈ s, B i) = ∑ i ∈ s, X.L (B i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [X.L_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, X.L_add, ih]

lemma rank_lt_of {κ : Type} [Fintype κ] {v : κ → Space H} (ind : LinearIndependent F v)
    (hc : Fintype.card H < Fintype.card α) : Fintype.card κ < Fintype.card α := by
  have h := ind.fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card] at h
  exact lt_of_le_of_lt h hc

/-- **Orthonormal-type residual: ONE block of rank `r`, in every engine.** -/
theorem orth (K : Calc α) (P P' : Matrix H H F) {r : ℕ} (z : Fin r → Space H)
    (ind : LinearIndependent F z) (hg : gram P' = gram P + ∑ i, tt (z i)) :
    FMv K (X.Φ P) (X.Φ P') [r] := by
  have hq : QPh (X.ph P') ((X.L (gram P) + X.B0) + ∑ i, tt (X.ι (z i))) := by
    refine (X.quad P').congr ?_
    rw [hg, X.L_add, X.L_sum, add_right_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [tt_eq_vv, X.L_vv]; rfl
  obtain ⟨c, hc⟩ := wrap_step (fun i => X.ι (z i)) (X.quad P) hq
  rw [X.hΦ P, X.hΦ P', hc]
  by_cases h0 : r = 0
  · subst h0
    rw [blockMat_zero, mul_one]
    exact FMv.zero (FMv.shift K _ c)
  · have ind' : LinearIndependent F (fun i => X.ι (z i)) :=
      ind.map' X.ι (LinearMap.ker_eq_bot.mpr X.inj)
    have hr : r < Fintype.card α := by simpa using rank_lt_of ind X.card
    rw [mul_assoc]
    exact (FMv.block _ ind' (by omega) hr).trans (FMv.shift K _ c)

/-- **Alternating residual of rank `2p`: the block ranks `ar p` of the engine.** -/
theorem alt {K : Calc α} {ar : ℕ → List ℕ} (hK : AltAt K ar) (P P' : Matrix H H F) {p : ℕ}
    (w w' : Fin p → Space H) (ind : LinearIndependent F (Sum.elim w w')) (hp : 1 ≤ p)
    (hg : gram P' = gram P + ∑ j, (vv (w j) (w' j) + vv (w' j) (w j))) :
    FMv K (X.Φ P) (X.Φ P') (ar p) := by
  have hq : QPh (X.ph P') ((X.L (gram P) + X.B0) +
      ∑ j, (vv (X.ι (w j)) (X.ι (w' j)) + vv (X.ι (w' j)) (X.ι (w j)))) := by
    refine (X.quad P').congr ?_
    rw [hg, X.L_add, X.L_sum, add_right_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [X.L_add, X.L_vv, X.L_vv]
  obtain ⟨c, hc⟩ := wrap_astep (fun j => X.ι (w j)) (fun j => X.ι (w' j)) (X.quad P) hq
  rw [X.hΦ P, X.hΦ P', hc, mul_assoc]
  have ind' : LinearIndependent F
      (Sum.elim (fun j => X.ι (w j)) (fun j => X.ι (w' j))) := by
    have h := ind.map' X.ι (LinearMap.ker_eq_bot.mpr X.inj)
    have e : (Sum.elim (fun j => X.ι (w j)) (fun j => X.ι (w' j)))
        = ⇑X.ι ∘ Sum.elim w w' := by
      funext s; cases s <;> rfl
    rw [e]; exact h
  have hr : 2 * p < Fintype.card α := by
    have h := rank_lt_of ind X.card
    rw [Fintype.card_sum, Fintype.card_fin] at h
    omega
  have h := (hK _ _ ind' hp hr (wrap (X.ph P))).trans (FMv.shift K _ c)
  rw [List.append_nil] at h
  exact h

/-- **Every stage-A move is a one-role move of the engine**, with its block ranks. -/
theorem mv {K : Calc α} {ar : ℕ → List ℕ} (hK : AltAt K ar) {U V : Lbl H} {rs : List ℕ}
    (h : GMv ar U V rs) : FMv K (X.Φ U.P) (X.Φ V.P) rs := by
  cases h with
  | stay U => exact FMv.zero (FMv.refl K _)
  | up h =>
    obtain ⟨z, ind, hg, _⟩ := h
    exact X.orth K _ _ z ind hg
  | down h =>
    obtain ⟨z, ind, hg, _⟩ := h
    exact X.orth K _ _ z ind (rel_symm hg)
  | aup h =>
    obtain ⟨w, w', ind, hp, hg, _⟩ := h
    exact X.alt hK _ _ w w' ind hp hg
  | adown h =>
    obtain ⟨w, w', ind, hp, hg, _⟩ := h
    exact X.alt hK _ _ w w' ind hp (rel_symm hg)

end GXMap
end
end
end PowerSaving.GF
end OAI

#print axioms OAI.PowerSaving.GF.GXMap.orth
#print axioms OAI.PowerSaving.GF.GXMap.alt
#print axioms OAI.PowerSaving.GF.GXMap.mv
