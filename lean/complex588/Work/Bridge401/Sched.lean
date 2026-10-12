import Work.Bank401.Frames
import Work.Gauge.Defs

/-!
# (key: bridge-401) Bank schedules of the #401 word and their bank frames

* `BankSched Sl`: `nb` banks per class; `use ρ l q` = the bank of the slot `q` in stage `l` of run `ρ` (injective per
  sub-stage: at most ONE use of a bank per sub-stage); `pad b` = the rank of the padding block of the bank `b`.
* `BankSched.load S r b` = the residual load of the bank `b` (`r q = 9 - e_q`).
* `entW X U`, `entN X U`: the entrance step `X.Φ U.top = entW X U * X.Φ U` and the right inverse `X.Φ U * entN X U = 1`
  of an entrance label `U` in a window `X` (`entW` = ONE kernel factor between free adapters).
* `sched_frames`: if `load + pad = card α` and `pad < card α` for every bank, the bank frames `Zb`, `Zp` of
  `bank_frames` exist for the 72 sub-stages `9 ρ + l` with the entrance steps of the windows `win l`.

Entrance gauges and residual banks: Dugongue (CrocSwap/integer-mult-bounds PR #401); bank patterns: Lydakis (#275);
engine: Jacob Sussman.  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace GX
open Binary Matrix Finset RAM CB GF B401
noncomputable section

/-- **A bank schedule of the #401 word** (per class: `nb` banks, 8 runs of 9 stages). -/
structure BankSched (Sl : Type) [Fintype Sl] where
  nb : ℕ
  use : Fin 8 → Fin 9 → Sl → Fin nb
  hinj : ∀ ρ l, Function.Injective (use ρ l)
  pad : Fin nb → ℕ

section Sched
variable {Sl : Type} [Fintype Sl] [DecidableEq Sl] (S : BankSched Sl)

/-- the use of sub-stage `k = 9 ρ + l`. -/
def BankSched.useK (k : ℕ) : Sl → Fin S.nb :=
  S.use ⟨k / 9 % 8, Nat.mod_lt _ (by norm_num)⟩ ⟨k % 9, Nat.mod_lt _ (by norm_num)⟩

lemma BankSched.useK_eq (ρ : Fin 8) (l : Fin 9) : S.useK (9 * ρ.val + l.val) = S.use ρ l := by
  unfold BankSched.useK
  have h1 : (⟨(9 * ρ.val + l.val) / 9 % 8, Nat.mod_lt _ (by norm_num)⟩ : Fin 8) = ρ := by
    apply Fin.ext
    show (9 * ρ.val + l.val) / 9 % 8 = ρ.val
    have := ρ.isLt
    have := l.isLt
    omega
  have h2 : (⟨(9 * ρ.val + l.val) % 9, Nat.mod_lt _ (by norm_num)⟩ : Fin 9) = l := by
    apply Fin.ext
    show (9 * ρ.val + l.val) % 9 = l.val
    have := l.isLt
    omega
  rw [h1, h2]

/-- the residual load of the bank `b`. -/
def BankSched.load (r : Sl → ℕ) (b : Fin S.nb) : ℕ :=
  ∑ ρ : Fin 8, ∑ l : Fin 9, ∑ q ∈ univ.filter (fun q => S.use ρ l q = b), r q

/-- **The residual condition** between a schedule and the entrance labels: `load + pad = 73`, `pad < 73`. -/
def BankSched.fits {H : Type} [Fintype H] (ent : Sl → SLbl H) : Prop :=
  (∀ b, S.load (fun q => Fintype.card H - (ent q).dim) b + S.pad b = 73) ∧ ∀ b, S.pad b < 73

lemma BankSched.L_eq (r : Sl → ℕ) (b : Fin S.nb) : L S.useK r 72 b = S.load r b := by
  unfold L BankSched.load
  rw [Finset.sum_range (fun k => rr S.useK r k b)]
  rw [← (finProdFinEquiv : Fin 8 × Fin 9 ≃ Fin 72).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun ρ _ => Finset.sum_congr rfl (fun l _ => ?_))
  have e : ((finProdFinEquiv : Fin 8 × Fin 9 ≃ Fin 72) (ρ, l)).val = 9 * ρ.val + l.val := by
    rw [finProdFinEquiv_apply_val]
    ring
  rw [e]
  unfold rr
  rw [S.useK_eq ρ l]

end Sched

section Ent
variable {H α : Type} [Fintype H] [DecidableEq H] [Fintype α] [DecidableEq α]

/-- the entrance step of the label `U` in the window `X`. -/
def entW (X : BXMap H α) (U : SLbl H) : CMat α :=
  kg (X.liftG U.G) * pk (X.liftS univ \ X.liftS U.s) * kg (apInv (X.liftG U.G))

/-- a right inverse of the frame of `U`. -/
def entN (X : BXMap H α) (U : SLbl H) : CMat α :=
  kg (X.liftG U.G) * (pk (X.liftS U.s) * shift (indv (X.liftS U.s))) * kg (apInv (X.liftG U.G))

lemma entN_spec (X : BXMap H α) (U : SLbl H) : X.Φ U * entN X U = 1 := by
  show core (X.liftG U.G) (X.liftS U.s) * _ = 1
  unfold core entN
  have e : kg (X.liftG U.G) * pk (X.liftS U.s) * kg (apInv (X.liftG U.G))
        * (kg (X.liftG U.G) * (pk (X.liftS U.s) * shift (indv (X.liftS U.s))) * kg (apInv (X.liftG U.G)))
      = kg (X.liftG U.G) * ((pk (X.liftS U.s) * ((kg (apInv (X.liftG U.G)) * kg (X.liftG U.G))
          * pk (X.liftS U.s))) * shift (indv (X.liftS U.s))) * kg (apInv (X.liftG U.G)) := by
    simp only [Matrix.mul_assoc]
  rw [e, kg_inv_mul, Matrix.one_mul, pk_sq, shift_sq, Matrix.mul_one, kg_mul_inv]

lemma entW_spec (X : BXMap H α) (U : SLbl H) : X.Φ U.top = entW X U * X.Φ U := by
  have hs : X.liftS U.s ⊆ X.liftS univ := X.mono (Finset.subset_univ _)
  show core (X.liftG U.G) (X.liftS univ) = entW X U * core (X.liftG U.G) (X.liftS U.s)
  rw [core_nested _ hs, entW, pk_eq_blockMat]

lemma entW_form (X : BXMap H α) (U : SLbl H) :
    ∃ (C C' : CMat α) (R : Finset α), Free C ∧ Free C' ∧ R.card = Fintype.card H - U.dim ∧
      entW X U = C * pk R * C' := by
  refine ⟨_, _, X.liftS univ \ X.liftS U.s, free_kg _, free_kg _, ?_, rfl⟩
  rw [X.card (Finset.subset_univ U.s), Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
  rfl

end Ent

section Frames
variable {H α Γ Sl : Type} [Fintype H] [DecidableEq H] [Fintype α] [DecidableEq α] [Fintype Sl] [DecidableEq Sl]

/-- **The bank frames of a schedule** (from `bank_frames`). -/
theorem sched_frames (S : BankSched Sl) (ent : Sl → SLbl H) (win : Fin 9 → Γ → GWin H α)
    (hres : ∀ b, S.load (fun q => Fintype.card H - (ent q).dim) b + S.pad b = Fintype.card α)
    (hpad : ∀ b, S.pad b < Fintype.card α) :
    ∃ Zb Zp : ℕ → Γ → Fin S.nb → CMat α,
      (∀ g b, Zb 0 g b = 1) ∧
      (∀ (ρ : Fin 8) (l : Fin 9) g b,
        GReach (Zb (9 * ρ.val + l.val) g b) (Zp (9 * ρ.val + l.val) g b) (fun _ => 0)) ∧
      (∀ (ρ : Fin 8) (l : Fin 9) g q, entW (win l g).X (ent q) * Zp (9 * ρ.val + l.val) g (S.use ρ l q)
        = Zb (9 * ρ.val + l.val + 1) g (S.use ρ l q)) ∧
      (∀ (ρ : Fin 8) (l : Fin 9) g b, (∀ q, S.use ρ l q ≠ b) →
        Zb (9 * ρ.val + l.val + 1) g b = Zp (9 * ρ.val + l.val) g b) ∧
      (∀ g b, GReach (Zb 72 g b) (kernel α) (fun φ => bcost φ (S.pad b))) := by
  let r : Sl → ℕ := fun q => Fintype.card H - (ent q).dim
  let Wn : ℕ → Γ → Sl → CMat α := fun k d q => entW (win ⟨k % 9, Nat.mod_lt _ (by norm_num)⟩ d).X (ent q)
  have hL : ∀ b, L S.useK r 72 b = S.load r b := S.L_eq r
  have hres' : ∀ b, S.load r b + S.pad b = Fintype.card α := hres
  obtain ⟨Zb, Zp, h0, hP, hU, hN, hpd⟩ := bank_frames S.useK r Wn 72
    (fun k _ => S.hinj _ _)
    (fun k _ d q => entW_form _ (ent q))
    (fun b => by rw [hL]; have := hres' b; omega)
    (fun b => by rw [hL]; have := hres' b; have := hpad b; omega)
  have hw : ∀ (ρ : Fin 8) (l : Fin 9),
      (⟨(9 * ρ.val + l.val) % 9, Nat.mod_lt _ (by norm_num)⟩ : Fin 9) = l := fun ρ l =>
    Fin.ext (by show (9 * ρ.val + l.val) % 9 = l.val; have := l.isLt; omega)
  refine ⟨Zb, Zp, h0, fun ρ l g b => hP _ (by have := ρ.isLt; have := l.isLt; omega) g b, ?_, ?_, ?_⟩
  · intro ρ l g q
    have h := hU (9 * ρ.val + l.val) (by have := ρ.isLt; have := l.isLt; omega) g q
    simp only [Wn, hw ρ l, S.useK_eq ρ l] at h
    exact h
  · intro ρ l g b hb
    refine hN (9 * ρ.val + l.val) (by have := ρ.isLt; have := l.isLt; omega) g b (fun q => ?_)
    rw [S.useK_eq ρ l]
    exact hb q
  · intro g b
    have h := hpd g b
    have e : Fintype.card α - L S.useK r 72 b = S.pad b := by
      rw [hL]; have := hres' b; omega
    rw [e] at h
    exact h

end Frames
end
end GX
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.GX.BankSched.L_eq
#print axioms OAI.PowerSaving.GX.sched_frames

