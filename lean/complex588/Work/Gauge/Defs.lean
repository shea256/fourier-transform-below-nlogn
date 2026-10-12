import Work.GCert.Chain.InvThm

/-!
# (key: gauge-401) L1 definitions: gauged invocations (entrance gauges, Dugongue PR #401)

DFT Bridge3, 2026-10-11.  `GScal` = Jacob's `Scal` + the E7 fact; `GLab` = Jacob's `Lab` with the slot start label
free; `GInvE` = `GInv` with a per-slot entrance step: slot `q` starts at the frame of its entrance label `ent q` and
ends at the frame of the full label in the same base (`SLbl.top`).
Credits: Jacob Sussman (engine, chain, Apache-2.0); Dugongue (#401 entrance gauges).  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.GF
/-- the full label in the base of `U`. -/
def SLbl.top {H : Type} [Fintype H] (U : SLbl H) : SLbl H := ⟨U.G, Finset.univ⟩
@[simp] lemma SLbl.top_G {H : Type} [Fintype H] (U : SLbl H) : U.top.G = U.G := rfl
@[simp] lemma SLbl.top_s {H : Type} [Fintype H] (U : SLbl H) : U.top.s = Finset.univ := rfl
lemma SLbl.top_dim {H : Type} [Fintype H] (U : SLbl H) : U.top.dim = Fintype.card H := Finset.card_univ
end PowerSaving.GF
namespace PowerSaving
namespace GX
open Binary Matrix Finset RAM SS CB BR CR GF RF
noncomputable section

/-- **Scalar half with entrance gauges**: a gauged slot never reaches a target (E7). -/
structure GScal (T Sl C : Type) [Fintype T] [DecidableEq T]
    [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] extends Scal T Sl C where
  gauged : Finset Sl
  hE : ∀ q ∈ gauged, ∀ t, (MB * scatM (Jr * Cc) * MA) (lY t) (lS q) = 0

/-- **Label half with entrance labels** (Jacob's `Lab` with `h0s` replaced by `h0s'`, `hent`). -/
structure GLab (H : Type) [Fintype H] [DecidableEq H] {T Sl C : Type} [Fintype T] [DecidableEq T]
    [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] (S : GScal T Sl C) where
  tv : T → Space H
  hunit : ∀ t, dot (tv t) (tv t) = 1
  hgap : ∀ t, ∃ p, tv t p = 0
  ent : Sl → SLbl H
  lab0 : L3 T Sl → SLbl H
  labA : L3 T Sl → SLbl H
  labB : L3 T Sl → SLbl H
  labF : L3 T Sl → SLbl H
  cen : C → SLbl H
  z0 : SLbl H
  hz0 : z0.dim = 0
  h0x : ∀ t, (lab0 (lX t)).dim = 1 ∧ (lab0 (lX t)).Mem (tv t)
  h0y : ∀ t, (lab0 (lY t)).dim = 0
  h0s' : ∀ q, lab0 (lS q) = ent q
  hent : ∀ q, q ∉ S.gauged → (ent q).dim = 0
  hAy : ∀ t, labA (lY t) = z0
  hAc : ∀ k q, S.Cc k q ≠ 0 → cen k = labA (lS q)
  hcen : ∀ k, 0 < (cen k).dim
  hFx : ∀ t, (labF (lX t)).dim = Fintype.card H
  hFs : ∀ q, (labF (lS q)).dim = Fintype.card H
  hFy : ∀ t, (labF (lY t)).dim + 1 = Fintype.card H ∧
    ∀ x, (labF (lY t)).Mem x → dot (tv t) x = 0
  rA : List ℕ
  rB : List ℕ
  rF : List ℕ
  pA : ∀ {α : Type} [Fintype α] [DecidableEq α] (X : BXMap H α),
    Fintype.card H < Fintype.card α →
    GRoute (fun r => X.Φ (lab0 r)) (fun r => X.Φ (labA r)) (actPoint S.MA)
        (fun φ => rcost φ rA) ∧
    GRoute (fun r => X.Φ (lab0 r)) (fun r => X.Φ (labA r)) (actPoint S.MAiᵀ)
        (fun φ => rcost φ rA)
  pB : ∀ {α : Type} [Fintype α] [DecidableEq α] (X : BXMap H α),
    Fintype.card H < Fintype.card α →
    GRoute (fun r => X.Φ (labA r)) (fun r => X.Φ (labB r)) (actPoint S.MB)
        (fun φ => rcost φ rB) ∧
    GRoute (fun r => X.Φ (labA r)) (fun r => X.Φ (labB r)) (actPoint S.MBiᵀ)
        (fun φ => rcost φ rB)
  pF : ∀ {α : Type} [Fintype α] [DecidableEq α] (X : BXMap H α),
    Fintype.card H < Fintype.card α →
    GRoute (fun r => X.Φ (labB r)) (fun r => X.Φ (labF r)) id (fun φ => rcost φ rF)

/-- price of one gauged invocation (as `Lab.cost`). -/
def GLab.cost {H : Type} [Fintype H] [DecidableEq H] {T Sl C : Type} [Fintype T] [DecidableEq T]
    [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] {S : GScal T Sl C} (L : GLab H S)
    (φ : ℕ → ℝ) : ℝ :=
  rcost φ L.rA + (∑ k, bcost φ (L.cen k).dim) + rcost φ L.rB + rcost φ L.rF

/-- **A gauged invocation, as a package** (`GInv` with a per-slot entrance step: slot `q` goes from
`X.Φ (ent q) * N q * Z q = Z q` to `X.Φ (ent q).top * N q * Z q = Wn q * Z q`). -/
structure GInvE (H T Sl C : Type) [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
    [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] where
  tv : T → Space H
  hunit : ∀ t, dot (tv t) (tv t) = 1
  hgap : ∀ t, ∃ p, tv t p = 0
  cost : (ℕ → ℝ) → ℝ
  ent : Sl → SLbl H
  fwd : ∀ {α : Type} [Fintype α] [DecidableEq α] (W : GWin H α) (N Wn : Sl → CMat α),
    (∀ q, W.X.Φ (ent q) * N q = 1) → (∀ q, W.X.Φ (ent q).top = Wn q * W.X.Φ (ent q)) →
    ∀ (Z : Sl → CMat α) (c0 c1 : C → CMat α),
    GRoute (iin W.Xm tv Z c0) (iout W.Xm tv (fun q => Wn q * Z q) c1) shearF cost
  bwd : ∀ {α : Type} [Fintype α] [DecidableEq α] (W : GWin H α) (N Wn : Sl → CMat α),
    (∀ q, W.X.Φ (ent q) * N q = 1) → (∀ q, W.X.Φ (ent q).top = Wn q * W.X.Φ (ent q)) →
    ∀ (Z : Sl → CMat α) (c0 c1 : C → CMat α),
    GRoute (iin W.Xm tv Z c0) (iout W.Xm tv (fun q => Wn q * Z q) c1) shearB cost

end
end GX
end PowerSaving
end OAI
