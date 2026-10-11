import Work.GCert.Chain.Phased
import Work.GFrame.Top.Api

/-!
# (key: gx-chain) A window of the generalised engine, and its four free end adapters

`GWin H α`: an old block frame map `Xm : XMap H α` (bank frames, slot base and top), a stage-B
frame map `X : BXMap H α` (arbitrary subspaces of `H`), and the FREE change between the old
frame of a coordinate subspace of an orthonormal basis and the representative of ANY label
naming the same subspace (`toNew`, `toOld`: no block).

Derived: `line`, `zero`, `full`, `perp` from dimensions and ONE-directional membership
(`insub_iff_of_card`: an inclusion of subspaces of equal dimension is an equality).

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace GX
open Binary Matrix Finset RAM SS CB BR CR GF
noncomputable section

section Sub
variable {α : Type} [Fintype α] [DecidableEq α]

lemma aperm_zero (G : APerm α) : G.π 0 = 0 := by
  have h := G.add 0 0
  rw [add_zero] at h
  exact add_left_cancel (h.symm.trans (add_zero _).symm)

lemma insub_zero (G : APerm α) (s : Finset α) : InSub G s 0 := fun k _ => by
  rw [aperm_zero]; rfl

/-- a label of dimension 0 names the zero subspace. -/
lemma mem_dim_zero (U : SLbl α) (hd : U.dim = 0) {x : Space α} (h : U.Mem x) : x = 0 := by
  have hs : U.s = ∅ := Finset.card_eq_zero.mp hd
  have h0 : U.G.π x = 0 := by
    funext k
    exact h k (by rw [hs]; exact Finset.notMem_empty k)
  exact U.G.π.injective (h0.trans (aperm_zero U.G).symm)

/-- **an inclusion of subspaces of equal dimension is an equality.** -/
theorem insub_iff_of_card (G G' : APerm α) (s t : Finset α)
    (h : ∀ x, InSub G s x → InSub G' t x) (hc : s.card = t.card) :
    ∀ x, InSub G s x ↔ InSub G' t x := by
  obtain ⟨G₀, s₀, t₀, hst, h1, h2⟩ := exists_common_base G G' s t h
  have hr := climb_rank h1 h2 hst
  have h0 : t₀ \ s₀ = ∅ := Finset.card_eq_zero.mp (by rw [hr, hc]; exact Nat.sub_self _)
  have e : s₀ = t₀ := Finset.Subset.antisymm hst (Finset.sdiff_eq_empty_iff_subset.mp h0)
  subst e
  exact fun x => (h1 x).trans (h2 x)

end Sub

/-- **A window of the generalised engine.**  See the file header. -/
structure GWin (H α : Type) [Fintype H] [DecidableEq H] [Fintype α] [DecidableEq α] where
  Xm : XMap H α
  X : BXMap H α
  big : Fintype.card H < Fintype.card α
  toNew : ∀ (A : OBase H) (s : Finset H) (U : SLbl H),
    (∀ x, U.Mem x ↔ InSub (coordPerm A) s x) →
    GReach (Xm.Φ (A.mat s)) (X.Φ U) (fun _ => 0)
  toOld : ∀ (A : OBase H) (s : Finset H) (U : SLbl H),
    (∀ x, U.Mem x ↔ InSub (coordPerm A) s x) →
    GReach (X.Φ U) (Xm.Φ (A.mat s)) (fun _ => 0)

section Ends
variable {H α : Type} [Fintype H] [DecidableEq H] [Fintype α] [DecidableEq α]

/-- a vector whose coordinates outside `l` vanish is `0` or the basis vector. -/
lemma coord_single (A : OBase H) (l : H) (x : Space H) (h : InSub (coordPerm A) {l} x) :
    x = 0 ∨ x = A.v l := by
  have hx : x = dot (A.v l) x • A.v l := by
    have e : ∑ k, dot (A.v k) x • A.v k = x := A.proj_univ x
    rw [Finset.sum_eq_single l (fun k _ hk => by
      rw [(insub_coordPerm A {l} x).mp h k (by simpa using hk), zero_smul])
      (fun hl => absurd (Finset.mem_univ l) hl)] at e
    exact e.symm
  rcases bit_cases (dot (A.v l) x) with h0 | h1
  · left; rw [hx, h0, zero_smul]
  · right; rw [hx, h1, one_smul]

lemma coord_empty (A : OBase H) (x : Space H) (h : InSub (coordPerm A) ∅ x) : x = 0 := by
  have e : ∑ k, dot (A.v k) x • A.v k = x := A.proj_univ x
  rw [Finset.sum_eq_zero (fun k _ => by
    rw [(insub_coordPerm A ∅ x).mp h k (Finset.notMem_empty k), zero_smul])] at e
  exact e.symm

namespace GWin
variable (W : GWin H α)

/-- start of an x role: the old frame of the line to ANY label of dimension 1 through it. -/
theorem line (A : OBase H) (l : H) (U : SLbl H) (hd : U.dim = 1) (hm : U.Mem (A.v l)) :
    GReach (W.Xm.Φ (tt (A.v l))) (W.X.Φ U) (fun _ => 0) := by
  rw [← mat_single]
  refine W.toNew A {l} U (fun x => (insub_iff_of_card (coordPerm A) U.G {l} U.s (fun y hy => ?_)
    (by rw [Finset.card_singleton]; exact hd.symm) x).symm)
  rcases coord_single A l y hy with rfl | rfl
  · exact insub_zero _ _
  · exact hm

/-- start of a y role or a slot: the old frame of 0 to ANY label of dimension 0. -/
theorem zero (U : SLbl H) (hd : U.dim = 0) :
    GReach (W.Xm.Φ 0) (W.X.Φ U) (fun _ => 0) := by
  rw [← mat_empty (OBase.canonical H)]
  refine W.toNew _ ∅ U (fun x => (insub_iff_of_card (coordPerm (OBase.canonical H)) U.G ∅ U.s
    (fun y hy => ?_) (by rw [Finset.card_empty]; exact hd.symm) x).symm)
  rw [coord_empty _ y hy]
  exact insub_zero _ _

/-- end of an x role or a slot: ANY label of full dimension to the old frame of 1. -/
theorem full (U : SLbl H) (hd : U.dim = Fintype.card H) :
    GReach (W.X.Φ U) (W.Xm.Φ 1) (fun _ => 0) := by
  have hU : U.s = univ := Finset.eq_univ_of_card U.s hd
  rw [← OBase.mat_univ (OBase.canonical H)]
  exact W.toOld _ univ U (fun x =>
    ⟨fun _ k hk => absurd (Finset.mem_univ k) hk,
     fun _ k hk => absurd (by rw [hU]; exact Finset.mem_univ k) hk⟩)

/-- end of a y role: ANY label of dimension `h - 1` orthogonal to the port to the old frame. -/
theorem perp (A : OBase H) (l : H) (U : SLbl H) (hd : U.dim + 1 = Fintype.card H)
    (hm : ∀ x, U.Mem x → dot (A.v l) x = 0) :
    GReach (W.X.Φ U) (W.Xm.Φ (1 + tt (A.v l))) (fun _ => 0) := by
  rw [← mat_compl_single]
  refine W.toOld A (univ \ {l}) U (insub_iff_of_card U.G (coordPerm A) U.s (univ \ {l})
    (fun y hy => (insub_coordPerm A _ y).mpr (fun k hk => ?_)) ?_)
  · have hk' : k = l := by
      by_contra hne
      exact hk (Finset.mem_sdiff.mpr ⟨Finset.mem_univ k, by simpa using hne⟩)
    rw [hk']
    exact hm y hy
  · rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Finset.card_singleton]
    have : U.s.card + 1 = Fintype.card H := hd
    omega

end GWin
end Ends
end
end GX
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.GX.insub_iff_of_card
#print axioms OAI.PowerSaving.GX.GWin.line
#print axioms OAI.PowerSaving.GX.GWin.zero
#print axioms OAI.PowerSaving.GX.GWin.full
#print axioms OAI.PowerSaving.GX.GWin.perp
