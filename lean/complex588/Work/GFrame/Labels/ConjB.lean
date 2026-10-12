import Work.GFrame.Labels.BXMap

/-!
# GFrame labels, part 15 (key: eng-labels): the STAGE B frame map of the bridged geometry

The geometry frames a label `U ⊂ F_2^H` on the address space `H ⊕ β` as the subspace
`d (U ⊕ span q)` (`d` orthogonal, `q` a set of the extra coordinates): for nondegenerate `U`
this is the subspace of `RF.PhiQ d q P`, `BG.PhiB d q P`.  Here the same for ARBITRARY `U`:

* `mvPerm d`        the additive bijection `y ↦ dᵀ y` (inverse `z ↦ d z`);
* `inlPerm G`       a base `G` of `H`, extended by the identity on `β`;
* `conjPerm d G`    `y ↦ (G (dᵀ y)_H, (dᵀ y)_β)`: the base of `H ⊕ β` adapted to `d (U ⊕ ·)`;
* `insub_conj`      `InSub (conjPerm d G) (s ⊔ q) y ↔ InSub G s (dᵀ y)_H ∧ (dᵀ y)_β ∈ span q`;
* `BXMap.ofConj d q`  the stage-B frame map `BXMap H (H ⊕ β)`.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.GF
open Binary Matrix Finset RAM CB
noncomputable section

section
variable {H β κ : Type} [Fintype H] [DecidableEq H] [Fintype β] [DecidableEq β]
  [Fintype κ] [DecidableEq κ]

/-- the additive bijection `y ↦ dᵀ y` of an orthogonal matrix. -/
def mvPerm (d : Matrix κ κ F) (hd : dᵀ * d = 1) (hd' : d * dᵀ = 1) : APerm κ where
  π :=
    { toFun := fun y => dᵀ *ᵥ y
      invFun := fun z => d *ᵥ z
      left_inv := fun y => by
        show d *ᵥ (dᵀ *ᵥ y) = y
        rw [Matrix.mulVec_mulVec, hd', Matrix.one_mulVec]
      right_inv := fun z => by
        show dᵀ *ᵥ (d *ᵥ z) = z
        rw [Matrix.mulVec_mulVec, hd, Matrix.one_mulVec] }
  add := fun x y => Matrix.mulVec_add _ x y

/-- a base of `H` extended by the identity on `β`. -/
def inlPerm (G : APerm H) : APerm (H ⊕ β) where
  π :=
    { toFun := fun y => Sum.elim (G.π (fun i => y (Sum.inl i))) (fun b => y (Sum.inr b))
      invFun := fun z => Sum.elim (G.π.symm (fun i => z (Sum.inl i))) (fun b => z (Sum.inr b))
      left_inv := fun y => by
        funext k
        cases k with
        | inl i => simp
        | inr b => simp
      right_inv := fun z => by
        funext k
        cases k with
        | inl i => simp
        | inr b => simp }
  add := fun x y => by
    funext k
    cases k with
    | inl i =>
      show G.π (fun i => (x + y) (Sum.inl i)) i
        = G.π (fun i => x (Sum.inl i)) i + G.π (fun i => y (Sum.inl i)) i
      have e : (fun i => (x + y) (Sum.inl i)) = (fun i => x (Sum.inl i)) + fun i => y (Sum.inl i) :=
        rfl
      rw [e, G.add]; rfl
    | inr b => rfl

/-- the base of `H ⊕ β` adapted to `d (U ⊕ ·)`. -/
def conjPerm (d : Matrix (H ⊕ β) (H ⊕ β) F) (hd : dᵀ * d = 1) (hd' : d * dᵀ = 1)
    (G : APerm H) : APerm (H ⊕ β) :=
  apComp (mvPerm d hd hd') (inlPerm G)

/-- the subspace named by the lifted label. -/
lemma insub_conj (d : Matrix (H ⊕ β) (H ⊕ β) F) (hd : dᵀ * d = 1) (hd' : d * dᵀ = 1)
    (G : APerm H) (s : Finset H) (q : Finset β) (y : Space (H ⊕ β)) :
    InSub (conjPerm d hd hd' G) (s.disjSum q) y ↔
      InSub G s (fun i => (dᵀ *ᵥ y) (Sum.inl i)) ∧ ∀ b, b ∉ q → (dᵀ *ᵥ y) (Sum.inr b) = 0 := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun b hb => ?_⟩
    · exact h (Sum.inl i) (fun hm => hi (Finset.inl_mem_disjSum.mp hm))
    · exact h (Sum.inr b) (fun hm => hb (Finset.inr_mem_disjSum.mp hm))
  · rintro ⟨h1, h2⟩ k hk
    cases k with
    | inl i => exact h1 i (fun hm => hk (Finset.inl_mem_disjSum.mpr hm))
    | inr b => exact h2 b (fun hm => hk (Finset.inr_mem_disjSum.mpr hm))

/-- **The stage-B frame map of the bridged geometry**: `U ↦ d (U ⊕ span q)`. -/
def BXMap.ofConj (d : Matrix (H ⊕ β) (H ⊕ β) F) (hd : dᵀ * d = 1) (hd' : d * dᵀ = 1)
    (q : Finset β) : BXMap H (H ⊕ β) where
  liftG := conjPerm d hd hd'
  liftS := fun s => s.disjSum q
  mono := fun h => Finset.disjSum_mono h (Finset.Subset.refl q)
  card := fun {s t} h => by
    have h' : s.disjSum q ⊆ t.disjSum q := Finset.disjSum_mono h (Finset.Subset.refl q)
    rw [Finset.card_sdiff_of_subset h', Finset.card_sdiff_of_subset h, Finset.card_disjSum,
      Finset.card_disjSum]
    omega
  sub := fun {G G' s s'} h y => by
    rw [insub_conj, insub_conj, h]

end
end
end PowerSaving.GF
end OAI

#print axioms OAI.PowerSaving.GF.insub_conj
#print axioms OAI.PowerSaving.GF.BXMap.ofConj
