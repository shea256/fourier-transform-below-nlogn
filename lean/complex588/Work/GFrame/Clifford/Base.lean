import Work.GFrame.Clifford.Old

/-!
# GFrame / Clifford, part 10 (STAGE B): every nested pair has a common base; THE FRAME LEMMA

(agent key: eng-clifford)

* `subOf G s`            the subspace named by `(G, s)` as a `Submodule`;
* `exists_flag_base`     for ANY subspaces `U ≤ V` of the label space there is ONE base `G₀` and
                         coordinate sets `s₀ ⊆ t₀` naming both (so every subspace has a
                         representative: `exists_rep`);
* `frame_lemma`          **for any two representatives of nested subspaces `U ⊆ V`**
                         `core G' t = A * blockMat z * B * core G s` with `A`, `B` free and `z` of
                         rank `dim V - dim U`: ONE block.  Degenerate, isotropic and alternating
                         cases are all covered; no hypothesis on the dot product is used.
No `sorry`.
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving.GF
open Binary Matrix Finset Complex Module
noncomputable section
section
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- the subspace named by `(G, s)`. -/
def subOf (G : APerm α) (s : Finset α) : Submodule F (Space α) where
  carrier := {x | InSub G s x}
  add_mem' := fun ha hb => insub_add G s ha hb
  zero_mem' := by
    intro k _
    rw [G.map_zero']; rfl
  smul_mem' := by
    intro c x hx k hk
    rw [G.map_smul', Pi.smul_apply, hx k hk, smul_zero]

@[simp] lemma mem_subOf (G : APerm α) (s : Finset α) (x : Space α) :
    x ∈ subOf G s ↔ InSub G s x := Iff.rfl

/-- **A base adapted to a nested pair of subspaces.** -/
theorem exists_flag_base (U V : Submodule F (Space α)) (hUV : U ≤ V) :
    ∃ (G₀ : APerm α) (s₀ t₀ : Finset α), s₀ ⊆ t₀ ∧ (∀ x, InSub G₀ s₀ x ↔ x ∈ U) ∧
      (∀ x, InSub G₀ t₀ x ↔ x ∈ V) := by
  classical
  obtain ⟨bU, hbU, -, hUspan, hbUli⟩ :=
    exists_linearIndepOn_id_extension (K := F) (linearIndependent_empty F (Space α))
      (Set.empty_subset (U : Set (Space α)))
  obtain ⟨bV, hbV, hUbV, hVspan, hbVli⟩ :=
    exists_linearIndepOn_id_extension hbUli (hbU.trans hUV : bU ⊆ (V : Set (Space α)))
  obtain ⟨b, -, hVb, hspan, hbli⟩ :=
    exists_linearIndepOn_id_extension hbVli (Set.subset_univ bV)
  haveI : Fintype b := Fintype.ofFinite b
  have hli : LinearIndependent F (fun x : b => (x : Space α)) := hbli
  have hsp : ⊤ ≤ Submodule.span F (Set.range (fun x : b => (x : Space α))) := by
    rw [Subtype.range_coe]
    exact fun x _ => hspan (Set.mem_univ x)
  let B0 : Basis b F (Space α) := Basis.mk hli hsp
  have hcard : Fintype.card b = Fintype.card α := by
    rw [← Module.finrank_eq_card_basis B0, Module.finrank_fintype_fun_eq_card]
  let e : b ≃ α := Fintype.equivOfCardEq hcard
  let B : Basis α F (Space α) := B0.reindex e
  have hB : ∀ k, B k = ((e.symm k : b) : Space α) := by
    intro k
    simp [B, B0]
  have key : ∀ c : Set (Space α), c ⊆ b → ∀ x,
      x ∈ Submodule.span F c ↔ ∀ k, ((e.symm k : b) : Space α) ∉ c → B.repr x k = 0 := by
    intro c hc x
    have himg : B '' {k | ((e.symm k : b) : Space α) ∈ c} = c := by
      ext y
      constructor
      · rintro ⟨k, hk, rfl⟩
        rw [hB]; exact hk
      · intro hy
        refine ⟨e ⟨y, hc hy⟩, ?_, ?_⟩
        · simp [hy]
        · rw [hB]; simp
    have hmem : x ∈ Submodule.span F c ↔
        ↑(B.repr x).support ⊆ {k | ((e.symm k : b) : Space α) ∈ c} := by
      conv_lhs => rw [← himg]
      exact Basis.mem_span_image B
    rw [hmem]
    constructor
    · intro h k hk
      by_contra hne
      exact hk (h (Finsupp.mem_support_iff.mpr hne))
    · intro h k hk
      by_contra hkc
      exact (Finsupp.mem_support_iff.mp hk) (h k hkc)
  have hUeq : Submodule.span F bU = U :=
    le_antisymm (Submodule.span_le.mpr hbU) hUspan
  have hVeq : Submodule.span F bV = V :=
    le_antisymm (Submodule.span_le.mpr hbV) hVspan
  let G₀ : APerm α := ⟨B.equivFun.toEquiv, fun x y => map_add B.equivFun x y⟩
  have hG : ∀ x k, G₀.π x k = B.repr x k := fun x k => by
    show B.equivFun x k = B.repr x k
    rw [Basis.equivFun_apply]
  refine ⟨G₀, univ.filter (fun k => ((e.symm k : b) : Space α) ∈ bU),
    univ.filter (fun k => ((e.symm k : b) : Space α) ∈ bV), ?_, ?_, ?_⟩
  · intro k hk
    rw [Finset.mem_filter] at hk ⊢
    exact ⟨hk.1, hUbV hk.2⟩
  · intro x
    rw [← hUeq, key bU (hUbV.trans hVb) x]
    unfold InSub
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hG]
  · intro x
    rw [← hVeq, key bV hVb x]
    unfold InSub
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hG]

/-- every subspace of the label space has a representative. -/
theorem exists_rep (U : Submodule F (Space α)) :
    ∃ (G : APerm α) (s : Finset α), ∀ x, InSub G s x ↔ x ∈ U := by
  obtain ⟨G, s, _, _, h, _⟩ := exists_flag_base U U le_rfl
  exact ⟨G, s, h⟩

theorem exists_common_base (G G' : APerm α) (s t : Finset α)
    (h : ∀ x, InSub G s x → InSub G' t x) :
    ∃ (G₀ : APerm α) (s₀ t₀ : Finset α), s₀ ⊆ t₀ ∧ (∀ x, InSub G s x ↔ InSub G₀ s₀ x) ∧
      (∀ x, InSub G₀ t₀ x ↔ InSub G' t x) := by
  obtain ⟨G₀, s₀, t₀, hst, hU, hV⟩ :=
    exists_flag_base (subOf G s) (subOf G' t) (fun x hx => h x hx)
  exact ⟨G₀, s₀, t₀, hst, fun x => (hU x).symm, fun x => hV x⟩

/-- **THE FRAME LEMMA** (arbitrary nested subspaces, arbitrary representatives): the transition
is ONE block of rank `dim V - dim U` between free adapters. -/
theorem frame_lemma (G G' : APerm α) (s t : Finset α)
    (h : ∀ x, InSub G s x → InSub G' t x) :
    ∃ (A B : CMat α) (z : Fin (t.card - s.card) → Space α), Free A ∧ Free B ∧
      LinearIndependent F z ∧ core G' t = A * blockMat z * B * core G s := by
  obtain ⟨G₀, s₀, t₀, hst, h1, h2⟩ := exists_common_base G G' s t h
  have key : ∀ r, (t₀ \ s₀).card = r → ∃ (A B : CMat α) (z : Fin r → Space α), Free A ∧
      Free B ∧ LinearIndependent F z ∧ core G' t = A * blockMat z * B * core G s := by
    intro r hr
    subst hr
    exact climb_any G G' G₀ s t s₀ t₀ h1 h2 hst
  exact key _ (climb_rank h1 h2 hst)

/-- nested subspaces have ordered dimensions. -/
theorem card_le_of_sub {G G' : APerm α} {s t : Finset α}
    (h : ∀ x, InSub G s x → InSub G' t x) : s.card ≤ t.card := by
  obtain ⟨G₀, s₀, t₀, hst, h1, h2⟩ := exists_common_base G G' s t h
  rw [same_card h1, ← same_card h2]
  exact Finset.card_le_card hst

end
end
end PowerSaving.GF
end OAI

#print axioms OAI.PowerSaving.GF.exists_flag_base
#print axioms OAI.PowerSaving.GF.exists_rep
#print axioms OAI.PowerSaving.GF.frame_lemma
#print axioms OAI.PowerSaving.GF.card_le_of_sub
