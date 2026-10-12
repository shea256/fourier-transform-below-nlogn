import Work.GFrame.Clifford.Cross

/-!
# GFrame / Clifford, part 13 (STAGE B): ANY two subspaces are ONE child

(agent key: eng-clifford)

* `exists_base_of_basis`  a basis of the label space (as a set) gives a base `G₀` in which the
                          span of every subset of the basis is a coordinate subspace;
* `exists_pair_base`      ANY two subspaces `U`, `V` are named by ONE base;
* `cross_lemma`           **for arbitrary representatives of ANY two subspaces** the transition is
                          ONE block of rank `r = dim U + dim V - 2 dim (U ∩ V)` between free
                          adapters (the outside note's rank formula `d(L_U, L_V)`).
No `sorry`.
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving.GF
open Binary Matrix Finset Complex Module
noncomputable section
section
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem exists_base_of_basis (b : Set (Space α)) (hbli : LinearIndepOn F id b)
    (hspan : (Set.univ : Set (Space α)) ⊆ Submodule.span F b) :
    ∃ (G₀ : APerm α) (f : Set (Space α) → Finset α),
      ∀ c, c ⊆ b → ∀ x, InSub G₀ (f c) x ↔ x ∈ Submodule.span F c := by
  classical
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
  let G₀ : APerm α := ⟨B.equivFun.toEquiv, fun x y => map_add B.equivFun x y⟩
  have hG : ∀ x k, G₀.π x k = B.repr x k := fun x k => by
    show B.equivFun x k = B.repr x k
    rw [Basis.equivFun_apply]
  refine ⟨G₀, fun c => univ.filter (fun k => ((e.symm k : b) : Space α) ∈ c), ?_⟩
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
  unfold InSub
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hG]
  constructor
  · intro h k hk
    by_contra hkc
    exact (Finsupp.mem_support_iff.mp hk) (h k hkc)
  · intro h k hk
    by_contra hne
    exact hk (h (Finsupp.mem_support_iff.mpr hne))

/-- **Any two subspaces are named by one base.** -/
theorem exists_pair_base (U V : Submodule F (Space α)) :
    ∃ (G₀ : APerm α) (s₀ t₀ : Finset α), (∀ x, InSub G₀ s₀ x ↔ x ∈ U) ∧
      (∀ x, InSub G₀ t₀ x ↔ x ∈ V) := by
  classical
  obtain ⟨bI, hbI, -, hIspan, hbIli⟩ :=
    exists_linearIndepOn_id_extension (K := F) (linearIndependent_empty F (Space α))
      (Set.empty_subset ((U ⊓ V : Submodule F (Space α)) : Set (Space α)))
  have hIU : bI ⊆ (U : Set (Space α)) := fun x hx => (Submodule.mem_inf.mp (hbI hx)).1
  have hIV : bI ⊆ (V : Set (Space α)) := fun x hx => (Submodule.mem_inf.mp (hbI hx)).2
  obtain ⟨bU, hbU, hIbU, hUspan, hbUli⟩ := exists_linearIndepOn_id_extension hbIli hIU
  obtain ⟨bV, hbV, hIbV, hVspan, hbVli⟩ := exists_linearIndepOn_id_extension hbIli hIV
  have hsplit : bI ∪ (bV \ bI) = bV := Set.union_diff_cancel hIbV
  have hd2 : Disjoint (Submodule.span F bI) (Submodule.span F (bV \ bI)) := by
    have h := (linearIndepOn_union_iff (R := F) (v := id)
      (Set.disjoint_sdiff_right (s := bI) (t := bV))).mp (by rw [hsplit]; exact hbVli)
    simpa using h.2.2
  have hdj : Disjoint (Submodule.span F bU) (Submodule.span F (bV \ bI)) := by
    rw [Submodule.disjoint_def]
    intro x hxU hxV
    have hxU' : x ∈ U := Submodule.span_le.mpr hbU hxU
    have hxV' : x ∈ V := Submodule.span_le.mpr hbV (Submodule.span_mono Set.diff_subset hxV)
    have hxI : x ∈ Submodule.span F bI := hIspan (Submodule.mem_inf.mpr ⟨hxU', hxV'⟩)
    exact Submodule.disjoint_def.mp hd2 x hxI hxV
  have hli : LinearIndepOn F id (bU ∪ (bV \ bI)) :=
    hbUli.id_union (hbVli.mono Set.diff_subset) hdj
  obtain ⟨b, -, hsub, hspan, hbli⟩ := exists_linearIndepOn_id_extension hli (Set.subset_univ _)
  obtain ⟨G₀, f, hf⟩ := exists_base_of_basis b hbli hspan
  have hUb : bU ⊆ b := Set.subset_union_left.trans hsub
  have hVb : bV ⊆ b := by
    rw [← hsplit]
    exact Set.union_subset (hIbU.trans hUb) (Set.subset_union_right.trans hsub)
  refine ⟨G₀, f bU, f bV, fun x => ?_, fun x => ?_⟩
  · rw [hf bU hUb x, le_antisymm (Submodule.span_le.mpr hbU) hUspan]
  · rw [hf bV hVb x, le_antisymm (Submodule.span_le.mpr hbV) hVspan]

lemma insub_inter (G : APerm α) (s t : Finset α) (x : Space α) :
    InSub G (s ∩ t) x ↔ InSub G s x ∧ InSub G t x := by
  constructor
  · intro h
    exact ⟨fun k hk => h k (fun hm => hk (Finset.mem_inter.mp hm).1),
      fun k hk => h k (fun hm => hk (Finset.mem_inter.mp hm).2)⟩
  · rintro ⟨h1, h2⟩ k hk
    by_cases hs : k ∈ s
    · exact h2 k (fun ht => hk (Finset.mem_inter.mpr ⟨hs, ht⟩))
    · exact h1 k hs

/-- **ANY two subspaces, ANY representatives: ONE child.**  `2^d` is the number of points of
`U ∩ V`, and the rank is `r = dim U + dim V - 2d`. -/
theorem cross_lemma (G G' : APerm α) (s t : Finset α) :
    ∃ (d r : ℕ) (A B : CMat α) (z : Fin r → Space α),
      Fintype.card {x // InSub G s x ∧ InSub G' t x} = 2 ^ d ∧ r + 2 * d = s.card + t.card ∧
      Free A ∧ Free B ∧ LinearIndependent F z ∧ core G' t = A * blockMat z * B * core G s := by
  obtain ⟨G₀, s₀, t₀, hU, hV⟩ := exists_pair_base (subOf G s) (subOf G' t)
  have h1 : ∀ x, InSub G s x ↔ InSub G₀ s₀ x := fun x => (hU x).symm
  have h2 : ∀ x, InSub G₀ t₀ x ↔ InSub G' t x := fun x => hV x
  obtain ⟨A, B, z, hA, hB, hz, e⟩ := cross_any G G' G₀ s t s₀ t₀ h1 h2
  refine ⟨(s₀ ∩ t₀).card, _, A, B, z, ?_, ?_, hA, hB, hz, e⟩
  · rw [← insub_card G₀ (s₀ ∩ t₀)]
    apply Fintype.card_congr
    apply Equiv.subtypeEquivRight
    intro x
    rw [insub_inter, ← h1 x, h2 x]
  · have c1 := Finset.card_sdiff_add_card_inter s₀ t₀
    have c2 := Finset.card_sdiff_add_card_inter t₀ s₀
    have c3 : ((s₀ \ t₀) ∪ (t₀ \ s₀)).card = (s₀ \ t₀).card + (t₀ \ s₀).card :=
      Finset.card_union_of_disjoint disjoint_sdiff_sdiff
    rw [Finset.inter_comm t₀ s₀] at c2
    rw [c3, same_card h1, ← same_card h2]
    omega

end
end
end PowerSaving.GF
end OAI

#print axioms OAI.PowerSaving.GF.exists_pair_base
#print axioms OAI.PowerSaving.GF.cross_lemma
