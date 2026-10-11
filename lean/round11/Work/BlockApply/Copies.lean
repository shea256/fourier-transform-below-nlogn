import Work.BlockApply.Exact

/-!
# Copies and padding for an ARBITRARY block scratch certificate (agent key: block-apply)

The engine needs `2^a` live slots.  A network with `W` live roles is usually padded once with
`2^a - W` spare roles; under whole-block accounting a spare role costs `((m-1)/m)^z + (1/m)^z`,
slightly more than one full role, so a badly filled table wastes saving.  Running `q` disjoint
copies of the network in one table and padding only the remainder fixes that.

This file proves the construction once, for any role type and any block word:

* `BCert α e c`        a scratch certificate in block form with exact price `c`
                       (`∃ w, Proper ∧ (∀ φ, w.costR φ = c φ) ∧ LiveKernel e w.flat`);
* `BCert.prod`         `ι` disjoint copies: price `card ι * c`;
* `BCert.sum`          two certificates side by side: price `c₁ + c₂`;
* `BCert.spare`        the trivial certificate on any role type `τ`: every role is live and
                       gets the kernel as blocks of ranks `m-1` and `1`;
* `BCert.copies`       `q` copies plus `p` spare roles: price `q * c + p * (φ (m-1) + φ 1)`;
* `engine_program_bcert`  the block engine fed with a `BCert` whose price is the price of a
                       block list that satisfies the strict moment inequality.

Scratch roles stay scratch: a copy's scratch roles are zero when its word starts because the
words of the other copies do not touch them (`walk_out`).  No network is constructed here.
(The full-contract, unit-move analogue is checks/wht4/quick-wins/CopiesCertificate.lean.)
No `sorry`.
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving.Binary
open Matrix Finset
noncomputable section
section
variable {α ρ σ ι : Type*}

lemma BWord.flat_flatMap (l : List ι) (g : ι → BWord α ρ) :
    BWord.flat (l.flatMap g) = l.flatMap (fun i => (g i).flat) := by
  induction l with
  | nil => rfl
  | cons i l ih => rw [List.flatMap_cons, BWord.flat_append, ih, List.flatMap_cons]

lemma BWord.costR_flatMap (φ : ℕ → ℝ) (l : List ι) (g : ι → BWord α ρ) (x : ℝ)
    (h : ∀ i, BWord.costR φ (g i) = x) :
    BWord.costR φ (l.flatMap g) = (l.length : ℝ) * x := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.flatMap_cons, BWord.costR_append, ih, h, List.length_cons]
    push_cast
    ring

lemma BWord.proper_flatMap (u : ℕ) (l : List ι) (g : ι → BWord α ρ)
    (h : ∀ i, BWord.Proper u (g i)) : BWord.Proper u (l.flatMap g) := by
  intro mv hmv
  obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hmv
  exact h i mv hi

end
end
end PowerSaving.Binary

namespace PowerSaving.RAM
open Binary Matrix Finset
noncomputable section
section
variable {α ρ σ ρ' σ' ι : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype ρ'] [DecidableEq ρ']

/-- A scratch certificate moved along an embedding of the roles gives the kernel on the image
of every live slot, provided the image of every scratch role holds zero. -/
lemma LiveKernel.over_live (em : ρ ↪ ρ') (e : σ → ρ) (p : PWord α ρ) (hw : LiveKernel e p)
    (f : ℕ) (x : Data α ρ' f) (hx : ∀ s, (∀ l, e l ≠ s) → x (em s) = 0) (l : σ) :
    walk f (p.map (Move.over em)) x (em (e l)) = matAct f (kernel α) (x (em (e l))) := by
  have h1 := congr_fun (walk_over em p f x) (e l)
  have h2 : walk f (p.map (Move.over em)) x (em (e l)) = walk f p (x ∘ em) (e l) := h1
  rw [h2]
  exact hw f (x ∘ em) hx l

/-- The embedding of the `i`-th copy. -/
def copyEmb (ι : Type*) (ρ : Type*) (i : ι) : ρ ↪ ι × ρ :=
  ⟨fun r => (i, r), fun _ _ hab => (Prod.mk.inj hab).2⟩

lemma copyEmb_out (i j : ι) (hij : j ≠ i) (r : ρ) : ((j, r) : ι × ρ) ∉ covered (copyEmb ι ρ i) := by
  intro h
  obtain ⟨a, ha⟩ := (cover_iff _ _).mp h
  exact hij (Prod.mk.inj ha).1.symm

variable [Fintype ι] [DecidableEq ι]

/-- **Copies of a scratch certificate, one after the other.**  If the scratch roles of the
copies in the list `l` hold zero, the word of those copies gives the kernel on their live
roles and leaves every role of the other copies untouched. -/
theorem walk_copies (e : σ → ρ) (p : PWord α ρ) (hw : LiveKernel e p)
    (l : List ι) (hl : l.Nodup) (f : ℕ) (x : Data α (ι × ρ) f)
    (hx : ∀ i ∈ l, ∀ s, (∀ t, e t ≠ s) → x (i, s) = 0) :
    (∀ i ∈ l, ∀ t, walk f (l.flatMap fun i => p.map (Move.over (copyEmb ι ρ i))) x (i, e t)
        = matAct f (kernel α) (x (i, e t))) ∧
    (∀ i, i ∉ l → ∀ r, walk f (l.flatMap fun i => p.map (Move.over (copyEmb ι ρ i))) x (i, r)
        = x (i, r)) := by
  induction l generalizing x with
  | nil =>
    refine ⟨fun i hi => absurd hi (by simp), fun i _ r => ?_⟩
    simp [walk]
  | cons i0 l ih =>
    have hnd := List.nodup_cons.mp hl
    rw [List.flatMap_cons]
    have hy_live : ∀ t, walk f (p.map (Move.over (copyEmb ι ρ i0))) x (i0, e t)
        = matAct f (kernel α) (x (i0, e t)) := fun t =>
      LiveKernel.over_live (copyEmb ι ρ i0) e p hw f x (hx i0 List.mem_cons_self) t
    have hy_out : ∀ j, j ≠ i0 → ∀ r, walk f (p.map (Move.over (copyEmb ι ρ i0))) x (j, r)
        = x (j, r) := fun j hj r =>
      walk_out (copyEmb ι ρ i0) p f x (copyEmb_out i0 j hj r)
    have hne : ∀ i ∈ l, i ≠ i0 := fun i hi h => hnd.1 (h ▸ hi)
    obtain ⟨hA, hB⟩ := ih hnd.2 (walk f (p.map (Move.over (copyEmb ι ρ i0))) x)
      (fun i hi s hs => by
        rw [hy_out i (hne i hi) s]
        exact hx i (List.mem_cons_of_mem _ hi) s hs)
    constructor
    · intro i hi t
      rw [walk_append]
      rcases List.mem_cons.mp hi with rfl | hi'
      · rw [hB i hnd.1 (e t), hy_live]
      · rw [hA i hi' t, hy_out i (hne i hi') (e t)]
    · intro i hi r
      have h1 : i ≠ i0 := fun h => hi (h ▸ List.mem_cons_self)
      have h2 : i ∉ l := fun h => hi (List.mem_cons_of_mem _ h)
      rw [walk_append, hB i h2 r, hy_out i h1 r]

end

section
variable (α : Type*) {ρ σ ρ' σ' : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype ρ'] [DecidableEq ρ']

/-- **Block scratch certificate with exact price**: a proper block word on the roles `ρ` that
gives the kernel on the live roles `e l` whenever the scratch roles (those outside the range
of `e`) start at zero, and whose price is `c φ` for every price list `φ`. -/
def BCert (e : σ → ρ) (c : (ℕ → ℝ) → ℝ) : Prop :=
  ∃ w : BWord α ρ, w.Proper (Fintype.card α) ∧ (∀ φ, w.costR φ = c φ) ∧ LiveKernel e w.flat

end

namespace BCert
variable {α ρ σ ρ' σ' : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype ρ'] [DecidableEq ρ']

theorem cast {e : σ → ρ} {c c' : (ℕ → ℝ) → ℝ} (h : BCert α e c) (hc : ∀ φ, c φ = c' φ) :
    BCert α e c' := by
  obtain ⟨w, hP, hcost, hw⟩ := h
  exact ⟨w, hP, fun φ => (hcost φ).trans (hc φ), hw⟩

/-- `ι` disjoint copies of a certificate; the scratch roles of every copy are scratch. -/
theorem prod (ι : Type*) [Fintype ι] [DecidableEq ι] {e : σ → ρ} {c : (ℕ → ℝ) → ℝ}
    (h : BCert α e c) :
    BCert α (Prod.map (id : ι → ι) e) (fun φ => (Fintype.card ι : ℝ) * c φ) := by
  obtain ⟨w, hP, hcost, hw⟩ := h
  refine ⟨(Finset.univ : Finset ι).toList.flatMap fun i => w.map (BMove.over (copyEmb ι ρ i)),
    ?_, ?_, ?_⟩
  · exact BWord.proper_flatMap _ _ _ (fun i => BWord.proper_over _ _ w hP)
  · intro φ
    rw [BWord.costR_flatMap φ _ _ (c φ) (fun i => by rw [BWord.costR_over]; exact hcost φ),
      Finset.length_toList, Finset.card_univ]
  · rw [BWord.flat_flatMap]
    have hfl : (fun i => BWord.flat (w.map (BMove.over (copyEmb ι ρ i))))
        = fun i => w.flat.map (Move.over (copyEmb ι ρ i)) := by
      funext i; exact BWord.flat_over _ w
    rw [hfl]
    intro f v hv l
    obtain ⟨i, t⟩ := l
    have hx : ∀ i ∈ (Finset.univ : Finset ι).toList, ∀ s, (∀ t, e t ≠ s) → v (i, s) = 0 := by
      intro i _ s hs
      apply hv (i, s)
      rintro ⟨j, t⟩ heq
      exact hs t (congrArg Prod.snd heq)
    exact (walk_copies e w.flat hw _ (Finset.nodup_toList _) f v hx).1 i (by simp) t

/-- Two certificates on disjoint role sets. -/
theorem sum {e₁ : σ → ρ} {e₂ : σ' → ρ'} {c₁ c₂ : (ℕ → ℝ) → ℝ}
    (h₁ : BCert α e₁ c₁) (h₂ : BCert α e₂ c₂) :
    BCert α (Sum.map e₁ e₂) (fun φ => c₁ φ + c₂ φ) := by
  obtain ⟨w₁, hP₁, hc₁, hw₁⟩ := h₁
  obtain ⟨w₂, hP₂, hc₂, hw₂⟩ := h₂
  let i₁ : ρ ↪ ρ ⊕ ρ' := Function.Embedding.inl
  let i₂ : ρ' ↪ ρ ⊕ ρ' := Function.Embedding.inr
  have out1 : ∀ r : ρ', i₂ r ∉ covered i₁ := by
    intro r h
    obtain ⟨b, hb⟩ := (cover_iff _ _).mp h
    cases hb
  have out2 : ∀ r : ρ, i₁ r ∉ covered i₂ := by
    intro r h
    obtain ⟨b, hb⟩ := (cover_iff _ _).mp h
    cases hb
  refine ⟨w₁.map (BMove.over i₁) ++ w₂.map (BMove.over i₂), ?_, ?_, ?_⟩
  · exact (BWord.proper_over _ _ w₁ hP₁).append (BWord.proper_over _ _ w₂ hP₂)
  · intro φ
    rw [BWord.costR_append, BWord.costR_over, BWord.costR_over, hc₁, hc₂]
  · rw [BWord.flat_append, BWord.flat_over, BWord.flat_over]
    intro f v hv l
    rw [walk_append]
    have hs1 : ∀ s, (∀ t, e₁ t ≠ s) → v (i₁ s) = 0 := by
      intro s hs
      apply hv (Sum.inl s)
      rintro (t|t) heq
      · exact hs t (Sum.inl_injective heq)
      · cases heq
    have hs2 : ∀ s, (∀ t, e₂ t ≠ s) → v (i₂ s) = 0 := by
      intro s hs
      apply hv (Sum.inr s)
      rintro (t|t) heq
      · cases heq
      · exact hs t (Sum.inr_injective heq)
    have hy2 : ∀ r : ρ', walk f (w₁.flat.map (Move.over i₁)) v (i₂ r) = v (i₂ r) := fun r =>
      walk_out i₁ w₁.flat f v (out1 r)
    rcases l with t | t
    · change walk f (w₂.flat.map (Move.over i₂)) (walk f (w₁.flat.map (Move.over i₁)) v)
        (i₁ (e₁ t)) = matAct f (kernel α) (v (i₁ (e₁ t)))
      rw [walk_out i₂ w₂.flat f _ (out2 (e₁ t))]
      exact LiveKernel.over_live i₁ e₁ w₁.flat hw₁ f v hs1 t
    · change walk f (w₂.flat.map (Move.over i₂)) (walk f (w₁.flat.map (Move.over i₁)) v)
        (i₂ (e₂ t)) = matAct f (kernel α) (v (i₂ (e₂ t)))
      rw [LiveKernel.over_live i₂ e₂ w₂.flat hw₂ f _
        (fun s hs => by rw [hy2 s]; exact hs2 s hs) t, hy2]

/-- **Spare roles**: on any role type every role can simply be given the kernel, as two blocks
of ranks `m-1` and `1` per role (`m = card α`).  All roles are live. -/
theorem spare (τ : Type*) [Fintype τ] [DecidableEq τ] (hm : 2 ≤ Fintype.card α) :
    BCert α (id : τ → τ)
      (fun φ => (Fintype.card τ : ℝ) * (φ (Fintype.card α - 1) + φ 1)) := by
  obtain ⟨w, hP, hcost, hw⟩ := XPath.reframe hm (fun _ : τ => OBase.canonical α)
    (fun _ => (∅ : Finset α)) (fun _ => (Finset.univ : Finset α))
  refine ⟨w, hP, fun φ => ?_, LiveKernel.of_full w.flat (fun f v => ?_)⟩
  · rw [hcost]
    have hne : Fintype.card α ≠ 0 := by omega
    simp only [Finset.empty_sdiff, Finset.sdiff_empty, Finset.card_empty, Finset.card_univ,
      splitCost_zero, splitCost_full φ hne, zero_add, Finset.sum_const, nsmul_eq_mul]
  · have h := hw f v
    have h1 : multiAct f (fun _ : τ => frame (OBase.canonical α) (∅ : Finset α)) v = v := by
      funext r
      simp [multiAct]
    have h2 : (fun _ : τ => frame (OBase.canonical α) (Finset.univ : Finset α))
        = fun _ => kernel α := by
      funext r
      exact frame_univ _
    rw [h1, h2] at h
    exact h

/-- **`q` copies plus `p` spare roles.**  Live slots: the live slots of every copy and all
spare roles.  Price: `q` times the price of one copy plus `p` times `φ (m-1) + φ 1`. -/
theorem copies (q p : ℕ) (hm : 2 ≤ Fintype.card α) {e : σ → ρ} {c : (ℕ → ℝ) → ℝ}
    (h : BCert α e c) :
    BCert α (Sum.map (Prod.map (id : Fin q → Fin q) e) (id : Fin p → Fin p))
      (fun φ => (q : ℝ) * c φ + (p : ℝ) * (φ (Fintype.card α - 1) + φ 1)) := by
  refine ((h.prod (Fin q)).sum (BCert.spare (α:=α) (Fin p) hm)).cast (fun φ => ?_)
  simp only [Fintype.card_fin]

end BCert
end

universe U

/-- **The block engine fed with a `BCert`** whose price is the price of a block list `L` that
satisfies the strict moment inequality.  Conclusion: upstream's `hills_program` statement with
envelope `⌈(k+1)^z⌉`. -/
theorem engine_program_bcert {α ρ σ : Type} [Fintype α] [DecidableEq α] [Fintype ρ]
    [DecidableEq ρ] [Fintype σ] [DecidableEq σ]
    (u a : ℕ) (hα : Fintype.card α = u) (hσ : Fintype.card σ = 2^a) (hu : 3 ≤ u)
    (e : σ → ρ) (he : Function.Injective e)
    (c : (ℕ → ℝ) → ℝ) (h : BCert α e c)
    (L : List (ℕ × ℕ)) (hL : ∀ φ : ℕ → ℝ, c φ = listCost φ L)
    (z : ℝ) (hz : 0 ≤ z)
    (hmom : BlockAccounting.moment u z L < (2:ℝ)^a)
    (cl : Paint) (m : Bool) {ι : Type U} (k : ι→ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*envelope z (k i)) := by
  obtain ⟨w, hP, hcost, hw⟩ := h
  rw [hα] at hP
  exact engine_program_xcert u a hα hσ hu e he w hw hP L (fun φ => (hcost φ).trans (hL φ))
    z hz hmom cl m k v

end PowerSaving.RAM
end OAI

#print axioms OAI.PowerSaving.RAM.walk_copies
#print axioms OAI.PowerSaving.RAM.BCert.prod
#print axioms OAI.PowerSaving.RAM.BCert.sum
#print axioms OAI.PowerSaving.RAM.BCert.spare
#print axioms OAI.PowerSaving.RAM.BCert.copies
#print axioms OAI.PowerSaving.RAM.engine_program_bcert
