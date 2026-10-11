import Work.GFrame.Engine.Over
import Work.BlockApply.Copies

/-!
# GFrame engine, part 10: generalised scratch certificates, copies and padding (agent key: eng-ram)

Analogue of `Work/BlockApply/Copies.lean` (`BCert`, `prod`, `sum`, `spare`, `copies`) for
generalised words:

* `GCert α e c`      `∃ w : GWord α ρ, Proper ∧ (∀ φ, w.costR φ = c φ) ∧ GLiveKernel e w`;
* `GCert.ofB`        every old certificate `BCert` is a `GCert` (same price);
* `GCert.ofRoute`    a certificate from a generalised route (`GRoute.liveKernel`);
* `GCert.prod`, `GCert.sum`, `GCert.copies`   `q` copies plus `p` spare roles: price
                     `q * c + p * (φ (m-1) + φ 1)` (spare roles use the old two-block kernel).
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving.GF
open Binary Matrix Finset RAM
noncomputable section

section
variable {α ρ σ ι : Type*}

lemma GWord.costR_flatMap (φ : ℕ → ℝ) (l : List ι) (g : ι → GWord α ρ) (x : ℝ)
    (h : ∀ i, GWord.costR φ (g i) = x) :
    GWord.costR φ (l.flatMap g) = (l.length : ℝ) * x := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.flatMap_cons, GWord.costR_append, ih, h, List.length_cons]
    push_cast
    ring

lemma GWord.proper_flatMap (u : ℕ) (l : List ι) (g : ι → GWord α ρ)
    (h : ∀ i, GWord.Proper u (g i)) : GWord.Proper u (l.flatMap g) := by
  intro mv hmv
  obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hmv
  exact h i mv hi

end

section
variable {α ρ σ ρ' σ' ι : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype ρ'] [DecidableEq ρ']

/-- A certificate moved along an embedding of the roles gives the kernel on the image of every
live slot, provided the image of every scratch role holds zero. -/
lemma GLiveKernel.over_live (em : ρ ↪ ρ') (e : σ → ρ) (p : GWord α ρ) (hw : GLiveKernel e p)
    (f : ℕ) (x : Data α ρ' f) (hx : ∀ s, (∀ l, e l ≠ s) → x (em s) = 0) (l : σ) :
    gwalk f (p.map (GMove.over em)) x (em (e l)) = matAct f (kernel α) (x (em (e l))) := by
  have h1 := congr_fun (gwalk_over em p f x) (e l)
  have h2 : gwalk f (p.map (GMove.over em)) x (em (e l)) = gwalk f p (x ∘ em) (e l) := h1
  rw [h2]
  exact hw f (x ∘ em) hx l

variable [Fintype ι] [DecidableEq ι]

/-- Copies of a generalised certificate, one after the other (as `RAM.walk_copies`). -/
theorem gwalk_copies (e : σ → ρ) (p : GWord α ρ) (hw : GLiveKernel e p)
    (l : List ι) (hl : l.Nodup) (f : ℕ) (x : Data α (ι × ρ) f)
    (hx : ∀ i ∈ l, ∀ s, (∀ t, e t ≠ s) → x (i, s) = 0) :
    (∀ i ∈ l, ∀ t, gwalk f (l.flatMap fun i => p.map (GMove.over (copyEmb ι ρ i))) x (i, e t)
        = matAct f (kernel α) (x (i, e t))) ∧
    (∀ i, i ∉ l → ∀ r, gwalk f (l.flatMap fun i => p.map (GMove.over (copyEmb ι ρ i))) x (i, r)
        = x (i, r)) := by
  induction l generalizing x with
  | nil =>
    refine ⟨fun i hi => absurd hi (by simp), fun i _ r => ?_⟩
    simp [gwalk]
  | cons i0 l ih =>
    have hnd := List.nodup_cons.mp hl
    rw [List.flatMap_cons]
    have hy_live : ∀ t, gwalk f (p.map (GMove.over (copyEmb ι ρ i0))) x (i0, e t)
        = matAct f (kernel α) (x (i0, e t)) := fun t =>
      GLiveKernel.over_live (copyEmb ι ρ i0) e p hw f x (hx i0 List.mem_cons_self) t
    have hy_out : ∀ j, j ≠ i0 → ∀ r, gwalk f (p.map (GMove.over (copyEmb ι ρ i0))) x (j, r)
        = x (j, r) := fun j hj r =>
      gwalk_out (copyEmb ι ρ i0) p f x (copyEmb_out i0 j hj r)
    have hne : ∀ i ∈ l, i ≠ i0 := fun i hi h => hnd.1 (h ▸ hi)
    obtain ⟨hA, hB⟩ := ih hnd.2 (gwalk f (p.map (GMove.over (copyEmb ι ρ i0))) x)
      (fun i hi s hs => by
        rw [hy_out i (hne i hi) s]
        exact hx i (List.mem_cons_of_mem _ hi) s hs)
    constructor
    · intro i hi t
      rw [gwalk_append]
      rcases List.mem_cons.mp hi with rfl | hi'
      · rw [hB i hnd.1 (e t), hy_live]
      · rw [hA i hi' t, hy_out i (hne i hi') (e t)]
    · intro i hi r
      have h1 : i ≠ i0 := fun h => hi (h ▸ List.mem_cons_self)
      have h2 : i ∉ l := fun h => hi (List.mem_cons_of_mem _ h)
      rw [gwalk_append, hB i h2 r, hy_out i h1 r]

end

section
variable (α : Type*) {ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

/-- **Generalised scratch certificate with exact price.** -/
def GCert (e : σ → ρ) (c : (ℕ → ℝ) → ℝ) : Prop :=
  ∃ w : GWord α ρ, w.Proper (Fintype.card α) ∧ (∀ φ, w.costR φ = c φ) ∧ GLiveKernel e w

end

namespace GCert
variable {α ρ σ ρ' σ' : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype ρ'] [DecidableEq ρ']

/-- Every old certificate is a generalised certificate, at the same price. -/
theorem ofB {e : σ → ρ} {c : (ℕ → ℝ) → ℝ} (h : BCert α e c) : GCert α e c := by
  obtain ⟨w, hP, hcost, hw⟩ := h
  exact ⟨GWord.ofB w, GWord.proper_ofB hP, fun φ => by rw [GWord.costR_ofB, hcost],
    GLiveKernel.ofB hw⟩

theorem cast {e : σ → ρ} {c c' : (ℕ → ℝ) → ℝ} (h : GCert α e c) (hc : ∀ φ, c φ = c' φ) :
    GCert α e c' := by
  obtain ⟨w, hP, hcost, hw⟩ := h
  exact ⟨w, hP, fun φ => (hcost φ).trans (hc φ), hw⟩

/-- A certificate from a generalised route (see `GRoute.liveKernel`). -/
theorem ofRoute (e : σ → ρ) (S S' T : ρ → CMat α) (hS : ∀ r, S r * S' r = 1)
    (g : (ρ→ℂ) → (ρ→ℂ)) (c : (ℕ → ℝ) → ℝ) (h : GRoute S T g c)
    (hg : ∀ x : ρ → ℂ, (∀ s, (∀ l, e l ≠ s) → x s = 0) → ∀ l, g x (e l) = x (e l))
    (hT : ∀ l, T (e l) = kernel α * S (e l)) : GCert α e c :=
  GRoute.liveKernel e S S' T hS g c h hg hT

/-- `ι` disjoint copies of a certificate; the scratch roles of every copy are scratch. -/
theorem prod (ι : Type*) [Fintype ι] [DecidableEq ι] {e : σ → ρ} {c : (ℕ → ℝ) → ℝ}
    (h : GCert α e c) :
    GCert α (Prod.map (id : ι → ι) e) (fun φ => (Fintype.card ι : ℝ) * c φ) := by
  obtain ⟨w, hP, hcost, hw⟩ := h
  refine ⟨(Finset.univ : Finset ι).toList.flatMap fun i => w.map (GMove.over (copyEmb ι ρ i)),
    ?_, ?_, ?_⟩
  · exact GWord.proper_flatMap _ _ _ (fun i => GWord.proper_over _ _ w hP)
  · intro φ
    rw [GWord.costR_flatMap φ _ _ (c φ) (fun i => by rw [GWord.costR_over]; exact hcost φ),
      Finset.length_toList, Finset.card_univ]
  · intro f v hv l
    obtain ⟨i, t⟩ := l
    have hx : ∀ i ∈ (Finset.univ : Finset ι).toList, ∀ s, (∀ t, e t ≠ s) → v (i, s) = 0 := by
      intro i _ s hs
      apply hv (i, s)
      rintro ⟨j, t⟩ heq
      exact hs t (congrArg Prod.snd heq)
    exact (gwalk_copies e w hw _ (Finset.nodup_toList _) f v hx).1 i (by simp) t

/-- Two certificates on disjoint role sets. -/
theorem sum {e₁ : σ → ρ} {e₂ : σ' → ρ'} {c₁ c₂ : (ℕ → ℝ) → ℝ}
    (h₁ : GCert α e₁ c₁) (h₂ : GCert α e₂ c₂) :
    GCert α (Sum.map e₁ e₂) (fun φ => c₁ φ + c₂ φ) := by
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
  refine ⟨w₁.map (GMove.over i₁) ++ w₂.map (GMove.over i₂), ?_, ?_, ?_⟩
  · exact (GWord.proper_over _ _ w₁ hP₁).append (GWord.proper_over _ _ w₂ hP₂)
  · intro φ
    rw [GWord.costR_append, GWord.costR_over, GWord.costR_over, hc₁, hc₂]
  · intro f v hv l
    rw [gwalk_append]
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
    have hy2 : ∀ r : ρ', gwalk f (w₁.map (GMove.over i₁)) v (i₂ r) = v (i₂ r) := fun r =>
      gwalk_out i₁ w₁ f v (out1 r)
    rcases l with t | t
    · change gwalk f (w₂.map (GMove.over i₂)) (gwalk f (w₁.map (GMove.over i₁)) v)
        (i₁ (e₁ t)) = matAct f (kernel α) (v (i₁ (e₁ t)))
      rw [gwalk_out i₂ w₂ f _ (out2 (e₁ t))]
      exact GLiveKernel.over_live i₁ e₁ w₁ hw₁ f v hs1 t
    · change gwalk f (w₂.map (GMove.over i₂)) (gwalk f (w₁.map (GMove.over i₁)) v)
        (i₂ (e₂ t)) = matAct f (kernel α) (v (i₂ (e₂ t)))
      rw [GLiveKernel.over_live i₂ e₂ w₂ hw₂ f _
        (fun s hs => by rw [hy2 s]; exact hs2 s hs) t, hy2]

/-- **`q` copies plus `p` spare roles.**  Price: `q * c + p * (φ (m-1) + φ 1)`. -/
theorem copies (q p : ℕ) (hm : 2 ≤ Fintype.card α) {e : σ → ρ} {c : (ℕ → ℝ) → ℝ}
    (h : GCert α e c) :
    GCert α (Sum.map (Prod.map (id : Fin q → Fin q) e) (id : Fin p → Fin p))
      (fun φ => (q : ℝ) * c φ + (p : ℝ) * (φ (Fintype.card α - 1) + φ 1)) := by
  refine ((h.prod (Fin q)).sum (GCert.ofB (BCert.spare (α:=α) (Fin p) hm))).cast (fun φ => ?_)
  simp only [Fintype.card_fin]

end GCert
end
end PowerSaving.GF
end OAI

#print axioms OAI.PowerSaving.GF.gwalk_copies
#print axioms OAI.PowerSaving.GF.GCert.ofB
#print axioms OAI.PowerSaving.GF.GCert.copies
