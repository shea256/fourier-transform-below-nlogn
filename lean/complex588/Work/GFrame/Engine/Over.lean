import Work.GFrame.Engine.Route

/-!
# GFrame engine, part 9: re-indexing roles; routes on disjoint sets of roles (agent key: eng-ram)

* `GMove.over e`, `gwalk_over`, `gwalk_out`   a word moved along an embedding of the roles (as
                     upstream `Move.over`, `walk_over`, `walk_out`);
* `GRoute.lift`      re-index a route on a sub-network of roles (as `XRoute.lift`);
* `GRoute.parallel`  compose routes on disjoint sets of roles; costs add (as `XRoute.parallel`).
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving.GF
open Binary Matrix Finset RAM
noncomputable section
section
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]

/-- Re-index the roles of a letter through an embedding. -/
def GMove.over (e : ρ ↪ σ) : GMove α ρ → GMove α σ
  | .old mv => .old (mv.over e)
  | .perm l G => .perm (e l) G
  | .phase l z c => .phase (e l) z c

lemma GMove.act_over (e : ρ ↪ σ) (mv : GMove α ρ) (f : ℕ) (x : Data α σ f) :
    ((mv.over e).act f x) ∘ e = mv.act f (x ∘ e) := by
  cases mv with
  | old mv =>
    change (mv.over e).act f x ∘ e = mv.act f (x ∘ e)
    rw [← walk_flat_move, ← walk_flat_move, BMove.flat_over]
    exact walk_over e mv.flat f x
  | perm l G => funext i; simp [GMove.over, GMove.act, Function.comp, roleAct]
  | phase l z c => funext i; simp [GMove.over, GMove.act, Function.comp, roleAct]

lemma GMove.act_out (e : ρ ↪ σ) (mv : GMove α ρ) (f : ℕ) (x : Data α σ f) {i : σ}
    (h : i ∉ covered e) : (mv.over e).act f x i = x i := by
  have hh (j : ρ) : i ≠ e j := fun g => h ((cover_iff ..).2 ⟨j,g.symm⟩)
  cases mv with
  | old mv =>
    change (mv.over e).act f x i = x i
    rw [← walk_flat_move, BMove.flat_over]
    exact walk_out e mv.flat f x h
  | perm l G => simp [GMove.over, GMove.act, roleAct, hh]
  | phase l z c => simp [GMove.over, GMove.act, roleAct, hh]

theorem gwalk_over (e : ρ ↪ σ) (p : GWord α ρ) (f : ℕ) (x : Data α σ f) :
    gwalk f (p.map (GMove.over e)) x ∘ e = gwalk f p (x ∘ e) := by
  induction p generalizing x with
  | nil => rfl
  | cons m p ih =>
    change gwalk f (p.map (GMove.over e)) ((m.over e).act f x) ∘ e = gwalk f p (m.act f (x∘e))
    rw [← GMove.act_over]
    exact ih _

theorem gwalk_out (e : ρ ↪ σ) (p : GWord α ρ) (f : ℕ) (x : Data α σ f)
    {i : σ} (h : i ∉ covered e) :
    gwalk f (p.map (GMove.over e)) x i = x i := by
  induction p generalizing x with
  | nil => rfl
  | cons m p ih => exact (ih _).trans (GMove.act_out e m f _ h)

lemma GMove.costR_over (φ : ℕ → ℝ) (e : ρ ↪ σ) (mv : GMove α ρ) :
    (mv.over e).costR φ = mv.costR φ := by
  cases mv with
  | old mv => cases mv <;> rfl
  | perm l G => rfl
  | phase l z c => rfl

lemma GWord.costR_over (φ : ℕ → ℝ) (e : ρ ↪ σ) (w : GWord α ρ) :
    GWord.costR φ (w.map (GMove.over e)) = GWord.costR φ w := by
  induction w with
  | nil => rfl
  | cons mv w ih =>
    rw [List.map_cons, GWord.costR_cons, GWord.costR_cons, ih, GMove.costR_over]

lemma GWord.proper_over (u : ℕ) (e : ρ ↪ σ) (w : GWord α ρ) (h : w.Proper u) :
    GWord.Proper u (w.map (GMove.over e)) := by
  intro mv hmv
  obtain ⟨m0, hm0, rfl⟩ := List.mem_map.mp hmv
  have h0 := h m0 hm0
  cases m0 with
  | old mv => cases mv <;> exact h0
  | perm l G => trivial
  | phase l z c => trivial

namespace GRoute

/-- Re-index a route on a sub-network of roles (as upstream `Path.lift`). -/
theorem lift (e : ρ ↪ σ) {S T : σ → CMat α}
    {g : (σ→ℂ) → (σ→ℂ)} {h : (ρ→ℂ) → (ρ→ℂ)} {c : (ℕ → ℝ) → ℝ}
    (q : GRoute (S ∘ e) (T ∘ e) h c)
    (hin : ∀ x, (g x) ∘ e = h (x ∘ e)) (hout : ∀ x i, i∉covered e → g x i=x i)
    (he : ∀ i, i∉covered e → S i = T i) :
    GRoute S T g c := by
  obtain ⟨w,hw,hc,ha⟩ := q
  refine ⟨w.map (GMove.over e), GWord.proper_over _ e w hw,
    fun φ => by rw [GWord.costR_over]; exact hc φ, ?_⟩
  intro f x
  have frame_cont (S : σ → CMat α) (x : Data α σ f) :
      multiAct f S x ∘ e = multiAct f (S∘e) (x∘e) := rfl
  have point_cont :
      point f g x ∘ e = point f h (x ∘ e) := by
    funext i j
    exact congr_fun (hin _) i
  funext i
  by_cases hm : i∈covered e
  · obtain ⟨j,rfl⟩ := (cover_iff ..).mp hm
    exact congr_fun (show gwalk f _ _ ∘ e = multiAct f T _ ∘ e by
      rw [gwalk_over,frame_cont, ha,frame_cont,point_cont]) j
  · rw [gwalk_out e w _ _ hm]
    unfold multiAct
    simp only [he i hm]
    apply congrArg
    funext j
    exact (hout (fun r => x r j) i hm).symm

section Parallel
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Compose routes on disjoint sets of roles (as upstream `Path.parallel`); costs add. -/
theorem parallel (e : J → ρ ↪ σ)
    (dis : ∀ i j, i ≠ j → ∀ r ∈ covered (e i), r ∉ covered (e j))
    {S T : σ → CMat α} {d : J → (ℕ → ℝ) → ℝ}
    {g : (σ→ℂ)→(σ→ℂ)} {h : J → (ρ→ℂ) → (ρ→ℂ)}
    (q : ∀ i, GRoute (S ∘ e i) (T ∘ e i) (h i) (d i))
    (hin : ∀ i x, (g x) ∘ e i = h i (x ∘ e i))
    (hout : ∀ x r, (∀ i, r∉covered (e i)) → g x r=x r)
    (he : ∀ r, (∀ i, r∉covered (e i)) → S r=T r) :
    GRoute S T g (fun φ => ∑ i, d i φ) := by
  let u (j : Finset J) := j.biUnion fun i => covered (e i)
  let l (j : Finset J) (r : σ) := if r∈u j then T r else S r
  let k (j : Finset J) (x : σ→ℂ) (r : σ) := if r∈u j then g x r else x r
  have hh (j : Finset J) : GRoute S (l j) (k j) (fun φ => ∑ i ∈ j, d i φ) := by
    induction j using Finset.induction with
    | empty =>
      simp only [k,l,u,biUnion_empty,notMem_empty,ite_false,sum_empty]
      exact GRoute.refl
    | insert i j hi ih =>
      have hiu (r) (hr : r∈covered (e i)) : r ∉ u j := by
        intro hg
        obtain ⟨w,hw,he'⟩ := mem_biUnion.mp hg
        have hw' : i ≠ w := fun hh => hi (hh ▸ hw)
        exact dis _ _ hw' r hr he'
      have hui (r) : r∈u (insert i j) ↔ r∈covered (e i) ∨ r∈u j := by
        simp [u]
      let fn (x : σ→ℂ) (r : σ) := if r∈covered (e i) then g x r else x r
      have compi (x) : fn x ∘ e i = h i (x∘e i) := by
        rw [← hin]
        funext j; simp [fn,covered]
      have gg : GRoute (l j) (l (insert i j)) fn (d i) := by
        apply GRoute.lift (e i) (h:=h i) _ compi
        · intro x l hl; simp [fn,hl]
        · intro r hr; simp [l,hui,hr]
        · have eq1 : l j ∘ e i = S ∘ e i := by
            funext r
            have h : e i r ∈ covered (e i) := by simp [covered]
            simp [l, hiu _ h]
          have eq2 : l (insert i j) ∘ e i = T ∘ e i := by
            funext r
            have h : e i r ∈ covered (e i) := by simp [covered]
            simp [l,hui,h]
          rw [eq1,eq2]; apply q
      have cmp : fn ∘ k j = k (insert i j) := by
        funext x r
        by_cases hqr : r ∈ covered (e i)
        · obtain ⟨r,rfl⟩ := (cover_iff ..).mp hqr
          change fn (k j x) _ = _
          have eq : k j x ∘ e i = x ∘ e i := by
            funext r
            have h : e i r ∈ covered (e i) := by simp [covered]
            simp [k,hiu _ h]
          have H := congr_fun (show fn (k j x) ∘ e i = g x ∘ e i by rw [compi,eq,hin]) r
          exact H.trans (by simp [k,hui,hqr])
        · simp [Function.comp,k,fn,hui,hqr]
      rw [← cmp]
      exact (ih.trans gg).cast (fun φ => by rw [sum_insert hi, add_comm])
  have ha (r) : r∉u univ ↔ ∀ i, r∉covered (e i) := by simp [u]
  have eq1 : l univ = T := by
    funext r; by_cases h : r∈u univ
    · simp [l,h]
    · simp [l,h,he r ((ha r).1 h)]
  have eq2 : k univ = g := by
    funext x r; by_cases h : r∈u univ
    · simp [k,h]
    · simp [k,h,hout x r ((ha r).1 h)]
  have H := hh univ
  rwa [eq1,eq2] at H

end Parallel

end GRoute
end
end
end PowerSaving.GF
end OAI

#print axioms OAI.PowerSaving.GF.gwalk_over
#print axioms OAI.PowerSaving.GF.gwalk_out
#print axioms OAI.PowerSaving.GF.GRoute.lift
#print axioms OAI.PowerSaving.GF.GRoute.parallel
