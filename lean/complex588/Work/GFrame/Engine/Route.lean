import Work.GFrame.Engine.Free

/-!
# GFrame engine, part 8: exact routes in the generalised language (agent key: eng-ram)

`GRoute S T g c`: a proper generalised word that carries role `r` from the matrix `S r` to the
matrix `T r` while the scalar network does `g`, with exact price `c`.  Analogue of `XRoute`
(`Work/BlockApply/Exact.lean`), with `walk f w.flat` replaced by `gwalk f w`.

* `GRoute.refl/cast/trans`, `GRoute.ofX` (every old route is a route);
* `GRoute.gate`     copy / overwrite / erase between roles with IDENTICAL matrices (no block);
* `GRoute.on_role`  a `GStep` on one role;
* `GRoute.shifts`   free translations of all roles;
* `GRoute.liveKernel`  assembling the scratch certificate `GLiveKernel` from a route.
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving.GF
open Binary Matrix Finset RAM
noncomputable section
section
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

/-- **Exact generalised route.** -/
def GRoute (S T : ρ → CMat α) (g : (ρ→ℂ) → (ρ→ℂ)) (c : (ℕ → ℝ) → ℝ) : Prop :=
  ∃ w : GWord α ρ, w.Proper (Fintype.card α) ∧ (∀ φ, w.costR φ = c φ) ∧
    ∀ (f : ℕ) (x : Data α ρ f), gwalk f w (multiAct f S x) = multiAct f T (point f g x)

namespace GRoute
variable {S T U : ρ → CMat α}

theorem refl : GRoute S S id (fun _ => 0) :=
  ⟨[], GWord.proper_nil _, fun _ => rfl, fun f x => rfl⟩

theorem cast {g : (ρ→ℂ) → (ρ→ℂ)} {c c' : (ℕ → ℝ) → ℝ} (h : GRoute S T g c)
    (hc : ∀ φ, c φ = c' φ) : GRoute S T g c' := by
  obtain ⟨w, hw, hcost, hwalk⟩ := h
  exact ⟨w, hw, fun φ => (hcost φ).trans (hc φ), hwalk⟩

theorem trans {g h : (ρ→ℂ) → (ρ→ℂ)} {c c' : (ℕ → ℝ) → ℝ} (a : GRoute S T g c)
    (b : GRoute T U h c') : GRoute S U (h ∘ g) (fun φ => c φ + c' φ) := by
  obtain ⟨p,hp,cp,ap⟩ := a
  obtain ⟨q,hq,cq,aq⟩ := b
  refine ⟨p++q, hp.append hq, fun φ => by rw [GWord.costR_append, cp, cq], ?_⟩
  intro f x
  rw [gwalk_append, ap, aq]; rfl

/-- Every old exact route is a generalised route. -/
theorem ofX {g : (ρ→ℂ) → (ρ→ℂ)} {c : (ℕ → ℝ) → ℝ} (h : XRoute S T g c) : GRoute S T g c := by
  obtain ⟨w, hw, hc, hwalk⟩ := h
  exact ⟨GWord.ofB w, GWord.proper_ofB hw, fun φ => by rw [GWord.costR_ofB, hc],
    fun f x => by rw [gwalk_ofB, hwalk]⟩

/-- **Copy / overwrite / erase gate** (no block): legal between roles that carry IDENTICAL
matrices. -/
theorem gate (g : Matrix ρ ρ ℚ) (S T : ρ → CMat α)
    (cond : ∀ i j, g i j ≠ 0 → T i = S j) :
    GRoute S T (actPoint g) (fun _ => 0) := ofX (XRoute.gate g S T cond)

/-- A generalised step on one role moves the matrix of that role only. -/
theorem on_role (S : ρ → CMat α) (l : ρ) (N : CMat α) {c : (ℕ → ℝ) → ℝ}
    (h : GStep l (S l) N c) :
    GRoute S (Function.update S l N) id c := by
  obtain ⟨w, V, hw, hc, hV, hwalk⟩ := h
  refine ⟨w, hw, hc, fun f x => ?_⟩
  rw [hwalk, show point f id x = x from rfl]
  funext j
  by_cases hj : j = l
  · subst hj
    simp [roleAct, multiAct, hV]
  · simp [roleAct, multiAct, hj]

/-- Free translations of all roles: no block. -/
theorem shifts (hm : 2 ≤ Fintype.card α) (S : ρ → CMat α) (z : ρ → Space α) :
    GRoute S (fun r => shift (z r) * S r) id (fun _ => 0) := ofX (XRoute.shifts hm S z)

/-- **Assembling a generalised scratch certificate from a route**, keeping the exact cost. -/
theorem liveKernel (e : σ → ρ) (S S' T : ρ → CMat α) (hS : ∀ r, S r * S' r = 1)
    (g : (ρ→ℂ) → (ρ→ℂ)) (c : (ℕ → ℝ) → ℝ) (h : GRoute S T g c)
    (hg : ∀ x : ρ → ℂ, (∀ s, (∀ l, e l ≠ s) → x s = 0) → ∀ l, g x (e l) = x (e l))
    (hT : ∀ l, T (e l) = kernel α * S (e l)) :
    ∃ w : GWord α ρ, w.Proper (Fintype.card α) ∧ (∀ φ, w.costR φ = c φ) ∧
      GLiveKernel e w := by
  obtain ⟨w,hp,hc,hw⟩ := h
  refine ⟨w, hp, hc, ?_⟩
  intro f v hv l
  let y : Data α ρ f := multiAct f S' v
  have hy : multiAct f S y = v := by
    funext r; simp [y, multiAct, hS]
  have hy0 (s : ρ) (hs : ∀ l, e l ≠ s) : y s = 0 := by
    change matAct f (S' s) (v s) = 0
    rw [hv s hs]; exact matAct_zero f _
  have hpt : point f g y (e l) = y (e l) := by
    funext i
    exact hg (fun r => y r i) (fun s hs => by rw [hy0 s hs]; rfl) l
  have h1 := congrFun (hw f y) (e l)
  rw [hy] at h1
  rw [h1]
  change matAct f (T (e l)) (point f g y (e l)) = _
  rw [hpt, hT, ← matAct_mul]
  exact congrArg _ (congrFun hy (e l))

end GRoute
end
end
end PowerSaving.GF
end OAI

#print axioms OAI.PowerSaving.GF.GRoute.trans
#print axioms OAI.PowerSaving.GF.GRoute.gate
#print axioms OAI.PowerSaving.GF.GRoute.on_role
#print axioms OAI.PowerSaving.GF.GRoute.liveKernel
