import Work.GFrame.Engine.Route

/-!
# (key: bridge-377) The sweep lemma: `n` routes one after the other

For the compressed nine-stage word of PR #377 (jacklightChen) every stage is a sweep over the 8 replicas.  This file
composes `n` exact generalised routes `S i → S (i+1)` (`GRoute.trans`, Jacob Sussman's `Work.GFrame.Engine.Route`)
into one route `S 0 → S n`:

* `sweepMap h`        `h (n-1) ∘ ... ∘ h 0`, by recursion on `n` (the order of `GRoute.trans`);
* `GRoute.sweep`      the composed route, with the summed cost `∑ i, c i φ`;
* `sweepMap_const`    all maps `id` give `id`;
* `GRoute.sweep_const`  all costs equal to `c0`: the cost is `n * c0 φ`;
* `sweepMap_fix`, `sweepMap_local`  a coordinate kept by all maps but one gets the value of that one map.

No `sorry`.
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving.GF
open Binary Matrix Finset RAM
noncomputable section

/-- `h (n-1) ∘ ... ∘ h 0`. -/
def sweepMap {X : Type*} : {n : ℕ} → (Fin n → X → X) → X → X
  | 0, _ => id
  | n + 1, h => h (Fin.last n) ∘ sweepMap (fun i : Fin n => h i.castSucc)

lemma sweepMap_zero {X : Type*} (h : Fin 0 → X → X) : sweepMap h = id := rfl

lemma sweepMap_succ {X : Type*} {n : ℕ} (h : Fin (n + 1) → X → X) :
    sweepMap h = h (Fin.last n) ∘ sweepMap (fun i : Fin n => h i.castSucc) := rfl

lemma sweepMap_const {X : Type*} : ∀ {n : ℕ} (h : Fin n → X → X), (∀ i, h i = id) → sweepMap h = id
  | 0, _, _ => rfl
  | n + 1, h, hh => by
    rw [sweepMap_succ, sweepMap_const (fun i : Fin n => h i.castSucc) (fun i => hh _), hh]
    rfl

/-- `sweepMap` keeps every coordinate of `A` when every map keeps it. -/
theorem sweepMap_fix {R V : Type*} (A : R → Prop) :
    ∀ {n : ℕ} (h : Fin n → (R → V) → (R → V)), (∀ i x s, A s → h i x s = x s) →
      ∀ x s, A s → sweepMap h x s = x s
  | 0, _, _, _, _, _ => rfl
  | n + 1, h, hh, x, s, hs =>
    (hh (Fin.last n) _ s hs).trans
      (sweepMap_fix A (fun i : Fin n => h i.castSucc) (fun i => hh i.castSucc) x s hs)

/-- **Locality of a sweep.**  If the maps other than `h j` keep every coordinate of `A`, and the
coordinate `r ∈ A` of `h j x` depends only on `x` on `A`, then the sweep gives `h j x` at `r`. -/
theorem sweepMap_local {R V : Type*} (A : R → Prop) (r : R) (hr : A r) :
    ∀ {n : ℕ} (h : Fin n → (R → V) → (R → V)) (j : Fin n),
      (∀ i, i ≠ j → ∀ x s, A s → h i x s = x s) →
      (∀ x x', (∀ s, A s → x s = x' s) → h j x r = h j x' r) →
      ∀ x, sweepMap h x r = h j x r
  | 0, _, j, _, _, _ => j.elim0
  | n + 1, h, j, hfix, hloc, x => by
    rw [sweepMap_succ, Function.comp_apply]
    by_cases hj : j = Fin.last n
    · subst hj
      exact hloc _ _ (fun s hs => sweepMap_fix A (fun i : Fin n => h i.castSucc)
        (fun i x s hs => hfix _ (Fin.castSucc_lt_last i).ne x s hs) x s hs)
    · obtain ⟨j', rfl⟩ := Fin.exists_castSucc_eq.mpr hj
      refine (hfix (Fin.last n) (fun e => hj e.symm) _ r hr).trans ?_
      exact sweepMap_local A r hr (fun i : Fin n => h i.castSucc) j'
        (fun i hi x s hs => hfix _ (fun e => hi (Fin.castSucc_injective _ e)) x s hs) hloc x

section
variable {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

namespace GRoute

/-- **Sweep**: `n` routes `S i → S (i+1)` one after the other give one route `S 0 → S n`, whose scalar map is
the composition and whose cost is the sum. -/
theorem sweep : ∀ (n : ℕ) (S : Fin (n + 1) → (ρ → CMat α)) (h : Fin n → (ρ → ℂ) → (ρ → ℂ))
    (c : Fin n → (ℕ → ℝ) → ℝ), (∀ i : Fin n, GRoute (S i.castSucc) (S i.succ) (h i) (c i)) →
    GRoute (S 0) (S (Fin.last n)) (sweepMap h) (fun φ => ∑ i, c i φ)
  | 0, S, h, c, R => (GRoute.refl (S := S 0)).cast (fun φ => by rw [Finset.univ_eq_empty, Finset.sum_empty])
  | n + 1, S, h, c, R => by
    have ih := sweep n (fun i : Fin (n + 1) => S i.castSucc) (fun i => h i.castSucc)
      (fun i => c i.castSucc) (fun i => R i.castSucc)
    have t := ih.trans (R (Fin.last n))
    refine t.cast (fun φ => ?_)
    rw [Fin.sum_univ_castSucc]

/-- **Sweep with equal costs**: the cost is `n * c0`. -/
theorem sweep_const (n : ℕ) (S : Fin (n + 1) → (ρ → CMat α)) (h : Fin n → (ρ → ℂ) → (ρ → ℂ))
    (c : Fin n → (ℕ → ℝ) → ℝ) (c0 : (ℕ → ℝ) → ℝ) (hc : ∀ i φ, c i φ = c0 φ)
    (R : ∀ i : Fin n, GRoute (S i.castSucc) (S i.succ) (h i) (c i)) :
    GRoute (S 0) (S (Fin.last n)) (sweepMap h) (fun φ => (n : ℝ) * c0 φ) :=
  (sweep n S h c R).cast (fun φ => by
    simp only [hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul])

end GRoute
end
end
end PowerSaving.GF
end OAI

#print axioms OAI.PowerSaving.GF.sweepMap_const
#print axioms OAI.PowerSaving.GF.GRoute.sweep
#print axioms OAI.PowerSaving.GF.GRoute.sweep_const
#print axioms OAI.PowerSaving.GF.sweepMap_fix
#print axioms OAI.PowerSaving.GF.sweepMap_local
