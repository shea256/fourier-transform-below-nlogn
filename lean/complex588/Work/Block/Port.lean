import Work.Block.WHT

/-!
# Block moves, part 13: porting kit (umbrella module: `import Work.Block.Port` gives everything)

(agent key: block-engine).  `BPath` versions of the combinators of upstream `Path`, with the
SAME argument lists as upstream (DirectionalWords.lean `refl`, `trans`; FrameLifting.lean
`lift`, `parallel`), so that an existing network development can be ported by replacing
`Path A s t g losses` with `BPath φ A s t g cost`:

| upstream                      | here                                                         |
|-------------------------------|--------------------------------------------------------------|
| `Path.refl`                   | `BPath.refl`                         cost `0`                |
| `Path.trans`                  | `BPath.trans`                        costs add               |
| `Path.gate g cond`            | `BPath.gate g cond`                  cost `0`                |
| `Path.inc A h`                | `BPath.inc hm A h`                   `∑ r, splitCost φ m |t r \ s r|` |
| `Path.reframe A s t`          | `BPath.reframe hm A s t`             `∑ r, splitCost .. |s r \ t r| + splitCost .. |t r \ s r|` |
| `Path.lift e A q hin hout he` | `BPath.lift e A q hin hout he`       same cost               |
| `Path.parallel e dis A q ..`  | `BPath.parallel e dis A q ..`        `∑ i, d i`              |

* `engine_program_bpath`  the engine fed with a block path between frames.
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Finset
noncomputable section
section
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]

namespace BPath
variable {φ : ℕ → ℝ} {A : ρ → OBase α} {s t u : ρ → Finset α}

theorem refl : BPath φ A s s id 0 := BRoute.refl

theorem trans {g h : (ρ→ℂ) → (ρ→ℂ)} {c c' : ℝ} (a : BPath φ A s t g c)
    (b : BPath φ A t u h c') : BPath φ A s u (h ∘ g) (c + c') := BRoute.trans a b

theorem mono {g : (ρ→ℂ) → (ρ→ℂ)} {c c' : ℝ} (h : BPath φ A s t g c) (hc : c ≤ c') :
    BPath φ A s t g c' := BRoute.mono h hc

/-- Same argument list as upstream `Path.lift` (FrameLifting.lean:102). -/
theorem lift (e : ρ ↪ σ) (A : σ → OBase α) {s t : σ → Finset α}
    {g : (σ→ℂ) → (σ→ℂ)} {h : (ρ→ℂ) → (ρ→ℂ)} {c : ℝ}
    (q : BPath φ (A ∘ e) (s ∘ e) (t ∘ e) h c)
    (hin : ∀ x, (g x) ∘ e = h (x ∘ e)) (hout : ∀ x i, i∉covered e → g x i=x i)
    (he : ∀ i, i∉covered e → s i = t i) :
    BPath φ A s t g c :=
  BRoute.lift e (S:=fun r => frame (A r) (s r)) (T:=fun r => frame (A r) (t r)) q hin hout
    (fun i hi => by
      change frame (A i) (s i) = frame (A i) (t i)
      rw [he i hi])

/-- Same argument list as upstream `Path.parallel` (FrameLifting.lean:146); costs add. -/
theorem parallel {J : Type*} [Fintype J] [DecidableEq J] (e : J → ρ ↪ σ)
    (dis : ∀ i j, i ≠ j → ∀ r ∈ covered (e i), r ∉ covered (e j))
    (A : σ → OBase α) {s t : σ → Finset α} {d : J → ℝ}
    {g : (σ→ℂ)→(σ→ℂ)} {h : J → (ρ→ℂ) → (ρ→ℂ)}
    (q : ∀ i, BPath φ (A ∘ e i) (s ∘ e i) (t ∘ e i) (h i) (d i))
    (hin : ∀ i x, (g x) ∘ e i = h i (x ∘ e i))
    (hout : ∀ x r, (∀ i, r∉covered (e i)) → g x r=x r)
    (he : ∀ r, (∀ i, r∉covered (e i)) → s r=t r) :
    BPath φ A s t g (∑ i, d i) :=
  BRoute.parallel e dis (S:=fun r => frame (A r) (s r)) (T:=fun r => frame (A r) (t r)) q hin
    hout (fun r hr => by
      change frame (A r) (s r) = frame (A r) (t r)
      rw [he r hr])

end BPath
end

universe U

/-- **The block engine fed with a block path between frames** of orthonormal bases: the path
must lead every live role from its start frame to `kernel * (start frame)`. -/
theorem engine_program_bpath {α ρ σ : Type} [Fintype α] [DecidableEq α] [Fintype ρ]
    [DecidableEq ρ] [Fintype σ] [DecidableEq σ]
    (u a : ℕ) (hα : Fintype.card α = u) (hσ : Fintype.card σ = 2^a) (hu : 3 ≤ u)
    (e : σ → ρ) (he : Function.Injective e)
    (z : ℝ) (hz : 0 ≤ z)
    (A : ρ → OBase α) (s t : ρ → Finset α)
    (g : (ρ→ℂ) → (ρ→ℂ)) (c : ℝ)
    (h : BPath (fun r => ((r:ℝ)/(u:ℝ))^z) A s t g c) (hc : c < (2:ℝ)^a)
    (hg : ∀ x : ρ → ℂ, (∀ s, (∀ l, e l ≠ s) → x s = 0) → ∀ l, g x (e l) = x (e l))
    (hT : ∀ l, frame (A (e l)) (t (e l)) = kernel α * frame (A (e l)) (s (e l)))
    (cl : Paint) (m : Bool) {ι : Type U} (k : ι→ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*envelope z (k i)) :=
  engine_program_broute u a hα hσ hu e he z hz (fun r => frame (A r) (s r))
    (fun r => unframe (A r) (s r)) (fun r => frame (A r) (t r))
    (fun r => unframe_right (A r) (s r)) g c h hc hg hT cl m k v

end
end PowerSaving.RAM
end OAI

#print axioms OAI.PowerSaving.RAM.BPath.parallel
#print axioms OAI.PowerSaving.RAM.engine_program_bpath
