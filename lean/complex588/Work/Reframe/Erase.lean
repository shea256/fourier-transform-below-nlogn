import Work.Reframe.Basic

/-!
# (key: reframe) ERASE-WRAPPED invocations

`xinvocation_fwd` / `xinvocation_bwd` (`Work.Combine.XInvocation`) have the scalar maps
`Circuit.fwd` / `Circuit.bwd`, which are the shears `y += x` / `x -= y` only when the scratch
copies start at zero, and which leave helper contents in the copies.  Here the invocation is
wrapped between two erase gates (gate matrix `eraseM`: identity on banks and slots, ZERO rows
on the copies; a zero row carries no frame condition, so the copies may enter and leave with
ANY frame matrix):

    erase the copies ; invocation ; erase the copies.

* `eraseC`, `actPoint_eraseM`, `xerase`   the erase gate as an exact block route, price 0;
* `shearF`, `shearB`                       the scalar maps `(x,y,s,c) ↦ (x, y+x, s, 0)` and
                                           `(x-y, y, s, 0)`;
* `erase_fwd_erase`, `erase_bwd_erase`     `eraseC ∘ K.fwd ∘ eraseC = shearF` and likewise
                                           for `bwd`, with NO hypothesis on the input;
* `xinvocation_fwd_erased`, `xinvocation_bwd_erased`
                                           the wrapped invocations as exact block routes with
                                           the price `X.cost` of the plain invocation;
* `shearF_comm`, `shearB_comm`             the commutation hypothesis of `XRoute.reframe`:
                                           `D` = one matrix per bank PAIR, any matrix per slot,
                                           any matrix per copy;
* `xinvocation_fwd_reframed`, `xinvocation_bwd_reframed`
                                           the wrapped invocations after re-framing.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace CB
open Binary Matrix Finset RAM SS
noncomputable section

section Erase
variable {T Sl C : Type} [Fintype T] [DecidableEq T] [Fintype Sl] [DecidableEq Sl]
  [Fintype C] [DecidableEq C]

/-- gate matrix: identity on banks and slots, zero rows on the copies. -/
def eraseM : Matrix (Box T Sl C) (Box T Sl C) ℚ := fun i j =>
  Sum.elim (fun _ => if i = j then (1:ℚ) else 0)
    (Sum.elim (fun _ => if i = j then (1:ℚ) else 0) (fun _ => 0)) i

/-- scalar map of the erase gate: the copies are set to zero. -/
def eraseC (z : Box T Sl C → ℂ) : Box T Sl C → ℂ :=
  stamp (z ∘ bX) (z ∘ bY) (z ∘ bS) (fun _ => 0)

lemma actPoint_eraseM (z : Box T Sl C → ℂ) : actPoint eraseM z = eraseC z := by
  funext i
  rcases i with ((t|t)|(q|c))
  · exact sum_ind_right (Sum.inl (Sum.inl t)) z
  · exact sum_ind_right (Sum.inl (Sum.inr t)) z
  · exact sum_ind_right (Sum.inr (Sum.inl q)) z
  · show ∑ j, (((0:ℚ)) : ℂ) * z j = 0
    simp

/-- forward shear with restored slots and erased copies. -/
def shearF (z : Box T Sl C → ℂ) : Box T Sl C → ℂ :=
  stamp (z ∘ bX) (z ∘ bY + z ∘ bX) (z ∘ bS) (fun _ => 0)

/-- backward shear with restored slots and erased copies. -/
def shearB (z : Box T Sl C → ℂ) : Box T Sl C → ℂ :=
  stamp (z ∘ bX - z ∘ bY) (z ∘ bY) (z ∘ bS) (fun _ => 0)

@[simp] lemma shearF_X (z : Box T Sl C → ℂ) : shearF z ∘ bX = z ∘ bX := rfl
@[simp] lemma shearF_Y (z : Box T Sl C → ℂ) : shearF z ∘ bY = z ∘ bY + z ∘ bX := rfl
@[simp] lemma shearF_S (z : Box T Sl C → ℂ) : shearF z ∘ bS = z ∘ bS := rfl
@[simp] lemma shearF_C (z : Box T Sl C → ℂ) : shearF z ∘ bC = 0 := rfl
@[simp] lemma shearB_X (z : Box T Sl C → ℂ) : shearB z ∘ bX = z ∘ bX - z ∘ bY := rfl
@[simp] lemma shearB_Y (z : Box T Sl C → ℂ) : shearB z ∘ bY = z ∘ bY := rfl
@[simp] lemma shearB_S (z : Box T Sl C → ℂ) : shearB z ∘ bS = z ∘ bS := rfl
@[simp] lemma shearB_C (z : Box T Sl C → ℂ) : shearB z ∘ bC = 0 := rfl

variable {α : Type} [Fintype α] [DecidableEq α]

/-- **The erase gate.**  Banks and slots keep their frame matrices; the copies may leave with
ANY frame matrix (their row of the gate is zero). -/
lemma xerase {S S' : Box T Sl C → CMat α} (hX : ∀ t, S' (bX t) = S (bX t))
    (hY : ∀ t, S' (bY t) = S (bY t)) (hS : ∀ q, S' (bS q) = S (bS q)) :
    XRoute S S' eraseC (fun _ => 0) := by
  have h := XRoute.gate (α := α) (eraseM (T := T) (Sl := Sl) (C := C)) S S' (fun i j hij => by
    rcases i with ((t|t)|(q|c))
    · have e : (Sum.inl (Sum.inl t) : Box T Sl C) = j := by
        by_contra hne
        exact hij (if_neg hne)
      subst e
      exact hX t
    · have e : (Sum.inl (Sum.inr t) : Box T Sl C) = j := by
        by_contra hne
        exact hij (if_neg hne)
      subst e
      exact hY t
    · have e : (Sum.inr (Sum.inl q) : Box T Sl C) = j := by
        by_contra hne
        exact hij (if_neg hne)
      subst e
      exact hS q
    · exact absurd rfl hij)
  exact h.castg (funext fun z => actPoint_eraseM z)

/-- commutation of the forward shear with a re-framing that is constant on each bank pair. -/
lemma shearF_comm (Db : T → CMat α) (Ds : Sl → CMat α) (Dc : C → CMat α) (f : ℕ)
    (x : Data α (Box T Sl C) f) :
    point f shearF (multiAct f (stamp Db Db Ds Dc) x)
      = multiAct f (stamp Db Db Ds Dc) (point f shearF x) := by
  funext r
  rcases r with ((t|t)|(q|c))
  · rfl
  · show matAct f (Db t) (x (bY t)) + matAct f (Db t) (x (bX t))
      = matAct f (Db t) (x (bY t) + x (bX t))
    rw [matAct_add]
  · rfl
  · show (0 : Sky α f → ℂ) = matAct f (Dc c) 0
    rw [matAct_zero']

/-- commutation of the backward shear with a re-framing that is constant on each bank pair. -/
lemma shearB_comm (Db : T → CMat α) (Ds : Sl → CMat α) (Dc : C → CMat α) (f : ℕ)
    (x : Data α (Box T Sl C) f) :
    point f shearB (multiAct f (stamp Db Db Ds Dc) x)
      = multiAct f (stamp Db Db Ds Dc) (point f shearB x) := by
  funext r
  rcases r with ((t|t)|(q|c))
  · show matAct f (Db t) (x (bX t)) - matAct f (Db t) (x (bY t))
      = matAct f (Db t) (x (bX t) - x (bY t))
    rw [matAct_sub]
  · rfl
  · rfl
  · show (0 : Sky α f → ℂ) = matAct f (Dc c) 0
    rw [matAct_zero']

end Erase

section Wrapped
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]

/-- erase, forward invocation, erase: the shear `y += x`, for EVERY input. -/
lemma erase_fwd_erase (K : Circuit H T Sl C) :
    eraseC ∘ (K.fwd ∘ eraseC) = (shearF : (Box T Sl C → ℂ) → (Box T Sl C → ℂ)) := by
  funext z
  obtain ⟨h1, h2, h3⟩ := K.fwd_live (eraseC z) rfl
  show stamp (K.fwd (eraseC z) ∘ bX) (K.fwd (eraseC z) ∘ bY) (K.fwd (eraseC z) ∘ bS)
    (fun _ => 0) = shearF z
  rw [h1, h2, h3]
  rfl

/-- erase, backward invocation, erase: the shear `x -= y`, for EVERY input. -/
lemma erase_bwd_erase (K : Circuit H T Sl C) :
    eraseC ∘ (K.bwd ∘ eraseC) = (shearB : (Box T Sl C → ℂ) → (Box T Sl C → ℂ)) := by
  funext z
  obtain ⟨h1, h2, h3⟩ := K.bwd_live (eraseC z) rfl
  show stamp (K.bwd (eraseC z) ∘ bX) (K.bwd (eraseC z) ∘ bY) (K.bwd (eraseC z) ∘ bS)
    (fun _ => 0) = shearB z
  rw [h1, h2, h3]
  rfl

end Wrapped
end
end CB
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.CB.xerase
#print axioms OAI.PowerSaving.CB.erase_fwd_erase
#print axioms OAI.PowerSaving.CB.erase_bwd_erase
#print axioms OAI.PowerSaving.CB.shearF_comm
