import OAI.Computability.FourierTransform.BinaryFrames

namespace OAI

/-! A word whose directional steps will become recursive tensor calls. The frame-path
  bookkeeping suffices to prove it at every amplification. -/
namespace PowerSaving.Binary
open Matrix Finset
noncomputable section

abbrev Sky (α : Type*) (f : ℕ) := (Fin f → Space α)
abbrev Data (α : Type*) (ρ : Type*) (f : ℕ) := ρ → Sky α f → ℂ

section
variable {α ρ : Type*} [Fintype α] [DecidableEq α]

def matAct (f : ℕ) (M : CMat α) (x : Sky α f → ℂ) : Sky α f → ℂ :=
  (digitProd (fun _ : Fin f => M)) *ᵥ x


@[simp] theorem matAct_mul (f : ℕ) (M N : CMat α) (x : Sky α f → ℂ) :
    matAct f M (matAct f N x) = matAct f (M*N) x := by
  rw [matAct,matAct,matAct,mulVec_mulVec,digitProd_mul]

@[simp] theorem matAct_one (f : ℕ) (x : Sky α f → ℂ) :
    matAct f (1 : CMat α) x=x := by rw [matAct,digitProd_one, Matrix.one_mulVec]

def multiAct (f : ℕ) (M : ρ → CMat α) (x : Data α ρ f) : Data α ρ f :=
  fun r => matAct f (M r) (x r)

def roleAct (f : ℕ) [DecidableEq ρ] (r : ρ) (M : CMat α) (x : Data α ρ f) : Data α ρ f :=
  fun j => if j=r then matAct f M (x j) else x j

@[simp] lemma roleAct_mul (f : ℕ) [DecidableEq ρ] (r : ρ) (M N : CMat α)
    (x : Data α ρ f) :
    roleAct f r M (roleAct f r N x) = roleAct f r (M*N) x := by
  funext j; by_cases j=r <;> simp [roleAct, *]

def point (f : ℕ) (g : (ρ→ℂ)→(ρ→ℂ)) (x : Data α ρ f) : Data α ρ f :=
  fun r i => g (fun r => x r i) r

end

section
variable {α ρ : Type*}

inductive Move (α ρ : Type*)
  | localM (g : Matrix ρ ρ ℚ)
  | dir (r : ρ) (z : Space α) (nz : z≠0)
  | shift (r : ρ) (z : Space α)

def toll : Move α ρ → ℕ
  | .dir _ _ _ => 1
  | _ => 0

abbrev PWord (α ρ : Type*) := List (Move α ρ)

def tally (s : PWord α ρ) : ℕ := (s.map toll).sum

theorem tally_append (p q : PWord α ρ) : tally (p++q)= tally p + tally q := by simp [tally]

variable [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]

def actPoint (g : Matrix ρ ρ ℚ) (x : ρ→ℂ) (r : ρ) := ∑ j, (g r j:ℂ)*x j

def Move.go (f : ℕ) : Move α ρ → Data α ρ f → Data α ρ f
  | .localM M => point f (actPoint M)
  | .dir r z _ => roleAct f r (Binary.dir z)
  | .shift r z => roleAct f r (Binary.shift z)

def walk (f : ℕ) (p : PWord α ρ) (x : Data α ρ f) : Data α ρ f :=
  p.foldl (fun y s => s.go f y) x

theorem walk_append (f : ℕ) (p q : PWord α ρ) (x : Data α ρ f) :
    walk f (p++q) x = walk f q (walk f p x) := by simp [walk]

/-- Frame mass. -/
def mass (s : ρ → Finset α) := ∑ r, (s r).card
def loss (s t : ρ → Finset α) := ∑ r, (s r \ t r).card

def withFrame (A : ρ → OBase α) (s : ρ → Finset α) (f : ℕ) : Data α ρ f → Data α ρ f :=
  multiAct f fun r => frame (A r) (s r)

/-- A point map surrounded by frame changes. The path identity applies to arbitrary
 initial arrays. `losses` accounts for decreases in dimension (shifts free). -/
def Path (A : ρ → OBase α) (s t : ρ → Finset α)
    (g : (ρ→ℂ) → (ρ→ℂ)) (losses : ℕ) : Prop :=
  ∃ p : PWord α ρ,
    tally p + mass s = mass t + 2 * losses ∧
    ∀ (f : ℕ) (x : Data α ρ f),
      walk f p (withFrame A s f x) = withFrame A t f (point f g x)

namespace Path
variable {A : ρ → OBase α} {s t u : ρ → Finset α}

theorem refl : Path A s s id 0 := by
  refine ⟨[], by simp [tally], ?_⟩
  intro f x; rfl

theorem trans {g h i j} (a : Path A s t g i) (b : Path A t u h j) :
    Path A s u (h ∘ g) (i+j) := by
  obtain ⟨p,hp,ap⟩ := a
  obtain ⟨q,hq,aq⟩ := b
  refine ⟨p++q, by rw [tally_append]; omega, ?_⟩
  intro f x
  rw [walk_append, ap, aq]; rfl

/-- Move through a gate. Its nonzero entries must stay within a common frame. -/
theorem gate (g : Matrix ρ ρ ℚ)
    (cond : ∀ i j, g i j ≠ 0 → frame (A i) (s i) = frame (A j) (s j)) :
    Path A s s (actPoint g) 0 := by
  refine ⟨[.localM g], by simp [tally,toll], ?_⟩
  intro f x
  let M (r : ρ) := digitProd (fun _ : Fin f => frame (A r) (s r))
  funext r i
  change ∑ j, (g r j:ℂ)* (∑ a, M j i a * x j a)
    = ∑ a, M r i a * (∑ j, (g r j:ℂ)*x j a)
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro j hj
  by_cases gh : g r j = 0
  · simp [gh]
  · dsimp only [M]
    have eq := cond r j gh
    rw [eq]
    ac_rfl

/-- One new line both upwards and downwards. -/
theorem change_one (s : ρ → Finset α) (r : ρ) (i : α) (hi : i ∉ s r) :
    let t := fun j => if j=r then insert i (s j) else s j
    Path A s t id 0 ∧ Path A t s id 1 := by
  intro t
  let z := (A r).v i
  have hz : dot z z=1 := OBase.self _ _
  have hn : z≠0 := OBase.nz _ _
  have hf : frame (A r) (t r) = delta z * frame (A r) (s r) := by
    dsimp [t]
    rw [ite_eq_left rfl, frame_ins _ _ _ hi]
  have ha (f : ℕ) (x : Data α ρ f) :
      roleAct f r (delta z) (withFrame A s f x) = withFrame A t f x := by
    funext j
    by_cases je : j=r
    · subst j; simp [roleAct, withFrame, multiAct, hf]
    · simp [roleAct, withFrame, multiAct, je,t]
  have hb (f : ℕ) (x : Data α ρ f) :
      roleAct f r (Binary.shift z * delta z) (withFrame A t f x) = withFrame A s f x := by
    rw [← ha, roleAct_mul, mul_assoc, delta_sq z hz, shift_sq]
    funext j; simp [roleAct]
  have hm : mass t = mass s + 1 := by
    unfold mass
    have e (j : ρ) : (t j).card = (s j).card + if j=r then 1 else 0 := by
      by_cases j=r
      next h => subst j; simp [t,hi]
      next h => simp [h,t]
    simp [e, sum_add_distrib]
  -- upward path for sign positive; downward path adds shift. If sign negative reverse.
  obtain he|he := lum_of_unit z hz
  · rw [delta_pos z he] at ha hb
    constructor
    · refine ⟨[.dir r z hn], by simp [tally,toll,hm,Nat.add_comm], ?_⟩
      exact ha
    · refine ⟨[.dir r z hn,.shift r z], by simp [tally,toll,hm]; omega, ?_⟩
      intro f x
      change roleAct f r _ (roleAct f r _ (withFrame A t f x)) = withFrame A s f x
      rw [roleAct_mul]
      apply hb
  · rw [delta_neg z he] at ha hb
    rw [← mul_assoc, shift_sq, one_mul] at hb
    constructor
    · refine ⟨[.dir r z hn,.shift r z], by simp [tally,toll,hm,Nat.add_comm], ?_⟩
      intro f x
      change roleAct f r _ (roleAct f r _ (withFrame A s f x)) = withFrame A t f x
      rw [roleAct_mul]
      apply ha
    · exact ⟨[.dir r z hn], by simp [tally,toll,hm]; omega,hb⟩

/-- Comparable mask sets. -/
private theorem reframe_le (x y : ρ → Finset α) (h : ∀ r, x r ⊆ y r) :
    Path A x y id 0 ∧ Path A y x id (loss y x) := by
  have eqn (s : ρ → Finset α) (hg : ∀ r, s r ⊆ y r) :
      loss y s + mass s = mass y := by
    unfold loss mass
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro j hj
    rw [Finset.card_sdiff_of_subset (hg j)]
    exact Nat.sub_add_cancel (Finset.card_le_card (hg j))
  generalize hw : loss y x = w at *
  induction w using Nat.strong_induction_on generalizing x with
  | h w ih =>
    by_cases hh : ∃ (r:ρ) (i:α), i∈y r ∧ i∉x r
    next hh =>
      obtain ⟨r,i,hi,he⟩ := hh
      let z := fun j => if j=r then insert i (x j) else x j
      have hz : ∀ j, z j ⊆ y j := by
        intro j
        by_cases j=r
        next hh =>
          subst j
          intro k hk
          simp [z] at hk
          obtain rfl | hv := hk
          · exact hi
          · exact h _ hv
        next hh => simpa only [z, ite_eq_right hh] using h j
      have hm : mass z = mass x + 1 := by
        unfold mass
        have e (j : ρ) : (z j).card = (x j).card + if j=r then 1 else 0 := by
          by_cases j=r
          next h => subst j; simp [z,he]
          next h => simp [h,z]
        simp [e, sum_add_distrib]
      have en := eqn z hz
      have ek := eqn x h
      have hw' : loss y z + 1 = w := by omega
      obtain ⟨ha,hb⟩ := ih (loss y z) (by omega) z hz rfl
      obtain ⟨hc,hd⟩ := change_one (A:=A) x r i he
      exact ⟨hc.trans ha, hw' ▸ hb.trans hd⟩
    next hh =>
      have hy : y = x := by
        funext j
        apply Finset.Subset.antisymm _ (h j)
        intro i hi
        by_contra he
        exact hh ⟨j,i,hi,he⟩
      subst x
      simp [loss] at hw
      subst w
      exact ⟨refl,refl⟩

theorem reframe (A : ρ → OBase α) (s t : ρ → Finset α) :
    Path A s t id (loss s t) := by
  let u := fun j => s j ∩ t j
  have ha := (reframe_le (A:=A) u s (fun _ => inter_subset_left)).2
  have hb := (reframe_le (A:=A) u t (fun _ => inter_subset_right)).1
  have eq : loss s u = loss s t := by
    unfold loss u
    simp
  have hh := ha.trans hb
  rw [add_zero, eq] at hh
  exact hh

theorem inc (A : ρ → OBase α) {s t : ρ → Finset α} (h : ∀ r, s r ⊆ t r) :
    Path A s t id 0 := (reframe_le s t h).1

end Path
end
end
end PowerSaving.Binary

end OAI
