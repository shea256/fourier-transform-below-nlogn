import Work.Block.Peel

/-!
# Block moves, part 3: RAM address arithmetic for a splitting

(agent key: block-engine).  Generalises upstream `ColumnAddresses.lean` (`from_grid`,
`to_grid`): going back and forth between an address in the grid `book X r f` and the pair
(address of the fibre in `book X' r f`, address inside the fibre in `bits (rk*f)`), for an
arbitrary splitting `S : Split α β (Fin rk)`, in O(1) RAM work.

The only fact used about `S` is additivity: over `ZMod 2` every coordinate of an additive map
is the XOR of a fixed set of input coordinates (`additive_functional`), and upstream's XOR
table (`Gear.addr_xor`) adds two `f`-bit rows in O(1).
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving.Binary
open Matrix Finset
noncomputable section

section
variable {α : Type*} [Fintype α] [DecidableEq α]

lemma single_one_eq_eu (a : α) : (Pi.single a (1:F) : Space α) = eu a := by
  funext j
  by_cases h : j = a
  · subst h; simp [eu]
  · simp [eu, h, Ne.symm h]

/-- Over `ZMod 2`, an additive functional is the sum of a fixed set of coordinates. -/
lemma additive_functional (g : Space α → F) (hg : ∀ x y, g (x+y) = g x + g y)
    (x : Space α) :
    g x = ∑ a ∈ univ.filter (fun a => g (eu a) = 1), x a := by
  let G : Space α →+ F := AddMonoidHom.mk' g hg
  have hx : x = ∑ a, Pi.single a (x a) := (Finset.univ_sum_single x).symm
  have h1 : g x = ∑ a, g (Pi.single a (x a)) := by
    conv_lhs => rw [hx]
    exact map_sum G _ _
  rw [h1, Finset.sum_filter]
  apply sum_congr rfl
  intro a _
  rcases bit_cases (x a) with h|h
  · rw [h, Pi.single_zero]
    have h0 : g 0 = 0 := G.map_zero
    rw [h0]; simp
  · rw [h, single_one_eq_eu]
    rcases bit_cases (g (eu a)) with h'|h'
    · rw [h']; simp
    · rw [h']; simp

end
end
end PowerSaving.Binary

namespace PowerSaving.RAM
open Binary Ty Finset
noncomputable section

universe U V
variable {ι : Type U}

namespace Gear
variable {m : Bool} {B f : ι → ℕ} {s t : Ty} {x : ι → T s}
variable (g : Gear m B f s x)
include g

lemma small_given : Small B f :=
  g.bound.mono (fun i => Nat.lt_two_pow_self.le)

/-- `2^(rk*f)`: the length of one fibre of a rank-`rk` block. -/
lemma powerB (rk : ℕ) : Knows m B s x (fun i => 2^(rk * f i)) :=
  (g.power.wpow_fixed rk g.bound).cong (fun _ => rfl)
    (fun i => by rw [← pow_mul, Nat.mul_comm])

lemma boundB (rk : ℕ) : Small B fun i => 2^(rk * f i) :=
  (g.bound.pow rk).mono (fun i => by rw [← pow_mul, Nat.mul_comm])

lemma givenB (rk : ℕ) : Knows m B s x (fun i => rk * f i) :=
  (Can.wc rk).times g.given (Small.const B rk) g.small_given

lemma small_givenB (rk : ℕ) : Small B fun i => rk * f i :=
  (Small.const B rk).mul g.small_given

/-- XOR of a fixed finite set of known `f`-bit rows. -/
lemma xor_rows {κ : Type*} (rws : κ → ∀ i, Bits (f i))
    (h : ∀ c, Knows m B s x fun i => (bits (f i)).loc (rws c i)) (T : Finset κ) :
    Knows m B s x fun i => (bits (f i)).loc (∑ c ∈ T, rws c i) := by
  classical
  induction T using Finset.induction with
  | empty =>
    refine (Can.wc 0).cong (fun _ => rfl) (fun i => ?_)
    rw [Finset.sum_empty, bits_loc]
    simp
  | insert c T hc ih =>
    let q (i : ι) : Bits (f i) × Bits (f i) := (rws c i, ∑ c ∈ T, rws c i)
    refine (g.addr_xor q (h c) ih).cong (fun _ => rfl) (fun i => ?_)
    rw [Finset.sum_insert hc]

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- One row of the columnwise image of a body under an additive functional. -/
lemma body_additive (X : Layout α) (g' : Space α → F)
    (hg : ∀ p q, g' (p+q) = g' p + g' q) (v : ∀ i, Sky α (f i))
    (h : Knows m B s x fun i => (bodyOrder X (f i)).loc (v i)) :
    Knows m B s x fun i => (bits (f i)).loc (fun l => g' (v i l)) := by
  have hr (a : α) := g.body_get X v a h
  have H := g.xor_rows (fun a i l => v i l a) hr (univ.filter (fun a => g' (eu a) = 1))
  refine H.cong (fun _ => rfl) (fun i => ?_)
  congr 1
  funext l
  rw [Finset.sum_apply, additive_functional g' hg]

/-- The same for a functional of two bodies. -/
lemma body_additive₂ {β γ : Type*} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    (X' : Layout β) (Y : Layout γ) (g' : Space β × Space γ → F)
    (hg : ∀ p q, g' (p+q) = g' p + g' q)
    (v1 : ∀ i, Sky β (f i)) (v2 : ∀ i, Sky γ (f i))
    (h1 : Knows m B s x fun i => (bodyOrder X' (f i)).loc (v1 i))
    (h2 : Knows m B s x fun i => (bodyOrder Y (f i)).loc (v2 i)) :
    Knows m B s x fun i => (bits (f i)).loc (fun l => g' (v1 i l, v2 i l)) := by
  have a1 := g.body_additive X' (fun y => g' (y,0))
    (fun p q => by rw [← hg]; simp) v1 h1
  have a2 := g.body_additive Y (fun w => g' (0,w))
    (fun p q => by rw [← hg]; simp) v2 h2
  let q (i : ι) : Bits (f i) × Bits (f i) :=
    (fun l => g' (v1 i l,0), fun l => g' (0,v2 i l))
  refine (g.addr_xor q a1 a2).cong (fun _ => rfl) (fun i => ?_)
  congr 1
  funext l
  change g' (v1 i l,0) + g' (0,v2 i l) = g' (v1 i l, v2 i l)
  rw [← hg]; simp

variable (X : Layout α) (r : ℕ)
variable {β : Type*} [Fintype β] [DecidableEq β] {rk : ℕ}

/-- Grid address ↦ (fibre address, address inside the fibre), for a block of rank `rk`. -/
lemma from_gridB (S : Split α β (Fin rk)) (X' : Layout β)
    (v : ∀ i, Grid α r (f i))
    (h : Knows m B s x (fun i => (book X r (f i)).loc (v i))) :
    Knows m B s x (fun i => (book X' r (f i)).loc (S.peel r (f i) (v i)).1) ∧
    Knows m B s x (fun i => (bits (rk * f i)).loc (S.peel r (f i) (v i)).2) := by
  obtain ⟨hg, hh⟩ := g.grid_fetch X r (v:=v) h
  constructor
  · refine g.grid_combine X' r (v:=fun i => (S.peel r (f i) (v i)).1) hg
      (g.body_set X' (fun i => (S.peel r (f i) (v i)).1.2) ?_)
    intro b
    exact g.body_additive X (fun y => (S.e y).1 b)
      (fun p q => by rw [S.add]; rfl) (fun i => (v i).2) hh
  · have hb : Knows m B s x (fun i => (bodyOrder (Layout.std rk) (f i)).loc
        (S.sky (f i) (v i).2).2) := by
      refine g.body_set (Layout.std rk) (fun i => (S.sky (f i) (v i).2).2) ?_
      intro c
      exact g.body_additive X (fun y => (S.e y).2 c)
        (fun p q => by rw [S.add]; rfl) (fun i => (v i).2) hh
    exact hb.cong (fun _ => rfl) (fun i => (flat_code rk (f i) _).symm)

/-- (fibre address, address inside the fibre) ↦ grid address. -/
lemma to_gridB (S : Split α β (Fin rk)) (X' : Layout β)
    (u : ∀ i, Grid β r (f i) × Bits (rk * f i))
    (h : Knows m B s x (fun i => (book X' r (f i)).loc (u i).1))
    (k : Knows m B s x (fun i => (bits (rk * f i)).loc (u i).2)) :
    Knows m B s x (fun i => (book X r (f i)).loc ((S.peel r (f i)).symm (u i))) := by
  obtain ⟨hg, hh⟩ := g.grid_fetch X' r (v:=fun i => (u i).1) h
  have hk : Knows m B s x (fun i => (bodyOrder (Layout.std rk) (f i)).loc
      ((flat rk (f i)).symm (u i).2)) :=
    k.cong (fun _ => rfl) (fun i => by rw [← flat_code, Equiv.apply_symm_apply])
  refine g.grid_combine X r (v:=fun i => (S.peel r (f i)).symm (u i)) hg
    (g.body_set X (fun i => ((S.peel r (f i)).symm (u i)).2) ?_)
  intro a
  exact g.body_additive₂ X' (Layout.std rk) (fun p => S.e.symm p a)
    (fun p q => by rw [S.symm_add]; rfl)
    (fun i => (u i).1.2) (fun i => (flat rk (f i)).symm (u i).2) hh hk

end Gear
end
end PowerSaving.RAM
end OAI

#print axioms OAI.PowerSaving.RAM.Gear.from_gridB
#print axioms OAI.PowerSaving.RAM.Gear.to_gridB
