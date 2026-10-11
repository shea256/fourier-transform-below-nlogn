import Work.GFrame.Labels.StageBSem
import Work.GCert.Labels.Def

/-!
# (key: gx-labels) The canonical representative of a coded subspace (spec statement 1)

For a family `b : α → Space α` and a set `piv` of coordinates with `b p q = δ_pq` on `piv`
(`Ech`): `canon piv b : APerm α`, `x ↦ x + ∑ p ∈ piv, x p • (b p + eu p)` (an involution), and

    InSub (canon piv b) piv x ↔ x = ∑ p ∈ piv, x p • b p            (`insub_canon`).

For a CODE `c` (see `Work.GCert.Labels.Def`): `Good h c`, the label `lab h c : SLbl (Fin h)`
(digit `p` of the code is the basis vector of pivot `p`), `lab_dim`, `lab_mem`, `lab_bas`,
`lab_sub` (containment of the digits gives containment of the subspaces).

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GLab
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.GF Finset

section Canon
variable {α : Type} [Fintype α] [DecidableEq α]

/-- echelon condition: on the pivots the family is the identity -/
def Ech (piv : Finset α) (b : α → Space α) : Prop :=
  ∀ p ∈ piv, ∀ q ∈ piv, b p q = if p = q then 1 else 0

/-- the nilpotent part of the coordinate change -/
def nil (piv : Finset α) (b : α → Space α) (x : Space α) : Space α :=
  ∑ p ∈ piv, x p • (b p + eu p)

variable {piv : Finset α} {b : α → Space α}

lemma nil_piv (hb : Ech piv b) (x : Space α) {q : α} (hq : q ∈ piv) : nil piv b x q = 0 := by
  unfold nil
  rw [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro p hp
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, eu]
  rw [hb p hp q hq]
  by_cases h : p = q
  · rw [if_pos h, show (1 : F) + 1 = 0 from by decide, mul_zero]
  · rw [if_neg h, add_zero, mul_zero]

lemma nil_add (piv : Finset α) (b : α → Space α) (x y : Space α) :
    nil piv b (x + y) = nil piv b x + nil piv b y := by
  unfold nil
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun p _ => by rw [Pi.add_apply, add_smul])

lemma nil_congr (x y : Space α) (h : ∀ p ∈ piv, x p = y p) : nil piv b x = nil piv b y :=
  Finset.sum_congr rfl (fun p hp => by rw [h p hp])

/-- the canonical coordinate change -/
def cfun (piv : Finset α) (b : α → Space α) (x : Space α) : Space α := x + nil piv b x

lemma cfun_invol (hb : Ech piv b) (x : Space α) : cfun piv b (cfun piv b x) = x := by
  unfold cfun
  have e : nil piv b (x + nil piv b x) = nil piv b x :=
    nil_congr _ _ (fun p hp => by rw [Pi.add_apply, nil_piv hb x hp, add_zero])
  rw [e, add_assoc, binary_cancel, add_zero]

/-- **the canonical representative**: coordinates in the echelon basis `b` -/
def canon (piv : Finset α) (b : α → Space α) (hb : Ech piv b) : APerm α :=
  ⟨⟨cfun piv b, cfun piv b, cfun_invol hb, cfun_invol hb⟩, fun x y => by
    show cfun piv b (x + y) = cfun piv b x + cfun piv b y
    unfold cfun; rw [nil_add]; abel⟩

/-- **membership in the coded subspace** -/
theorem insub_canon (hb : Ech piv b) (x : Space α) :
    InSub (canon piv b hb) piv x ↔ x = ∑ p ∈ piv, x p • b p := by
  have key : cfun piv b x = (x + ∑ p ∈ piv, x p • b p) + ∑ p ∈ piv, x p • eu p := by
    unfold cfun nil
    rw [add_assoc, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl (fun p _ => smul_add _ _ _)
  have eup : ∀ k, (∑ p ∈ piv, x p • eu p) k = if k ∈ piv then x k else 0 := by
    intro k
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, eu, smul_eq_mul, mul_ite, mul_one, mul_zero]
    exact Finset.sum_ite_eq' piv k x
  constructor
  · intro h
    have z : x + ∑ p ∈ piv, x p • b p = 0 := by
      funext k
      have h2 := congrFun key k
      rw [Pi.add_apply, eup] at h2
      by_cases hk : k ∈ piv
      · have h1 : cfun piv b x k = x k := by
          unfold cfun; rw [Pi.add_apply, nil_piv hb x hk, add_zero]
        rw [if_pos hk, h1] at h2
        exact (add_eq_right.mp h2.symm)
      · have h1 : cfun piv b x k = 0 := h k hk
        rw [if_neg hk, h1, add_zero] at h2
        exact h2.symm
    have e := congrArg (fun y => y + ∑ p ∈ piv, x p • b p) z
    simp only [add_assoc, binary_cancel, add_zero, zero_add] at e
    exact e
  · intro h k hk
    show cfun piv b x k = 0
    rw [key, Pi.add_apply, eup, if_neg hk, add_zero, ← h, binary_cancel]; rfl

lemma aperm_zero (G : APerm α) : G.π 0 = 0 := by
  have h := G.add 0 0
  rw [add_zero] at h
  exact add_left_cancel (a := G.π 0) (by rw [add_zero]; exact h.symm)

lemma mem_zero (U : SLbl α) : U.Mem 0 := fun k _ => by rw [aperm_zero]; rfl

lemma mem_add (U : SLbl α) {x y : Space α} (hx : U.Mem x) (hy : U.Mem y) : U.Mem (x + y) :=
  fun k hk => by
    rw [U.G.add]
    show U.G.π x k + U.G.π y k = 0
    rw [hx k hk, hy k hk, add_zero]

lemma mem_smul (U : SLbl α) (a : F) {x : Space α} (hx : U.Mem x) : U.Mem (a • x) := by
  have ha : a = 0 ∨ a = 1 := by revert a; decide
  rcases ha with rfl | rfl
  · rw [zero_smul]; exact mem_zero U
  · rw [one_smul]; exact hx

end Canon

/-! ## codes -/

/-- the field element of a bit -/
def bF (b : Bool) : F := if b then 1 else 0

/-- digit `p` (width `h`) of `P` as a vector -/
def dv (h P p : Nat) : Space (Fin h) := fun q => bF (P.testBit (h * p + q.val))

/-- the packed basis of a code -/
def cP (h c : Nat) : Nat := c >>> (8 + h)
/-- the dimension field of a code -/
def cdim (c : Nat) : Nat := c &&& 255

/-- basis vector of pivot `p` (zero if `p` is not a pivot) -/
def bas (h P : Nat) (p : Fin h) : Space (Fin h) := dv h P p.val
/-- the pivots -/
def pivs (h P : Nat) : Finset (Fin h) := univ.filter fun p => bas h P p ≠ 0

/-- `c` is the code of an echelon basis -/
structure Good (h c : Nat) : Prop where
  ech : Ech (pivs h (cP h c)) (bas h (cP h c))
  dim : (pivs h (cP h c)).card = cdim c
  bnd : cP h c < 2 ^ (h * h)

open Classical in
/-- **the label of a code** -/
noncomputable def lab (h c : Nat) : SLbl (Fin h) :=
  if hg : Good h c then ⟨canon _ _ hg.ech, pivs h (cP h c)⟩ else ⟨apId _, ∅⟩

variable {h c : Nat}

theorem lab_dim (hg : Good h c) : (lab h c).dim = cdim c := by
  unfold lab; rw [dif_pos hg]; exact hg.dim

theorem lab_mem (hg : Good h c) (x : Space (Fin h)) :
    (lab h c).Mem x ↔ x = ∑ p ∈ pivs h (cP h c), x p • bas h (cP h c) p := by
  unfold lab; rw [dif_pos hg]; exact insub_canon hg.ech x

/-- every digit of a code lies in its subspace -/
theorem lab_bas (hg : Good h c) (p : Fin h) : (lab h c).Mem (bas h (cP h c) p) := by
  by_cases hp : p ∈ pivs h (cP h c)
  · rw [lab_mem hg]
    have e : ∑ q ∈ pivs h (cP h c), bas h (cP h c) p q • bas h (cP h c) q
        = ∑ q ∈ pivs h (cP h c), if p = q then bas h (cP h c) q else 0 :=
      Finset.sum_congr rfl (fun q hq => by rw [hg.ech p hp q hq]; split <;> simp)
    rw [e, Finset.sum_ite_eq, if_pos hp]
  · have e : bas h (cP h c) p = 0 := by
      by_contra hne
      exact hp (mem_filter.mpr ⟨mem_univ _, hne⟩)
    rw [e]; exact mem_zero _

/-- **containment from the digits** -/
theorem lab_sub {ca cb : Nat} (ha : Good h ca)
    (H : ∀ p : Fin h, (lab h cb).Mem (bas h (cP h ca) p)) :
    ∀ x, (lab h ca).Mem x → (lab h cb).Mem x := by
  intro x hx
  rw [(lab_mem ha x).mp hx]
  exact Finset.sum_induction _ (fun y => (lab h cb).Mem y) (fun _ _ => mem_add _) (mem_zero _)
    (fun p _ => mem_smul _ _ (H p))

end GLab

#print axioms GLab.insub_canon
#print axioms GLab.lab_bas
#print axioms GLab.lab_sub
