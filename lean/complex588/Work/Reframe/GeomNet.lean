import Work.Reframe.Geom3
import Work.Reframe.SCert

/-!
# (key: reframe) The shared three-stage word F3 on the label space `H ⊕ (Bool × H)`: geometry

Instance of `Fold3S` (`Work.Reframe.SCert`) for ANY block circuit `X` whose input vectors are
the vectors of index `l` of orthonormal bases `base t` (`hbase`), with

* `Γ = Orth (L3 H)`, the orthogonal matrices of the label space (`m = 3h`);
* stage 1: window `g W_0`, base `0`; stage 2: window `d W_0`, base `d H'`, `H' = W_0'` minus the
  coordinate `l` (`qB false l`); stage 3: window `e W_0`, base `e (H' + H'')` (`q3 l`);
* `r1 t = ` right multiplication by `rho_t`, `r2 t = ` by `rho'_t` (`Orth.conjPerm`, `piF`);
* `s2⁻¹`, `s3⁻¹ = ` right multiplication by the block exchanges `W_0 ↔ W_0'`, `W_0 ↔ W_0''`
  (`Orth.colPerm (tauF c)`): the helper set `g` serves the windows `g W_0`, `g W_0'`, `g W_0''`;
* final blocks of the banks: rank `2` each.

`fold3s_bcert`: the resulting `BCert`, price `card Γ * (3 * X.cost φ + card T * (2 * bcost φ 2))`,
live roles `card Γ * (2 card T + card Sl)`.  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace RF
open Binary Matrix Finset RAM SS CB
noncomputable section

section Q
variable {H : Type} [Fintype H] [DecidableEq H]

/-- explicit instances for `Γ = Orth (L3 H)`: they keep the instance terms of the role types
small (the role type mentions `Γ` four times; the default search exceeds its size limit). -/
instance instFintypeOrthL3 : Fintype (Orth (L3 H)) := inferInstance

instance instDecEqOrthL3 : DecidableEq (Orth (L3 H)) := inferInstance

/-- the block `c` minus the coordinate `l`. -/
def qB (c : Bool) (l : H) : Finset (Bool × H) := ({c} : Finset Bool) ×ˢ (univ \ {l})

/-- both blocks minus the coordinate `l`. -/
def q3 (l : H) : Finset (Bool × H) := (univ : Finset Bool) ×ˢ (univ \ {l})

lemma mem_qB (c : Bool) (l : H) (b : Bool) (j : H) : (b, j) ∈ qB c l ↔ b = c ∧ j ≠ l := by
  unfold qB
  rw [Finset.mem_product]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨Finset.mem_singleton.mp h1,
      fun e => (Finset.mem_sdiff.mp h2).2 (Finset.mem_singleton.mpr e)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨Finset.mem_singleton.mpr h1,
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, fun e => h2 (Finset.mem_singleton.mp e)⟩⟩

lemma mem_q3 (l : H) (b : Bool) (j : H) : (b, j) ∈ q3 l ↔ j ≠ l := by
  unfold q3
  rw [Finset.mem_product]
  constructor
  · rintro ⟨_, h2⟩
    exact fun e => (Finset.mem_sdiff.mp h2).2 (Finset.mem_singleton.mpr e)
  · intro h2
    exact ⟨Finset.mem_univ b,
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, fun e => h2 (Finset.mem_singleton.mp e)⟩⟩

lemma card_q3 (l : H) : (q3 l).card = 2 * (Fintype.card H - 1) := by
  unfold q3
  rw [Finset.card_product, Finset.card_univ, Fintype.card_bool,
    Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Finset.card_singleton]

lemma blockOf_qB (c : Bool) (l : H) : BlockOf c l (qB c l) :=
  fun j => (mem_qB c l c j).trans ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩

lemma rest_qB (c : Bool) (l : H) : Rest c (qB c l) ∅ :=
  fun b j => ⟨fun h => absurd h (Finset.notMem_empty _),
    fun h => absurd ((mem_qB c l b j).mp h.2).1 h.1⟩

lemma blockOf_q3 (l : H) : BlockOf true l (q3 l) := fun j => mem_q3 l true j

lemma rest_q3 (l : H) : Rest true (q3 l) (qB false l) := by
  intro b j
  rw [mem_qB, mem_q3]
  cases b
  · exact ⟨fun h => ⟨fun e => Bool.noConfusion e, h.2⟩, fun h => ⟨rfl, h.2⟩⟩
  · exact ⟨fun h => Bool.noConfusion h.1, fun h => absurd rfl h.1⟩

lemma fb_one (q : Finset (Bool × H)) :
    Matrix.fromBlocks (1 : Matrix H H F) 0 0 (diagI q) = diagI (J univ q) := by
  rw [diagI_J, diagI_univ]

lemma fb_zero (q : Finset (Bool × H)) :
    Matrix.fromBlocks (0 : Matrix H H F) 0 0 (diagI q) = diagI (J ∅ q) := by
  rw [diagI_J, diagI_empty]

lemma J_split (q : Finset (Bool × H)) : J (univ : Finset H) q = J univ ∅ ∪ J ∅ q := by
  ext x
  rcases x with i | b
  · constructor
    · intro _
      exact Finset.mem_union_left _ (Finset.inl_mem_disjSum.mpr (Finset.mem_univ i))
    · intro _
      exact Finset.inl_mem_disjSum.mpr (Finset.mem_univ i)
  · constructor
    · intro h
      exact Finset.mem_union_right _ (Finset.inr_mem_disjSum.mpr (Finset.inr_mem_disjSum.mp h))
    · intro h
      rcases Finset.mem_union.mp h with h | h
      · exact absurd (Finset.inr_mem_disjSum.mp h) (Finset.notMem_empty b)
      · exact Finset.inr_mem_disjSum.mpr (Finset.inr_mem_disjSum.mp h)

lemma J_split_disj (q : Finset (Bool × H)) : Disjoint (J (univ : Finset H) ∅) (J ∅ q) :=
  Finset.disjoint_left.mpr (fun x h1 h2 => by
    rcases x with i | b
    · exact absurd (Finset.inl_mem_disjSum.mp h2) (Finset.notMem_empty i)
    · exact absurd (Finset.inr_mem_disjSum.mp h1) (Finset.notMem_empty b))

/-- `PhiQ d q 1 = (frame of the window d W_0) * (frame of the base d q)`. -/
lemma PhiQ_one (d : Orth (L3 H)) (q : Finset (Bool × H)) :
    PhiQ d q 1 = frameM (d.1 * diagI (J univ ∅) * d.1ᵀ) * PhiQ d q 0 := by
  unfold PhiQ
  rw [fb_one, fb_zero, J_split q, diagI_union _ _ (J_split_disj q),
    frameM_conj_add d.1 d.2 _ _ (diagI_orth _ _ (J_split_disj q))]

lemma PhiQ_zero_empty (d : Orth (L3 H)) : PhiQ d ∅ 0 = 1 := by
  unfold PhiQ
  rw [diagI_empty, Matrix.fromBlocks_zero, Matrix.mul_zero, Matrix.zero_mul, frameM_zero]

/-- the block frame map of the window `d W_0` on the base `d q`. -/
def fmapQ (hH : 1 ≤ Fintype.card H) (d : Orth (L3 H)) (q : Finset (Bool × H)) :
    XMap H (L3 H) where
  Φ := PhiQ d q
  up := fun A s t hst => by
    rw [PhiQ_eq, PhiQ_eq]
    have hm : 2 ≤ Fintype.card (L3 H) := by rw [card_L3]; omega
    refine (XReach.of_subset hm _ (Finset.disjSum_mono hst (Finset.Subset.refl q))).cast
      (fun φ => ?_)
    rw [J_sdiff_card]
    exact split_bcost φ (by rw [card_L3]; have := Finset.card_le_univ (t \ s); omega)
  down := fun A s t hst => by
    rw [PhiQ_eq, PhiQ_eq]
    have hm : 2 ≤ Fintype.card (L3 H) := by rw [card_L3]; omega
    refine (XReach.down_subset hm _ (Finset.disjSum_mono hst (Finset.Subset.refl q))).cast
      (fun φ => ?_)
    rw [J_sdiff_card]
    exact split_bcost φ (by rw [card_L3]; have := Finset.card_le_univ (t \ s); omega)

end Q

section Banks
variable {H : Type} [Fintype H] [DecidableEq H]
variable (base : OBase H) (l : H)

/-- right multiplication by `rho` (`c = false`) or `rho'` (`c = true`) of the triple whose basis
is `base` with pivot `l`. -/
def Rr (c : Bool) : Orth (L3 H) ≃ Orth (L3 H) :=
  Orth.conjPerm (blk base) (blk_orth base) (piF c l)

/-- the basis `g (base ⊕ std)`. -/
def BB (g : Orth (L3 H)) : OBase (L3 H) := ofCols (g.1 * blk base) (mul_orth g.2 (blk_orth base))

lemma PhiQ_BB (g : Orth (L3 H)) (q : Finset (Bool × H)) (s : Finset H) :
    PhiQ g q (base.mat s) = frame (BB base g) (J s q) := PhiQ_eq g q base s

lemma PhiQ_step (c : Bool) (g : Orth (L3 H)) (s s' : Finset H) (q q' : Finset (Bool × H))
    (hmap : (J s q).map (piF c l).toEmbedding = J s' q') :
    PhiQ (Rr base l c g) q (base.mat s) = PhiQ g q' (base.mat s') :=
  PhiQ_perm (Rr base l c g) g base (piF c l)
    (Orth.conjPerm_mul (blk base) (blk_orth base) (piF c l) g) s s' q q' hmap

/-- `X` leaves stage 1 where it enters stage 2. -/
lemma bank_x12 (g : Orth (L3 H)) :
    PhiQ g ∅ (base.mat univ) = PhiQ (Rr base l false g) (qB false l) (base.mat {l}) :=
  (PhiQ_step base l false g {l} univ (qB false l) ∅
    (map_piF_single false l (qB false l) ∅ (blockOf_qB false l) (rest_qB false l))).symm

/-- `Y` leaves stage 1 where it enters stage 2. -/
lemma bank_y12 (g : Orth (L3 H)) :
    PhiQ g ∅ (base.mat (univ \ {l})) = PhiQ (Rr base l false g) (qB false l) (base.mat ∅) :=
  (PhiQ_step base l false g ∅ (univ \ {l}) (qB false l) ∅
    (map_piF_empty false l (qB false l) ∅ (blockOf_qB false l) (rest_qB false l))).symm

/-- `X` leaves stage 2 where it enters stage 3. -/
lemma bank_x23 (g : Orth (L3 H)) :
    PhiQ (Rr base l false g) (qB false l) (base.mat univ)
      = PhiQ (Rr base l true g) (q3 l) (base.mat {l}) :=
  (PhiQ_step base l false g univ univ (qB false l) (qB false l)
    (map_piF_univ false l (qB false l) (blockOf_qB false l))).trans
  (PhiQ_step base l true g {l} univ (q3 l) (qB false l)
    (map_piF_single true l (q3 l) (qB false l) (blockOf_q3 l) (rest_q3 l))).symm

/-- `Y` leaves stage 2 where it enters stage 3. -/
lemma bank_y23 (g : Orth (L3 H)) :
    PhiQ (Rr base l false g) (qB false l) (base.mat (univ \ {l}))
      = PhiQ (Rr base l true g) (q3 l) (base.mat ∅) :=
  (PhiQ_step base l false g (univ \ {l}) (univ \ {l}) (qB false l) (qB false l)
    (map_piF_compl false l (qB false l) (blockOf_qB false l))).trans
  (PhiQ_step base l true g ∅ (univ \ {l}) (q3 l) (qB false l)
    (map_piF_empty true l (q3 l) (qB false l) (blockOf_q3 l) (rest_q3 l))).symm

/-- `X` after stage 3, in the basis `g (base ⊕ std)`. -/
lemma bank_x3 (g : Orth (L3 H)) :
    PhiQ (Rr base l true g) (q3 l) (base.mat univ) = frame (BB base g) (J univ (q3 l)) :=
  (PhiQ_step base l true g univ univ (q3 l) (q3 l)
    (map_piF_univ true l (q3 l) (blockOf_q3 l))).trans (PhiQ_BB base g (q3 l) univ)

/-- `Y` after stage 3, in the basis `g (base ⊕ std)`. -/
lemma bank_y3 (g : Orth (L3 H)) :
    PhiQ (Rr base l true g) (q3 l) (base.mat (univ \ {l}))
      = frame (BB base g) (J (univ \ {l}) (q3 l)) :=
  (PhiQ_step base l true g (univ \ {l}) (univ \ {l}) (q3 l) (q3 l)
    (map_piF_compl true l (q3 l) (blockOf_q3 l))).trans
  (PhiQ_BB base g (q3 l) (univ \ {l}))

end Banks

section Helpers
variable {n : Type} [Fintype n] [DecidableEq n]

/-- three orthogonal coordinate blocks that make up everything give the kernel. -/
lemma frameM_three (g : Orth n) (S0 S1 S2 : Finset n) (d10 : Disjoint S1 S0)
    (d2 : Disjoint S2 (S1 ∪ S0)) (hu : S2 ∪ (S1 ∪ S0) = univ) :
    frameM (g.1 * diagI S2 * g.1ᵀ) * (frameM (g.1 * diagI S1 * g.1ᵀ)
      * frameM (g.1 * diagI S0 * g.1ᵀ)) = kernel n := by
  rw [← frameM_conj_add g.1 g.2 (diagI S1) (diagI S0) (diagI_orth S1 S0 d10),
    ← diagI_union S1 S0 d10,
    ← frameM_conj_add g.1 g.2 (diagI S2) (diagI (S1 ∪ S0)) (diagI_orth S2 (S1 ∪ S0) d2),
    ← diagI_union S2 (S1 ∪ S0) d2, hu, diagI_univ, Matrix.mul_one, Orth.orth' g, frameM_one]

end Helpers

section Helpers3
variable {H : Type} [Fintype H] [DecidableEq H]

/-- the window frame of the invocation `g tau_c` is the frame of the block `c` in the basis
of the columns of `g`. -/
lemma W_tau (c : Bool) (g : Orth (L3 H)) :
    frameM ((Orth.colPerm (tauF c) g).1 * diagI (J univ ∅) * (Orth.colPerm (tauF c) g).1ᵀ)
      = frameM (g.1 * diagI (J ∅ (blockB c)) * g.1ᵀ) := by
  rw [Orth.colPerm_val, submatrix_diagI, map_tauF]

lemma blocks_disj10 :
    Disjoint (J (∅ : Finset H) (blockB false)) (J (univ : Finset H) ∅) :=
  Finset.disjoint_left.mpr (fun x h1 h2 => by
    rcases x with i | b
    · exact absurd (Finset.inl_mem_disjSum.mp h1) (Finset.notMem_empty i)
    · exact absurd (Finset.inr_mem_disjSum.mp h2) (Finset.notMem_empty b))

lemma blocks_disj2 :
    Disjoint (J (∅ : Finset H) (blockB true))
      (J (∅ : Finset H) (blockB false) ∪ J (univ : Finset H) ∅) :=
  Finset.disjoint_left.mpr (fun x h1 h2 => by
    rcases x with i | ⟨b, j⟩
    · exact absurd (Finset.inl_mem_disjSum.mp h1) (Finset.notMem_empty i)
    · have hb : b = true := (mem_blockB true b j).mp (Finset.inr_mem_disjSum.mp h1)
      rcases Finset.mem_union.mp h2 with h | h
      · have hb' : b = false := (mem_blockB false b j).mp (Finset.inr_mem_disjSum.mp h)
        rw [hb] at hb'
        exact Bool.noConfusion hb'
      · exact absurd (Finset.inr_mem_disjSum.mp h) (Finset.notMem_empty _))

lemma blocks_union :
    J (∅ : Finset H) (blockB true) ∪ (J (∅ : Finset H) (blockB false) ∪ J (univ : Finset H) ∅)
      = univ := by
  ext x
  constructor
  · intro _
    exact Finset.mem_univ x
  · intro _
    rcases x with i | ⟨b, j⟩
    · exact Finset.mem_union_right _ (Finset.mem_union_right _
        (Finset.inl_mem_disjSum.mpr (Finset.mem_univ i)))
    · cases b
      · exact Finset.mem_union_right _ (Finset.mem_union_left _
          (Finset.inr_mem_disjSum.mpr ((mem_blockB false false j).mpr rfl)))
      · exact Finset.mem_union_left _
          (Finset.inr_mem_disjSum.mpr ((mem_blockB true true j).mpr rfl))

/-- the three windows `g W_0`, `g W_0'`, `g W_0''` of the helper set `g` make up the kernel. -/
lemma helper_fin (g : Orth (L3 H)) :
    frameM ((Orth.colPerm (tauF true) g).1 * diagI (J univ ∅) * (Orth.colPerm (tauF true) g).1ᵀ)
      * (frameM ((Orth.colPerm (tauF false) g).1 * diagI (J univ ∅)
            * (Orth.colPerm (tauF false) g).1ᵀ) * PhiQ g ∅ 1) = kernel (L3 H) := by
  rw [W_tau, W_tau]
  unfold PhiQ
  rw [fb_one]
  exact frameM_three g _ _ _ blocks_disj10 blocks_disj2 blocks_union

lemma J_single (l : H) : J ({l} : Finset H) ∅ = {Sum.inl l} := by
  ext x
  rcases x with i | b
  · rw [Finset.inl_mem_disjSum, Finset.mem_singleton, Finset.mem_singleton]
    exact ⟨fun h => by rw [h], fun h => Sum.inl.inj h⟩
  · rw [Finset.inr_mem_disjSum, Finset.mem_singleton]
    exact ⟨fun h => absurd h (Finset.notMem_empty b), fun h => absurd h Sum.inr_ne_inl⟩

/-- the final block of `X` has rank 2. -/
lemma card_compl_X (hH : 1 ≤ Fintype.card H) (l : H) :
    ((univ : Finset (L3 H)) \ J univ (q3 l)).card = 2 := by
  have hsub : J (univ : Finset H) (q3 l) ⊆ univ := Finset.subset_univ _
  have h1 := Finset.card_sdiff_add_card_eq_card hsub
  have c1 : (J (univ : Finset H) (q3 l)).card = Fintype.card H + 2 * (Fintype.card H - 1) := by
    rw [Finset.card_disjSum, card_q3, Finset.card_univ]
  have c2 : (univ : Finset (L3 H)).card = 3 * Fintype.card H := by
    rw [Finset.card_univ, card_L3]
  rw [c1, c2] at h1
  omega

lemma J_compl_sub (l : H) :
    J ((univ : Finset H) \ {l}) (q3 l) ⊆ (univ : Finset (L3 H)) \ {Sum.inl l} := by
  intro x hx
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, fun e => ?_⟩
  rw [Finset.mem_singleton.mp e] at hx
  exact (Finset.mem_sdiff.mp (Finset.inl_mem_disjSum.mp hx)).2 (Finset.mem_singleton_self l)

/-- the final block of `Y` has rank 2. -/
lemma card_compl_Y (hH : 1 ≤ Fintype.card H) (l : H) :
    (((univ : Finset (L3 H)) \ {Sum.inl l}) \ J ((univ : Finset H) \ {l}) (q3 l)).card = 2 := by
  have h1 := Finset.card_sdiff_add_card_eq_card (J_compl_sub l)
  have c1 : (J ((univ : Finset H) \ {l}) (q3 l)).card
      = (Fintype.card H - 1) + 2 * (Fintype.card H - 1) := by
    rw [Finset.card_disjSum, card_q3, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, Finset.card_singleton]
  have c2 : ((univ : Finset (L3 H)) \ {Sum.inl l}).card = 3 * Fintype.card H - 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Finset.card_singleton, card_L3]
  rw [c1, c2] at h1
  omega

end Helpers3

section Net
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]
variable (X : XCircuit H T Sl C) (base : T → OBase H) (l : H)
  (hbase : ∀ t, X.K.tv t = (base t).v l) (hH : 1 ≤ Fintype.card H)
include hbase

lemma geom_x12 (g : Orth (L3 H)) (t : T) :
    PhiQ g ∅ 1 = PhiQ (Rr (base t) l false g) (qB false l) (tt (X.K.tv t)) := by
  have e := bank_x12 (base t) l g
  rw [OBase.mat_univ, mat_single, ← hbase t] at e
  exact e

lemma geom_y12 (g : Orth (L3 H)) (t : T) :
    PhiQ g ∅ (1 + tt (X.K.tv t)) = PhiQ (Rr (base t) l false g) (qB false l) 0 := by
  have e := bank_y12 (base t) l g
  rw [mat_compl_single, mat_empty, ← hbase t] at e
  exact e

lemma geom_x23 (g : Orth (L3 H)) (t : T) :
    PhiQ (Rr (base t) l false g) (qB false l) 1
      = PhiQ (Rr (base t) l true g) (q3 l) (tt (X.K.tv t)) := by
  have e := bank_x23 (base t) l g
  rw [OBase.mat_univ, mat_single, ← hbase t] at e
  exact e

lemma geom_y23 (g : Orth (L3 H)) (t : T) :
    PhiQ (Rr (base t) l false g) (qB false l) (1 + tt (X.K.tv t))
      = PhiQ (Rr (base t) l true g) (q3 l) 0 := by
  have e := bank_y23 (base t) l g
  rw [mat_compl_single, mat_empty, ← hbase t] at e
  exact e

include hH

/-- the last block of `X(g,t)`: rank 2, up to the kernel. -/
lemma geom_fX (g : Orth (L3 H)) (t : T) :
    XReach (PhiQ (Rr (base t) l true g) (q3 l) 1) (kernel (L3 H)) (fun φ => bcost φ 2) := by
  have e : PhiQ (Rr (base t) l true g) (q3 l) 1 = frame (BB (base t) g) (J univ (q3 l)) := by
    rw [← bank_x3 (base t) l g, OBase.mat_univ]
  have hm : 2 ≤ Fintype.card (L3 H) := by rw [card_L3]; omega
  rw [e, ← frame_univ (BB (base t) g)]
  refine (XReach.of_subset hm (BB (base t) g) (Finset.subset_univ _)).cast (fun φ => ?_)
  rw [card_compl_X hH l]
  exact split_bcost φ (by rw [card_L3]; omega)

/-- the last block of `Y(g,t)`: rank 2, up to `u^⊥`. -/
lemma geom_fY (g : Orth (L3 H)) (t : T) :
    XReach (PhiQ (Rr (base t) l true g) (q3 l) (1 + tt (X.K.tv t)))
      (frame (BB (base t) g) (univ \ {Sum.inl l})) (fun φ => bcost φ 2) := by
  have e : PhiQ (Rr (base t) l true g) (q3 l) (1 + tt (X.K.tv t))
      = frame (BB (base t) g) (J (univ \ {l}) (q3 l)) := by
    rw [← bank_y3 (base t) l g, mat_compl_single, hbase t]
  have hm : 2 ≤ Fintype.card (L3 H) := by rw [card_L3]; omega
  rw [e]
  refine (XReach.of_subset hm (BB (base t) g) (J_compl_sub l)).cast (fun φ => ?_)
  rw [card_compl_Y hH l]
  exact split_bcost φ (by rw [card_L3]; omega)

omit hH in
/-- terminal identity of the bank pair `(g,t)`. -/
lemma geom_term (g : Orth (L3 H)) (t : T) :
    kernel (L3 H) * PhiQ g ∅ (tt (X.K.tv t))
      = shift ((BB (base t) g).v (Sum.inl l)) * frame (BB (base t) g) (univ \ {Sum.inl l}) := by
  have e : PhiQ g ∅ (tt (X.K.tv t)) = frame (BB (base t) g) {Sum.inl l} := by
    rw [hbase t, ← mat_single, PhiQ_BB, J_single]
  rw [e]
  exact terminal_calc _ _

/-- **The shared three-stage word F3 as an instance of `Fold3S`.** -/
def geomNet : Fold3S H T Sl C (L3 H) (Orth (L3 H)) where
  X := X
  M1 := fun g => fmapQ hH g ∅
  M2 := fun d => fmapQ hH d (qB false l)
  M3 := fun d => fmapQ hH d (q3 l)
  r1 := fun t => Rr (base t) l false
  r2 := fun t => Rr (base t) l true
  s2 := (Orth.colPerm (tauF false)).symm
  s3 := (Orth.colPerm (tauF true)).symm
  N2 := fun d => unframeM (d.1 * Matrix.fromBlocks 0 0 0 (diagI (qB false l)) * d.1ᵀ)
  W2 := fun d => frameM (d.1 * diagI (J univ ∅) * d.1ᵀ)
  N3 := fun d => unframeM (d.1 * Matrix.fromBlocks 0 0 0 (diagI (q3 l)) * d.1ᵀ)
  W3 := fun d => frameM (d.1 * diagI (J univ ∅) * d.1ᵀ)
  u := fun g t => (BB (base t) g).v (Sum.inl l)
  YF := fun g t => frame (BB (base t) g) (univ \ {Sum.inl l})
  hm := by rw [card_L3]; omega
  eX := 2
  eY := 2
  inv1 := fun g t => ⟨unframeM (g.1 * Matrix.fromBlocks (tt (X.K.tv t)) 0 0 (diagI ∅) * g.1ᵀ),
    frameM_unframeM _⟩
  z1 := fun g => PhiQ_zero_empty g
  hN2 := fun d => frameM_unframeM _
  hW2 := fun d => PhiQ_one d (qB false l)
  hN3 := fun d => frameM_unframeM _
  hW3 := fun d => PhiQ_one d (q3 l)
  x12 := fun g t => geom_x12 X base l hbase g t
  y12 := fun g t => geom_y12 X base l hbase g t
  x23 := fun g t => geom_x23 X base l hbase g t
  y23 := fun g t => geom_y23 X base l hbase g t
  sfin := fun g => helper_fin g
  fX := fun g t => geom_fX X base l hbase hH g t
  fY := fun g t => geom_fY X base l hbase hH g t
  term := fun g t => geom_term X base l hbase g t

/-- **Block certificate of the shared three-stage word F3** for a block circuit whose input
vectors are the vectors of index `l` of orthonormal bases. -/
theorem fold3s_bcert_geom :
    BCert (L3 H) (Sum.inl : SLive (Orth (L3 H)) T Sl → SRole (Orth (L3 H)) T Sl C)
      (fun φ => (Fintype.card (Orth (L3 H)) : ℝ)
        * (3 * X.cost φ + (Fintype.card T : ℝ) * (bcost φ 2 + bcost φ 2))) :=
  fold3s_certificate (geomNet X base l hbase hH)

end Net

end
end RF
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.RF.fmapQ
#print axioms OAI.PowerSaving.RF.helper_fin
#print axioms OAI.PowerSaving.RF.geomNet
#print axioms OAI.PowerSaving.RF.fold3s_bcert_geom
