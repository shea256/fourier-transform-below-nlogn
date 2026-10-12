import Work.BridgeGeom.Blocks
import Work.Combine.XG

/-!
# (key: bridge-geom) Stages, bank frames and climbs on the label space `H ⊕ (B × H)`

The part of `Work.Reframe.GeomNet` that does not mention a network, for ANY finite block index
`B` and ANY set `bs : Finset B` of base blocks.

* `qS bs l`       the blocks `bs` minus the coordinate `l` of each (index set of a base);
* `wS bs`         the blocks `bs` (index set of windows);
* `fmapB hB hH d q`   the block frame map `XMap H (LB B H)` with `Φ = PhiB d q`;
                  `PhiB_one` (window frame times base frame), `PhiB_zero_empty`;
* `RrB base l c`  right multiplication by `rho^(c)` of the triple with basis `base`, pivot `l`;
* `BBB base g`    the ONE orthonormal basis `g (base ⊕ std)` in which every bank frame of the
                  class `(g, base)` is a coordinate frame:
    - `bank_inX`  `PhiB (RrB c g) (qS (insert c bs) l) (base.mat {l}) = frame BBB (JB univ (qS bs l))`
    - `bank_inY`  `PhiB (RrB c g) (qS (insert c bs) l) (base.mat ∅) = frame BBB (JB (univ \ {l}) (qS bs l))`
    - `bank_outX` `PhiB (RrB c g) (qS bs l) (base.mat univ) = frame BBB (JB univ (qS bs l))`      (`c ∈ bs`)
    - `bank_outY` `PhiB (RrB c g) (qS bs l) (base.mat (univ \ {l})) = frame BBB (JB (univ \ {l}) (qS bs l))`
* climbs inside `BBB`, each ONE block (`climb_X0 .. climb_Yend`), with their ranks;
* the window frames of a helper set and their product (`W_tauB`, `win_step`, `win_all`).

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace BG
open Binary Matrix Finset RAM SS CB RF
noncomputable section

section Q
variable {B H : Type} [Fintype B] [DecidableEq B] [Fintype H] [DecidableEq H]

/-- explicit instances for `Γ = Orth (LB B H)` (they keep the instance terms of role types small). -/
instance instFintypeOrthLB : Fintype (Orth (LB B H)) := inferInstance

instance instDecEqOrthLB : DecidableEq (Orth (LB B H)) := inferInstance

lemma two_le_card_LB (hB : 1 ≤ Fintype.card B) (hH : 1 ≤ Fintype.card H) :
    2 ≤ Fintype.card (LB B H) := by
  have h1 : 1 * 1 ≤ Fintype.card B * Fintype.card H := Nat.mul_le_mul hB hH
  simp only [Fintype.card_sum, Fintype.card_prod]
  omega

lemma card_lt_LB (hB : 1 ≤ Fintype.card B) (hH : 1 ≤ Fintype.card H) (s : Finset H) :
    s.card < Fintype.card (LB B H) := by
  have h1 : 1 * 1 ≤ Fintype.card B * Fintype.card H := Nat.mul_le_mul hB hH
  have h2 := Finset.card_le_univ s
  simp only [Fintype.card_sum, Fintype.card_prod]
  omega

/-- the blocks `bs` minus the coordinate `l` of each. -/
def qS (bs : Finset B) (l : H) : Finset (B × H) := bs ×ˢ (univ \ {l})

lemma mem_qS (bs : Finset B) (l : H) (b : B) (j : H) : (b, j) ∈ qS bs l ↔ b ∈ bs ∧ j ≠ l := by
  unfold qS
  rw [Finset.mem_product]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun e => (Finset.mem_sdiff.mp h2).2 (Finset.mem_singleton.mpr e)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, fun e => h2 (Finset.mem_singleton.mp e)⟩⟩

lemma qS_empty (l : H) : qS (∅ : Finset B) l = ∅ := by
  unfold qS
  exact Finset.empty_product _

lemma card_qS (bs : Finset B) (l : H) : (qS bs l).card = bs.card * (Fintype.card H - 1) := by
  unfold qS
  rw [Finset.card_product, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    Finset.card_singleton]

lemma qS_mono {bs bs' : Finset B} (h : bs ⊆ bs') (l : H) : qS bs l ⊆ qS bs' l :=
  Finset.product_subset_product h (Finset.Subset.refl _)

lemma blockOf_qS (bs : Finset B) (c : B) (hc : c ∈ bs) (l : H) : BlockOfB c l (qS bs l) :=
  fun j => (mem_qS bs l c j).trans ⟨fun h => h.2, fun h => ⟨hc, h⟩⟩

lemma rest_qS (bs : Finset B) (c : B) (hc : c ∉ bs) (l : H) :
    RestB c (qS (insert c bs) l) (qS bs l) := by
  intro b j
  rw [mem_qS, mem_qS, Finset.mem_insert]
  constructor
  · rintro ⟨hb, hj⟩
    exact ⟨fun e => hc (by rw [← e]; exact hb), Or.inr hb, hj⟩
  · rintro ⟨hne, hb, hj⟩
    rcases hb with hb | hb
    · exact absurd hb hne
    · exact ⟨hb, hj⟩

lemma fbB_one (q : Finset (B × H)) :
    Matrix.fromBlocks (1 : Matrix H H F) 0 0 (diagI q) = diagI (JB univ q) := by
  rw [diagI_JB, diagI_univ]

lemma fbB_zero (q : Finset (B × H)) :
    Matrix.fromBlocks (0 : Matrix H H F) 0 0 (diagI q) = diagI (JB ∅ q) := by
  rw [diagI_JB, diagI_empty]

lemma JB_split (q : Finset (B × H)) : JB (univ : Finset H) q = JB univ ∅ ∪ JB ∅ q := by
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

lemma JB_split_disj (q : Finset (B × H)) : Disjoint (JB (univ : Finset H) ∅) (JB ∅ q) :=
  Finset.disjoint_left.mpr (fun x h1 h2 => by
    rcases x with i | b
    · exact absurd (Finset.inl_mem_disjSum.mp h2) (Finset.notMem_empty i)
    · exact absurd (Finset.inr_mem_disjSum.mp h1) (Finset.notMem_empty b))

/-- `PhiB d q 1 = (frame of the window d W_0) * (frame of the base d q)`. -/
lemma PhiB_one (d : Orth (LB B H)) (q : Finset (B × H)) :
    PhiB d q 1 = frameM (d.1 * diagI (JB univ ∅) * d.1ᵀ) * PhiB d q 0 := by
  unfold PhiB
  rw [fbB_one, fbB_zero, JB_split q, diagI_union _ _ (JB_split_disj q),
    frameM_conj_add d.1 d.2 _ _ (diagI_orth _ _ (JB_split_disj q))]

lemma PhiB_zero_empty (d : Orth (LB B H)) : PhiB d ∅ 0 = 1 := by
  unfold PhiB
  rw [diagI_empty, Matrix.fromBlocks_zero, Matrix.mul_zero, Matrix.zero_mul, frameM_zero]

/-- the block frame map of the window `d W_0` on the base `d q`. -/
def fmapB (hB : 1 ≤ Fintype.card B) (hH : 1 ≤ Fintype.card H) (d : Orth (LB B H))
    (q : Finset (B × H)) : XMap H (LB B H) where
  Φ := PhiB d q
  up := fun A s t hst => by
    rw [PhiB_eq, PhiB_eq]
    refine (XReach.of_subset (two_le_card_LB hB hH) _
      (Finset.disjSum_mono hst (Finset.Subset.refl q))).cast (fun φ => ?_)
    rw [JB_sdiff_card]
    exact split_bcost φ (card_lt_LB hB hH _)
  down := fun A s t hst => by
    rw [PhiB_eq, PhiB_eq]
    refine (XReach.down_subset (two_le_card_LB hB hH) _
      (Finset.disjSum_mono hst (Finset.Subset.refl q))).cast (fun φ => ?_)
    rw [JB_sdiff_card]
    exact split_bcost φ (card_lt_LB hB hH _)

lemma fmapB_Φ (hB : 1 ≤ Fintype.card B) (hH : 1 ≤ Fintype.card H) (d : Orth (LB B H))
    (q : Finset (B × H)) (P : Matrix H H F) : (fmapB hB hH d q).Φ P = PhiB d q P := rfl

end Q

section Banks
variable {B H : Type} [Fintype B] [DecidableEq B] [Fintype H] [DecidableEq H]
variable (base : OBase H) (l : H)

/-- right multiplication by `rho^(c)` of the triple whose basis is `base` with pivot `l`. -/
def RrB (c : B) : Orth (LB B H) ≃ Orth (LB B H) :=
  Orth.conjPerm (blkB B base) (blkB_orth base) (piB c l)

/-- the basis `g (base ⊕ std)`. -/
def BBB (g : Orth (LB B H)) : OBase (LB B H) :=
  ofCols (g.1 * blkB B base) (mul_orth g.2 (blkB_orth base))

lemma PhiB_BBB (g : Orth (LB B H)) (q : Finset (B × H)) (s : Finset H) :
    PhiB g q (base.mat s) = frame (BBB base g) (JB s q) := PhiB_eq g q base s

lemma PhiB_step (c : B) (g : Orth (LB B H)) (s s' : Finset H) (q q' : Finset (B × H))
    (hmap : (JB s q).map (piB c l).toEmbedding = JB s' q') :
    PhiB (RrB base l c g) q (base.mat s) = PhiB g q' (base.mat s') :=
  PhiB_perm (RrB base l c g) g base (piB c l)
    (Orth.conjPerm_mul (blkB B base) (blkB_orth base) (piB c l) g) s s' q q' hmap

/-- `X` ENTERS the stage of the block `c` (base: the blocks `insert c bs`) with the coordinate
frame `W_0 + bs` of the basis `g (base ⊕ std)`. -/
lemma bank_inX (bs : Finset B) (c : B) (hc : c ∉ bs) (g : Orth (LB B H)) :
    PhiB (RrB base l c g) (qS (insert c bs) l) (base.mat {l})
      = frame (BBB base g) (JB univ (qS bs l)) :=
  (PhiB_step base l c g {l} univ (qS (insert c bs) l) (qS bs l)
    (map_piB_single c l (qS (insert c bs) l) (qS bs l)
      (blockOf_qS (insert c bs) c (Finset.mem_insert_self c bs) l) (rest_qS bs c hc l))).trans
  (PhiB_BBB base g (qS bs l) univ)

/-- `Y` ENTERS the stage of the block `c` with the coordinate frame `(W_0 ∩ u^⊥) + bs`. -/
lemma bank_inY (bs : Finset B) (c : B) (hc : c ∉ bs) (g : Orth (LB B H)) :
    PhiB (RrB base l c g) (qS (insert c bs) l) (base.mat ∅)
      = frame (BBB base g) (JB (univ \ {l}) (qS bs l)) :=
  (PhiB_step base l c g ∅ (univ \ {l}) (qS (insert c bs) l) (qS bs l)
    (map_piB_empty c l (qS (insert c bs) l) (qS bs l)
      (blockOf_qS (insert c bs) c (Finset.mem_insert_self c bs) l) (rest_qS bs c hc l))).trans
  (PhiB_BBB base g (qS bs l) (univ \ {l}))

/-- `X` LEAVES the stage of the block `c` (base: the blocks `bs ∋ c`) with the coordinate frame
`W_0 + bs`. -/
lemma bank_outX (bs : Finset B) (c : B) (hc : c ∈ bs) (g : Orth (LB B H)) :
    PhiB (RrB base l c g) (qS bs l) (base.mat univ) = frame (BBB base g) (JB univ (qS bs l)) :=
  (PhiB_step base l c g univ univ (qS bs l) (qS bs l)
    (map_piB_univ c l (qS bs l) (blockOf_qS bs c hc l))).trans (PhiB_BBB base g (qS bs l) univ)

/-- `Y` LEAVES the stage of the block `c` with the coordinate frame `(W_0 ∩ u^⊥) + bs`. -/
lemma bank_outY (bs : Finset B) (c : B) (hc : c ∈ bs) (g : Orth (LB B H)) :
    PhiB (RrB base l c g) (qS bs l) (base.mat (univ \ {l}))
      = frame (BBB base g) (JB (univ \ {l}) (qS bs l)) :=
  (PhiB_step base l c g (univ \ {l}) (univ \ {l}) (qS bs l) (qS bs l)
    (map_piB_compl c l (qS bs l) (blockOf_qS bs c hc l))).trans
  (PhiB_BBB base g (qS bs l) (univ \ {l}))

/-- consecutive stages (blocks `c ∈ bs`, then `c' ∉ bs`): `X` leaves where it enters. -/
lemma bank_xx (bs : Finset B) (c c' : B) (hc : c ∈ bs) (hc' : c' ∉ bs) (g : Orth (LB B H)) :
    PhiB (RrB base l c g) (qS bs l) (base.mat univ)
      = PhiB (RrB base l c' g) (qS (insert c' bs) l) (base.mat {l}) :=
  (bank_outX base l bs c hc g).trans (bank_inX base l bs c' hc' g).symm

/-- consecutive stages: `Y` leaves where it enters. -/
lemma bank_yy (bs : Finset B) (c c' : B) (hc : c ∈ bs) (hc' : c' ∉ bs) (g : Orth (LB B H)) :
    PhiB (RrB base l c g) (qS bs l) (base.mat (univ \ {l}))
      = PhiB (RrB base l c' g) (qS (insert c' bs) l) (base.mat ∅) :=
  (bank_outY base l bs c hc g).trans (bank_inY base l bs c' hc' g).symm

/-- stage 0 to the first block `c`: `X` leaves where it enters. -/
lemma bank_x0 (c : B) (g : Orth (LB B H)) :
    PhiB g ∅ (base.mat univ) = PhiB (RrB base l c g) (qS {c} l) (base.mat {l}) := by
  have e := bank_inX base l ∅ c (Finset.notMem_empty c) g
  rw [qS_empty, Finset.insert_empty] at e
  rw [e]
  exact PhiB_BBB base g ∅ univ

/-- stage 0 to the first block `c`: `Y` leaves where it enters. -/
lemma bank_y0 (c : B) (g : Orth (LB B H)) :
    PhiB g ∅ (base.mat (univ \ {l})) = PhiB (RrB base l c g) (qS {c} l) (base.mat ∅) := by
  have e := bank_inY base l ∅ c (Finset.notMem_empty c) g
  rw [qS_empty, Finset.insert_empty] at e
  rw [e]
  exact PhiB_BBB base g ∅ (univ \ {l})

end Banks

section Reach
variable {n : Type} [Fintype n] [DecidableEq n]

/-- one block inside one basis; the lower index set is not empty. -/
lemma reach_of_pos (hm : 2 ≤ Fintype.card n) (A : OBase n) {s t : Finset n} (h : s ⊆ t)
    (k : ℕ) (hk : k + s.card = t.card) (hs : 1 ≤ s.card) :
    XReach (frame A s) (frame A t) (fun φ => bcost φ k) := by
  refine (XReach.of_subset hm A h).cast (fun φ => ?_)
  have h1 := Finset.card_sdiff_add_card_eq_card h
  have h2 := Finset.card_le_univ t
  have e : (t \ s).card = k := by omega
  rw [e]
  exact split_bcost φ (by omega)

/-- one block inside one basis; the upper index set is not everything. -/
lemma reach_of_lt (hm : 2 ≤ Fintype.card n) (A : OBase n) {s t : Finset n} (h : s ⊆ t)
    (k : ℕ) (hk : k + s.card = t.card) (ht : t.card < Fintype.card n) :
    XReach (frame A s) (frame A t) (fun φ => bcost φ k) := by
  refine (XReach.of_subset hm A h).cast (fun φ => ?_)
  have h1 := Finset.card_sdiff_add_card_eq_card h
  have e : (t \ s).card = k := by omega
  rw [e]
  exact split_bcost φ (by omega)

end Reach

section Climbs
variable {B H : Type} [Fintype B] [DecidableEq B] [Fintype H] [DecidableEq H]

lemma card_JB (s : Finset H) (q : Finset (B × H)) : (JB s q).card = s.card + q.card :=
  Finset.card_disjSum s q

lemma card_compl_single (l : H) : ((univ : Finset H) \ {l}).card = Fintype.card H - 1 := by
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Finset.card_singleton]

lemma card_univ_LB :
    (univ : Finset (LB B H)).card = Fintype.card H + Fintype.card B * Fintype.card H := by
  rw [Finset.card_univ]
  simp only [Fintype.card_sum, Fintype.card_prod]

lemma card_JBX (bs : Finset B) (l : H) :
    (JB (univ : Finset H) (qS bs l)).card
      = Fintype.card H + bs.card * (Fintype.card H - 1) := by
  rw [card_JB, card_qS, Finset.card_univ]

lemma card_JBY (bs : Finset B) (l : H) :
    (JB ((univ : Finset H) \ {l}) (qS bs l)).card
      = (Fintype.card H - 1) + bs.card * (Fintype.card H - 1) := by
  rw [card_JB, card_qS, card_compl_single]

/-- the index set of a `Y` frame never contains the pivot of block 0. -/
lemma JBY_sub (l : H) (q : Finset (B × H)) :
    JB ((univ : Finset H) \ {l}) q ⊆ (univ : Finset (LB B H)) \ {Sum.inl l} := by
  intro x hx
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, fun e => ?_⟩
  rw [Finset.mem_singleton.mp e] at hx
  exact (Finset.mem_sdiff.mp (Finset.inl_mem_disjSum.mp hx)).2 (Finset.mem_singleton_self l)

lemma card_JBY_lt (hH : 1 ≤ Fintype.card H) (l : H) (q : Finset (B × H)) :
    (JB ((univ : Finset H) \ {l}) q).card < Fintype.card (LB B H) := by
  have h1 := Finset.card_le_card (JBY_sub l q)
  have h2 : ((univ : Finset (LB B H)) \ {Sum.inl l}).card = Fintype.card (LB B H) - 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Finset.card_singleton]
  have h3 : 1 ≤ Fintype.card (LB B H) := Fintype.card_pos_iff.mpr ⟨Sum.inl l⟩
  omega

lemma card_JBX_pos (l : H) (q : Finset (B × H)) : 1 ≤ (JB (univ : Finset H) q).card :=
  Finset.card_pos.mpr ⟨Sum.inl l, Finset.inl_mem_disjSum.mpr (Finset.mem_univ l)⟩

lemma JB_single (l : H) : JB ({l} : Finset H) (∅ : Finset (B × H)) = {Sum.inl l} := by
  ext x
  rcases x with i | b
  · rw [Finset.inl_mem_disjSum, Finset.mem_singleton, Finset.mem_singleton]
    exact ⟨fun h => by rw [h], fun h => Sum.inl.inj h⟩
  · rw [Finset.inr_mem_disjSum, Finset.mem_singleton]
    exact ⟨fun h => absurd h (Finset.notMem_empty b), fun h => absurd h Sum.inr_ne_inl⟩

variable (hB : 1 ≤ Fintype.card B) (hH : 1 ≤ Fintype.card H) (A : OBase (LB B H)) (l : H)
include hB hH

/-- `X` from its line up to `W_0 + bs`: ONE block. -/
lemma climb_X0 (bs : Finset B) (k : ℕ)
    (hk : k + 1 = Fintype.card H + bs.card * (Fintype.card H - 1)) :
    XReach (frame A (JB {l} ∅)) (frame A (JB univ (qS bs l))) (fun φ => bcost φ k) := by
  refine reach_of_pos (two_le_card_LB hB hH) A
    (Finset.disjSum_mono (Finset.subset_univ _) (Finset.empty_subset _)) k ?_ ?_
  · rw [card_JBX, card_JB, Finset.card_singleton, Finset.card_empty]
    omega
  · exact Finset.card_pos.mpr ⟨Sum.inl l, Finset.inl_mem_disjSum.mpr (Finset.mem_singleton_self l)⟩

/-- `Y` from `0` up to `(W_0 ∩ u^⊥) + bs`: ONE block. -/
lemma climb_Y0 (bs : Finset B) (k : ℕ)
    (hk : k = (Fintype.card H - 1) + bs.card * (Fintype.card H - 1)) :
    XReach (frame A (JB ∅ ∅)) (frame A (JB (univ \ {l}) (qS bs l))) (fun φ => bcost φ k) := by
  refine reach_of_lt (two_le_card_LB hB hH) A
    (Finset.disjSum_mono (Finset.empty_subset _) (Finset.empty_subset _)) k ?_
    (card_JBY_lt hH l _)
  rw [card_JBY, card_JB, Finset.card_empty, Finset.card_empty]
  omega

/-- `X` from `W_0 + bs` up to `W_0 + bs'`: ONE block. -/
lemma climb_X (bs bs' : Finset B) (h : bs ⊆ bs') (k : ℕ)
    (hk : k + bs.card * (Fintype.card H - 1) = bs'.card * (Fintype.card H - 1)) :
    XReach (frame A (JB univ (qS bs l))) (frame A (JB univ (qS bs' l)))
      (fun φ => bcost φ k) := by
  refine reach_of_pos (two_le_card_LB hB hH) A
    (Finset.disjSum_mono (Finset.Subset.refl _) (qS_mono h l)) k ?_ (card_JBX_pos l _)
  rw [card_JBX, card_JBX]
  omega

/-- `Y` from `(W_0 ∩ u^⊥) + bs` up to `(W_0 ∩ u^⊥) + bs'`: ONE block. -/
lemma climb_Y (bs bs' : Finset B) (h : bs ⊆ bs') (k : ℕ)
    (hk : k + bs.card * (Fintype.card H - 1) = bs'.card * (Fintype.card H - 1)) :
    XReach (frame A (JB (univ \ {l}) (qS bs l))) (frame A (JB (univ \ {l}) (qS bs' l)))
      (fun φ => bcost φ k) := by
  refine reach_of_lt (two_le_card_LB hB hH) A
    (Finset.disjSum_mono (Finset.Subset.refl _) (qS_mono h l)) k ?_ (card_JBY_lt hH l _)
  rw [card_JBY, card_JBY]
  omega

/-- `X` from `W_0 + bs` up to everything (the kernel): ONE block. -/
lemma climb_Xend (bs : Finset B) (k : ℕ)
    (hk : k + bs.card * (Fintype.card H - 1) = Fintype.card B * Fintype.card H) :
    XReach (frame A (JB univ (qS bs l))) (kernel (LB B H)) (fun φ => bcost φ k) := by
  rw [← frame_univ A]
  refine reach_of_pos (two_le_card_LB hB hH) A (Finset.subset_univ _) k ?_ (card_JBX_pos l _)
  rw [card_JBX, card_univ_LB]
  omega

/-- `Y` from `(W_0 ∩ u^⊥) + bs` up to `u^⊥`: ONE block. -/
lemma climb_Yend (bs : Finset B) (k : ℕ)
    (hk : k + bs.card * (Fintype.card H - 1) = Fintype.card B * Fintype.card H) :
    XReach (frame A (JB (univ \ {l}) (qS bs l))) (frame A (univ \ {Sum.inl l}))
      (fun φ => bcost φ k) := by
  have h3 : (univ : Finset (LB B H)).card = Fintype.card (LB B H) := Finset.card_univ
  have h4 : 1 ≤ Fintype.card (LB B H) := Fintype.card_pos_iff.mpr ⟨Sum.inl l⟩
  have h2 : ((univ : Finset (LB B H)) \ {Sum.inl l}).card
      = Fintype.card H + Fintype.card B * Fintype.card H - 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), card_univ_LB, Finset.card_singleton]
  refine reach_of_lt (two_le_card_LB hB hH) A (JBY_sub l _) k ?_ ?_
  · rw [card_JBY, h2]
    omega
  · have h5 := card_univ_LB (B := B) (H := H)
    rw [h2]
    omega

end Climbs

section Windows
variable {B H : Type} [Fintype B] [DecidableEq B] [Fintype H] [DecidableEq H]

/-- the blocks `bs`, whole. -/
def wS (bs : Finset B) : Finset (B × H) := bs ×ˢ univ

lemma mem_wS (bs : Finset B) (b : B) (j : H) : (b, j) ∈ wS (H := H) bs ↔ b ∈ bs := by
  unfold wS
  rw [Finset.mem_product]
  exact ⟨fun h => h.1, fun h => ⟨h, Finset.mem_univ j⟩⟩

lemma blockS_eq (c : B) : blockS (H := H) c = wS {c} := by
  ext ⟨b, j⟩
  rw [mem_blockS, mem_wS, Finset.mem_singleton]

lemma wS_empty : wS (H := H) (∅ : Finset B) = ∅ := by
  unfold wS
  exact Finset.empty_product _

/-- the window frame of the invocation `g tau_c` is the frame of the block `c` in the basis of
the columns of `g`. -/
lemma W_tauB (c : B) (g : Orth (LB B H)) :
    frameM ((Orth.colPerm (tauB c) g).1 * diagI (JB univ ∅) * (Orth.colPerm (tauB c) g).1ᵀ)
      = frameM (g.1 * diagI (JB ∅ (wS {c})) * g.1ᵀ) := by
  rw [Orth.colPerm_val, submatrix_diagI, map_tauB, blockS_eq]

lemma win_disj (c : B) (bs : Finset B) (hc : c ∉ bs) (s : Finset H) :
    Disjoint (JB (∅ : Finset H) (wS {c})) (JB s (wS bs)) :=
  Finset.disjoint_left.mpr (fun x h1 h2 => by
    rcases x with i | ⟨b, j⟩
    · exact absurd (Finset.inl_mem_disjSum.mp h1) (Finset.notMem_empty i)
    · have hb : b = c :=
        Finset.mem_singleton.mp ((mem_wS {c} b j).mp (Finset.inr_mem_disjSum.mp h1))
      have hb' : b ∈ bs := (mem_wS bs b j).mp (Finset.inr_mem_disjSum.mp h2)
      exact hc (by rw [← hb]; exact hb'))

lemma win_union (c : B) (bs : Finset B) (s : Finset H) :
    JB (∅ : Finset H) (wS {c}) ∪ JB s (wS bs) = JB s (wS (insert c bs)) := by
  ext x
  rcases x with i | ⟨b, j⟩
  · rw [Finset.mem_union, Finset.inl_mem_disjSum, Finset.inl_mem_disjSum,
      Finset.inl_mem_disjSum]
    exact ⟨fun h => h.elim (fun h' => absurd h' (Finset.notMem_empty i)) id, fun h => Or.inr h⟩
  · rw [Finset.mem_union, Finset.inr_mem_disjSum, Finset.inr_mem_disjSum,
      Finset.inr_mem_disjSum, mem_wS, mem_wS, mem_wS, Finset.mem_singleton, Finset.mem_insert]

/-- one more window: the frames of disjoint blocks multiply. -/
lemma win_step (g : Orth (LB B H)) (c : B) (bs : Finset B) (hc : c ∉ bs) (s : Finset H) :
    frameM (g.1 * diagI (JB ∅ (wS {c})) * g.1ᵀ) * frameM (g.1 * diagI (JB s (wS bs)) * g.1ᵀ)
      = frameM (g.1 * diagI (JB s (wS (insert c bs))) * g.1ᵀ) := by
  rw [← frameM_conj_add g.1 g.2 _ _ (diagI_orth _ _ (win_disj c bs hc s)),
    ← diagI_union _ _ (win_disj c bs hc s), win_union]

/-- the window of stage 0. -/
lemma win_start (g : Orth (LB B H)) :
    PhiB g ∅ 1 = frameM (g.1 * diagI (JB univ (wS ∅)) * g.1ᵀ) := by
  unfold PhiB
  rw [fbB_one, wS_empty]

lemma JB_univ_wS : JB (univ : Finset H) (wS (univ : Finset B)) = univ := by
  ext x
  rcases x with i | ⟨b, j⟩
  · exact ⟨fun _ => Finset.mem_univ _, fun _ => Finset.inl_mem_disjSum.mpr (Finset.mem_univ i)⟩
  · exact ⟨fun _ => Finset.mem_univ _,
      fun _ => Finset.inr_mem_disjSum.mpr ((mem_wS univ b j).mpr (Finset.mem_univ b))⟩

/-- all the windows of a helper set together: the kernel. -/
lemma win_all (g : Orth (LB B H)) :
    frameM (g.1 * diagI (JB univ (wS univ)) * g.1ᵀ) = kernel (LB B H) := by
  rw [JB_univ_wS, diagI_univ, Matrix.mul_one, Orth.orth' g, frameM_one]

/-- terminal identity of a bank pair of the class `(g, base)`. -/
lemma class_term (base : OBase H) (l : H) (g : Orth (LB B H)) :
    kernel (LB B H) * PhiB g ∅ (tt (base.v l))
      = shift ((BBB base g).v (Sum.inl l)) * frame (BBB base g) (univ \ {Sum.inl l}) := by
  have e : PhiB g ∅ (tt (base.v l)) = frame (BBB base g) {Sum.inl l} := by
    rw [← mat_single, PhiB_BBB, JB_single]
  rw [e]
  exact terminal_calc _ _

end Windows

/-! ## The same facts in the form a network asks for: projectors `tt u`, `1`, `1 + tt u`, `0` of
the line `u = base.v l` of the class. -/

section ClassT
variable {B H : Type} [Fintype B] [DecidableEq B] [Fintype H] [DecidableEq H]
variable (base : OBase H) (l : H)

/-- stage 0 to the stage of the first block `c`: `X`. -/
lemma bankT_x0 (c : B) (g : Orth (LB B H)) :
    PhiB g ∅ 1 = PhiB (RrB base l c g) (qS {c} l) (tt (base.v l)) := by
  have e := bank_x0 base l c g
  rw [OBase.mat_univ, mat_single] at e
  exact e

/-- stage 0 to the stage of the first block `c`: `Y`. -/
lemma bankT_y0 (c : B) (g : Orth (LB B H)) :
    PhiB g ∅ (1 + tt (base.v l)) = PhiB (RrB base l c g) (qS {c} l) 0 := by
  have e := bank_y0 base l c g
  rw [mat_compl_single, mat_empty] at e
  exact e

/-- the stage of `c ∈ bs` to the stage of `c' ∉ bs`: `X`. -/
lemma bankT_xx (bs : Finset B) (c c' : B) (hc : c ∈ bs) (hc' : c' ∉ bs) (g : Orth (LB B H)) :
    PhiB (RrB base l c g) (qS bs l) 1
      = PhiB (RrB base l c' g) (qS (insert c' bs) l) (tt (base.v l)) := by
  have e := bank_xx base l bs c c' hc hc' g
  rw [OBase.mat_univ, mat_single] at e
  exact e

/-- the stage of `c ∈ bs` to the stage of `c' ∉ bs`: `Y`. -/
lemma bankT_yy (bs : Finset B) (c c' : B) (hc : c ∈ bs) (hc' : c' ∉ bs) (g : Orth (LB B H)) :
    PhiB (RrB base l c g) (qS bs l) (1 + tt (base.v l))
      = PhiB (RrB base l c' g) (qS (insert c' bs) l) 0 := by
  have e := bank_yy base l bs c c' hc hc' g
  rw [mat_compl_single, mat_empty] at e
  exact e

/-- frames of the class in the basis `BBB base g`: start of `X`, start of `Y`, `X` and `Y`
after the stage of `c ∈ bs`. -/
lemma classT_X0 (g : Orth (LB B H)) :
    PhiB g ∅ (tt (base.v l)) = frame (BBB base g) (JB {l} ∅) := by
  have e := PhiB_BBB base g ∅ {l}
  rw [mat_single] at e
  exact e

lemma classT_Y0 (g : Orth (LB B H)) : PhiB g ∅ 0 = frame (BBB base g) (JB ∅ ∅) := by
  have e := PhiB_BBB base g ∅ ∅
  rw [mat_empty] at e
  exact e

lemma classT_X (bs : Finset B) (c : B) (hc : c ∈ bs) (g : Orth (LB B H)) :
    PhiB (RrB base l c g) (qS bs l) 1 = frame (BBB base g) (JB univ (qS bs l)) := by
  have e := bank_outX base l bs c hc g
  rw [OBase.mat_univ] at e
  exact e

lemma classT_Y (bs : Finset B) (c : B) (hc : c ∈ bs) (g : Orth (LB B H)) :
    PhiB (RrB base l c g) (qS bs l) (1 + tt (base.v l))
      = frame (BBB base g) (JB (univ \ {l}) (qS bs l)) := by
  have e := bank_outY base l bs c hc g
  rw [mat_compl_single] at e
  exact e

variable (hB : 1 ≤ Fintype.card B) (hH : 1 ≤ Fintype.card H)
include hB hH

/-- IDLE CLIMB of an `X` role over stage 0 and the stage of the first block `c`: ONE block from
its line to the frame its twin has after that stage. -/
lemma idle_X0 (c : B) (g : Orth (LB B H)) (k : ℕ)
    (hk : k + 1 = Fintype.card H + (Fintype.card H - 1)) :
    XReach (PhiB g ∅ (tt (base.v l))) (PhiB (RrB base l c g) (qS {c} l) 1)
      (fun φ => bcost φ k) := by
  rw [classT_X0, classT_X base l {c} c (Finset.mem_singleton_self c) g]
  exact climb_X0 hB hH (BBB base g) l {c} k (by rw [Finset.card_singleton, one_mul]; exact hk)

/-- the same for the `Y` role. -/
lemma idle_Y0 (c : B) (g : Orth (LB B H)) (k : ℕ)
    (hk : k = (Fintype.card H - 1) + (Fintype.card H - 1)) :
    XReach (PhiB g ∅ 0) (PhiB (RrB base l c g) (qS {c} l) (1 + tt (base.v l)))
      (fun φ => bcost φ k) := by
  rw [classT_Y0, classT_Y base l {c} c (Finset.mem_singleton_self c) g]
  exact climb_Y0 hB hH (BBB base g) l {c} k (by rw [Finset.card_singleton, one_mul]; exact hk)

/-- IDLE CLIMB of an `X` role from the frame after the stage of `c ∈ bs` to the end (all later
stages and the last moves): ONE block. -/
lemma idle_Xend (bs : Finset B) (c : B) (hc : c ∈ bs) (g : Orth (LB B H)) (k : ℕ)
    (hk : k + bs.card * (Fintype.card H - 1) = Fintype.card B * Fintype.card H) :
    XReach (PhiB (RrB base l c g) (qS bs l) 1) (kernel (LB B H)) (fun φ => bcost φ k) := by
  rw [classT_X base l bs c hc g]
  exact climb_Xend hB hH (BBB base g) l bs k hk

/-- the same for the `Y` role, up to `u^⊥`. -/
lemma idle_Yend (bs : Finset B) (c : B) (hc : c ∈ bs) (g : Orth (LB B H)) (k : ℕ)
    (hk : k + bs.card * (Fintype.card H - 1) = Fintype.card B * Fintype.card H) :
    XReach (PhiB (RrB base l c g) (qS bs l) (1 + tt (base.v l)))
      (frame (BBB base g) (univ \ {Sum.inl l})) (fun φ => bcost φ k) := by
  rw [classT_Y base l bs c hc g]
  exact climb_Yend hB hH (BBB base g) l bs k hk

/-- IDLE CLIMB over the stages of the blocks `bs' \ bs` (`c ∈ bs`, `c' ∈ bs'`): ONE block. -/
lemma idle_X (bs bs' : Finset B) (h : bs ⊆ bs') (c c' : B) (hc : c ∈ bs) (hc' : c' ∈ bs')
    (g : Orth (LB B H)) (k : ℕ)
    (hk : k + bs.card * (Fintype.card H - 1) = bs'.card * (Fintype.card H - 1)) :
    XReach (PhiB (RrB base l c g) (qS bs l) 1) (PhiB (RrB base l c' g) (qS bs' l) 1)
      (fun φ => bcost φ k) := by
  rw [classT_X base l bs c hc g, classT_X base l bs' c' hc' g]
  exact climb_X hB hH (BBB base g) l bs bs' h k hk

lemma idle_Y (bs bs' : Finset B) (h : bs ⊆ bs') (c c' : B) (hc : c ∈ bs) (hc' : c' ∈ bs')
    (g : Orth (LB B H)) (k : ℕ)
    (hk : k + bs.card * (Fintype.card H - 1) = bs'.card * (Fintype.card H - 1)) :
    XReach (PhiB (RrB base l c g) (qS bs l) (1 + tt (base.v l)))
      (PhiB (RrB base l c' g) (qS bs' l) (1 + tt (base.v l))) (fun φ => bcost φ k) := by
  rw [classT_Y base l bs c hc g, classT_Y base l bs' c' hc' g]
  exact climb_Y hB hH (BBB base g) l bs bs' h k hk

end ClassT
end
end BG
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.BG.fmapB
#print axioms OAI.PowerSaving.BG.bank_xx
#print axioms OAI.PowerSaving.BG.bank_yy
#print axioms OAI.PowerSaving.BG.climb_X0
#print axioms OAI.PowerSaving.BG.climb_Yend
#print axioms OAI.PowerSaving.BG.win_step
#print axioms OAI.PowerSaving.BG.win_all
#print axioms OAI.PowerSaving.BG.class_term
