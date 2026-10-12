import Work.BridgeC.Blocks
import Work.Combine.XG

/-!
# (key: bridge-c) Stages, bank frames and climbs on the compressed label space `H ⊕ (B × H')`

Port of `Work.BridgeGeom.Stage` (namespace `BG`) to `LC B H l` (`Work.BridgeC.Blocks`), without the slot
windows (`wS`, `W_tauB`, `win_*`): the banks of PR #377 are in `Work.BridgeC.Bank`.  Substitutions:
`LB B H → LC B H l`, `qS bs l → qC bs = bs ×ˢ univ`, `piB c l → piC l c`, `BlockOfB c l → BlockOfC c`; the ranks
of the blocks other than block 0 are `card H - 1`.

* `qC bs`        the blocks `bs` (index set of a base);
* `fmapC hB hH d q`   the block frame map `XMap H (LC B H l)` with `Φ = PhiC d q`;
                 `PhiC_one` (window frame times base frame), `PhiC_zero_empty`;
* `RrC base l c` right multiplication by `rho^(c)` of the triple with basis `base`, pivot `l`;
* `BBC base g`   the ONE orthonormal basis `g (base ⊕ std)` in which every bank frame of the class
                 `(g, base)` is a coordinate frame (`bank_inX/inY/outX/outY`, `bank_xx/yy/x0/y0`);
* climbs inside `BBC`, each ONE block (`climb_X0 .. climb_Yend`), with their ranks;
* `class_term`, `bankT_*`, `classT_*`, `idle_*`: the same facts in the form a network asks for.

Hypotheses: `hB : 1 ≤ card B`, `hH : 2 ≤ card H` (with `card H = 1` the blocks other than block 0 are empty).
Credit: Jacob Sussman's `Work.BridgeGeom.Stage` (Apache-2.0), proof by proof; layout of PR #377 (jacklightChen).
No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace BC
open Binary Matrix Finset RAM SS CB RF
noncomputable section

section Q
variable {B H : Type} [Fintype B] [DecidableEq B] [Fintype H] [DecidableEq H] {l : H}

/-- explicit instances for `Γ = Orth (LC B H l)` (they keep the instance terms of role types small). -/
instance instFintypeOrthLC : Fintype (Orth (LC B H l)) := inferInstance

instance instDecEqOrthLC : DecidableEq (Orth (LC B H l)) := inferInstance

lemma two_le_card_LC (hB : 1 ≤ Fintype.card B) (hH : 2 ≤ Fintype.card H) :
    2 ≤ Fintype.card (LC B H l) := by
  rw [card_LC]
  omega

lemma card_lt_LC (hB : 1 ≤ Fintype.card B) (hH : 2 ≤ Fintype.card H) (s : Finset H) :
    s.card < Fintype.card (LC B H l) := by
  have h1 : 1 * 1 ≤ Fintype.card B * (Fintype.card H - 1) := Nat.mul_le_mul hB (by omega)
  have h2 := Finset.card_le_univ s
  rw [card_LC]
  omega

/-- the blocks `bs`, whole (in `LC` the pivot coordinates are already gone). -/
def qC (bs : Finset B) : Finset (B × Hp H l) := bs ×ˢ univ

lemma mem_qC (bs : Finset B) (b : B) (j : Hp H l) : (b, j) ∈ qC bs ↔ b ∈ bs := by
  unfold qC
  rw [Finset.mem_product]
  exact ⟨fun h => h.1, fun h => ⟨h, Finset.mem_univ j⟩⟩

lemma qC_empty : qC (l := l) (∅ : Finset B) = ∅ := by
  unfold qC
  exact Finset.empty_product _

lemma card_qC (bs : Finset B) : (qC (l := l) bs).card = bs.card * (Fintype.card H - 1) := by
  unfold qC
  rw [Finset.card_product, Finset.card_univ, card_Hp]

lemma qC_mono {bs bs' : Finset B} (h : bs ⊆ bs') : qC (l := l) bs ⊆ qC bs' :=
  Finset.product_subset_product h (Finset.Subset.refl _)

lemma blockOf_qC (bs : Finset B) (c : B) (hc : c ∈ bs) : BlockOfC (l := l) c (qC bs) :=
  fun j => (mem_qC bs c j).mpr hc

lemma rest_qC (bs : Finset B) (c : B) (hc : c ∉ bs) :
    RestC (l := l) c (qC (insert c bs)) (qC bs) := by
  intro b j
  rw [mem_qC, mem_qC, Finset.mem_insert]
  constructor
  · intro hb
    exact ⟨fun e => hc (by rw [← e]; exact hb), Or.inr hb⟩
  · rintro ⟨hne, hb⟩
    rcases hb with hb | hb
    · exact absurd hb hne
    · exact hb

lemma fbC_one (q : Finset (B × Hp H l)) :
    Matrix.fromBlocks (1 : Matrix H H F) 0 0 (diagI q) = diagI (JC univ q) := by
  rw [diagI_JC, diagI_univ]

lemma fbC_zero (q : Finset (B × Hp H l)) :
    Matrix.fromBlocks (0 : Matrix H H F) 0 0 (diagI q) = diagI (JC ∅ q) := by
  rw [diagI_JC, diagI_empty]

lemma JC_split (q : Finset (B × Hp H l)) : JC (univ : Finset H) q = JC univ ∅ ∪ JC ∅ q := by
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

lemma JC_split_disj (q : Finset (B × Hp H l)) : Disjoint (JC (univ : Finset H) ∅) (JC ∅ q) :=
  Finset.disjoint_left.mpr (fun x h1 h2 => by
    rcases x with i | b
    · exact absurd (Finset.inl_mem_disjSum.mp h2) (Finset.notMem_empty i)
    · exact absurd (Finset.inr_mem_disjSum.mp h1) (Finset.notMem_empty b))

/-- `PhiC d q 1 = (frame of the window d W_0) * (frame of the base d q)`. -/
lemma PhiC_one (d : Orth (LC B H l)) (q : Finset (B × Hp H l)) :
    PhiC d q 1 = frameM (d.1 * diagI (JC univ ∅) * d.1ᵀ) * PhiC d q 0 := by
  unfold PhiC
  rw [fbC_one, fbC_zero, JC_split q, diagI_union _ _ (JC_split_disj q),
    frameM_conj_add d.1 d.2 _ _ (diagI_orth _ _ (JC_split_disj q))]

lemma PhiC_zero_empty (d : Orth (LC B H l)) : PhiC d ∅ 0 = 1 := by
  unfold PhiC
  rw [diagI_empty, Matrix.fromBlocks_zero, Matrix.mul_zero, Matrix.zero_mul, frameM_zero]

/-- the block frame map of the window `d W_0` on the base `d q`. -/
def fmapC (hB : 1 ≤ Fintype.card B) (hH : 2 ≤ Fintype.card H) (d : Orth (LC B H l))
    (q : Finset (B × Hp H l)) : XMap H (LC B H l) where
  Φ := PhiC d q
  up := fun A s t hst => by
    rw [PhiC_eq, PhiC_eq]
    refine (XReach.of_subset (two_le_card_LC hB hH) _
      (Finset.disjSum_mono hst (Finset.Subset.refl q))).cast (fun φ => ?_)
    rw [JC_sdiff_card]
    exact split_bcost φ (card_lt_LC hB hH _)
  down := fun A s t hst => by
    rw [PhiC_eq, PhiC_eq]
    refine (XReach.down_subset (two_le_card_LC hB hH) _
      (Finset.disjSum_mono hst (Finset.Subset.refl q))).cast (fun φ => ?_)
    rw [JC_sdiff_card]
    exact split_bcost φ (card_lt_LC hB hH _)

lemma fmapC_Φ (hB : 1 ≤ Fintype.card B) (hH : 2 ≤ Fintype.card H) (d : Orth (LC B H l))
    (q : Finset (B × Hp H l)) (P : Matrix H H F) : (fmapC hB hH d q).Φ P = PhiC d q P := rfl

end Q

section Banks
variable {B H : Type} [Fintype B] [DecidableEq B] [Fintype H] [DecidableEq H]
variable (base : OBase H) (l : H)

/-- right multiplication by `rho^(c)` of the triple whose basis is `base` with pivot `l`. -/
def RrC (c : B) : Orth (LC B H l) ≃ Orth (LC B H l) :=
  Orth.conjPerm (blkC B l base) (blkC_orth base) (piC l c)

/-- the basis `g (base ⊕ std)`. -/
def BBC (g : Orth (LC B H l)) : OBase (LC B H l) :=
  ofCols (g.1 * blkC B l base) (mul_orth g.2 (blkC_orth base))

lemma PhiC_BBC (g : Orth (LC B H l)) (q : Finset (B × Hp H l)) (s : Finset H) :
    PhiC g q (base.mat s) = frame (BBC base l g) (JC s q) := PhiC_eq g q base s

lemma PhiC_step (c : B) (g : Orth (LC B H l)) (s s' : Finset H) (q q' : Finset (B × Hp H l))
    (hmap : (JC s q).map (piC l c).toEmbedding = JC s' q') :
    PhiC (RrC base l c g) q (base.mat s) = PhiC g q' (base.mat s') :=
  PhiC_perm (RrC base l c g) g base (piC l c)
    (Orth.conjPerm_mul (blkC B l base) (blkC_orth base) (piC l c) g) s s' q q' hmap

/-- `X` ENTERS the stage of the block `c` (base: the blocks `insert c bs`) with the coordinate
frame `W_0 + bs` of the basis `g (base ⊕ std)`. -/
lemma bank_inX (bs : Finset B) (c : B) (hc : c ∉ bs) (g : Orth (LC B H l)) :
    PhiC (RrC base l c g) (qC (insert c bs)) (base.mat {l})
      = frame (BBC base l g) (JC univ (qC bs)) :=
  (PhiC_step base l c g {l} univ (qC (insert c bs)) (qC bs)
    (map_piC_single l c (qC (insert c bs)) (qC bs)
      (blockOf_qC (insert c bs) c (Finset.mem_insert_self c bs)) (rest_qC bs c hc))).trans
  (PhiC_BBC base l g (qC bs) univ)

/-- `Y` ENTERS the stage of the block `c` with the coordinate frame `(W_0 ∩ u^⊥) + bs`. -/
lemma bank_inY (bs : Finset B) (c : B) (hc : c ∉ bs) (g : Orth (LC B H l)) :
    PhiC (RrC base l c g) (qC (insert c bs)) (base.mat ∅)
      = frame (BBC base l g) (JC (univ \ {l}) (qC bs)) :=
  (PhiC_step base l c g ∅ (univ \ {l}) (qC (insert c bs)) (qC bs)
    (map_piC_empty l c (qC (insert c bs)) (qC bs)
      (blockOf_qC (insert c bs) c (Finset.mem_insert_self c bs)) (rest_qC bs c hc))).trans
  (PhiC_BBC base l g (qC bs) (univ \ {l}))

/-- `X` LEAVES the stage of the block `c` (base: the blocks `bs ∋ c`) with the coordinate frame
`W_0 + bs`. -/
lemma bank_outX (bs : Finset B) (c : B) (hc : c ∈ bs) (g : Orth (LC B H l)) :
    PhiC (RrC base l c g) (qC bs) (base.mat univ) = frame (BBC base l g) (JC univ (qC bs)) :=
  (PhiC_step base l c g univ univ (qC bs) (qC bs)
    (map_piC_univ l c (qC bs) (blockOf_qC bs c hc))).trans (PhiC_BBC base l g (qC bs) univ)

/-- `Y` LEAVES the stage of the block `c` with the coordinate frame `(W_0 ∩ u^⊥) + bs`. -/
lemma bank_outY (bs : Finset B) (c : B) (hc : c ∈ bs) (g : Orth (LC B H l)) :
    PhiC (RrC base l c g) (qC bs) (base.mat (univ \ {l}))
      = frame (BBC base l g) (JC (univ \ {l}) (qC bs)) :=
  (PhiC_step base l c g (univ \ {l}) (univ \ {l}) (qC bs) (qC bs)
    (map_piC_compl l c (qC bs) (blockOf_qC bs c hc))).trans
  (PhiC_BBC base l g (qC bs) (univ \ {l}))

/-- consecutive stages (blocks `c ∈ bs`, then `c' ∉ bs`): `X` leaves where it enters. -/
lemma bank_xx (bs : Finset B) (c c' : B) (hc : c ∈ bs) (hc' : c' ∉ bs) (g : Orth (LC B H l)) :
    PhiC (RrC base l c g) (qC bs) (base.mat univ)
      = PhiC (RrC base l c' g) (qC (insert c' bs)) (base.mat {l}) :=
  (bank_outX base l bs c hc g).trans (bank_inX base l bs c' hc' g).symm

/-- consecutive stages: `Y` leaves where it enters. -/
lemma bank_yy (bs : Finset B) (c c' : B) (hc : c ∈ bs) (hc' : c' ∉ bs) (g : Orth (LC B H l)) :
    PhiC (RrC base l c g) (qC bs) (base.mat (univ \ {l}))
      = PhiC (RrC base l c' g) (qC (insert c' bs)) (base.mat ∅) :=
  (bank_outY base l bs c hc g).trans (bank_inY base l bs c' hc' g).symm

/-- stage 0 to the first block `c`: `X` leaves where it enters. -/
lemma bank_x0 (c : B) (g : Orth (LC B H l)) :
    PhiC g ∅ (base.mat univ) = PhiC (RrC base l c g) (qC {c}) (base.mat {l}) := by
  have e := bank_inX base l ∅ c (Finset.notMem_empty c) g
  rw [qC_empty, Finset.insert_empty] at e
  rw [e]
  exact PhiC_BBC base l g ∅ univ

/-- stage 0 to the first block `c`: `Y` leaves where it enters. -/
lemma bank_y0 (c : B) (g : Orth (LC B H l)) :
    PhiC g ∅ (base.mat (univ \ {l})) = PhiC (RrC base l c g) (qC {c}) (base.mat ∅) := by
  have e := bank_inY base l ∅ c (Finset.notMem_empty c) g
  rw [qC_empty, Finset.insert_empty] at e
  rw [e]
  exact PhiC_BBC base l g ∅ (univ \ {l})

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

lemma card_JC {l : H} (s : Finset H) (q : Finset (B × Hp H l)) : (JC s q).card = s.card + q.card :=
  Finset.card_disjSum s q

lemma card_compl_single (l : H) : ((univ : Finset H) \ {l}).card = Fintype.card H - 1 := by
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Finset.card_singleton]

lemma card_univ_LC (l : H) :
    (univ : Finset (LC B H l)).card = Fintype.card H + Fintype.card B * (Fintype.card H - 1) := by
  rw [Finset.card_univ, card_LC]

lemma card_JCX (bs : Finset B) (l : H) :
    (JC (univ : Finset H) (qC (l := l) bs)).card
      = Fintype.card H + bs.card * (Fintype.card H - 1) := by
  rw [card_JC, card_qC, Finset.card_univ]

lemma card_JCY (bs : Finset B) (l : H) :
    (JC ((univ : Finset H) \ {l}) (qC (l := l) bs)).card
      = (Fintype.card H - 1) + bs.card * (Fintype.card H - 1) := by
  rw [card_JC, card_qC, card_compl_single]

/-- the index set of a `Y` frame never contains the pivot of block 0. -/
lemma JCY_sub (l : H) (q : Finset (B × Hp H l)) :
    JC ((univ : Finset H) \ {l}) q ⊆ (univ : Finset (LC B H l)) \ {Sum.inl l} := by
  intro x hx
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, fun e => ?_⟩
  rw [Finset.mem_singleton.mp e] at hx
  exact (Finset.mem_sdiff.mp (Finset.inl_mem_disjSum.mp hx)).2 (Finset.mem_singleton_self l)

lemma card_JCY_lt (l : H) (q : Finset (B × Hp H l)) :
    (JC ((univ : Finset H) \ {l}) q).card < Fintype.card (LC B H l) := by
  have h1 := Finset.card_le_card (JCY_sub l q)
  have h2 : ((univ : Finset (LC B H l)) \ {Sum.inl l}).card = Fintype.card (LC B H l) - 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Finset.card_singleton]
  have h3 : 1 ≤ Fintype.card (LC B H l) := Fintype.card_pos_iff.mpr ⟨Sum.inl l⟩
  omega

lemma card_JCX_pos (l : H) (q : Finset (B × Hp H l)) : 1 ≤ (JC (univ : Finset H) q).card :=
  Finset.card_pos.mpr ⟨Sum.inl l, Finset.inl_mem_disjSum.mpr (Finset.mem_univ l)⟩

lemma JC_single (l : H) : JC ({l} : Finset H) (∅ : Finset (B × Hp H l)) = {Sum.inl l} := by
  ext x
  rcases x with i | b
  · rw [Finset.inl_mem_disjSum, Finset.mem_singleton, Finset.mem_singleton]
    exact ⟨fun h => by rw [h], fun h => Sum.inl.inj h⟩
  · rw [Finset.inr_mem_disjSum, Finset.mem_singleton]
    exact ⟨fun h => absurd h (Finset.notMem_empty b), fun h => absurd h Sum.inr_ne_inl⟩

variable (hB : 1 ≤ Fintype.card B) (hH : 2 ≤ Fintype.card H) (l : H) (A : OBase (LC B H l))
include hB hH

/-- `X` from its line up to `W_0 + bs`: ONE block. -/
lemma climb_X0 (bs : Finset B) (k : ℕ)
    (hk : k + 1 = Fintype.card H + bs.card * (Fintype.card H - 1)) :
    XReach (frame A (JC {l} ∅)) (frame A (JC univ (qC bs))) (fun φ => bcost φ k) := by
  refine reach_of_pos (two_le_card_LC hB hH) A
    (Finset.disjSum_mono (Finset.subset_univ _) (Finset.empty_subset _)) k ?_ ?_
  · rw [card_JCX, card_JC, Finset.card_singleton, Finset.card_empty]
    omega
  · exact Finset.card_pos.mpr ⟨Sum.inl l, Finset.inl_mem_disjSum.mpr (Finset.mem_singleton_self l)⟩

/-- `Y` from `0` up to `(W_0 ∩ u^⊥) + bs`: ONE block. -/
lemma climb_Y0 (bs : Finset B) (k : ℕ)
    (hk : k = (Fintype.card H - 1) + bs.card * (Fintype.card H - 1)) :
    XReach (frame A (JC ∅ ∅)) (frame A (JC (univ \ {l}) (qC bs))) (fun φ => bcost φ k) := by
  refine reach_of_lt (two_le_card_LC hB hH) A
    (Finset.disjSum_mono (Finset.empty_subset _) (Finset.empty_subset _)) k ?_
    (card_JCY_lt l _)
  rw [card_JCY, card_JC, Finset.card_empty, Finset.card_empty]
  omega

/-- `X` from `W_0 + bs` up to `W_0 + bs'`: ONE block. -/
lemma climb_X (bs bs' : Finset B) (h : bs ⊆ bs') (k : ℕ)
    (hk : k + bs.card * (Fintype.card H - 1) = bs'.card * (Fintype.card H - 1)) :
    XReach (frame A (JC univ (qC bs))) (frame A (JC univ (qC bs')))
      (fun φ => bcost φ k) := by
  refine reach_of_pos (two_le_card_LC hB hH) A
    (Finset.disjSum_mono (Finset.Subset.refl _) (qC_mono h)) k ?_ (card_JCX_pos l _)
  rw [card_JCX, card_JCX]
  omega

/-- `Y` from `(W_0 ∩ u^⊥) + bs` up to `(W_0 ∩ u^⊥) + bs'`: ONE block. -/
lemma climb_Y (bs bs' : Finset B) (h : bs ⊆ bs') (k : ℕ)
    (hk : k + bs.card * (Fintype.card H - 1) = bs'.card * (Fintype.card H - 1)) :
    XReach (frame A (JC (univ \ {l}) (qC bs))) (frame A (JC (univ \ {l}) (qC bs')))
      (fun φ => bcost φ k) := by
  refine reach_of_lt (two_le_card_LC hB hH) A
    (Finset.disjSum_mono (Finset.Subset.refl _) (qC_mono h)) k ?_ (card_JCY_lt l _)
  rw [card_JCY, card_JCY]
  omega

/-- `X` from `W_0 + bs` up to everything (the kernel): ONE block. -/
lemma climb_Xend (bs : Finset B) (k : ℕ)
    (hk : k + bs.card * (Fintype.card H - 1) = Fintype.card B * (Fintype.card H - 1)) :
    XReach (frame A (JC univ (qC bs))) (kernel (LC B H l)) (fun φ => bcost φ k) := by
  rw [← frame_univ A]
  refine reach_of_pos (two_le_card_LC hB hH) A (Finset.subset_univ _) k ?_ (card_JCX_pos l _)
  rw [card_JCX, card_univ_LC]
  omega

/-- `Y` from `(W_0 ∩ u^⊥) + bs` up to `u^⊥`: ONE block. -/
lemma climb_Yend (bs : Finset B) (k : ℕ)
    (hk : k + bs.card * (Fintype.card H - 1) = Fintype.card B * (Fintype.card H - 1)) :
    XReach (frame A (JC (univ \ {l}) (qC bs))) (frame A (univ \ {Sum.inl l}))
      (fun φ => bcost φ k) := by
  have h4 : 1 ≤ Fintype.card (LC B H l) := Fintype.card_pos_iff.mpr ⟨Sum.inl l⟩
  have h2 : ((univ : Finset (LC B H l)) \ {Sum.inl l}).card
      = Fintype.card H + Fintype.card B * (Fintype.card H - 1) - 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), card_univ_LC, Finset.card_singleton]
  refine reach_of_lt (two_le_card_LC hB hH) A (JCY_sub l _) k ?_ ?_
  · rw [card_JCY, h2]
    omega
  · have h5 := card_LC (B := B) l
    rw [h2]
    omega

end Climbs

section Term
variable {B H : Type} [Fintype B] [DecidableEq B] [Fintype H] [DecidableEq H]

/-- terminal identity of a bank pair of the class `(g, base)`. -/
lemma class_term (base : OBase H) (l : H) (g : Orth (LC B H l)) :
    kernel (LC B H l) * PhiC g ∅ (tt (base.v l))
      = shift ((BBC base l g).v (Sum.inl l)) * frame (BBC base l g) (univ \ {Sum.inl l}) := by
  have e : PhiC g ∅ (tt (base.v l)) = frame (BBC base l g) {Sum.inl l} := by
    rw [← mat_single, PhiC_BBC, JC_single]
  rw [e]
  exact terminal_calc _ _

end Term

/-! ## The same facts in the form a network asks for: projectors `tt u`, `1`, `1 + tt u`, `0` of
the line `u = base.v l` of the class. -/

section ClassT
variable {B H : Type} [Fintype B] [DecidableEq B] [Fintype H] [DecidableEq H]
variable (base : OBase H) (l : H)

/-- stage 0 to the stage of the first block `c`: `X`. -/
lemma bankT_x0 (c : B) (g : Orth (LC B H l)) :
    PhiC g ∅ 1 = PhiC (RrC base l c g) (qC {c}) (tt (base.v l)) := by
  have e := bank_x0 base l c g
  rw [OBase.mat_univ, mat_single] at e
  exact e

/-- stage 0 to the stage of the first block `c`: `Y`. -/
lemma bankT_y0 (c : B) (g : Orth (LC B H l)) :
    PhiC g ∅ (1 + tt (base.v l)) = PhiC (RrC base l c g) (qC {c}) 0 := by
  have e := bank_y0 base l c g
  rw [mat_compl_single, mat_empty] at e
  exact e

/-- the stage of `c ∈ bs` to the stage of `c' ∉ bs`: `X`. -/
lemma bankT_xx (bs : Finset B) (c c' : B) (hc : c ∈ bs) (hc' : c' ∉ bs) (g : Orth (LC B H l)) :
    PhiC (RrC base l c g) (qC bs) 1
      = PhiC (RrC base l c' g) (qC (insert c' bs)) (tt (base.v l)) := by
  have e := bank_xx base l bs c c' hc hc' g
  rw [OBase.mat_univ, mat_single] at e
  exact e

/-- the stage of `c ∈ bs` to the stage of `c' ∉ bs`: `Y`. -/
lemma bankT_yy (bs : Finset B) (c c' : B) (hc : c ∈ bs) (hc' : c' ∉ bs) (g : Orth (LC B H l)) :
    PhiC (RrC base l c g) (qC bs) (1 + tt (base.v l))
      = PhiC (RrC base l c' g) (qC (insert c' bs)) 0 := by
  have e := bank_yy base l bs c c' hc hc' g
  rw [mat_compl_single, mat_empty] at e
  exact e

/-- frames of the class in the basis `BBC base l g`: start of `X`, start of `Y`, `X` and `Y`
after the stage of `c ∈ bs`. -/
lemma classT_X0 (g : Orth (LC B H l)) :
    PhiC g ∅ (tt (base.v l)) = frame (BBC base l g) (JC {l} ∅) := by
  have e := PhiC_BBC base l g ∅ {l}
  rw [mat_single] at e
  exact e

lemma classT_Y0 (g : Orth (LC B H l)) : PhiC g ∅ 0 = frame (BBC base l g) (JC ∅ ∅) := by
  have e := PhiC_BBC base l g ∅ ∅
  rw [mat_empty] at e
  exact e

lemma classT_X (bs : Finset B) (c : B) (hc : c ∈ bs) (g : Orth (LC B H l)) :
    PhiC (RrC base l c g) (qC bs) 1 = frame (BBC base l g) (JC univ (qC bs)) := by
  have e := bank_outX base l bs c hc g
  rw [OBase.mat_univ] at e
  exact e

lemma classT_Y (bs : Finset B) (c : B) (hc : c ∈ bs) (g : Orth (LC B H l)) :
    PhiC (RrC base l c g) (qC bs) (1 + tt (base.v l))
      = frame (BBC base l g) (JC (univ \ {l}) (qC bs)) := by
  have e := bank_outY base l bs c hc g
  rw [mat_compl_single] at e
  exact e

variable (hB : 1 ≤ Fintype.card B) (hH : 2 ≤ Fintype.card H)
include hB hH

/-- IDLE CLIMB of an `X` role over stage 0 and the stage of the first block `c`: ONE block from
its line to the frame its twin has after that stage. -/
lemma idle_X0 (c : B) (g : Orth (LC B H l)) (k : ℕ)
    (hk : k + 1 = Fintype.card H + (Fintype.card H - 1)) :
    XReach (PhiC g ∅ (tt (base.v l))) (PhiC (RrC base l c g) (qC {c}) 1)
      (fun φ => bcost φ k) := by
  rw [classT_X0, classT_X base l {c} c (Finset.mem_singleton_self c) g]
  exact climb_X0 hB hH l (BBC base l g) {c} k (by rw [Finset.card_singleton, one_mul]; exact hk)

/-- the same for the `Y` role. -/
lemma idle_Y0 (c : B) (g : Orth (LC B H l)) (k : ℕ)
    (hk : k = (Fintype.card H - 1) + (Fintype.card H - 1)) :
    XReach (PhiC g ∅ 0) (PhiC (RrC base l c g) (qC {c}) (1 + tt (base.v l)))
      (fun φ => bcost φ k) := by
  rw [classT_Y0, classT_Y base l {c} c (Finset.mem_singleton_self c) g]
  exact climb_Y0 hB hH l (BBC base l g) {c} k (by rw [Finset.card_singleton, one_mul]; exact hk)

/-- IDLE CLIMB of an `X` role from the frame after the stage of `c ∈ bs` to the end (all later
stages and the last moves): ONE block. -/
lemma idle_Xend (bs : Finset B) (c : B) (hc : c ∈ bs) (g : Orth (LC B H l)) (k : ℕ)
    (hk : k + bs.card * (Fintype.card H - 1) = Fintype.card B * (Fintype.card H - 1)) :
    XReach (PhiC (RrC base l c g) (qC bs) 1) (kernel (LC B H l)) (fun φ => bcost φ k) := by
  rw [classT_X base l bs c hc g]
  exact climb_Xend hB hH l (BBC base l g) bs k hk

/-- the same for the `Y` role, up to `u^⊥`. -/
lemma idle_Yend (bs : Finset B) (c : B) (hc : c ∈ bs) (g : Orth (LC B H l)) (k : ℕ)
    (hk : k + bs.card * (Fintype.card H - 1) = Fintype.card B * (Fintype.card H - 1)) :
    XReach (PhiC (RrC base l c g) (qC bs) (1 + tt (base.v l)))
      (frame (BBC base l g) (univ \ {Sum.inl l})) (fun φ => bcost φ k) := by
  rw [classT_Y base l bs c hc g]
  exact climb_Yend hB hH l (BBC base l g) bs k hk

/-- IDLE CLIMB over the stages of the blocks `bs' \ bs` (`c ∈ bs`, `c' ∈ bs'`): ONE block. -/
lemma idle_X (bs bs' : Finset B) (h : bs ⊆ bs') (c c' : B) (hc : c ∈ bs) (hc' : c' ∈ bs')
    (g : Orth (LC B H l)) (k : ℕ)
    (hk : k + bs.card * (Fintype.card H - 1) = bs'.card * (Fintype.card H - 1)) :
    XReach (PhiC (RrC base l c g) (qC bs) 1) (PhiC (RrC base l c' g) (qC bs') 1)
      (fun φ => bcost φ k) := by
  rw [classT_X base l bs c hc g, classT_X base l bs' c' hc' g]
  exact climb_X hB hH l (BBC base l g) bs bs' h k hk

lemma idle_Y (bs bs' : Finset B) (h : bs ⊆ bs') (c c' : B) (hc : c ∈ bs) (hc' : c' ∈ bs')
    (g : Orth (LC B H l)) (k : ℕ)
    (hk : k + bs.card * (Fintype.card H - 1) = bs'.card * (Fintype.card H - 1)) :
    XReach (PhiC (RrC base l c g) (qC bs) (1 + tt (base.v l)))
      (PhiC (RrC base l c' g) (qC bs') (1 + tt (base.v l))) (fun φ => bcost φ k) := by
  rw [classT_Y base l bs c hc g, classT_Y base l bs' c' hc' g]
  exact climb_Y hB hH l (BBC base l g) bs bs' h k hk

end ClassT
end
end BC
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.BC.fmapC
#print axioms OAI.PowerSaving.BC.bank_xx
#print axioms OAI.PowerSaving.BC.bank_yy
#print axioms OAI.PowerSaving.BC.climb_X0
#print axioms OAI.PowerSaving.BC.climb_Yend
#print axioms OAI.PowerSaving.BC.class_term
#print axioms OAI.PowerSaving.BC.idle_Xend
#print axioms OAI.PowerSaving.BC.idle_Yend
#print axioms OAI.PowerSaving.BC.bankT_xx
