import Work.Reframe.GeomBase

/-!
# (key: reframe) The label space `H ⊕ (Bool × H)` of the shared three-stage word (`m = 3h`)

Three blocks: `W_0 = inl _`, `W_0' = inr (false, _)`, `W_0'' = inr (true, _)`.

* `J s q`        index set: `s` in block 0, `q` in the other two blocks;
* `blk A`        orthogonal matrix: the columns of the basis `A` on block 0, the standard basis
                 elsewhere; `blk_conj : blk A * diagI (J s q) * (blk A)ᵀ = fromBlocks (A.mat s) 0 0 (diagI q)`;
* `PhiQ d q P`   frame of `d (P ⊕ q) dᵀ`: the window `d W_0` carrying the projector `P`, on the
                 base `d q`; `PhiQ_eq`: in the basis `d (A ⊕ std)` it is the frame of `J s q`;
* `fmapQ`        the block frame map `XMap H (L3 H)` with `Φ = PhiQ d q`;
* `PhiQ_perm`    if the columns of `d (A ⊕ std)` are those of `g (A ⊕ std)` permuted by `π`, then
                 `PhiQ d q (A.mat s) = PhiQ g q' (A.mat s')` whenever `π (J s q) = J s' q'`;
* `piF c l`      the involution exchanging `inl i` with `inr (c, i)` for `i ≠ l` (this is `rho_t`
                 for `c = false` and `rho'_t` for `c = true`, in the basis of the triple `t`, when
                 the pivot of every triple is `l`); `map_piF_single/_empty/_univ/_compl`;
* `tauF c`       the involution exchanging the blocks `0` and `c`; `map_tauF`.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace RF
open Binary Matrix Finset RAM SS CB
noncomputable section

/-- the label space: three copies of `H`. -/
abbrev L3 (H : Type) := H ⊕ (Bool × H)

section Blocks
variable {H : Type} [Fintype H] [DecidableEq H]

lemma card_L3 : Fintype.card (L3 H) = 3 * Fintype.card H := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool]
  ring

/-- index set: `s` in block 0, `q` in the two other blocks. -/
abbrev J (s : Finset H) (q : Finset (Bool × H)) : Finset (L3 H) := s.disjSum q

lemma J_sdiff (s t : Finset H) (q : Finset (Bool × H)) : J t q \ J s q = J (t \ s) ∅ := by
  ext x
  rcases x with i | b
  · rw [Finset.mem_sdiff, Finset.inl_mem_disjSum, Finset.inl_mem_disjSum,
      Finset.inl_mem_disjSum, Finset.mem_sdiff]
  · rw [Finset.mem_sdiff, Finset.inr_mem_disjSum, Finset.inr_mem_disjSum,
      Finset.inr_mem_disjSum]
    exact ⟨fun h => absurd h.1 h.2, fun h => absurd h (Finset.notMem_empty b)⟩

lemma J_sdiff_card (s t : Finset H) (q : Finset (Bool × H)) :
    (J t q \ J s q).card = (t \ s).card := by
  rw [J_sdiff, Finset.card_disjSum, Finset.card_empty, add_zero]

lemma diagI_J (s : Finset H) (q : Finset (Bool × H)) :
    diagI (J s q) = Matrix.fromBlocks (diagI s) 0 0 (diagI q) := by
  ext x y
  rcases x with i | b <;> rcases y with j | b'
  · show diagI (J s q) (Sum.inl i) (Sum.inl j) = diagI s i j
    rw [diagI_apply, diagI_apply]
    by_cases h : i = j
    · subst h
      rw [if_pos rfl, if_pos rfl]
      by_cases hi : i ∈ s
      · rw [if_pos hi, if_pos (Finset.inl_mem_disjSum.mpr hi)]
      · rw [if_neg hi,
          if_neg (fun h' : (Sum.inl i : L3 H) ∈ J s q => hi (Finset.inl_mem_disjSum.mp h'))]
    · rw [if_neg h, if_neg (fun h' : (Sum.inl i : L3 H) = Sum.inl j => h (Sum.inl.inj h'))]
  · show diagI (J s q) (Sum.inl i) (Sum.inr b') = 0
    rw [diagI_apply, if_neg Sum.inl_ne_inr]
  · show diagI (J s q) (Sum.inr b) (Sum.inl j) = 0
    rw [diagI_apply, if_neg Sum.inr_ne_inl]
  · show diagI (J s q) (Sum.inr b) (Sum.inr b') = diagI q b b'
    rw [diagI_apply, diagI_apply]
    by_cases h : b = b'
    · subst h
      rw [if_pos rfl, if_pos rfl]
      by_cases hi : b ∈ q
      · rw [if_pos hi, if_pos (Finset.inr_mem_disjSum.mpr hi)]
      · rw [if_neg hi,
          if_neg (fun h' : (Sum.inr b : L3 H) ∈ J s q => hi (Finset.inr_mem_disjSum.mp h'))]
    · rw [if_neg h, if_neg (fun h' : (Sum.inr b : L3 H) = Sum.inr b' => h (Sum.inr.inj h'))]

/-- the columns of `A` on block 0, the standard basis on the other blocks. -/
def blk (A : OBase H) : Matrix (L3 H) (L3 H) F := Matrix.fromBlocks (cmat A) 0 0 1

lemma blk_orth (A : OBase H) : (blk A)ᵀ * blk A = 1 := by
  unfold blk
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  simp only [cmat_orth, Matrix.transpose_zero, Matrix.transpose_one, Matrix.mul_zero,
    Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero, zero_add,
    Matrix.fromBlocks_one]

lemma blk_conj (A : OBase H) (s : Finset H) (q : Finset (Bool × H)) :
    blk A * diagI (J s q) * (blk A)ᵀ = Matrix.fromBlocks (A.mat s) 0 0 (diagI q) := by
  rw [diagI_J, mat_eq_cmat]
  unfold blk
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.transpose_zero, Matrix.transpose_one, Matrix.mul_zero, Matrix.zero_mul,
    Matrix.mul_one, Matrix.one_mul, add_zero, zero_add]

/-- frame of `d (P ⊕ q) dᵀ`. -/
def PhiQ (d : Orth (L3 H)) (q : Finset (Bool × H)) (P : Matrix H H F) : CMat (L3 H) :=
  frameM (d.1 * Matrix.fromBlocks P 0 0 (diagI q) * d.1ᵀ)

lemma conj_blk (d : Matrix (L3 H) (L3 H) F) (A : OBase H) (s : Finset H)
    (q : Finset (Bool × H)) :
    d * Matrix.fromBlocks (A.mat s) 0 0 (diagI q) * dᵀ
      = (d * blk A) * diagI (J s q) * (d * blk A)ᵀ := by
  rw [← blk_conj]
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]

/-- in the basis `d (A ⊕ std)` the frame `PhiQ d q (A.mat s)` is the frame of `J s q`. -/
lemma PhiQ_eq (d : Orth (L3 H)) (q : Finset (Bool × H)) (A : OBase H) (s : Finset H) :
    PhiQ d q (A.mat s) = frame (ofCols (d.1 * blk A) (mul_orth d.2 (blk_orth A))) (J s q) := by
  rw [frame_ofCols]
  unfold PhiQ
  rw [conj_blk]

/-- column permutation: `PhiQ` of the permuted matrix is `PhiQ` of the permuted index set. -/
lemma PhiQ_perm (d g : Orth (L3 H)) (A : OBase H) (π : Equiv.Perm (L3 H))
    (hd : d.1 * blk A = (g.1 * blk A).submatrix id π) (s s' : Finset H)
    (q q' : Finset (Bool × H)) (hmap : (J s q).map π.toEmbedding = J s' q') :
    PhiQ d q (A.mat s) = PhiQ g q' (A.mat s') := by
  unfold PhiQ
  rw [conj_blk, conj_blk, hd, submatrix_diagI, hmap]

end Blocks

section Perms
variable {H : Type} [Fintype H] [DecidableEq H]

/-- exchange `inl i` with `inr (c, i)` for `i ≠ l`; everything else is fixed. -/
def fF (c : Bool) (l : H) : L3 H → L3 H
  | .inl i => if i = l then .inl i else .inr (c, i)
  | .inr (b, j) => if b = c ∧ j ≠ l then .inl j else .inr (b, j)

lemma fF_inl_eq (c : Bool) (l i : H) (hi : i = l) : fF c l (Sum.inl i) = Sum.inl i := if_pos hi
lemma fF_inl_ne (c : Bool) (l i : H) (hi : i ≠ l) : fF c l (Sum.inl i) = Sum.inr (c, i) :=
  if_neg hi
lemma fF_inr_pos (c : Bool) (l : H) (b : Bool) (j : H) (h : b = c ∧ j ≠ l) :
    fF c l (Sum.inr (b, j)) = Sum.inl j := if_pos h
lemma fF_inr_neg (c : Bool) (l : H) (b : Bool) (j : H) (h : ¬ (b = c ∧ j ≠ l)) :
    fF c l (Sum.inr (b, j)) = Sum.inr (b, j) := if_neg h

lemma fF_invol (c : Bool) (l : H) : Function.Involutive (fF c l) := by
  intro x
  rcases x with i | ⟨b, j⟩
  · by_cases hi : i = l
    · rw [fF_inl_eq c l i hi, fF_inl_eq c l i hi]
    · rw [fF_inl_ne c l i hi, fF_inr_pos c l c i ⟨rfl, hi⟩]
  · by_cases hb : b = c ∧ j ≠ l
    · rw [fF_inr_pos c l b j hb, fF_inl_ne c l j hb.2, hb.1]
    · rw [fF_inr_neg c l b j hb, fF_inr_neg c l b j hb]

/-- `rho_t` (for `c = false`) and `rho'_t` (for `c = true`) as permutations of the indices of
the basis `(base t) ⊕ std`, when the pivot of `t` is `l`. -/
def piF (c : Bool) (l : H) : Equiv.Perm (L3 H) :=
  ⟨fF c l, fF c l, fF_invol c l, fF_invol c l⟩

lemma mem_map_piF (c : Bool) (l : H) (S : Finset (L3 H)) (x : L3 H) :
    x ∈ S.map (piF c l).toEmbedding ↔ fF c l x ∈ S :=
  Finset.mem_map_equiv

/-- what the base index set `q` must satisfy on the block `c`: all of it except `l`. -/
def BlockOf (c : Bool) (l : H) (q : Finset (Bool × H)) : Prop := ∀ j, (c, j) ∈ q ↔ j ≠ l

lemma fF_inl_mem (c : Bool) (l : H) (s : Finset H) (q : Finset (Bool × H))
    (hq : BlockOf c l q) (i : H) : fF c l (Sum.inl i) ∈ J s q ↔ (i ≠ l ∨ l ∈ s) := by
  by_cases hi : i = l
  · rw [fF_inl_eq c l i hi, Finset.inl_mem_disjSum, hi]
    exact ⟨fun h => Or.inr h, fun h => h.elim (fun h' => absurd rfl h') id⟩
  · rw [fF_inl_ne c l i hi, Finset.inr_mem_disjSum]
    exact ⟨fun _ => Or.inl hi, fun _ => (hq i).mpr hi⟩

lemma fF_inrc_mem (c : Bool) (l : H) (s : Finset H) (q : Finset (Bool × H))
    (hq : BlockOf c l q) (j : H) : fF c l (Sum.inr (c, j)) ∈ J s q ↔ (j ≠ l ∧ j ∈ s) := by
  by_cases hj : j = l
  · rw [fF_inr_neg c l c j (fun h => h.2 hj), Finset.inr_mem_disjSum]
    exact ⟨fun h => absurd hj ((hq j).mp h), fun h => absurd hj h.1⟩
  · rw [fF_inr_pos c l c j ⟨rfl, hj⟩, Finset.inl_mem_disjSum]
    exact ⟨fun h => ⟨hj, h⟩, fun h => h.2⟩

lemma fF_inro_mem (c : Bool) (l : H) (s : Finset H) (q : Finset (Bool × H)) (b : Bool)
    (hb : b ≠ c) (j : H) : fF c l (Sum.inr (b, j)) ∈ J s q ↔ (b, j) ∈ q := by
  rw [fF_inr_neg c l b j (fun h => hb h.1), Finset.inr_mem_disjSum]

/-- the part of `q` outside the block `c`. -/
def Rest (c : Bool) (q r : Finset (Bool × H)) : Prop := ∀ b j, (b, j) ∈ r ↔ (b ≠ c ∧ (b, j) ∈ q)

/-- `X` entering the next stage: `<u> + base` is carried to `W_0 +` (the rest of the base). -/
lemma map_piF_single (c : Bool) (l : H) (q r : Finset (Bool × H)) (hq : BlockOf c l q)
    (hr : Rest c q r) : (J {l} q).map (piF c l).toEmbedding = J univ r := by
  ext x
  rw [mem_map_piF]
  rcases x with i | ⟨b, j⟩
  · rw [fF_inl_mem c l _ q hq, Finset.inl_mem_disjSum]
    exact ⟨fun _ => Finset.mem_univ i, fun _ => Or.inr (Finset.mem_singleton_self l)⟩
  · by_cases hb : b = c
    · rw [hb, fF_inrc_mem c l _ q hq, Finset.inr_mem_disjSum]
      exact ⟨fun h => absurd (Finset.mem_singleton.mp h.2) h.1,
        fun h => absurd rfl ((hr c j).mp h).1⟩
    · rw [fF_inro_mem c l _ q b hb, Finset.inr_mem_disjSum]
      exact ⟨fun h => (hr b j).mpr ⟨hb, h⟩, fun h => ((hr b j).mp h).2⟩

/-- `Y` entering the next stage: the base is carried to `(W_0 ∩ u^⊥) +` (the rest). -/
lemma map_piF_empty (c : Bool) (l : H) (q r : Finset (Bool × H)) (hq : BlockOf c l q)
    (hr : Rest c q r) : (J ∅ q).map (piF c l).toEmbedding = J (univ \ {l}) r := by
  ext x
  rw [mem_map_piF]
  rcases x with i | ⟨b, j⟩
  · rw [fF_inl_mem c l _ q hq, Finset.inl_mem_disjSum]
    constructor
    · intro h
      rcases h with h | h
      · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, fun h' => h (Finset.mem_singleton.mp h')⟩
      · exact absurd h (Finset.notMem_empty l)
    · intro h
      exact Or.inl (fun e => (Finset.mem_sdiff.mp h).2 (Finset.mem_singleton.mpr e))
  · by_cases hb : b = c
    · rw [hb, fF_inrc_mem c l _ q hq, Finset.inr_mem_disjSum]
      exact ⟨fun h => absurd h.2 (Finset.notMem_empty j),
        fun h => absurd rfl ((hr c j).mp h).1⟩
    · rw [fF_inro_mem c l _ q b hb, Finset.inr_mem_disjSum]
      exact ⟨fun h => (hr b j).mpr ⟨hb, h⟩, fun h => ((hr b j).mp h).2⟩

/-- `X` after its invocation: `W_0 + base` is preserved. -/
lemma map_piF_univ (c : Bool) (l : H) (q : Finset (Bool × H)) (hq : BlockOf c l q) :
    (J univ q).map (piF c l).toEmbedding = J univ q := by
  ext x
  rw [mem_map_piF]
  rcases x with i | ⟨b, j⟩
  · rw [fF_inl_mem c l _ q hq, Finset.inl_mem_disjSum]
    exact ⟨fun _ => Finset.mem_univ i, fun _ => Or.inr (Finset.mem_univ l)⟩
  · by_cases hb : b = c
    · rw [hb, fF_inrc_mem c l _ q hq, Finset.inr_mem_disjSum]
      exact ⟨fun h => (hq j).mpr h.1, fun h => ⟨(hq j).mp h, Finset.mem_univ j⟩⟩
    · rw [fF_inro_mem c l _ q b hb, Finset.inr_mem_disjSum]

/-- `Y` after its invocation: `(W_0 ∩ u^⊥) + base` is preserved. -/
lemma map_piF_compl (c : Bool) (l : H) (q : Finset (Bool × H)) (hq : BlockOf c l q) :
    (J (univ \ {l}) q).map (piF c l).toEmbedding = J (univ \ {l}) q := by
  ext x
  rw [mem_map_piF]
  rcases x with i | ⟨b, j⟩
  · rw [fF_inl_mem c l _ q hq, Finset.inl_mem_disjSum]
    constructor
    · intro h
      rcases h with h | h
      · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, fun h' => h (Finset.mem_singleton.mp h')⟩
      · exact absurd (Finset.mem_singleton_self l) (Finset.mem_sdiff.mp h).2
    · intro h
      exact Or.inl (fun e => (Finset.mem_sdiff.mp h).2 (Finset.mem_singleton.mpr e))
  · by_cases hb : b = c
    · rw [hb, fF_inrc_mem c l _ q hq, Finset.inr_mem_disjSum]
      exact ⟨fun h => (hq j).mpr h.1, fun h => ⟨(hq j).mp h, Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ j, fun h' => (hq j).mp h (Finset.mem_singleton.mp h')⟩⟩⟩
    · rw [fF_inro_mem c l _ q b hb, Finset.inr_mem_disjSum]

/-- exchange the blocks `0` and `c`. -/
def fT (c : Bool) : L3 H → L3 H
  | .inl i => .inr (c, i)
  | .inr (b, j) => if b = c then .inl j else .inr (b, j)

lemma fT_inl (c : Bool) (i : H) : fT c (Sum.inl i) = Sum.inr (c, i) := rfl
lemma fT_inr_pos (c b : Bool) (j : H) (h : b = c) : fT c (Sum.inr (b, j)) = Sum.inl j := if_pos h
lemma fT_inr_neg (c b : Bool) (j : H) (h : ¬ b = c) : fT c (Sum.inr (b, j)) = Sum.inr (b, j) :=
  if_neg h

lemma fT_invol (c : Bool) : Function.Involutive (fT (H := H) c) := by
  intro x
  rcases x with i | ⟨b, j⟩
  · rw [fT_inl, fT_inr_pos c c i rfl]
  · by_cases hb : b = c
    · rw [fT_inr_pos c b j hb, fT_inl, hb]
    · rw [fT_inr_neg c b j hb, fT_inr_neg c b j hb]

/-- the isometry `tau` that carries `W_0` to the block `c`, as a permutation of indices. -/
def tauF (c : Bool) : Equiv.Perm (L3 H) := ⟨fT c, fT c, fT_invol c, fT_invol c⟩

lemma mem_map_tauF (c : Bool) (S : Finset (L3 H)) (x : L3 H) :
    x ∈ S.map (tauF c).toEmbedding ↔ fT c x ∈ S :=
  Finset.mem_map_equiv

/-- the block `c` as a set of indices. -/
def blockB (c : Bool) : Finset (Bool × H) := univ.filter fun b => b.1 = c

lemma mem_blockB (c b : Bool) (j : H) : (b, j) ∈ blockB (H := H) c ↔ b = c := by
  unfold blockB
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

lemma map_tauF (c : Bool) :
    (J (univ : Finset H) ∅).map (tauF c).toEmbedding = J ∅ (blockB c) := by
  ext x
  rw [mem_map_tauF]
  rcases x with i | ⟨b, j⟩
  · rw [fT_inl, Finset.inr_mem_disjSum, Finset.inl_mem_disjSum]
    exact ⟨fun h => absurd h (Finset.notMem_empty _), fun h => absurd h (Finset.notMem_empty _)⟩
  · by_cases hb : b = c
    · rw [fT_inr_pos c b j hb, Finset.inl_mem_disjSum, Finset.inr_mem_disjSum]
      exact ⟨fun _ => (mem_blockB c b j).mpr hb, fun _ => Finset.mem_univ j⟩
    · rw [fT_inr_neg c b j hb, Finset.inr_mem_disjSum, Finset.inr_mem_disjSum]
      exact ⟨fun h => absurd h (Finset.notMem_empty _),
        fun h => absurd ((mem_blockB c b j).mp h) hb⟩

end Perms
end
end RF
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.RF.PhiQ_eq
#print axioms OAI.PowerSaving.RF.PhiQ_perm
#print axioms OAI.PowerSaving.RF.map_piF_single
#print axioms OAI.PowerSaving.RF.map_piF_compl
#print axioms OAI.PowerSaving.RF.map_tauF
