import Work.Reframe.GeomBase

/-!
# (key: bridge-geom) The label space `H ⊕ (B × H)` for ANY finite block index `B` (`m = (|B|+1) h`)

`Work.Reframe.Geom3` with the block index `Bool` replaced by an arbitrary type `B` with decidable
equality.  Blocks: `W_0 = inl _`, and one block `inr (c, _)` for every `c : B`.  For the bridged
word `B_2` take `B = Fin 4` (`m = 5h`); for `B_j` take `B = Fin (2j)`.

* `JB s q`       index set: `s` in block 0, `q` in the other blocks;
* `blkB B A`       orthogonal matrix: the columns of the basis `A` on block 0, the standard basis
                 elsewhere;
* `PhiB d q P`   frame of `d (P ⊕ q) dᵀ`: the window `d W_0` carrying the projector `P`, on the
                 base `d q`; `PhiB_eq`: in the basis `d (A ⊕ std)` it is the frame of `JB s q`;
* `PhiB_perm`    if the columns of `d (A ⊕ std)` are those of `g (A ⊕ std)` permuted by `π`, then
                 `PhiB d q (A.mat s) = PhiB g q' (A.mat s')` whenever `π (JB s q) = JB s' q'`;
* `piB c l`      the involution exchanging `inl i` with `inr (c, i)` for `i ≠ l` (this is
                 `rho^(c)_t` in the basis of the triple `t`, when the pivot of every triple is `l`);
                 `map_piB_single/_empty/_univ/_compl`;
* `tauB c`       the involution exchanging the blocks `0` and `c`; `map_tauB`.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace BG
open Binary Matrix Finset RAM SS CB RF
noncomputable section

/-- the label space: block 0 and one copy of `H` for every `c : B`. -/
abbrev LB (B H : Type) := H ⊕ (B × H)

section Blocks
variable {B H : Type} [Fintype B] [DecidableEq B] [Fintype H] [DecidableEq H]

lemma card_LB : Fintype.card (LB B H) = (Fintype.card B + 1) * Fintype.card H := by
  simp only [Fintype.card_sum, Fintype.card_prod]
  ring

/-- index set: `s` in block 0, `q` in the other blocks. -/
abbrev JB (s : Finset H) (q : Finset (B × H)) : Finset (LB B H) := s.disjSum q

lemma JB_sdiff (s t : Finset H) (q : Finset (B × H)) : JB t q \ JB s q = JB (t \ s) ∅ := by
  ext x
  rcases x with i | b
  · rw [Finset.mem_sdiff, Finset.inl_mem_disjSum, Finset.inl_mem_disjSum,
      Finset.inl_mem_disjSum, Finset.mem_sdiff]
  · rw [Finset.mem_sdiff, Finset.inr_mem_disjSum, Finset.inr_mem_disjSum,
      Finset.inr_mem_disjSum]
    exact ⟨fun h => absurd h.1 h.2, fun h => absurd h (Finset.notMem_empty b)⟩

lemma JB_sdiff_card (s t : Finset H) (q : Finset (B × H)) :
    (JB t q \ JB s q).card = (t \ s).card := by
  rw [JB_sdiff, Finset.card_disjSum, Finset.card_empty, add_zero]

lemma diagI_JB (s : Finset H) (q : Finset (B × H)) :
    diagI (JB s q) = Matrix.fromBlocks (diagI s) 0 0 (diagI q) := by
  ext x y
  rcases x with i | b <;> rcases y with j | b'
  · show diagI (JB s q) (Sum.inl i) (Sum.inl j) = diagI s i j
    rw [diagI_apply, diagI_apply]
    by_cases h : i = j
    · subst h
      rw [if_pos rfl, if_pos rfl]
      by_cases hi : i ∈ s
      · rw [if_pos hi, if_pos (Finset.inl_mem_disjSum.mpr hi)]
      · rw [if_neg hi,
          if_neg (fun h' : (Sum.inl i : LB B H) ∈ JB s q => hi (Finset.inl_mem_disjSum.mp h'))]
    · rw [if_neg h, if_neg (fun h' : (Sum.inl i : LB B H) = Sum.inl j => h (Sum.inl.inj h'))]
  · show diagI (JB s q) (Sum.inl i) (Sum.inr b') = 0
    rw [diagI_apply, if_neg Sum.inl_ne_inr]
  · show diagI (JB s q) (Sum.inr b) (Sum.inl j) = 0
    rw [diagI_apply, if_neg Sum.inr_ne_inl]
  · show diagI (JB s q) (Sum.inr b) (Sum.inr b') = diagI q b b'
    rw [diagI_apply, diagI_apply]
    by_cases h : b = b'
    · subst h
      rw [if_pos rfl, if_pos rfl]
      by_cases hi : b ∈ q
      · rw [if_pos hi, if_pos (Finset.inr_mem_disjSum.mpr hi)]
      · rw [if_neg hi,
          if_neg (fun h' : (Sum.inr b : LB B H) ∈ JB s q => hi (Finset.inr_mem_disjSum.mp h'))]
    · rw [if_neg h, if_neg (fun h' : (Sum.inr b : LB B H) = Sum.inr b' => h (Sum.inr.inj h'))]

variable (B) in
/-- the columns of `A` on block 0, the standard basis on the other blocks (`B` explicit). -/
def blkB (A : OBase H) : Matrix (LB B H) (LB B H) F := Matrix.fromBlocks (cmat A) 0 0 1

lemma blkB_orth (A : OBase H) : (blkB B A)ᵀ * blkB B A = 1 := by
  unfold blkB
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  simp only [cmat_orth, Matrix.transpose_zero, Matrix.transpose_one, Matrix.mul_zero,
    Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero, zero_add,
    Matrix.fromBlocks_one]

lemma blkB_conj (A : OBase H) (s : Finset H) (q : Finset (B × H)) :
    blkB B A * diagI (JB s q) * (blkB B A)ᵀ = Matrix.fromBlocks (A.mat s) 0 0 (diagI q) := by
  rw [diagI_JB, mat_eq_cmat]
  unfold blkB
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.transpose_zero, Matrix.transpose_one, Matrix.mul_zero, Matrix.zero_mul,
    Matrix.mul_one, Matrix.one_mul, add_zero, zero_add]

/-- frame of `d (P ⊕ q) dᵀ`. -/
def PhiB (d : Orth (LB B H)) (q : Finset (B × H)) (P : Matrix H H F) : CMat (LB B H) :=
  frameM (d.1 * Matrix.fromBlocks P 0 0 (diagI q) * d.1ᵀ)

lemma conj_blkB (d : Matrix (LB B H) (LB B H) F) (A : OBase H) (s : Finset H)
    (q : Finset (B × H)) :
    d * Matrix.fromBlocks (A.mat s) 0 0 (diagI q) * dᵀ
      = (d * blkB B A) * diagI (JB s q) * (d * blkB B A)ᵀ := by
  rw [← blkB_conj]
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]

/-- in the basis `d (A ⊕ std)` the frame `PhiB d q (A.mat s)` is the frame of `JB s q`. -/
lemma PhiB_eq (d : Orth (LB B H)) (q : Finset (B × H)) (A : OBase H) (s : Finset H) :
    PhiB d q (A.mat s) = frame (ofCols (d.1 * blkB B A) (mul_orth d.2 (blkB_orth A))) (JB s q) := by
  rw [frame_ofCols]
  unfold PhiB
  rw [conj_blkB]

/-- column permutation: `PhiB` of the permuted matrix is `PhiB` of the permuted index set. -/
lemma PhiB_perm (d g : Orth (LB B H)) (A : OBase H) (π : Equiv.Perm (LB B H))
    (hd : d.1 * blkB B A = (g.1 * blkB B A).submatrix id π) (s s' : Finset H)
    (q q' : Finset (B × H)) (hmap : (JB s q).map π.toEmbedding = JB s' q') :
    PhiB d q (A.mat s) = PhiB g q' (A.mat s') := by
  unfold PhiB
  rw [conj_blkB, conj_blkB, hd, submatrix_diagI, hmap]

end Blocks

section Perms
variable {B H : Type} [Fintype B] [DecidableEq B] [Fintype H] [DecidableEq H]

/-- exchange `inl i` with `inr (c, i)` for `i ≠ l`; everything else is fixed. -/
def fFB (c : B) (l : H) : LB B H → LB B H
  | .inl i => if i = l then .inl i else .inr (c, i)
  | .inr (b, j) => if b = c ∧ j ≠ l then .inl j else .inr (b, j)

lemma fFB_inl_eq (c : B) (l i : H) (hi : i = l) : fFB c l (Sum.inl i) = Sum.inl i := if_pos hi
lemma fFB_inl_ne (c : B) (l i : H) (hi : i ≠ l) : fFB c l (Sum.inl i) = Sum.inr (c, i) :=
  if_neg hi
lemma fFB_inr_pos (c : B) (l : H) (b : B) (j : H) (h : b = c ∧ j ≠ l) :
    fFB c l (Sum.inr (b, j)) = Sum.inl j := if_pos h
lemma fFB_inr_neg (c : B) (l : H) (b : B) (j : H) (h : ¬ (b = c ∧ j ≠ l)) :
    fFB c l (Sum.inr (b, j)) = Sum.inr (b, j) := if_neg h

lemma fFB_invol (c : B) (l : H) : Function.Involutive (fFB c l) := by
  intro x
  rcases x with i | ⟨b, j⟩
  · by_cases hi : i = l
    · rw [fFB_inl_eq c l i hi, fFB_inl_eq c l i hi]
    · rw [fFB_inl_ne c l i hi, fFB_inr_pos c l c i ⟨rfl, hi⟩]
  · by_cases hb : b = c ∧ j ≠ l
    · rw [fFB_inr_pos c l b j hb, fFB_inl_ne c l j hb.2, hb.1]
    · rw [fFB_inr_neg c l b j hb, fFB_inr_neg c l b j hb]

/-- `rho^(c)_t` as a permutation of the indices of the basis `(base t) ⊕ std`, when the pivot of
`t` is `l`. -/
def piB (c : B) (l : H) : Equiv.Perm (LB B H) :=
  ⟨fFB c l, fFB c l, fFB_invol c l, fFB_invol c l⟩

lemma mem_map_piB (c : B) (l : H) (S : Finset (LB B H)) (x : LB B H) :
    x ∈ S.map (piB c l).toEmbedding ↔ fFB c l x ∈ S :=
  Finset.mem_map_equiv

/-- what the base index set `q` must satisfy on the block `c`: all of it except `l`. -/
def BlockOfB (c : B) (l : H) (q : Finset (B × H)) : Prop := ∀ j, (c, j) ∈ q ↔ j ≠ l

lemma fFB_inl_mem (c : B) (l : H) (s : Finset H) (q : Finset (B × H))
    (hq : BlockOfB c l q) (i : H) : fFB c l (Sum.inl i) ∈ JB s q ↔ (i ≠ l ∨ l ∈ s) := by
  by_cases hi : i = l
  · rw [fFB_inl_eq c l i hi, Finset.inl_mem_disjSum, hi]
    exact ⟨fun h => Or.inr h, fun h => h.elim (fun h' => absurd rfl h') id⟩
  · rw [fFB_inl_ne c l i hi, Finset.inr_mem_disjSum]
    exact ⟨fun _ => Or.inl hi, fun _ => (hq i).mpr hi⟩

lemma fFB_inrc_mem (c : B) (l : H) (s : Finset H) (q : Finset (B × H))
    (hq : BlockOfB c l q) (j : H) : fFB c l (Sum.inr (c, j)) ∈ JB s q ↔ (j ≠ l ∧ j ∈ s) := by
  by_cases hj : j = l
  · rw [fFB_inr_neg c l c j (fun h => h.2 hj), Finset.inr_mem_disjSum]
    exact ⟨fun h => absurd hj ((hq j).mp h), fun h => absurd hj h.1⟩
  · rw [fFB_inr_pos c l c j ⟨rfl, hj⟩, Finset.inl_mem_disjSum]
    exact ⟨fun h => ⟨hj, h⟩, fun h => h.2⟩

lemma fFB_inro_mem (c : B) (l : H) (s : Finset H) (q : Finset (B × H)) (b : B)
    (hb : b ≠ c) (j : H) : fFB c l (Sum.inr (b, j)) ∈ JB s q ↔ (b, j) ∈ q := by
  rw [fFB_inr_neg c l b j (fun h => hb h.1), Finset.inr_mem_disjSum]

/-- the part of `q` outside the block `c`. -/
def RestB (c : B) (q r : Finset (B × H)) : Prop := ∀ b j, (b, j) ∈ r ↔ (b ≠ c ∧ (b, j) ∈ q)

/-- `X` entering the next stage: `<u> + base` is carried to `W_0 +` (the rest of the base). -/
lemma map_piB_single (c : B) (l : H) (q r : Finset (B × H)) (hq : BlockOfB c l q)
    (hr : RestB c q r) : (JB {l} q).map (piB c l).toEmbedding = JB univ r := by
  ext x
  rw [mem_map_piB]
  rcases x with i | ⟨b, j⟩
  · rw [fFB_inl_mem c l _ q hq, Finset.inl_mem_disjSum]
    exact ⟨fun _ => Finset.mem_univ i, fun _ => Or.inr (Finset.mem_singleton_self l)⟩
  · by_cases hb : b = c
    · rw [hb, fFB_inrc_mem c l _ q hq, Finset.inr_mem_disjSum]
      exact ⟨fun h => absurd (Finset.mem_singleton.mp h.2) h.1,
        fun h => absurd rfl ((hr c j).mp h).1⟩
    · rw [fFB_inro_mem c l _ q b hb, Finset.inr_mem_disjSum]
      exact ⟨fun h => (hr b j).mpr ⟨hb, h⟩, fun h => ((hr b j).mp h).2⟩

/-- `Y` entering the next stage: the base is carried to `(W_0 ∩ u^⊥) +` (the rest). -/
lemma map_piB_empty (c : B) (l : H) (q r : Finset (B × H)) (hq : BlockOfB c l q)
    (hr : RestB c q r) : (JB ∅ q).map (piB c l).toEmbedding = JB (univ \ {l}) r := by
  ext x
  rw [mem_map_piB]
  rcases x with i | ⟨b, j⟩
  · rw [fFB_inl_mem c l _ q hq, Finset.inl_mem_disjSum]
    constructor
    · intro h
      rcases h with h | h
      · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, fun h' => h (Finset.mem_singleton.mp h')⟩
      · exact absurd h (Finset.notMem_empty l)
    · intro h
      exact Or.inl (fun e => (Finset.mem_sdiff.mp h).2 (Finset.mem_singleton.mpr e))
  · by_cases hb : b = c
    · rw [hb, fFB_inrc_mem c l _ q hq, Finset.inr_mem_disjSum]
      exact ⟨fun h => absurd h.2 (Finset.notMem_empty j),
        fun h => absurd rfl ((hr c j).mp h).1⟩
    · rw [fFB_inro_mem c l _ q b hb, Finset.inr_mem_disjSum]
      exact ⟨fun h => (hr b j).mpr ⟨hb, h⟩, fun h => ((hr b j).mp h).2⟩

/-- `X` after its invocation: `W_0 + base` is preserved. -/
lemma map_piB_univ (c : B) (l : H) (q : Finset (B × H)) (hq : BlockOfB c l q) :
    (JB univ q).map (piB c l).toEmbedding = JB univ q := by
  ext x
  rw [mem_map_piB]
  rcases x with i | ⟨b, j⟩
  · rw [fFB_inl_mem c l _ q hq, Finset.inl_mem_disjSum]
    exact ⟨fun _ => Finset.mem_univ i, fun _ => Or.inr (Finset.mem_univ l)⟩
  · by_cases hb : b = c
    · rw [hb, fFB_inrc_mem c l _ q hq, Finset.inr_mem_disjSum]
      exact ⟨fun h => (hq j).mpr h.1, fun h => ⟨(hq j).mp h, Finset.mem_univ j⟩⟩
    · rw [fFB_inro_mem c l _ q b hb, Finset.inr_mem_disjSum]

/-- `Y` after its invocation: `(W_0 ∩ u^⊥) + base` is preserved. -/
lemma map_piB_compl (c : B) (l : H) (q : Finset (B × H)) (hq : BlockOfB c l q) :
    (JB (univ \ {l}) q).map (piB c l).toEmbedding = JB (univ \ {l}) q := by
  ext x
  rw [mem_map_piB]
  rcases x with i | ⟨b, j⟩
  · rw [fFB_inl_mem c l _ q hq, Finset.inl_mem_disjSum]
    constructor
    · intro h
      rcases h with h | h
      · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, fun h' => h (Finset.mem_singleton.mp h')⟩
      · exact absurd (Finset.mem_singleton_self l) (Finset.mem_sdiff.mp h).2
    · intro h
      exact Or.inl (fun e => (Finset.mem_sdiff.mp h).2 (Finset.mem_singleton.mpr e))
  · by_cases hb : b = c
    · rw [hb, fFB_inrc_mem c l _ q hq, Finset.inr_mem_disjSum]
      exact ⟨fun h => (hq j).mpr h.1, fun h => ⟨(hq j).mp h, Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ j, fun h' => (hq j).mp h (Finset.mem_singleton.mp h')⟩⟩⟩
    · rw [fFB_inro_mem c l _ q b hb, Finset.inr_mem_disjSum]

/-- exchange the blocks `0` and `c`. -/
def fTB (c : B) : LB B H → LB B H
  | .inl i => .inr (c, i)
  | .inr (b, j) => if b = c then .inl j else .inr (b, j)

lemma fTB_inl (c : B) (i : H) : fTB c (Sum.inl i) = Sum.inr (c, i) := rfl
lemma fTB_inr_pos (c b : B) (j : H) (h : b = c) : fTB c (Sum.inr (b, j)) = Sum.inl j := if_pos h
lemma fTB_inr_neg (c b : B) (j : H) (h : ¬ b = c) : fTB c (Sum.inr (b, j)) = Sum.inr (b, j) :=
  if_neg h

lemma fTB_invol (c : B) : Function.Involutive (fTB (H := H) c) := by
  intro x
  rcases x with i | ⟨b, j⟩
  · rw [fTB_inl, fTB_inr_pos c c i rfl]
  · by_cases hb : b = c
    · rw [fTB_inr_pos c b j hb, fTB_inl, hb]
    · rw [fTB_inr_neg c b j hb, fTB_inr_neg c b j hb]

/-- the isometry that carries `W_0` to the block `c`, as a permutation of indices. -/
def tauB (c : B) : Equiv.Perm (LB B H) := ⟨fTB c, fTB c, fTB_invol c, fTB_invol c⟩

lemma mem_map_tauB (c : B) (S : Finset (LB B H)) (x : LB B H) :
    x ∈ S.map (tauB c).toEmbedding ↔ fTB c x ∈ S :=
  Finset.mem_map_equiv

/-- the block `c` as a set of indices. -/
def blockS (c : B) : Finset (B × H) := univ.filter fun b => b.1 = c

lemma mem_blockS (c b : B) (j : H) : (b, j) ∈ blockS (H := H) c ↔ b = c := by
  unfold blockS
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

lemma map_tauB (c : B) :
    (JB (univ : Finset H) ∅).map (tauB c).toEmbedding = JB ∅ (blockS c) := by
  ext x
  rw [mem_map_tauB]
  rcases x with i | ⟨b, j⟩
  · rw [fTB_inl, Finset.inr_mem_disjSum, Finset.inl_mem_disjSum]
    exact ⟨fun h => absurd h (Finset.notMem_empty _), fun h => absurd h (Finset.notMem_empty _)⟩
  · by_cases hb : b = c
    · rw [fTB_inr_pos c b j hb, Finset.inl_mem_disjSum, Finset.inr_mem_disjSum]
      exact ⟨fun _ => (mem_blockS c b j).mpr hb, fun _ => Finset.mem_univ j⟩
    · rw [fTB_inr_neg c b j hb, Finset.inr_mem_disjSum, Finset.inr_mem_disjSum]
      exact ⟨fun h => absurd h (Finset.notMem_empty _),
        fun h => absurd ((mem_blockS c b j).mp h) hb⟩

end Perms
end
end BG
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.BG.PhiB_eq
#print axioms OAI.PowerSaving.BG.PhiB_perm
#print axioms OAI.PowerSaving.BG.map_piB_single
#print axioms OAI.PowerSaving.BG.map_piB_compl
#print axioms OAI.PowerSaving.BG.map_tauB
