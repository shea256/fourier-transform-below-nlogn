import Work.Reframe.GeomBase

/-!
# (key: bridge-c) The compressed label space `H ⊕ (B × H')`, `H' = {j : H // j ≠ l}`

Port of `Work.BridgeGeom.Blocks` (namespace `BG`) to the label space of the compressed nine-stage word of
CrocSwap/integer-mult-bounds PR #377 (jacklightChen): the `|B|` pivot coordinates `inr (c, l)` of `LB B H` are
deleted, so `card LC = h + |B| (h - 1)` (73 for `B = Fin 8`, `card H = 9`).  Blocks: `W_0 = inl _` (card `h`), and
one block `inr (c, _)` of card `h - 1` for every `c : B`.

* `JC s q`       index set: `s` in block 0, `q` in the other blocks;
* `blkC B l A`   orthogonal matrix: the columns of the basis `A` on block 0, the standard basis elsewhere;
* `PhiC d q P`   frame of `d (P ⊕ q) dᵀ`; `PhiC_eq`: in the basis `d (A ⊕ std)` it is the frame of `JC s q`;
* `PhiC_perm`    column permutations;
* `piC l c`      the involution exchanging `inl i` with `inr (c, i)` for `i ≠ l`;
                 `map_piC_single/_empty/_univ/_compl`.

The slot-window part of `BG` (`tauB`, `wS`, ...) is not ported: the banks of #377 are in `Work.BridgeC.Bank`.
Credit: the label geometry and every proof pattern are Jacob Sussman's (`Work.BridgeGeom`, Apache-2.0); the
compressed layout is jacklightChen's (PR #377).  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace BC
open Binary Matrix Finset RAM SS CB RF
noncomputable section

/-- the coordinates of a block other than block 0: `H` without the pivot `l`. -/
abbrev Hp (H : Type) (l : H) := {j : H // j ≠ l}

/-- the compressed label space: block 0 and one copy of `H \ {l}` for every `c : B`. -/
abbrev LC (B H : Type) (l : H) := H ⊕ (B × Hp H l)

section Blocks
variable {B H : Type} [Fintype B] [DecidableEq B] [Fintype H] [DecidableEq H] {l : H}

lemma card_Hp (l : H) : Fintype.card (Hp H l) = Fintype.card H - 1 := by
  rw [Fintype.card_subtype, Finset.filter_ne' Finset.univ l,
    Finset.card_erase_of_mem (Finset.mem_univ l), Finset.card_univ]

lemma card_LC (l : H) :
    Fintype.card (LC B H l) = Fintype.card H + Fintype.card B * (Fintype.card H - 1) := by
  simp only [Fintype.card_sum, Fintype.card_prod, card_Hp]

/-- index set: `s` in block 0, `q` in the other blocks. -/
abbrev JC (s : Finset H) (q : Finset (B × Hp H l)) : Finset (LC B H l) := s.disjSum q

lemma JC_sdiff (s t : Finset H) (q : Finset (B × Hp H l)) : JC t q \ JC s q = JC (t \ s) ∅ := by
  ext x
  rcases x with i | b
  · rw [Finset.mem_sdiff, Finset.inl_mem_disjSum, Finset.inl_mem_disjSum,
      Finset.inl_mem_disjSum, Finset.mem_sdiff]
  · rw [Finset.mem_sdiff, Finset.inr_mem_disjSum, Finset.inr_mem_disjSum,
      Finset.inr_mem_disjSum]
    exact ⟨fun h => absurd h.1 h.2, fun h => absurd h (Finset.notMem_empty b)⟩

lemma JC_sdiff_card (s t : Finset H) (q : Finset (B × Hp H l)) :
    (JC t q \ JC s q).card = (t \ s).card := by
  rw [JC_sdiff, Finset.card_disjSum, Finset.card_empty, add_zero]

lemma diagI_JC (s : Finset H) (q : Finset (B × Hp H l)) :
    diagI (JC s q) = Matrix.fromBlocks (diagI s) 0 0 (diagI q) := by
  ext x y
  rcases x with i | b <;> rcases y with j | b'
  · show diagI (JC s q) (Sum.inl i) (Sum.inl j) = diagI s i j
    rw [diagI_apply, diagI_apply]
    by_cases h : i = j
    · subst h
      rw [if_pos rfl, if_pos rfl]
      by_cases hi : i ∈ s
      · rw [if_pos hi, if_pos (Finset.inl_mem_disjSum.mpr hi)]
      · rw [if_neg hi,
          if_neg (fun h' : (Sum.inl i : LC B H l) ∈ JC s q => hi (Finset.inl_mem_disjSum.mp h'))]
    · rw [if_neg h, if_neg (fun h' : (Sum.inl i : LC B H l) = Sum.inl j => h (Sum.inl.inj h'))]
  · show diagI (JC s q) (Sum.inl i) (Sum.inr b') = 0
    rw [diagI_apply, if_neg Sum.inl_ne_inr]
  · show diagI (JC s q) (Sum.inr b) (Sum.inl j) = 0
    rw [diagI_apply, if_neg Sum.inr_ne_inl]
  · show diagI (JC s q) (Sum.inr b) (Sum.inr b') = diagI q b b'
    rw [diagI_apply, diagI_apply]
    by_cases h : b = b'
    · subst h
      rw [if_pos rfl, if_pos rfl]
      by_cases hi : b ∈ q
      · rw [if_pos hi, if_pos (Finset.inr_mem_disjSum.mpr hi)]
      · rw [if_neg hi,
          if_neg (fun h' : (Sum.inr b : LC B H l) ∈ JC s q => hi (Finset.inr_mem_disjSum.mp h'))]
    · rw [if_neg h, if_neg (fun h' : (Sum.inr b : LC B H l) = Sum.inr b' => h (Sum.inr.inj h'))]

variable (B l) in
/-- the columns of `A` on block 0, the standard basis on the other blocks (`B`, `l` explicit). -/
def blkC (A : OBase H) : Matrix (LC B H l) (LC B H l) F := Matrix.fromBlocks (cmat A) 0 0 1

lemma blkC_orth (A : OBase H) : (blkC B l A)ᵀ * blkC B l A = 1 := by
  unfold blkC
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  simp only [cmat_orth, Matrix.transpose_zero, Matrix.transpose_one, Matrix.mul_zero,
    Matrix.zero_mul, Matrix.mul_one, add_zero, zero_add, Matrix.fromBlocks_one]

lemma blkC_conj (A : OBase H) (s : Finset H) (q : Finset (B × Hp H l)) :
    blkC B l A * diagI (JC s q) * (blkC B l A)ᵀ = Matrix.fromBlocks (A.mat s) 0 0 (diagI q) := by
  rw [diagI_JC, mat_eq_cmat]
  unfold blkC
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.transpose_zero, Matrix.transpose_one, Matrix.mul_zero, Matrix.zero_mul,
    Matrix.mul_one, Matrix.one_mul, add_zero, zero_add]

/-- frame of `d (P ⊕ q) dᵀ`. -/
def PhiC (d : Orth (LC B H l)) (q : Finset (B × Hp H l)) (P : Matrix H H F) : CMat (LC B H l) :=
  frameM (d.1 * Matrix.fromBlocks P 0 0 (diagI q) * d.1ᵀ)

lemma conj_blkC (d : Matrix (LC B H l) (LC B H l) F) (A : OBase H) (s : Finset H)
    (q : Finset (B × Hp H l)) :
    d * Matrix.fromBlocks (A.mat s) 0 0 (diagI q) * dᵀ
      = (d * blkC B l A) * diagI (JC s q) * (d * blkC B l A)ᵀ := by
  rw [← blkC_conj]
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]

/-- in the basis `d (A ⊕ std)` the frame `PhiC d q (A.mat s)` is the frame of `JC s q`. -/
lemma PhiC_eq (d : Orth (LC B H l)) (q : Finset (B × Hp H l)) (A : OBase H) (s : Finset H) :
    PhiC d q (A.mat s)
      = frame (ofCols (d.1 * blkC B l A) (mul_orth d.2 (blkC_orth A))) (JC s q) := by
  rw [frame_ofCols]
  unfold PhiC
  rw [conj_blkC]

/-- column permutation: `PhiC` of the permuted matrix is `PhiC` of the permuted index set. -/
lemma PhiC_perm (d g : Orth (LC B H l)) (A : OBase H) (π : Equiv.Perm (LC B H l))
    (hd : d.1 * blkC B l A = (g.1 * blkC B l A).submatrix id π) (s s' : Finset H)
    (q q' : Finset (B × Hp H l)) (hmap : (JC s q).map π.toEmbedding = JC s' q') :
    PhiC d q (A.mat s) = PhiC g q' (A.mat s') := by
  unfold PhiC
  rw [conj_blkC, conj_blkC, hd, submatrix_diagI, hmap]

end Blocks

section Perms
variable {B H : Type} [Fintype B] [DecidableEq B] [Fintype H] [DecidableEq H]

variable (l : H) in
/-- exchange `inl i` with `inr (c, i)` for `i ≠ l`; everything else is fixed. -/
def fFC (c : B) : LC B H l → LC B H l
  | .inl i => if h : i = l then .inl i else .inr (c, ⟨i, h⟩)
  | .inr (b, j) => if b = c then .inl j.1 else .inr (b, j)

lemma fFC_inl_eq (l : H) (c : B) (i : H) (hi : i = l) :
    fFC l c (Sum.inl i : LC B H l) = Sum.inl i := dif_pos hi
lemma fFC_inl_ne (l : H) (c : B) (i : H) (hi : i ≠ l) :
    fFC l c (Sum.inl i : LC B H l) = Sum.inr (c, ⟨i, hi⟩) := dif_neg hi
lemma fFC_inr_pos (l : H) (c b : B) (j : Hp H l) (h : b = c) :
    fFC l c (Sum.inr (b, j) : LC B H l) = Sum.inl j.1 := if_pos h
lemma fFC_inr_neg (l : H) (c b : B) (j : Hp H l) (h : ¬ b = c) :
    fFC l c (Sum.inr (b, j) : LC B H l) = Sum.inr (b, j) := if_neg h

lemma fFC_invol (l : H) (c : B) : Function.Involutive (fFC l c (B := B)) := by
  intro x
  rcases x with i | ⟨b, j⟩
  · by_cases hi : i = l
    · rw [fFC_inl_eq l c i hi, fFC_inl_eq l c i hi]
    · rw [fFC_inl_ne l c i hi, fFC_inr_pos l c c ⟨i, hi⟩ rfl]
  · by_cases hb : b = c
    · rw [fFC_inr_pos l c b j hb, fFC_inl_ne l c j.1 j.2, hb]
    · rw [fFC_inr_neg l c b j hb, fFC_inr_neg l c b j hb]

/-- `rho^(c)_t` as a permutation of the indices of the basis `(base t) ⊕ std`, when the pivot of
`t` is `l` (the pivot coordinates of the other blocks are deleted in `LC`). -/
def piC (l : H) (c : B) : Equiv.Perm (LC B H l) :=
  ⟨fFC l c, fFC l c, fFC_invol l c, fFC_invol l c⟩

lemma mem_map_piC (l : H) (c : B) (S : Finset (LC B H l)) (x : LC B H l) :
    x ∈ S.map (piC l c).toEmbedding ↔ fFC l c x ∈ S :=
  Finset.mem_map_equiv

/-- what the base index set `q` must satisfy on the block `c`: all of it. -/
def BlockOfC {l : H} (c : B) (q : Finset (B × Hp H l)) : Prop := ∀ j, (c, j) ∈ q

lemma fFC_inl_mem (l : H) (c : B) (s : Finset H) (q : Finset (B × Hp H l))
    (hq : BlockOfC c q) (i : H) : fFC l c (Sum.inl i) ∈ JC s q ↔ (i ≠ l ∨ l ∈ s) := by
  by_cases hi : i = l
  · rw [fFC_inl_eq l c i hi, Finset.inl_mem_disjSum, hi]
    exact ⟨fun h => Or.inr h, fun h => h.elim (fun h' => absurd rfl h') id⟩
  · rw [fFC_inl_ne l c i hi, Finset.inr_mem_disjSum]
    exact ⟨fun _ => Or.inl hi, fun _ => hq ⟨i, hi⟩⟩

lemma fFC_inrc_mem (l : H) (c : B) (s : Finset H) (q : Finset (B × Hp H l)) (j : Hp H l) :
    fFC l c (Sum.inr (c, j)) ∈ JC s q ↔ j.1 ∈ s := by
  rw [fFC_inr_pos l c c j rfl, Finset.inl_mem_disjSum]

lemma fFC_inro_mem (l : H) (c : B) (s : Finset H) (q : Finset (B × Hp H l)) (b : B)
    (hb : b ≠ c) (j : Hp H l) : fFC l c (Sum.inr (b, j)) ∈ JC s q ↔ (b, j) ∈ q := by
  rw [fFC_inr_neg l c b j hb, Finset.inr_mem_disjSum]

/-- the part of `q` outside the block `c`. -/
def RestC {l : H} (c : B) (q r : Finset (B × Hp H l)) : Prop :=
  ∀ b j, (b, j) ∈ r ↔ (b ≠ c ∧ (b, j) ∈ q)

/-- `X` entering the next stage: `<u> + base` is carried to `W_0 +` (the rest of the base). -/
lemma map_piC_single (l : H) (c : B) (q r : Finset (B × Hp H l)) (hq : BlockOfC c q)
    (hr : RestC c q r) : (JC {l} q).map (piC l c).toEmbedding = JC univ r := by
  ext x
  rw [mem_map_piC]
  rcases x with i | ⟨b, j⟩
  · rw [fFC_inl_mem l c _ q hq, Finset.inl_mem_disjSum]
    exact ⟨fun _ => Finset.mem_univ i, fun _ => Or.inr (Finset.mem_singleton_self l)⟩
  · by_cases hb : b = c
    · rw [hb, fFC_inrc_mem l c _ q, Finset.inr_mem_disjSum]
      exact ⟨fun h => absurd (Finset.mem_singleton.mp h) j.2,
        fun h => absurd rfl ((hr c j).mp h).1⟩
    · rw [fFC_inro_mem l c _ q b hb, Finset.inr_mem_disjSum]
      exact ⟨fun h => (hr b j).mpr ⟨hb, h⟩, fun h => ((hr b j).mp h).2⟩

/-- `Y` entering the next stage: the base is carried to `(W_0 ∩ u^⊥) +` (the rest). -/
lemma map_piC_empty (l : H) (c : B) (q r : Finset (B × Hp H l)) (hq : BlockOfC c q)
    (hr : RestC c q r) : (JC ∅ q).map (piC l c).toEmbedding = JC (univ \ {l}) r := by
  ext x
  rw [mem_map_piC]
  rcases x with i | ⟨b, j⟩
  · rw [fFC_inl_mem l c _ q hq, Finset.inl_mem_disjSum]
    constructor
    · intro h
      rcases h with h | h
      · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, fun h' => h (Finset.mem_singleton.mp h')⟩
      · exact absurd h (Finset.notMem_empty l)
    · intro h
      exact Or.inl (fun e => (Finset.mem_sdiff.mp h).2 (Finset.mem_singleton.mpr e))
  · by_cases hb : b = c
    · rw [hb, fFC_inrc_mem l c _ q, Finset.inr_mem_disjSum]
      exact ⟨fun h => absurd h (Finset.notMem_empty j.1),
        fun h => absurd rfl ((hr c j).mp h).1⟩
    · rw [fFC_inro_mem l c _ q b hb, Finset.inr_mem_disjSum]
      exact ⟨fun h => (hr b j).mpr ⟨hb, h⟩, fun h => ((hr b j).mp h).2⟩

/-- `X` after its invocation: `W_0 + base` is preserved. -/
lemma map_piC_univ (l : H) (c : B) (q : Finset (B × Hp H l)) (hq : BlockOfC c q) :
    (JC univ q).map (piC l c).toEmbedding = JC univ q := by
  ext x
  rw [mem_map_piC]
  rcases x with i | ⟨b, j⟩
  · rw [fFC_inl_mem l c _ q hq, Finset.inl_mem_disjSum]
    exact ⟨fun _ => Finset.mem_univ i, fun _ => Or.inr (Finset.mem_univ l)⟩
  · by_cases hb : b = c
    · rw [hb, fFC_inrc_mem l c _ q, Finset.inr_mem_disjSum]
      exact ⟨fun _ => hq j, fun _ => Finset.mem_univ j.1⟩
    · rw [fFC_inro_mem l c _ q b hb, Finset.inr_mem_disjSum]

/-- `Y` after its invocation: `(W_0 ∩ u^⊥) + base` is preserved. -/
lemma map_piC_compl (l : H) (c : B) (q : Finset (B × Hp H l)) (hq : BlockOfC c q) :
    (JC (univ \ {l}) q).map (piC l c).toEmbedding = JC (univ \ {l}) q := by
  ext x
  rw [mem_map_piC]
  rcases x with i | ⟨b, j⟩
  · rw [fFC_inl_mem l c _ q hq, Finset.inl_mem_disjSum]
    constructor
    · intro h
      rcases h with h | h
      · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, fun h' => h (Finset.mem_singleton.mp h')⟩
      · exact absurd (Finset.mem_singleton_self l) (Finset.mem_sdiff.mp h).2
    · intro h
      exact Or.inl (fun e => (Finset.mem_sdiff.mp h).2 (Finset.mem_singleton.mpr e))
  · by_cases hb : b = c
    · rw [hb, fFC_inrc_mem l c _ q, Finset.inr_mem_disjSum]
      exact ⟨fun _ => hq j, fun _ => Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ j.1, fun h' => j.2 (Finset.mem_singleton.mp h')⟩⟩
    · rw [fFC_inro_mem l c _ q b hb, Finset.inr_mem_disjSum]

end Perms
end
end BC
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.BC.card_LC
#print axioms OAI.PowerSaving.BC.PhiC_eq
#print axioms OAI.PowerSaving.BC.PhiC_perm
#print axioms OAI.PowerSaving.BC.map_piC_single
#print axioms OAI.PowerSaving.BC.map_piC_empty
#print axioms OAI.PowerSaving.BC.map_piC_univ
#print axioms OAI.PowerSaving.BC.map_piC_compl
