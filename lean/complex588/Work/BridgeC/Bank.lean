import Work.BridgeC.Stage

/-!
# (key: bridge-c) The banks of the compressed nine-stage word (PR #377)

The label space `LC (Fin 8) H l` (`Work.BridgeC.Blocks`) has `card H + 8 (card H - 1)` coordinates: block 0
(`inl _`, `card H` of them) and 8 rows `inr (c, _)` of `card H - 1`.  For `card H = 9` that is `73 = 8·9 + 1`.  A bank
climbs its frame window by window: in sub-stage `ρ` the window `blk ρ` (9 coordinates), then ONE rank-1 climb over
the padding coordinate `pad`.  Given an enumeration `f : Fin 8 ≃ H \ {l}` of a row:

* `blk 0 = JC univ ∅` (block 0);  `blk ρ = row ρ ∪ {inr (0, f ρ)}` for `ρ ≠ 0`;  `pad = inr (0, f 0)`;
  `blk_disj`, `card_blk` (`= card H`), `biUnion_blk` (`⋃ ρ, blk ρ = univ \ {pad}`);
* `sig ρ`  an involution of the coordinates with `(JC univ ∅).map (sig ρ) = blk ρ` (`map_sig`), and `W_sig`: the
  window of the invocation `g · sig ρ` is the frame of `blk ρ` in the basis of the columns of `g`;
* `bacc ρ = ⋃_{ρ' < ρ} blk ρ'`; `bwin_step` (one more window), `bacc_zero`, `bwin_all` (all eight windows give the
  frame of `univ \ {pad}`), `pad_climb` (ONE rank-1 climb to the kernel), `bank_start`.

The windows are the analog of `BG.tauB` / `BG.win_*` (Jacob Sussman, `Work.BridgeGeom.Stage`); the banks of 8 windows
of 9 plus one padding coordinate are jacklightChen's (CrocSwap/integer-mult-bounds PR #377).  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace BC
open Binary Matrix Finset RAM SS CB RF
noncomputable section

section Bank
variable {H : Type} [Fintype H] [DecidableEq H] (l : H) (f : Fin 8 ≃ Hp H l)

include l f in
lemma card_H_of_enum : Fintype.card H = 9 := by
  have h := Fintype.card_congr f
  rw [Fintype.card_fin, card_Hp] at h
  have h1 : 1 ≤ Fintype.card H := Fintype.card_pos_iff.mpr ⟨l⟩
  omega

include f in
lemma card_LC_enum : Fintype.card (LC (Fin 8) H l) = 73 := by
  rw [card_LC, Fintype.card_fin, card_H_of_enum l f]

/-- membership in the window `ρ`, as a Boolean. -/
def bk (ρ : Fin 8) : LC (Fin 8) H l → Bool
  | .inl _ => decide (ρ = 0)
  | .inr (b, j) => decide (ρ ≠ 0 ∧ (b = ρ ∨ (b = 0 ∧ j = f ρ)))

/-- the window of sub-stage `ρ`. -/
def blk (ρ : Fin 8) : Finset (LC (Fin 8) H l) := univ.filter (fun x => bk l f ρ x = true)

/-- the padding coordinate. -/
def pad : LC (Fin 8) H l := Sum.inr (0, f 0)

lemma mem_blk_inl (ρ : Fin 8) (i : H) : (Sum.inl i : LC (Fin 8) H l) ∈ blk l f ρ ↔ ρ = 0 := by
  unfold blk bk
  rw [Finset.mem_filter, decide_eq_true_iff]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

lemma mem_blk_inr (ρ b : Fin 8) (j : Hp H l) :
    (Sum.inr (b, j) : LC (Fin 8) H l) ∈ blk l f ρ ↔ (ρ ≠ 0 ∧ (b = ρ ∨ (b = 0 ∧ j = f ρ))) := by
  unfold blk bk
  rw [Finset.mem_filter, decide_eq_true_iff]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

lemma blk_zero : blk l f 0 = JC univ ∅ := by
  ext x
  rcases x with i | ⟨b, j⟩
  · rw [mem_blk_inl, Finset.inl_mem_disjSum]
    exact ⟨fun _ => Finset.mem_univ i, fun _ => rfl⟩
  · rw [mem_blk_inr, Finset.inr_mem_disjSum]
    exact ⟨fun h => absurd rfl h.1, fun h => absurd h (Finset.notMem_empty _)⟩

lemma blk_disj {ρ ρ' : Fin 8} (h : ρ ≠ ρ') : Disjoint (blk l f ρ) (blk l f ρ') := by
  refine Finset.disjoint_left.mpr (fun x h1 h2 => ?_)
  rcases x with i | ⟨b, j⟩
  · rw [mem_blk_inl] at h1 h2
    exact h (h1.trans h2.symm)
  · rw [mem_blk_inr] at h1 h2
    rcases h1 with ⟨h1, e1 | ⟨e1, j1⟩⟩ <;> rcases h2 with ⟨h2, e2 | ⟨e2, j2⟩⟩
    · exact h (e1.symm.trans e2)
    · exact h1 (e1.symm.trans e2)
    · exact h2 (e2.symm.trans e1)
    · exact h (f.injective (j1.symm.trans j2))

lemma pad_not_mem (ρ : Fin 8) : pad l f ∉ blk l f ρ := by
  unfold pad
  rw [mem_blk_inr]
  rintro ⟨h, e | ⟨_, e⟩⟩
  · exact h e.symm
  · exact h (f.injective e).symm

/-- the row `ρ` of a window. -/
def rowE (ρ : Fin 8) : Hp H l ↪ LC (Fin 8) H l := ⟨fun j => Sum.inr (ρ, j), fun a b h => by
  have := Sum.inr.inj h
  exact (Prod.mk.inj this).2⟩

lemma blk_ne (ρ : Fin 8) (hρ : ρ ≠ 0) :
    blk l f ρ = insert (Sum.inr (0, f ρ)) ((univ : Finset (Hp H l)).map (rowE l ρ)) := by
  ext x
  rw [Finset.mem_insert, Finset.mem_map]
  rcases x with i | ⟨b, j⟩
  · rw [mem_blk_inl]
    constructor
    · intro h
      exact absurd h hρ
    · rintro (h | ⟨a, _, h⟩)
      · exact absurd h Sum.inl_ne_inr
      · exact absurd h Sum.inr_ne_inl
  · rw [mem_blk_inr]
    constructor
    · rintro ⟨_, e | ⟨e1, e2⟩⟩
      · exact Or.inr ⟨j, Finset.mem_univ j, by rw [e]; rfl⟩
      · exact Or.inl (by rw [e1, e2])
    · rintro (h | ⟨a, _, h⟩)
      · have h' := Prod.mk.inj (Sum.inr.inj h)
        exact ⟨hρ, Or.inr ⟨h'.1, h'.2⟩⟩
      · have h' := Prod.mk.inj (Sum.inr.inj h)
        exact ⟨hρ, Or.inl h'.1.symm⟩

lemma card_blk (ρ : Fin 8) : (blk l f ρ).card = Fintype.card H := by
  by_cases hρ : ρ = 0
  · rw [hρ, blk_zero, Finset.card_disjSum, Finset.card_univ, Finset.card_empty, add_zero]
  · have hn : (Sum.inr (0, f ρ) : LC (Fin 8) H l) ∉ (univ : Finset (Hp H l)).map (rowE l ρ) := by
      rw [Finset.mem_map]
      rintro ⟨a, _, h⟩
      exact hρ (Prod.mk.inj (Sum.inr.inj h)).1
    have h1 : 1 ≤ Fintype.card H := Fintype.card_pos_iff.mpr ⟨l⟩
    rw [blk_ne l f ρ hρ, Finset.card_insert_of_notMem hn, Finset.card_map, Finset.card_univ, card_Hp]
    omega

/-- all eight windows: everything but the padding coordinate. -/
lemma biUnion_blk : (univ : Finset (Fin 8)).biUnion (blk l f) = univ \ {pad l f} := by
  ext x
  rw [Finset.mem_biUnion, Finset.mem_sdiff, Finset.mem_singleton]
  constructor
  · rintro ⟨ρ, _, h⟩
    exact ⟨Finset.mem_univ x, fun e => pad_not_mem l f ρ (e ▸ h)⟩
  · rintro ⟨_, hx⟩
    rcases x with i | ⟨b, j⟩
    · exact ⟨0, Finset.mem_univ _, (mem_blk_inl l f 0 i).mpr rfl⟩
    · by_cases hb : b = 0
      · refine ⟨f.symm j, Finset.mem_univ _, (mem_blk_inr l f _ b j).mpr ⟨fun e => hx ?_, Or.inr ⟨hb, ?_⟩⟩⟩
        · unfold pad
          rw [hb, ← e, Equiv.apply_symm_apply]
        · rw [Equiv.apply_symm_apply]
      · exact ⟨b, Finset.mem_univ _, (mem_blk_inr l f b b j).mpr ⟨hb, Or.inl rfl⟩⟩

/-! ### the involutions `sig ρ` -/

/-- exchange block 0 with the window `ρ`: `inl l ↔ inr (0, f ρ)`, `inl i ↔ inr (ρ, i)` (`i ≠ l`); the identity
for `ρ = 0`. -/
def fSG (ρ : Fin 8) : LC (Fin 8) H l → LC (Fin 8) H l
  | .inl i => if ρ = 0 then .inl i else if h : i = l then .inr (0, f ρ) else .inr (ρ, ⟨i, h⟩)
  | .inr (b, j) => if ρ = 0 then .inr (b, j) else if b = ρ then .inl j.1
      else if b = 0 ∧ j = f ρ then .inl l else .inr (b, j)

lemma fSG_zero (x : LC (Fin 8) H l) : fSG l f 0 x = x := by
  rcases x with i | ⟨b, j⟩ <;> simp [fSG]

lemma fSG_inl_l (ρ : Fin 8) (hρ : ρ ≠ 0) : fSG l f ρ (Sum.inl l) = Sum.inr (0, f ρ) := by
  show (if ρ = 0 then _ else _) = _
  rw [if_neg hρ, dif_pos rfl]

lemma fSG_inl_ne (ρ : Fin 8) (hρ : ρ ≠ 0) (i : H) (hi : i ≠ l) :
    fSG l f ρ (Sum.inl i) = Sum.inr (ρ, ⟨i, hi⟩) := by
  show (if ρ = 0 then _ else _) = _
  rw [if_neg hρ, dif_neg hi]

lemma fSG_row (ρ : Fin 8) (hρ : ρ ≠ 0) (j : Hp H l) :
    fSG l f ρ (Sum.inr (ρ, j)) = Sum.inl j.1 := by
  show (if ρ = 0 then _ else _) = _
  rw [if_neg hρ, if_pos rfl]

lemma fSG_pad (ρ : Fin 8) (hρ : ρ ≠ 0) : fSG l f ρ (Sum.inr (0, f ρ)) = Sum.inl l := by
  show (if ρ = 0 then _ else _) = _
  rw [if_neg hρ, if_neg (fun e => hρ e.symm), if_pos ⟨rfl, rfl⟩]

lemma fSG_other (ρ : Fin 8) (b : Fin 8) (j : Hp H l) (hb : b ≠ ρ) (h0 : ¬ (b = 0 ∧ j = f ρ)) :
    fSG l f ρ (Sum.inr (b, j)) = Sum.inr (b, j) := by
  by_cases hρ : ρ = 0
  · rw [hρ]
    exact fSG_zero l f _
  · show (if ρ = 0 then _ else _) = _
    rw [if_neg hρ, if_neg hb, if_neg h0]

lemma fSG_invol (ρ : Fin 8) : Function.Involutive (fSG l f ρ) := by
  intro x
  by_cases hρ : ρ = 0
  · rw [hρ, fSG_zero, fSG_zero]
  rcases x with i | ⟨b, j⟩
  · by_cases hi : i = l
    · rw [hi, fSG_inl_l l f ρ hρ, fSG_pad l f ρ hρ]
    · rw [fSG_inl_ne l f ρ hρ i hi, fSG_row l f ρ hρ]
  · by_cases hb : b = ρ
    · rw [hb, fSG_row l f ρ hρ, fSG_inl_ne l f ρ hρ j.1 j.2]
    · by_cases h0 : b = 0 ∧ j = f ρ
      · rw [h0.1, h0.2, fSG_pad l f ρ hρ, fSG_inl_l l f ρ hρ]
      · rw [fSG_other l f ρ b j hb h0, fSG_other l f ρ b j hb h0]

/-- the involution exchanging block 0 with the window `ρ`. -/
def sig (ρ : Fin 8) : Equiv.Perm (LC (Fin 8) H l) :=
  ⟨fSG l f ρ, fSG l f ρ, fSG_invol l f ρ, fSG_invol l f ρ⟩

lemma sig_invol (ρ : Fin 8) : (sig l f ρ) * (sig l f ρ) = 1 :=
  Equiv.ext (fun x => fSG_invol l f ρ x)

lemma map_sig (ρ : Fin 8) : (JC (univ : Finset H) ∅).map (sig l f ρ).toEmbedding = blk l f ρ := by
  by_cases hρ : ρ = 0
  · rw [hρ, blk_zero]
    ext x
    rw [Finset.mem_map_equiv]
    show fSG l f 0 x ∈ _ ↔ _
    rw [fSG_zero]
  ext x
  rw [Finset.mem_map_equiv]
  show fSG l f ρ x ∈ _ ↔ _
  rcases x with i | ⟨b, j⟩
  · rw [mem_blk_inl]
    by_cases hi : i = l
    · rw [hi, fSG_inl_l l f ρ hρ, Finset.inr_mem_disjSum]
      exact ⟨fun h => absurd h (Finset.notMem_empty _), fun h => absurd h hρ⟩
    · rw [fSG_inl_ne l f ρ hρ i hi, Finset.inr_mem_disjSum]
      exact ⟨fun h => absurd h (Finset.notMem_empty _), fun h => absurd h hρ⟩
  · rw [mem_blk_inr]
    by_cases hb : b = ρ
    · rw [hb, fSG_row l f ρ hρ, Finset.inl_mem_disjSum]
      exact ⟨fun _ => ⟨hρ, Or.inl rfl⟩, fun _ => Finset.mem_univ _⟩
    · by_cases h0 : b = 0 ∧ j = f ρ
      · rw [h0.1, h0.2, fSG_pad l f ρ hρ, Finset.inl_mem_disjSum]
        exact ⟨fun _ => ⟨hρ, Or.inr ⟨rfl, rfl⟩⟩, fun _ => Finset.mem_univ _⟩
      · rw [fSG_other l f ρ b j hb h0, Finset.inr_mem_disjSum]
        constructor
        · intro h
          exact absurd h (Finset.notMem_empty _)
        · rintro ⟨_, e | e⟩
          · exact absurd e hb
          · exact absurd e h0

/-- the window frame of the invocation `g · sig ρ` is the frame of the window `blk ρ` in the basis of the columns
of `g` (analog of `BG.W_tauB`). -/
lemma W_sig (ρ : Fin 8) (g : Orth (LC (Fin 8) H l)) :
    frameM ((Orth.colPerm (sig l f ρ) g).1 * diagI (JC univ ∅) * (Orth.colPerm (sig l f ρ) g).1ᵀ)
      = frameM (g.1 * diagI (blk l f ρ) * g.1ᵀ) := by
  rw [Orth.colPerm_val, submatrix_diagI, map_sig]

/-! ### accumulated windows -/

/-- frames of disjoint index sets, transported by `g`, multiply. -/
lemma frame_union {n : Type} [Fintype n] [DecidableEq n] (g : Orth n) (S T : Finset n)
    (h : Disjoint S T) :
    frameM (g.1 * diagI S * g.1ᵀ) * frameM (g.1 * diagI T * g.1ᵀ)
      = frameM (g.1 * diagI (S ∪ T) * g.1ᵀ) := by
  rw [← frameM_conj_add g.1 g.2 _ _ (diagI_orth _ _ h), ← diagI_union _ _ h]

/-- the windows before sub-stage `ρ`. -/
def bacc (ρ : Fin 8) : Finset (LC (Fin 8) H l) :=
  (univ.filter (fun ρ' : Fin 8 => ρ' < ρ)).biUnion (blk l f)

/-- the windows up to and including sub-stage `ρ`. -/
def bupto (ρ : Fin 8) : Finset (LC (Fin 8) H l) :=
  (univ.filter (fun ρ' : Fin 8 => ρ' ≤ ρ)).biUnion (blk l f)

lemma bacc_zero : bacc l f 0 = ∅ := by
  unfold bacc
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.notMem_empty, iff_false]
  rintro ⟨ρ', ⟨_, h⟩, _⟩
  exact Fin.not_lt_zero ρ' h

lemma bacc_succ (ρ : Fin 8) (ρ' : Fin 8) (h : ρ'.val = ρ.val + 1) : bacc l f ρ' = bupto l f ρ := by
  unfold bacc bupto
  congr 1
  ext c
  rw [Finset.mem_filter, Finset.mem_filter, Fin.lt_def, Fin.le_def, h]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by omega⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by omega⟩

lemma bupto_last : bupto l f 7 = univ \ {pad l f} := by
  rw [← biUnion_blk l f]
  unfold bupto
  congr 1

lemma blk_disj_bacc (ρ : Fin 8) : Disjoint (blk l f ρ) (bacc l f ρ) := by
  unfold bacc
  rw [Finset.disjoint_biUnion_right]
  intro ρ' h
  exact blk_disj l f (fun e => (lt_irrefl ρ') (e ▸ (Finset.mem_filter.mp h).2))

lemma blk_union_bacc (ρ : Fin 8) : blk l f ρ ∪ bacc l f ρ = bupto l f ρ := by
  unfold bacc bupto
  ext x
  rw [Finset.mem_union, Finset.mem_biUnion, Finset.mem_biUnion]
  constructor
  · rintro (h | ⟨ρ', h1, h2⟩)
    · exact ⟨ρ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_refl ρ⟩, h⟩
    · exact ⟨ρ', Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_lt (Finset.mem_filter.mp h1).2⟩, h2⟩
  · rintro ⟨ρ', h1, h2⟩
    rcases lt_or_eq_of_le (Finset.mem_filter.mp h1).2 with h3 | h3
    · exact Or.inr ⟨ρ', Finset.mem_filter.mpr ⟨Finset.mem_univ _, h3⟩, h2⟩
    · exact Or.inl (h3 ▸ h2)

/-- one more window: the frame of `blk ρ` times the frame of the earlier windows. -/
lemma bwin_step (g : Orth (LC (Fin 8) H l)) (ρ : Fin 8) :
    frameM (g.1 * diagI (blk l f ρ) * g.1ᵀ) * frameM (g.1 * diagI (bacc l f ρ) * g.1ᵀ)
      = frameM (g.1 * diagI (bupto l f ρ) * g.1ᵀ) := by
  rw [frame_union g _ _ (blk_disj_bacc l f ρ), blk_union_bacc]

/-- all eight windows together: the frame of everything but the padding coordinate. -/
lemma bwin_all (g : Orth (LC (Fin 8) H l)) :
    frameM (g.1 * diagI ((univ : Finset (Fin 8)).biUnion (blk l f)) * g.1ᵀ)
      = frameM (g.1 * diagI (univ \ {pad l f}) * g.1ᵀ) := by
  rw [biUnion_blk]

/-- a bank starts at frame `1`. -/
lemma bank_start (g : Orth (LC (Fin 8) H l)) : frameM (g.1 * diagI ∅ * g.1ᵀ) = 1 := by
  rw [diagI_empty, Matrix.mul_zero, Matrix.zero_mul, frameM_zero]

/-- the padding step: ONE rank-1 climb to the kernel. -/
lemma pad_climb (g : Orth (LC (Fin 8) H l)) :
    XReach (frameM (g.1 * diagI (univ \ {pad l f}) * g.1ᵀ)) (kernel (LC (Fin 8) H l))
      (fun φ => bcost φ 1) := by
  have hc := card_LC_enum l f
  rw [← frame_ofCols g.1 g.2, ← frame_univ (ofCols g.1 g.2)]
  refine reach_of_pos (by omega) (ofCols g.1 g.2) (Finset.sdiff_subset) 1 ?_ ?_
  · rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr (Finset.mem_univ _)),
      Finset.card_univ, Finset.card_singleton, hc]
  · rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr (Finset.mem_univ _)),
      Finset.card_univ, Finset.card_singleton, hc]
    omega

end Bank

/-- an enumeration of a row, for `card H = 9` (any one serves). -/
def enumOf {H : Type} [Fintype H] [DecidableEq H] (l : H) (hH : Fintype.card H = 9) : Fin 8 ≃ Hp H l :=
  (Fintype.equivFinOfCardEq (by rw [card_Hp, hH])).symm

end
end BC
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.BC.card_blk
#print axioms OAI.PowerSaving.BC.biUnion_blk
#print axioms OAI.PowerSaving.BC.map_sig
#print axioms OAI.PowerSaving.BC.W_sig
#print axioms OAI.PowerSaving.BC.bwin_step
#print axioms OAI.PowerSaving.BC.bupto_last
#print axioms OAI.PowerSaving.BC.pad_climb
#print axioms OAI.PowerSaving.BC.bank_start
#print axioms OAI.PowerSaving.BC.enumOf
