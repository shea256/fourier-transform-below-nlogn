import Work.Bridge401.GNetCert
import Work.Bridge401.Sched
import Work.Bridge377.WinC
import Work.BridgeC.Bank
import Work.GCert.Chain.Geom

/-!
# (key: bridge-401) The compressed nine-stage word of PR #377 delivers a `GCert` (geometry on `LC (Fin 8) H l`)

Credits: the entrance gauges and the residual banks are Dugongue's (CrocSwap/integer-mult-bounds PR #401); the bank
patterns are Lydakis's (#275); the compressed nine-stage layout is jacklightChen's (#377); the bridged word B_K is
DaysSky's (#363); B_2, the engine, the stage geometry and the E8 unit are Jacob Sussman's (wht-power-saving-lean,
Apache-2.0).  Written by w-newsums/gen401/gen401.py (from gen377.py).  Copy of genk's GGeom (B_4) on the compressed label space of Work/BridgeC (`H ⊕ (Fin 8 × (H \ {l}))`,
73 coordinates for `card H = 9`), with the banks of Work/BridgeC/Bank.lean.

`bridge401_gcert I hH l`: for every generalised invocation package, a `GCert` on
`card Γ * (64 card T + 9 card Sl)` live roles, label dimension 73, unit price
`unitPrice401 I φ = 72 * I.cost φ + card T * bankPrice377 φ + 9 card Sl * bcost φ 1`.  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace OAI
namespace PowerSaving
namespace GX
open Binary Matrix Finset RAM SS CB RF BR GF
noncomputable section

open BC

abbrev bs401_1 : Finset (Fin 8) := {0}
abbrev bs401_2 : Finset (Fin 8) := insert 1 bs401_1
abbrev bs401_3 : Finset (Fin 8) := insert 2 bs401_2
abbrev bs401_4 : Finset (Fin 8) := insert 3 bs401_3
abbrev bs401_5 : Finset (Fin 8) := insert 4 bs401_4
abbrev bs401_6 : Finset (Fin 8) := insert 5 bs401_5
abbrev bs401_7 : Finset (Fin 8) := insert 6 bs401_6
abbrev bs401_8 : Finset (Fin 8) := insert 7 bs401_7

lemma mem401_1 : (1 : Fin 8) ∉ bs401_1 := by decide
lemma mem401_2 : (2 : Fin 8) ∉ bs401_2 := by decide
lemma mem401_3 : (3 : Fin 8) ∉ bs401_3 := by decide
lemma mem401_4 : (4 : Fin 8) ∉ bs401_4 := by decide
lemma mem401_5 : (5 : Fin 8) ∉ bs401_5 := by decide
lemma mem401_6 : (6 : Fin 8) ∉ bs401_6 := by decide
lemma mem401_7 : (7 : Fin 8) ∉ bs401_7 := by decide

lemma card_bs401_1 : bs401_1.card = 1 := by
  first
    | decide
    | rfl
    | simp
lemma card_bs401_2 : bs401_2.card = 2 := by
  first
    | decide
    | rfl
    | simp
lemma card_bs401_3 : bs401_3.card = 3 := by
  first
    | decide
    | rfl
    | simp
lemma card_bs401_4 : bs401_4.card = 4 := by
  first
    | decide
    | rfl
    | simp
lemma card_bs401_5 : bs401_5.card = 5 := by
  first
    | decide
    | rfl
    | simp
lemma card_bs401_6 : bs401_6.card = 6 := by
  first
    | decide
    | rfl
    | simp
lemma card_bs401_7 : bs401_7.card = 7 := by
  first
    | decide
    | rfl
    | simp
lemma card_bs401_8 : bs401_8.card = 8 := by
  first
    | decide
    | rfl
    | simp

lemma hB401 : 1 ≤ Fintype.card (Fin 8) := by
  first
    | exact Fintype.card_pos
    | simp
    | decide


section Frames401
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]

/-- the window of stage `n` of the invocation `d`. -/
def win401N (l : H) (hH : Fintype.card H = 9) (n : ℕ) (d : Orth (BC.LC (Fin 8) H l)) : GWin H (BC.LC (Fin 8) H l) :=
  match n with
  | 0 => gwinC hB401 (by omega) d ∅
  | 1 => gwinC hB401 (by omega) d (qC bs401_1)
  | 2 => gwinC hB401 (by omega) d (qC bs401_2)
  | 3 => gwinC hB401 (by omega) d (qC bs401_3)
  | 4 => gwinC hB401 (by omega) d (qC bs401_4)
  | 5 => gwinC hB401 (by omega) d (qC bs401_5)
  | 6 => gwinC hB401 (by omega) d (qC bs401_6)
  | 7 => gwinC hB401 (by omega) d (qC bs401_7)
  | 8 => gwinC hB401 (by omega) d (qC bs401_8)
  | _ => gwinC hB401 (by omega) d ∅

/-- the window of stage `k` of the invocation `d`. -/
def win401 (l : H) (hH : Fintype.card H = 9) (k : Fin 9) (d : Orth (BC.LC (Fin 8) H l)) : GWin H (BC.LC (Fin 8) H l) :=
  win401N l hH k.val d

lemma card_LC401 (l : H) (hH : Fintype.card H = 9) : Fintype.card (BC.LC (Fin 8) H l) = 73 :=
  card_LC_enum l (enumOf l hH)

/-- the bank frames of the schedule `S` (`sched_frames`): before the free adapter of each sub-stage. -/
def zb401 (I : GInvE H T Sl C) (l : H) (hH : Fintype.card H = 9) (S : BankSched Sl)
    (hres : ∀ b, S.load (fun q => Fintype.card H - (I.ent q).dim) b + S.pad b = 73)
    (hpad : ∀ b, S.pad b < 73) : ℕ → Orth (BC.LC (Fin 8) H l) → Fin S.nb → CMat (BC.LC (Fin 8) H l) :=
  Classical.choose (sched_frames S I.ent (win401 l hH) (by rw [card_LC401 l hH]; exact hres)
    (by rw [card_LC401 l hH]; exact hpad))

/-- the bank frames of the schedule `S`: after the free adapter of each sub-stage. -/
def zp401 (I : GInvE H T Sl C) (l : H) (hH : Fintype.card H = 9) (S : BankSched Sl)
    (hres : ∀ b, S.load (fun q => Fintype.card H - (I.ent q).dim) b + S.pad b = 73)
    (hpad : ∀ b, S.pad b < 73) : ℕ → Orth (BC.LC (Fin 8) H l) → Fin S.nb → CMat (BC.LC (Fin 8) H l) :=
  Classical.choose (Classical.choose_spec (sched_frames S I.ent (win401 l hH) (by rw [card_LC401 l hH]; exact hres)
    (by rw [card_LC401 l hH]; exact hpad)))

lemma zfr401_spec (I : GInvE H T Sl C) (l : H) (hH : Fintype.card H = 9) (S : BankSched Sl)
    (hres : ∀ b, S.load (fun q => Fintype.card H - (I.ent q).dim) b + S.pad b = 73)
    (hpad : ∀ b, S.pad b < 73) :
    (∀ g b, zb401 I l hH S hres hpad 0 g b = 1) ∧
      (∀ (ρ : Fin 8) (k : Fin 9) g b, GReach (zb401 I l hH S hres hpad (9 * ρ.val + k.val) g b)
        (zp401 I l hH S hres hpad (9 * ρ.val + k.val) g b) (fun _ => 0)) ∧
      (∀ (ρ : Fin 8) (k : Fin 9) g q, entW (win401 l hH k g).X (I.ent q)
          * zp401 I l hH S hres hpad (9 * ρ.val + k.val) g (S.use ρ k q)
        = zb401 I l hH S hres hpad (9 * ρ.val + k.val + 1) g (S.use ρ k q)) ∧
      (∀ (ρ : Fin 8) (k : Fin 9) g b, (∀ q, S.use ρ k q ≠ b) →
        zb401 I l hH S hres hpad (9 * ρ.val + k.val + 1) g b = zp401 I l hH S hres hpad (9 * ρ.val + k.val) g b) ∧
      (∀ g b, GReach (zb401 I l hH S hres hpad 72 g b) (kernel (BC.LC (Fin 8) H l)) (fun φ => bcost φ (S.pad b))) :=
  Classical.choose_spec (Classical.choose_spec (sched_frames S I.ent (win401 l hH)
    (by rw [card_LC401 l hH]; exact hres) (by rw [card_LC401 l hH]; exact hpad)))

end Frames401

section Net
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]
variable (I : GInvE H T Sl C) (base : T → OBase H) (l : H)
  (hbase : ∀ t, I.tv t = (base t).v l) (hH : Fintype.card H = 9)
include hbase

lemma g401geom_x01 (g : Orth (BC.LC (Fin 8) H l)) (t : T) :
    PhiC g ∅ 1 = PhiC (RrC (base t) l (0 : Fin 8) g) (qC bs401_1) (tt (I.tv t)) := by
  rw [hbase t]
  exact bankT_x0 (base t) l (0 : Fin 8) g

lemma g401geom_y01 (g : Orth (BC.LC (Fin 8) H l)) (t : T) :
    PhiC g ∅ (1 + tt (I.tv t)) = PhiC (RrC (base t) l (0 : Fin 8) g) (qC bs401_1) 0 := by
  rw [hbase t]
  exact bankT_y0 (base t) l (0 : Fin 8) g

lemma g401geom_xx (bs : Finset (Fin 8)) (c c' : Fin 8) (hc : c ∈ bs) (hc' : c' ∉ bs)
    (g : Orth (BC.LC (Fin 8) H l)) (t : T) :
    PhiC (RrC (base t) l c g) (qC bs) 1
      = PhiC (RrC (base t) l c' g) (qC (insert c' bs)) (tt (I.tv t)) := by
  rw [hbase t]
  exact bankT_xx (base t) l bs c c' hc hc' g

lemma g401geom_yy (bs : Finset (Fin 8)) (c c' : Fin 8) (hc : c ∈ bs) (hc' : c' ∉ bs)
    (g : Orth (BC.LC (Fin 8) H l)) (t : T) :
    PhiC (RrC (base t) l c g) (qC bs) (1 + tt (I.tv t))
      = PhiC (RrC (base t) l c' g) (qC (insert c' bs)) 0 := by
  rw [hbase t]
  exact bankT_yy (base t) l bs c c' hc hc' g

lemma g401geom_term (g : Orth (BC.LC (Fin 8) H l)) (t : T) :
    kernel (BC.LC (Fin 8) H l) * PhiC g ∅ (tt (I.tv t))
      = shift ((BBC (base t) l g).v (Sum.inl l)) * frame (BBC (base t) l g) (univ \ {Sum.inl l}) := by
  rw [hbase t]
  exact class_term (base t) l g

include hH

/-- pair 2 before its first gate layer, `X`: ONE block of rank 16. -/
lemma g401geom_aX2 (g : Orth (BC.LC (Fin 8) H l)) (t : T) :
    XReach (PhiC g ∅ (tt (I.tv t))) (PhiC (RrC (base t) l (0 : Fin 8) g) (qC bs401_1) 1)
      (fun φ => bcost φ 16) := by
  rw [hbase t, classT_X0 (base t) l g, classT_X (base t) l bs401_1 (0 : Fin 8) (Finset.mem_singleton_self _) g]
  exact climb_X0 hB401 (by omega) l (BBC (base t) l g) bs401_1 _ (by rw [card_bs401_1]; omega)

/-- pair 2 before its first gate layer, `Y`: ONE block of rank 16. -/
lemma g401geom_aY2 (g : Orth (BC.LC (Fin 8) H l)) (t : T) :
    XReach (PhiC g ∅ 0) (PhiC (RrC (base t) l (0 : Fin 8) g) (qC bs401_1) (1 + tt (I.tv t)))
      (fun φ => bcost φ 16) := by
  rw [hbase t, classT_Y0 (base t) l g, classT_Y (base t) l bs401_1 (0 : Fin 8) (Finset.mem_singleton_self _) g]
  exact climb_Y0 hB401 (by omega) l (BBC (base t) l g) bs401_1 _ (by rw [card_bs401_1]; omega)

/-- pair 3 before its first gate layer, `X`: ONE block of rank 32. -/
lemma g401geom_aX3 (g : Orth (BC.LC (Fin 8) H l)) (t : T) :
    XReach (PhiC g ∅ (tt (I.tv t))) (PhiC (RrC (base t) l (2 : Fin 8) g) (qC bs401_3) 1)
      (fun φ => bcost φ 32) := by
  rw [hbase t, classT_X0 (base t) l g, classT_X (base t) l bs401_3 (2 : Fin 8) (Finset.mem_insert_self _ _) g]
  exact climb_X0 hB401 (by omega) l (BBC (base t) l g) bs401_3 _ (by rw [card_bs401_3]; omega)

/-- pair 3 before its first gate layer, `Y`: ONE block of rank 32. -/
lemma g401geom_aY3 (g : Orth (BC.LC (Fin 8) H l)) (t : T) :
    XReach (PhiC g ∅ 0) (PhiC (RrC (base t) l (2 : Fin 8) g) (qC bs401_3) (1 + tt (I.tv t)))
      (fun φ => bcost φ 32) := by
  rw [hbase t, classT_Y0 (base t) l g, classT_Y (base t) l bs401_3 (2 : Fin 8) (Finset.mem_insert_self _ _) g]
  exact climb_Y0 hB401 (by omega) l (BBC (base t) l g) bs401_3 _ (by rw [card_bs401_3]; omega)

/-- pair 4 before its first gate layer, `X`: ONE block of rank 48. -/
lemma g401geom_aX4 (g : Orth (BC.LC (Fin 8) H l)) (t : T) :
    XReach (PhiC g ∅ (tt (I.tv t))) (PhiC (RrC (base t) l (4 : Fin 8) g) (qC bs401_5) 1)
      (fun φ => bcost φ 48) := by
  rw [hbase t, classT_X0 (base t) l g, classT_X (base t) l bs401_5 (4 : Fin 8) (Finset.mem_insert_self _ _) g]
  exact climb_X0 hB401 (by omega) l (BBC (base t) l g) bs401_5 _ (by rw [card_bs401_5]; omega)

/-- pair 4 before its first gate layer, `Y`: ONE block of rank 48. -/
lemma g401geom_aY4 (g : Orth (BC.LC (Fin 8) H l)) (t : T) :
    XReach (PhiC g ∅ 0) (PhiC (RrC (base t) l (4 : Fin 8) g) (qC bs401_5) (1 + tt (I.tv t)))
      (fun φ => bcost φ 48) := by
  rw [hbase t, classT_Y0 (base t) l g, classT_Y (base t) l bs401_5 (4 : Fin 8) (Finset.mem_insert_self _ _) g]
  exact climb_Y0 hB401 (by omega) l (BBC (base t) l g) bs401_5 _ (by rw [card_bs401_5]; omega)

/-- pair 1 after stage 2, `X`: ONE final block of rank 48. -/
lemma g401geom_fX1 (g : Orth (BC.LC (Fin 8) H l)) (t : T) :
    XReach (PhiC (RrC (base t) l (1 : Fin 8) g) (qC bs401_2) 1) (kernel (BC.LC (Fin 8) H l))
      (fun φ => bcost φ 48) :=
  idle_Xend (base t) l hB401 (by omega) bs401_2 (1 : Fin 8) (Finset.mem_insert_self _ _) g _
    (by rw [card_bs401_2, Fintype.card_fin]; omega)

/-- pair 1 after stage 2, `Y`: ONE final block of rank 48. -/
lemma g401geom_fY1 (g : Orth (BC.LC (Fin 8) H l)) (t : T) :
    XReach (PhiC (RrC (base t) l (1 : Fin 8) g) (qC bs401_2) (1 + tt (I.tv t)))
      (frame (BBC (base t) l g) (univ \ {Sum.inl l}))
      (fun φ => bcost φ 48) := by
  rw [hbase t]
  exact idle_Yend (base t) l hB401 (by omega) bs401_2 (1 : Fin 8) (Finset.mem_insert_self _ _) g _
    (by rw [card_bs401_2, Fintype.card_fin]; omega)

/-- pair 2 after stage 4, `X`: ONE final block of rank 32. -/
lemma g401geom_fX2 (g : Orth (BC.LC (Fin 8) H l)) (t : T) :
    XReach (PhiC (RrC (base t) l (3 : Fin 8) g) (qC bs401_4) 1) (kernel (BC.LC (Fin 8) H l))
      (fun φ => bcost φ 32) :=
  idle_Xend (base t) l hB401 (by omega) bs401_4 (3 : Fin 8) (Finset.mem_insert_self _ _) g _
    (by rw [card_bs401_4, Fintype.card_fin]; omega)

/-- pair 2 after stage 4, `Y`: ONE final block of rank 32. -/
lemma g401geom_fY2 (g : Orth (BC.LC (Fin 8) H l)) (t : T) :
    XReach (PhiC (RrC (base t) l (3 : Fin 8) g) (qC bs401_4) (1 + tt (I.tv t)))
      (frame (BBC (base t) l g) (univ \ {Sum.inl l}))
      (fun φ => bcost φ 32) := by
  rw [hbase t]
  exact idle_Yend (base t) l hB401 (by omega) bs401_4 (3 : Fin 8) (Finset.mem_insert_self _ _) g _
    (by rw [card_bs401_4, Fintype.card_fin]; omega)

/-- pair 3 after stage 6, `X`: ONE final block of rank 16. -/
lemma g401geom_fX3 (g : Orth (BC.LC (Fin 8) H l)) (t : T) :
    XReach (PhiC (RrC (base t) l (5 : Fin 8) g) (qC bs401_6) 1) (kernel (BC.LC (Fin 8) H l))
      (fun φ => bcost φ 16) :=
  idle_Xend (base t) l hB401 (by omega) bs401_6 (5 : Fin 8) (Finset.mem_insert_self _ _) g _
    (by rw [card_bs401_6, Fintype.card_fin]; omega)

/-- pair 3 after stage 6, `Y`: ONE final block of rank 16. -/
lemma g401geom_fY3 (g : Orth (BC.LC (Fin 8) H l)) (t : T) :
    XReach (PhiC (RrC (base t) l (5 : Fin 8) g) (qC bs401_6) (1 + tt (I.tv t)))
      (frame (BBC (base t) l g) (univ \ {Sum.inl l}))
      (fun φ => bcost φ 16) := by
  rw [hbase t]
  exact idle_Yend (base t) l hB401 (by omega) bs401_6 (5 : Fin 8) (Finset.mem_insert_self _ _) g _
    (by rw [card_bs401_6, Fintype.card_fin]; omega)

/-- pair 4 after stage 8, `X`: ONE final block of rank 0. -/
lemma g401geom_fX4 (g : Orth (BC.LC (Fin 8) H l)) (t : T) :
    XReach (PhiC (RrC (base t) l (7 : Fin 8) g) (qC bs401_8) 1) (kernel (BC.LC (Fin 8) H l))
      (fun φ => bcost φ 0) :=
  idle_Xend (base t) l hB401 (by omega) bs401_8 (7 : Fin 8) (Finset.mem_insert_self _ _) g _
    (by rw [card_bs401_8, Fintype.card_fin]; omega)

/-- pair 4 after stage 8, `Y`: ONE final block of rank 0. -/
lemma g401geom_fY4 (g : Orth (BC.LC (Fin 8) H l)) (t : T) :
    XReach (PhiC (RrC (base t) l (7 : Fin 8) g) (qC bs401_8) (1 + tt (I.tv t)))
      (frame (BBC (base t) l g) (univ \ {Sum.inl l}))
      (fun φ => bcost φ 0) := by
  rw [hbase t]
  exact idle_Yend (base t) l hB401 (by omega) bs401_8 (7 : Fin 8) (Finset.mem_insert_self _ _) g _
    (by rw [card_bs401_8, Fintype.card_fin]; omega)

/-- **The nine-stage word with entrance gauges and residual banks as a term of `G401`** on the label space
`LC (Fin 8) H l`, for any gauged invocation package whose lines are the vectors of index `l` of orthonormal bases and
any bank schedule `S` with `load + pad = 73`, `pad < 73`. -/
def ggeom401 (S : BankSched Sl)
    (hres : ∀ b, S.load (fun q => Fintype.card H - (I.ent q).dim) b + S.pad b = 73)
    (hpad : ∀ b, S.pad b < 73) : G401 H T Sl C (BC.LC (Fin 8) H l) (Orth (BC.LC (Fin 8) H l)) S.nb where
  I := I
  G0 := fun d => gwinC hB401 (by omega) d ∅
  G1 := fun d => gwinC hB401 (by omega) d (qC bs401_1)
  G2 := fun d => gwinC hB401 (by omega) d (qC bs401_2)
  G3 := fun d => gwinC hB401 (by omega) d (qC bs401_3)
  G4 := fun d => gwinC hB401 (by omega) d (qC bs401_4)
  G5 := fun d => gwinC hB401 (by omega) d (qC bs401_5)
  G6 := fun d => gwinC hB401 (by omega) d (qC bs401_6)
  G7 := fun d => gwinC hB401 (by omega) d (qC bs401_7)
  G8 := fun d => gwinC hB401 (by omega) d (qC bs401_8)
  r1 := fun t => RrC (base t) l (0 : Fin 8)
  r2 := fun t => RrC (base t) l (1 : Fin 8)
  r3 := fun t => RrC (base t) l (2 : Fin 8)
  r4 := fun t => RrC (base t) l (3 : Fin 8)
  r5 := fun t => RrC (base t) l (4 : Fin 8)
  r6 := fun t => RrC (base t) l (5 : Fin 8)
  r7 := fun t => RrC (base t) l (6 : Fin 8)
  r8 := fun t => RrC (base t) l (7 : Fin 8)
  N0 := fun d q => entN (gwinC hB401 (by omega) d ∅).X (I.ent q)
  Wn0 := fun d q => entW (gwinC hB401 (by omega) d ∅).X (I.ent q)
  N1 := fun d q => entN (gwinC hB401 (by omega) d (qC bs401_1)).X (I.ent q)
  Wn1 := fun d q => entW (gwinC hB401 (by omega) d (qC bs401_1)).X (I.ent q)
  N2 := fun d q => entN (gwinC hB401 (by omega) d (qC bs401_2)).X (I.ent q)
  Wn2 := fun d q => entW (gwinC hB401 (by omega) d (qC bs401_2)).X (I.ent q)
  N3 := fun d q => entN (gwinC hB401 (by omega) d (qC bs401_3)).X (I.ent q)
  Wn3 := fun d q => entW (gwinC hB401 (by omega) d (qC bs401_3)).X (I.ent q)
  N4 := fun d q => entN (gwinC hB401 (by omega) d (qC bs401_4)).X (I.ent q)
  Wn4 := fun d q => entW (gwinC hB401 (by omega) d (qC bs401_4)).X (I.ent q)
  N5 := fun d q => entN (gwinC hB401 (by omega) d (qC bs401_5)).X (I.ent q)
  Wn5 := fun d q => entW (gwinC hB401 (by omega) d (qC bs401_5)).X (I.ent q)
  N6 := fun d q => entN (gwinC hB401 (by omega) d (qC bs401_6)).X (I.ent q)
  Wn6 := fun d q => entW (gwinC hB401 (by omega) d (qC bs401_6)).X (I.ent q)
  N7 := fun d q => entN (gwinC hB401 (by omega) d (qC bs401_7)).X (I.ent q)
  Wn7 := fun d q => entW (gwinC hB401 (by omega) d (qC bs401_7)).X (I.ent q)
  N8 := fun d q => entN (gwinC hB401 (by omega) d (qC bs401_8)).X (I.ent q)
  Wn8 := fun d q => entW (gwinC hB401 (by omega) d (qC bs401_8)).X (I.ent q)
  use := S.use
  hinj := S.hinj
  Zb := zb401 I l hH S hres hpad
  Zp := zp401 I l hH S hres hpad
  pad := S.pad
  u := fun g t => (BBC (base t) l g).v (Sum.inl l)
  YF := fun g t => frame (BBC (base t) l g) (univ \ {Sum.inl l})
  hm := two_le_card_LC hB401 (by omega)
  caX2 := fun φ => bcost φ 16
  caY2 := fun φ => bcost φ 16
  caX3 := fun φ => bcost φ 32
  caY3 := fun φ => bcost φ 32
  caX4 := fun φ => bcost φ 48
  caY4 := fun φ => bcost φ 48
  cX1 := fun φ => bcost φ 48
  cY1 := fun φ => bcost φ 48
  cX2 := fun φ => bcost φ 32
  cY2 := fun φ => bcost φ 32
  cX3 := fun φ => bcost φ 16
  cY3 := fun φ => bcost φ 16
  cX4 := fun φ => bcost φ 0
  cY4 := fun φ => bcost φ 0
  inv0 := fun g t => ⟨unframeM (g.1 * Matrix.fromBlocks (tt (I.tv t)) 0 0 (diagI ∅) * g.1ᵀ),
    frameM_unframeM _⟩
  z0 := fun g => PhiC_zero_empty g
  hN0 := fun d q => entN_spec _ _
  hW0 := fun d q => entW_spec _ _
  hN1 := fun d q => entN_spec _ _
  hW1 := fun d q => entW_spec _ _
  hN2 := fun d q => entN_spec _ _
  hW2 := fun d q => entW_spec _ _
  hN3 := fun d q => entN_spec _ _
  hW3 := fun d q => entW_spec _ _
  hN4 := fun d q => entN_spec _ _
  hW4 := fun d q => entW_spec _ _
  hN5 := fun d q => entN_spec _ _
  hW5 := fun d q => entW_spec _ _
  hN6 := fun d q => entN_spec _ _
  hW6 := fun d q => entW_spec _ _
  hN7 := fun d q => entN_spec _ _
  hW7 := fun d q => entW_spec _ _
  hN8 := fun d q => entN_spec _ _
  hW8 := fun d q => entW_spec _ _
  x01 := fun g t => g401geom_x01 I base l hbase g t
  y01 := fun g t => g401geom_y01 I base l hbase g t
  x12 := fun g t => g401geom_xx I base l hbase bs401_1 0 1 (Finset.mem_singleton_self _) mem401_1 g t
  y12 := fun g t => g401geom_yy I base l hbase bs401_1 0 1 (Finset.mem_singleton_self _) mem401_1 g t
  x23 := fun g t => g401geom_xx I base l hbase bs401_2 1 2 (Finset.mem_insert_self _ _) mem401_2 g t
  y23 := fun g t => g401geom_yy I base l hbase bs401_2 1 2 (Finset.mem_insert_self _ _) mem401_2 g t
  x34 := fun g t => g401geom_xx I base l hbase bs401_3 2 3 (Finset.mem_insert_self _ _) mem401_3 g t
  y34 := fun g t => g401geom_yy I base l hbase bs401_3 2 3 (Finset.mem_insert_self _ _) mem401_3 g t
  x45 := fun g t => g401geom_xx I base l hbase bs401_4 3 4 (Finset.mem_insert_self _ _) mem401_4 g t
  y45 := fun g t => g401geom_yy I base l hbase bs401_4 3 4 (Finset.mem_insert_self _ _) mem401_4 g t
  x56 := fun g t => g401geom_xx I base l hbase bs401_5 4 5 (Finset.mem_insert_self _ _) mem401_5 g t
  y56 := fun g t => g401geom_yy I base l hbase bs401_5 4 5 (Finset.mem_insert_self _ _) mem401_5 g t
  x67 := fun g t => g401geom_xx I base l hbase bs401_6 5 6 (Finset.mem_insert_self _ _) mem401_6 g t
  y67 := fun g t => g401geom_yy I base l hbase bs401_6 5 6 (Finset.mem_insert_self _ _) mem401_6 g t
  x78 := fun g t => g401geom_xx I base l hbase bs401_7 6 7 (Finset.mem_insert_self _ _) mem401_7 g t
  y78 := fun g t => g401geom_yy I base l hbase bs401_7 6 7 (Finset.mem_insert_self _ _) mem401_7 g t
  z0b := (zfr401_spec I l hH S hres hpad).1
  hP0 := fun ρ g b => (zfr401_spec I l hH S hres hpad).2.1 ρ 0 g b
  hZ0 := fun ρ g q => (zfr401_spec I l hH S hres hpad).2.2.1 ρ 0 g q
  hZn0 := fun ρ g b hb => (zfr401_spec I l hH S hres hpad).2.2.2.1 ρ 0 g b hb
  hP1 := fun ρ g b => (zfr401_spec I l hH S hres hpad).2.1 ρ 1 g b
  hZ1 := fun ρ g q => (zfr401_spec I l hH S hres hpad).2.2.1 ρ 1 g q
  hZn1 := fun ρ g b hb => (zfr401_spec I l hH S hres hpad).2.2.2.1 ρ 1 g b hb
  hP2 := fun ρ g b => (zfr401_spec I l hH S hres hpad).2.1 ρ 2 g b
  hZ2 := fun ρ g q => (zfr401_spec I l hH S hres hpad).2.2.1 ρ 2 g q
  hZn2 := fun ρ g b hb => (zfr401_spec I l hH S hres hpad).2.2.2.1 ρ 2 g b hb
  hP3 := fun ρ g b => (zfr401_spec I l hH S hres hpad).2.1 ρ 3 g b
  hZ3 := fun ρ g q => (zfr401_spec I l hH S hres hpad).2.2.1 ρ 3 g q
  hZn3 := fun ρ g b hb => (zfr401_spec I l hH S hres hpad).2.2.2.1 ρ 3 g b hb
  hP4 := fun ρ g b => (zfr401_spec I l hH S hres hpad).2.1 ρ 4 g b
  hZ4 := fun ρ g q => (zfr401_spec I l hH S hres hpad).2.2.1 ρ 4 g q
  hZn4 := fun ρ g b hb => (zfr401_spec I l hH S hres hpad).2.2.2.1 ρ 4 g b hb
  hP5 := fun ρ g b => (zfr401_spec I l hH S hres hpad).2.1 ρ 5 g b
  hZ5 := fun ρ g q => (zfr401_spec I l hH S hres hpad).2.2.1 ρ 5 g q
  hZn5 := fun ρ g b hb => (zfr401_spec I l hH S hres hpad).2.2.2.1 ρ 5 g b hb
  hP6 := fun ρ g b => (zfr401_spec I l hH S hres hpad).2.1 ρ 6 g b
  hZ6 := fun ρ g q => (zfr401_spec I l hH S hres hpad).2.2.1 ρ 6 g q
  hZn6 := fun ρ g b hb => (zfr401_spec I l hH S hres hpad).2.2.2.1 ρ 6 g b hb
  hP7 := fun ρ g b => (zfr401_spec I l hH S hres hpad).2.1 ρ 7 g b
  hZ7 := fun ρ g q => (zfr401_spec I l hH S hres hpad).2.2.1 ρ 7 g q
  hZn7 := fun ρ g b hb => (zfr401_spec I l hH S hres hpad).2.2.2.1 ρ 7 g b hb
  hP8 := fun ρ g b => (zfr401_spec I l hH S hres hpad).2.1 ρ 8 g b
  hZ8 := fun ρ g q => (zfr401_spec I l hH S hres hpad).2.2.1 ρ 8 g q
  hZn8 := fun ρ g b hb => (zfr401_spec I l hH S hres hpad).2.2.2.1 ρ 8 g b hb
  bpad := (zfr401_spec I l hH S hres hpad).2.2.2.2
  aX2 := fun g t => g401geom_aX2 I base l hbase hH g t
  aY2 := fun g t => g401geom_aY2 I base l hbase hH g t
  aX3 := fun g t => g401geom_aX3 I base l hbase hH g t
  aY3 := fun g t => g401geom_aY3 I base l hbase hH g t
  aX4 := fun g t => g401geom_aX4 I base l hbase hH g t
  aY4 := fun g t => g401geom_aY4 I base l hbase hH g t
  fX1 := fun g t => g401geom_fX1 I base l hbase hH g t
  fY1 := fun g t => g401geom_fY1 I base l hbase hH g t
  fX2 := fun g t => g401geom_fX2 I base l hbase hH g t
  fY2 := fun g t => g401geom_fY2 I base l hbase hH g t
  fX3 := fun g t => g401geom_fX3 I base l hbase hH g t
  fY3 := fun g t => g401geom_fY3 I base l hbase hH g t
  fX4 := fun g t => g401geom_fX4 I base l hbase hH g t
  fY4 := fun g t => g401geom_fY4 I base l hbase hH g t
  term := fun g t => g401geom_term I base l hbase g t

end Net

section End
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]

/-- the unit price of the nine-stage word with entrance gauges and residual banks. -/
def unitPrice401 {nb : ℕ} (I : GInvE H T Sl C) (pad : Fin nb → ℕ) (φ : ℕ → ℝ) : ℝ :=
  72 * I.cost φ + (Fintype.card T : ℝ) * bankPrice377 φ + ∑ b, bcost φ (pad b)

/-- **Generalised certificate of the nine-stage word with entrance gauges and residual banks (PR #401)** for a
gauged invocation package and a bank schedule. -/
theorem bridge401_gcert (I : GInvE H T Sl C) (hH : Fintype.card H = 9) (l : H) (S : BankSched Sl)
    (hres : S.fits I.ent) :
    GCert (BC.LC (Fin 8) H l)
      (Sum.inl : BLive401 (Orth (BC.LC (Fin 8) H l)) T S.nb → BRole401 (Orth (BC.LC (Fin 8) H l)) T S.nb C)
      (fun φ => (Fintype.card (Orth (BC.LC (Fin 8) H l)) : ℝ) * unitPrice401 I S.pad φ) := by
  have hb : ∀ t, ∃ A : OBase H, I.tv t = A.v l :=
    fun t => base_ex (I.tv t) (I.hunit t) (I.hgap t) l
  choose base hbase using hb
  have hc := g401_certificate (ggeom401 I base l hbase hH S hres.1 hres.2)
  have e : (fun φ => (Fintype.card (Orth (BC.LC (Fin 8) H l)) : ℝ)
        * (ggeom401 I base l hbase hH S hres.1 hres.2).unit φ)
      = (fun φ => (Fintype.card (Orth (BC.LC (Fin 8) H l)) : ℝ) * unitPrice401 I S.pad φ) := by
    funext φ
    simp only [G401.unit, G401.runUnit, ggeom401, unitPrice401, bankPrice377, hH, bcost_zero]
    first
      | ring
      | (norm_num; ring)
      | norm_num
  rw [e] at hc
  exact hc

end End
end
end GX
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.GX.ggeom401
#print axioms OAI.PowerSaving.GX.bridge401_gcert
