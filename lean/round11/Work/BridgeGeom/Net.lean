import Work.BridgeGeom.Stage
import Work.Bridge.Net

/-!
# (key: bridge-geom) The bridged word B_2 on the label space `H ⊕ (Fin 4 × H)`: geometry

Term of `BR.Bridge2` (`Work.Bridge.Net`, agent bridge-net) for ANY invocation package `I` whose
lines are the vectors of index `l` of orthonormal bases `base t` (`hbase`), with

* `Γ = Orth (L5 H)`, the orthogonal matrices of the label space (`m = 5h`);
* stage 0: window `g W_0`, base `0`; stage `k = 1..4`: window `d W_0`, base `d` (the blocks
  `0 .. k-1` of `Fin 4`, each minus the coordinate `l`): `qS bs_k l`;
* `r_k t = ` right multiplication by `rho^(k-1)_t` (`RrB (base t) l (k-1)`);
* `s_k⁻¹ = ` right multiplication by the exchange of block 0 and block `k-1`
  (`Orth.colPerm (tauB (k-1))`): the helper set `g` serves the five windows `g W^(0..4)`;
* idle climbs, each ONE block inside the basis `g (base t ⊕ std)`: pair 2 before the first gate
  layer `2h-2`, pair 1 at the end `2h+2`, pair 2 at the end `4`.

No `sorry` in this file.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace BG
open Binary Matrix Finset RAM SS CB RF BR
noncomputable section

/-- the label space of the bridged word `B_2`: five blocks. -/
abbrev L5 (H : Type) := LB (Fin 4) H

/-- the base blocks of the stages 1, 2, 3, 4. -/
abbrev bs1 : Finset (Fin 4) := {0}
abbrev bs2 : Finset (Fin 4) := insert 1 bs1
abbrev bs3 : Finset (Fin 4) := insert 2 bs2
abbrev bs4 : Finset (Fin 4) := insert 3 bs3

lemma hB4 : 1 ≤ Fintype.card (Fin 4) := by
  first
    | exact Fintype.card_pos
    | simp
    | decide

lemma mem1 : (1 : Fin 4) ∉ bs1 := by decide
lemma mem2 : (2 : Fin 4) ∉ bs2 := by decide
lemma mem3 : (3 : Fin 4) ∉ bs3 := by decide
lemma card_bs2 : bs2.card = 2 := by
  first
    | decide
    | rfl
    | simp
lemma card_bs4 : bs4.card = 4 := by
  first
    | decide
    | rfl
    | simp

section Five
variable {H : Type} [Fintype H] [DecidableEq H]

lemma card_L5 : Fintype.card (L5 H) = 5 * Fintype.card H := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  omega

lemma w_all : insert (3 : Fin 4) (insert 2 (insert 1 (insert 0 ∅))) = (univ : Finset (Fin 4)) := by
  first
    | decide
    | (ext x; fin_cases x <;> simp)

/-- the five windows `g W^(0)`, .., `g W^(4)` of the helper set `g` make up the kernel. -/
lemma helper_fin5 (g : Orth (L5 H)) :
    frameM ((Orth.colPerm (tauB (3 : Fin 4)) g).1 * diagI (JB univ ∅)
        * (Orth.colPerm (tauB (3 : Fin 4)) g).1ᵀ)
      * (frameM ((Orth.colPerm (tauB (2 : Fin 4)) g).1 * diagI (JB univ ∅)
          * (Orth.colPerm (tauB (2 : Fin 4)) g).1ᵀ)
        * (frameM ((Orth.colPerm (tauB (1 : Fin 4)) g).1 * diagI (JB univ ∅)
            * (Orth.colPerm (tauB (1 : Fin 4)) g).1ᵀ)
          * (frameM ((Orth.colPerm (tauB (0 : Fin 4)) g).1 * diagI (JB univ ∅)
              * (Orth.colPerm (tauB (0 : Fin 4)) g).1ᵀ) * PhiB g ∅ 1))) = kernel (L5 H) := by
  rw [W_tauB, W_tauB, W_tauB, W_tauB, win_start,
    win_step g (0 : Fin 4) ∅ (Finset.notMem_empty _) univ,
    win_step g (1 : Fin 4) (insert 0 ∅) (by decide) univ,
    win_step g (2 : Fin 4) (insert 1 (insert 0 ∅)) (by decide) univ,
    win_step g (3 : Fin 4) (insert 2 (insert 1 (insert 0 ∅))) (by decide) univ, w_all]
  exact win_all g

end Five

section Net
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]
variable (I : Inv H T Sl C) (base : T → OBase H) (l : H)
  (hbase : ∀ t, I.tv t = (base t).v l) (hH : 1 ≤ Fintype.card H)
include hbase

lemma geom_x01 (g : Orth (L5 H)) (t : T) :
    PhiB g ∅ 1 = PhiB (RrB (base t) l (0 : Fin 4) g) (qS bs1 l) (tt (I.tv t)) := by
  rw [hbase t]
  exact bankT_x0 (base t) l (0 : Fin 4) g

lemma geom_y01 (g : Orth (L5 H)) (t : T) :
    PhiB g ∅ (1 + tt (I.tv t)) = PhiB (RrB (base t) l (0 : Fin 4) g) (qS bs1 l) 0 := by
  rw [hbase t]
  exact bankT_y0 (base t) l (0 : Fin 4) g

/-- consecutive stages `c ∈ bs`, `c' ∉ bs`: `X` leaves where it enters. -/
lemma geom_xx (bs : Finset (Fin 4)) (c c' : Fin 4) (hc : c ∈ bs) (hc' : c' ∉ bs)
    (g : Orth (L5 H)) (t : T) :
    PhiB (RrB (base t) l c g) (qS bs l) 1
      = PhiB (RrB (base t) l c' g) (qS (insert c' bs) l) (tt (I.tv t)) := by
  rw [hbase t]
  exact bankT_xx (base t) l bs c c' hc hc' g

/-- consecutive stages: `Y` leaves where it enters. -/
lemma geom_yy (bs : Finset (Fin 4)) (c c' : Fin 4) (hc : c ∈ bs) (hc' : c' ∉ bs)
    (g : Orth (L5 H)) (t : T) :
    PhiB (RrB (base t) l c g) (qS bs l) (1 + tt (I.tv t))
      = PhiB (RrB (base t) l c' g) (qS (insert c' bs) l) 0 := by
  rw [hbase t]
  exact bankT_yy (base t) l bs c c' hc hc' g

/-- terminal identity of the bank pairs of the class `(g,t)`. -/
lemma geom_term5 (g : Orth (L5 H)) (t : T) :
    kernel (L5 H) * PhiB g ∅ (tt (I.tv t))
      = shift ((BBB (base t) g).v (Sum.inl l))
          * frame (BBB (base t) g) (univ \ {Sum.inl l}) := by
  rw [hbase t]
  exact class_term (base t) l g

include hH

/-- pair 2 before the first gate layer, `X`: ONE block of rank `2h-2`. -/
lemma geom_aX2 (g : Orth (L5 H)) (t : T) :
    XReach (PhiB g ∅ (tt (I.tv t))) (PhiB (RrB (base t) l (0 : Fin 4) g) (qS bs1 l) 1)
      (fun φ => bcost φ (2 * Fintype.card H - 2)) := by
  rw [hbase t]
  exact idle_X0 (base t) l hB4 hH (0 : Fin 4) g _ (by omega)

/-- pair 2 before the first gate layer, `Y`: ONE block of rank `2h-2`. -/
lemma geom_aY2 (g : Orth (L5 H)) (t : T) :
    XReach (PhiB g ∅ 0) (PhiB (RrB (base t) l (0 : Fin 4) g) (qS bs1 l) (1 + tt (I.tv t)))
      (fun φ => bcost φ (2 * Fintype.card H - 2)) := by
  rw [hbase t]
  exact idle_Y0 (base t) l hB4 hH (0 : Fin 4) g _ (by omega)

/-- pair 1 at the end (idle in stages 3, 4, then the last four moves), `X`: ONE block `2h+2`. -/
lemma geom_fX1 (g : Orth (L5 H)) (t : T) :
    XReach (PhiB (RrB (base t) l (1 : Fin 4) g) (qS bs2 l) 1) (kernel (L5 H))
      (fun φ => bcost φ (2 * Fintype.card H + 2)) :=
  idle_Xend (base t) l hB4 hH bs2 (1 : Fin 4) (Finset.mem_insert_self _ _) g _
    (by rw [card_bs2, Fintype.card_fin]; omega)

/-- pair 1 at the end, `Y`: ONE block of rank `2h+2`. -/
lemma geom_fY1 (g : Orth (L5 H)) (t : T) :
    XReach (PhiB (RrB (base t) l (1 : Fin 4) g) (qS bs2 l) (1 + tt (I.tv t)))
      (frame (BBB (base t) g) (univ \ {Sum.inl l}))
      (fun φ => bcost φ (2 * Fintype.card H + 2)) := by
  rw [hbase t]
  exact idle_Yend (base t) l hB4 hH bs2 (1 : Fin 4) (Finset.mem_insert_self _ _) g _
    (by rw [card_bs2, Fintype.card_fin]; omega)

/-- pair 2 after stage 4, `X`: ONE block of rank `4`. -/
lemma geom_fX2 (g : Orth (L5 H)) (t : T) :
    XReach (PhiB (RrB (base t) l (3 : Fin 4) g) (qS bs4 l) 1) (kernel (L5 H))
      (fun φ => bcost φ 4) :=
  idle_Xend (base t) l hB4 hH bs4 (3 : Fin 4) (Finset.mem_insert_self _ _) g _
    (by rw [card_bs4, Fintype.card_fin]; omega)

/-- pair 2 after stage 4, `Y`: ONE block of rank `4`. -/
lemma geom_fY2 (g : Orth (L5 H)) (t : T) :
    XReach (PhiB (RrB (base t) l (3 : Fin 4) g) (qS bs4 l) (1 + tt (I.tv t)))
      (frame (BBB (base t) g) (univ \ {Sum.inl l})) (fun φ => bcost φ 4) := by
  rw [hbase t]
  exact idle_Yend (base t) l hB4 hH bs4 (3 : Fin 4) (Finset.mem_insert_self _ _) g _
    (by rw [card_bs4, Fintype.card_fin]; omega)

/-- **The bridged word B_2 as a term of `BR.Bridge2`**: five stages on the label space
`H ⊕ (Fin 4 × H)`, for any invocation package whose lines are the vectors of index `l` of
orthonormal bases. -/
def geomBridge2 : Bridge2 H T Sl C (L5 H) (Orth (L5 H)) where
  I := I
  M0 := fun g => fmapB hB4 hH g ∅
  M1 := fun d => fmapB hB4 hH d (qS bs1 l)
  M2 := fun d => fmapB hB4 hH d (qS bs2 l)
  M3 := fun d => fmapB hB4 hH d (qS bs3 l)
  M4 := fun d => fmapB hB4 hH d (qS bs4 l)
  r1 := fun t => RrB (base t) l (0 : Fin 4)
  r2 := fun t => RrB (base t) l (1 : Fin 4)
  r3 := fun t => RrB (base t) l (2 : Fin 4)
  r4 := fun t => RrB (base t) l (3 : Fin 4)
  s1 := (Orth.colPerm (tauB (0 : Fin 4))).symm
  s2 := (Orth.colPerm (tauB (1 : Fin 4))).symm
  s3 := (Orth.colPerm (tauB (2 : Fin 4))).symm
  s4 := (Orth.colPerm (tauB (3 : Fin 4))).symm
  N1 := fun d => unframeM (d.1 * Matrix.fromBlocks 0 0 0 (diagI (qS bs1 l)) * d.1ᵀ)
  W1 := fun d => frameM (d.1 * diagI (JB univ ∅) * d.1ᵀ)
  N2 := fun d => unframeM (d.1 * Matrix.fromBlocks 0 0 0 (diagI (qS bs2 l)) * d.1ᵀ)
  W2 := fun d => frameM (d.1 * diagI (JB univ ∅) * d.1ᵀ)
  N3 := fun d => unframeM (d.1 * Matrix.fromBlocks 0 0 0 (diagI (qS bs3 l)) * d.1ᵀ)
  W3 := fun d => frameM (d.1 * diagI (JB univ ∅) * d.1ᵀ)
  N4 := fun d => unframeM (d.1 * Matrix.fromBlocks 0 0 0 (diagI (qS bs4 l)) * d.1ᵀ)
  W4 := fun d => frameM (d.1 * diagI (JB univ ∅) * d.1ᵀ)
  u := fun g t => (BBB (base t) g).v (Sum.inl l)
  YF := fun g t => frame (BBB (base t) g) (univ \ {Sum.inl l})
  hm := two_le_card_LB hB4 hH
  caX := fun φ => bcost φ (2 * Fintype.card H - 2)
  caY := fun φ => bcost φ (2 * Fintype.card H - 2)
  cX1 := fun φ => bcost φ (2 * Fintype.card H + 2)
  cY1 := fun φ => bcost φ (2 * Fintype.card H + 2)
  cX2 := fun φ => bcost φ 4
  cY2 := fun φ => bcost φ 4
  inv0 := fun g t => ⟨unframeM (g.1 * Matrix.fromBlocks (tt (I.tv t)) 0 0 (diagI ∅) * g.1ᵀ),
    frameM_unframeM _⟩
  z0 := fun g => PhiB_zero_empty g
  hN1 := fun d => frameM_unframeM _
  hW1 := fun d => PhiB_one d (qS bs1 l)
  hN2 := fun d => frameM_unframeM _
  hW2 := fun d => PhiB_one d (qS bs2 l)
  hN3 := fun d => frameM_unframeM _
  hW3 := fun d => PhiB_one d (qS bs3 l)
  hN4 := fun d => frameM_unframeM _
  hW4 := fun d => PhiB_one d (qS bs4 l)
  x01 := fun g t => geom_x01 I base l hbase g t
  y01 := fun g t => geom_y01 I base l hbase g t
  x12 := fun g t => geom_xx I base l hbase bs1 0 1 (Finset.mem_singleton_self _) mem1 g t
  y12 := fun g t => geom_yy I base l hbase bs1 0 1 (Finset.mem_singleton_self _) mem1 g t
  x23 := fun g t => geom_xx I base l hbase bs2 1 2 (Finset.mem_insert_self _ _) mem2 g t
  y23 := fun g t => geom_yy I base l hbase bs2 1 2 (Finset.mem_insert_self _ _) mem2 g t
  x34 := fun g t => geom_xx I base l hbase bs3 2 3 (Finset.mem_insert_self _ _) mem3 g t
  y34 := fun g t => geom_yy I base l hbase bs3 2 3 (Finset.mem_insert_self _ _) mem3 g t
  sfin := fun g => helper_fin5 g
  aX2 := fun g t => geom_aX2 I base l hbase hH g t
  aY2 := fun g t => geom_aY2 I base l hbase hH g t
  fX1 := fun g t => geom_fX1 I base l hbase hH g t
  fY1 := fun g t => geom_fY1 I base l hbase hH g t
  fX2 := fun g t => geom_fX2 I base l hbase hH g t
  fY2 := fun g t => geom_fY2 I base l hbase hH g t
  term := fun g t => geom_term5 I base l hbase g t

end Net
end
end BG
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.BG.helper_fin5
#print axioms OAI.PowerSaving.BG.geomBridge2
