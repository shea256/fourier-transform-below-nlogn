import Work.Reframe.GeomNet
import Work.Combine.XCirc

/-!
# (key: reframe) The shared three-stage word F3: block certificate for ANY checked helper circuit

* `fold3s_bcert N`            for every `CB.XNetData` (block circuit, bases through its input
                              vectors; `pad` is ignored): there is a finite type `Γ` (the orthogonal
                              matrices of the label space `L3 H = H ⊕ (Bool × H)`, `m = 3h`) and a
                              block certificate with
                                live roles  `card Γ * (2 card T + card Sl)`        (`RF.card_SLive`)
                                price       `card Γ * (3 * X.cost φ + card T * (2 * bcost φ 2))`;
* `fold3s_bcert_pcert V hid h2`  the same for a certificate `c : SSC.PCert` accepted by the kernel
                              checks: price `card Γ * (3 * (rcost φ c.invRanks + 2 v bcost φ (h-1)) + 2 v bcost φ 2)`,
                              i.e. the unit price of PLAN.md B2 / `FoldRate.F3*.unitPrice`.

One helper set (`R` dirty live slots) per element of `Γ` serves three pairwise orthogonal windows,
one per stage; no helper slot makes any block outside its three invocations.  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace RF
open Binary Matrix Finset RAM SS CB
noncomputable section

section
variable {H : Type} [Fintype H] [DecidableEq H]

/-- re-index an orthonormal basis. -/
def reindex (A : OBase H) (σ : Equiv.Perm H) : OBase H where
  v := fun i => A.v (σ i)
  rows := fun i j => by
    rw [A.rows]
    by_cases h : i = j
    · subst h
      rw [if_pos rfl, if_pos rfl]
    · rw [if_neg h, if_neg (fun e : σ i = σ j => h (σ.injective e))]

end

section
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]

/-- **Block certificate of the shared three-stage word F3**, for any block circuit with bases
through its input vectors. -/
theorem fold3s_bcert (N : CB.XNetData H T Sl C) :
    ∃ (Γ : Type) (_ : Fintype Γ) (_ : DecidableEq Γ), 1 ≤ Fintype.card Γ ∧
      BCert (L3 H) (Sum.inl : SLive Γ T Sl → SRole Γ T Sl C)
        (fun φ => (Fintype.card Γ : ℝ)
          * (3 * N.X.cost φ + (Fintype.card T : ℝ) * (2 * bcost φ 2))) := by
  have hH2 := N.hH
  have hH1 : 1 ≤ Fintype.card H := by omega
  have hpos : 0 < Fintype.card H := by omega
  obtain ⟨l⟩ : Nonempty H := Fintype.card_pos_iff.mp hpos
  have hb : ∀ t, N.X.K.tv t = (reindex (N.base t) (Equiv.swap (N.piv t) l)).v l := by
    intro t
    rw [N.hbase t]
    show (N.base t).v (N.piv t) = (N.base t).v (Equiv.swap (N.piv t) l l)
    rw [Equiv.swap_apply_right]
  refine ⟨Orth (L3 H), inferInstance, inferInstance, Orth.card_pos, ?_⟩
  exact (fold3s_bcert_geom N.X (fun t => reindex (N.base t) (Equiv.swap (N.piv t) l)) l hb
    hH1).cast (fun φ => by ring)

end
end
end RF
end PowerSaving
end OAI

namespace SSC
namespace PCert
open OAI OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM OAI.PowerSaving.CB
  OAI.PowerSaving.RF

variable {c : PCert}

/-- **Block certificate of the shared three-stage word F3 with a kernel-checked helper
circuit.**  `v = c.v` triples, `R = c.R` helper slots, `h = c.p.h`; label dimension `3h`. -/
theorem Valid.fold3s_bcert (V : c.Valid) (hid : c.ScalarId V.hR) (h2 : 2 ≤ c.p.h) :
    ∃ (Γ : Type) (_ : Fintype Γ) (_ : DecidableEq Γ), 1 ≤ Fintype.card Γ ∧
      BCert (L3 (Fin c.p.h))
        (Sum.inl : SLive Γ (Fin c.v) (Fin c.R) → SRole Γ (Fin c.v) (Fin c.R) (Fin c.p.h))
        (fun φ => (Fintype.card Γ : ℝ)
          * (3 * (rcost φ c.invRanks + 2 * ((c.v : ℝ) * bcost φ (c.p.h - 1)))
              + 2 * ((c.v : ℝ) * bcost φ 2))) := by
  obtain ⟨Γ, i1, i2, hG, h⟩ := RF.fold3s_bcert (V.xnetdata hid 0 h2)
  refine ⟨Γ, i1, i2, hG, h.cast (fun φ => ?_)⟩
  show (Fintype.card Γ : ℝ) * (3 * (V.xcircuit hid).cost φ
      + (Fintype.card (Fin c.v) : ℝ) * (2 * bcost φ 2)) = _
  rw [V.xcost hid φ, Fintype.card_fin]
  ring

end PCert
end SSC

#print axioms OAI.PowerSaving.RF.fold3s_bcert
#print axioms SSC.PCert.Valid.fold3s_bcert
