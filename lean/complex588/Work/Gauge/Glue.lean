import Work.Gauge.ECheck
import Work.Gauge.Labels
import Work.Gauge.Inv
import Work.GCert.Data.Glue

/-!
# (key: gauge-401) Glue: a checked GAUGED certificate is a gauged invocation package

DFT Bridge3, 2026-10-11.  For ANY `c : GXD.Raw` and gauge batches `es : List (SPar × List Nat)` (gauge list `es.flatMap Prod.snd`) (nothing is evaluated here):
* `gscalOf`  the gauged scalar half: Jacob's `scalOf` + `gauged` = the slots whose register is in one of the batches
             `es` (at most `v` registers per batch, `gPre`) + E7 from the kernel checks `eCheck` (`GS.eCheck_sound`);
* `ginvOf`   the gauged invocation package `GX.GInvE` from `GLab.ValidE` (label check with `endKE`), via `GLab.inv`;
* `ginvOf_cost`  its price: `rcost rA + Σ_k bcost (dim of copy k) + rcost rB + rcost rF` (`glab_ranks`).
Base: Jacob Sussman's `Work/GCert/Data/Glue.lean` (Apache-2.0); entrance gauges: Dugongue (PR #401).  No `sorry`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace GXD
open SSC OAI.PowerSaving OAI.PowerSaving.CR OAI.PowerSaving.CB Matrix Finset

section
variable (c : Raw) (hv : 0 < c.v)
    (hAi : GS.MAi c hv * GS.MA c hv = 1) (hBi : GS.MBi c hv * GS.MB c hv = 1)
    (hx : ∀ (t : Fin c.v) (j : GS.Rl c), (GS.MB c hv * scatM (GS.Jrm c * GS.Ccm c) * GS.MA c hv)
      (lX t) j = if lX t = j then 1 else 0)
    (hy : ∀ (i : GS.Rl c) (t : Fin c.v), (GS.MB c hv * scatM (GS.Jrm c * GS.Ccm c) * GS.MA c hv)
      i (lY t) = if i = lY t then 1 else 0)
    (hid : ∀ S t : Fin c.v, (GS.MB c hv * scatM (GS.Jrm c * GS.Ccm c) * GS.MA c hv)
      (lY S) (lX t) = if S = t then 1 else 0)
    (es : List (GS.SPar × List Nat)) (he : ∀ e ∈ es, GS.eCheck c e.1 e.2 = true)

/-- **the gauged scalar half**, from the five scalar identities and the E7 kernel check -/
noncomputable def gscalOf : GX.GScal (Fin c.v) (Fin c.R) (Fin c.ret.length) where
  toScal := scalOf c hv hAi hBi hx hy hid
  gauged := univ.filter (fun q : Fin c.R => 2 * c.v + q.val ∈ es.flatMap Prod.snd)
  hE := fun q hq t => by
    obtain ⟨e, he1, he2⟩ := List.mem_flatMap.mp (Finset.mem_filter.mp hq).2
    exact GS.eCheck_sound hv (he e he1) q he2 t

theorem gscalOf_gauged (q : Fin c.R) :
    q ∈ (gscalOf c hv hAi hBi hx hy hid es he).gauged ↔ 2 * c.v + q.val ∈ es.flatMap Prod.snd := by
  show q ∈ univ.filter (fun q : Fin c.R => 2 * c.v + q.val ∈ es.flatMap Prod.snd) ↔ _
  simp

variable (a : GLab.Aux) (V : GLab.ValidE c a (es.flatMap Prod.snd))

/-- the gauged label half of a checked certificate over its gauged scalar half -/
noncomputable def glabOf : GX.GLab (Fin a.p.h) (gscalOf c hv hAi hBi hx hy hid es he) :=
  V.glab (gscalOf c hv hAi hBi hx hy hid es he) (roles c hv) GS.toCoef
    (scalOf_MA c hv hAi hBi hx hy hid) (scalOf_MAi c hv hAi hBi hx hy hid)
    (scalOf_MB c hv hAi hBi hx hy hid) (scalOf_MBi c hv hAi hBi hx hy hid)
    (reg c) (reg_slot c hv hAi hBi hx hy hid) (reg_mem c)
    (fun q hq => (gscalOf_gauged c hv hAi hBi hx hy hid es he q).mpr hq)

/-- **a checked gauged certificate is a gauged invocation package** (`GLab.inv`) -/
noncomputable def ginvOf : GX.GInvE (Fin a.p.h) (Fin c.v) (Fin c.R) (Fin c.ret.length) :=
  (glabOf c hv hAi hBi hx hy hid es he a V).inv

/-- its price, from the ranks of the three replays and the dimensions of the copies -/
theorem ginvOf_cost (φ : ℕ → ℝ) :
    (ginvOf c hv hAi hBi hx hy hid es he a V).cost φ
      = rcost φ a.rA + (∑ k : Fin c.ret.length, bcost φ (GLab.cdim (a.p.tab.get (a.SA.get (reg c k)))))
        + rcost φ a.rB + rcost φ a.rF := by
  obtain ⟨h1, h2, h3, h4⟩ := V.glab_ranks (gscalOf c hv hAi hBi hx hy hid es he) (roles c hv) GS.toCoef
    (scalOf_MA c hv hAi hBi hx hy hid) (scalOf_MAi c hv hAi hBi hx hy hid)
    (scalOf_MB c hv hAi hBi hx hy hid) (scalOf_MBi c hv hAi hBi hx hy hid)
    (reg c) (reg_slot c hv hAi hBi hx hy hid) (reg_mem c)
    (fun q hq => (gscalOf_gauged c hv hAi hBi hx hy hid es he q).mpr hq)
  show GX.GLab.cost (glabOf c hv hAi hBi hx hy hid es he a V) φ = _
  unfold GX.GLab.cost
  unfold glabOf
  rw [h1, h2, h3]
  simp only [h4]

/-- the dimension of the entrance label of slot `q`: the frame dimension of its register in the start state -/
theorem ginvOf_ent_dim (q : Fin c.R) :
    ((ginvOf c hv hAi hBi hx hy hid es he a V).ent q).dim
      = GLab.cdim (a.p.tab.get (a.S0.get (2 * c.v + q.val))) :=
  GLab.lab_dim (GLab.tabK_good _ _ V.tab _)

end

end GXD

#print axioms GXD.gscalOf
#print axioms GXD.ginvOf
#print axioms GXD.ginvOf_cost
#print axioms GXD.ginvOf_ent_dim
