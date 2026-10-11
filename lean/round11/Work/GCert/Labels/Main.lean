import Work.GCert.Chain.Phased
import Work.GCert.Labels.RouteRun
import Work.GCert.Labels.EndSound

/-!
# (key: gx-labels) THE LABEL HALF of a checked `gcert/1` certificate (spec statement 4, label part)

`Aux`    what the generator emits next to `raw : GXD.Raw`: parameters (with the frame table), the
         states at the start, at the scatter, after B, at the end, the final climbs, the ranks.
`Valid`  the kernel-checked facts: table (`tabK`), three replays (`Run`, composed from the
         segments by `Run.of_seg` / `Run.append`), `noAdds`, `endK`.
`Valid.lab`  **`Valid c a → GX.Lab (Fin a.p.h) S`** for the scalar half `S` whose gate matrices
         are the ordered products of the adds of `raw` (`Roles`: the numbering of the roles).

No `sorry`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace GLab
open SSC GXD OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.GF OAI.PowerSaving.RAM
  OAI.PowerSaving.CB Finset Matrix

theorem rOut_wf {d : Nat} (f : Nat) : ∀ (l : List Nat) (S : Trie), S.wf d → (rOut f S l).wf d := by
  intro l
  induction l with
  | nil => intro S h; exact h
  | cons r l ih =>
    intro S h
    refine ih _ ?_
    unfold vOut; split
    · exact h
    · exact Trie.wf_set d S h r f

theorem runOut_wf {d : Nat} : ∀ (gs : List Gate) (S : Trie), S.wf d → (runOut S gs).wf d := by
  intro gs
  induction gs with
  | nil => intro S h; exact h
  | cons g gs ih => intro S h; exact ih _ (rOut_wf _ _ S h)

theorem Run.wf {p : Par} {S S' : Trie} {gs : List Gate} {rs : List Nat} (R : Run p S gs S' rs)
    (hS : S.wf p.d) : S'.wf p.d := by
  rw [← R.2.1]; exact runOut_wf gs S hS

theorem noAdds_sound : ∀ gs : List Gate, noAdds gs = true → gs.flatMap Gate.adds = [] := by
  intro gs
  induction gs with
  | nil => intro _; rfl
  | cons g gs ih =>
    intro H
    cases g with
    | out f s ts ex =>
      cases ts with
      | nil =>
        have H' : noAdds gs = true := H
        show Gate.adds (.out f s [] ex) ++ gs.flatMap Gate.adds = []
        rw [ih H']; rfl
      | cons t ts => exact absurd H Bool.false_ne_true
    | inn f t ss => exact absurd H Bool.false_ne_true

/-- generated next to `raw`: parameters, states (start, scatter, after B, end), final climbs,
block ranks of the three phases -/
structure Aux where
  p : Par
  S0 : Trie
  SA : Trie
  SB : Trie
  SF : Trie
  fins : List Gate
  rA : List Nat
  rB : List Nat
  rF : List Nat

/-- **the kernel-checked label facts** of a certificate -/
structure Valid (c : Raw) (a : Aux) : Prop where
  hn : a.p.n = 2 * c.v + c.R
  tab : tabK a.p.h a.p.tab = true
  runA : Run a.p a.S0 c.gatesA a.SA a.rA
  runB : Run a.p a.SA c.gatesB a.SB a.rB
  runF : Run a.p a.SB a.fins a.SF a.rF
  fin : noAdds a.fins = true
  ends : endK a.p c.v c.ports (c.ret.map Prod.fst) a.S0 a.SA a.SF = true

/-- the numbering of the roles: `x_t = t`, `y_t = v + t`, slot `q = 2 v + q` -/
structure Roles (v R : Nat) (emb : CR.L3 (Fin v) (Fin R) → Nat) (un : Nat → CR.L3 (Fin v) (Fin R)) :
    Prop where
  hun : ∀ q, un (emb q) = q
  hin : ∀ r, r < 2 * v + R → emb (un r) = r
  hlt : ∀ q, emb q < 2 * v + R
  eX : ∀ t : Fin v, emb (CR.lX t) = t.val
  eY : ∀ t : Fin v, emb (CR.lY t) = v + t.val
  eS : ∀ q : Fin R, emb (CR.lS q) = 2 * v + q.val

/-- **THE LABEL HALF**: a checked certificate gives `GX.Lab` for its scalar half. -/
noncomputable def Valid.lab {c : Raw} {a : Aux} (V : Valid c a) {C : Type} [Fintype C]
    [DecidableEq C] (S : GX.Scal (Fin c.v) (Fin c.R) C)
    {emb : CR.L3 (Fin c.v) (Fin c.R) → Nat} {un : Nat → CR.L3 (Fin c.v) (Fin c.R)}
    (Ro : Roles c.v c.R emb un) (cf : Co → Coef)
    (hMA : S.MA = matP un (mic cf (c.gatesA.flatMap Gate.adds)))
    (hMAi : S.MAi = matPinv un (mic cf (c.gatesA.flatMap Gate.adds)))
    (hMB : S.MB = matP un (mic cf (c.gatesB.flatMap Gate.adds)))
    (hMBi : S.MBi = matPinv un (mic cf (c.gatesB.flatMap Gate.adds)))
    (reg : C → Nat) (hCc : ∀ k (q : Fin c.R), S.Cc k q ≠ 0 → reg k = 2 * c.v + q.val)
    (hreg : ∀ k, reg k ∈ c.ret.map Prod.fst) : GX.Lab (Fin a.p.h) S :=
  have E := endK_sound V.tab V.ends
  have C0 : Ctx a.p emb un := ⟨V.tab, E.hn, Ro.hun,
    fun r hr => Ro.hin r (by have := V.hn; omega),
    fun q => by have := V.hn; have := Ro.hlt q; omega⟩
  have wA := V.runA.wf E.w0
  have wB := V.runB.wf wA
  have G : ∀ k, (GLab.lab a.p.h (a.p.tab.get k)).dim = cdim (a.p.tab.get k) :=
    fun k => lab_dim (tabK_good _ _ V.tab k)
  { tv := fun t => tvec a.p.h (c.ports.getD t.val 0)
    hunit := fun t => (E.port t.val t.isLt).unit
    hgap := fun t => (E.port t.val t.isLt).gap
    lab0 := fun q => a.p.labS a.S0 (emb q)
    labA := fun q => a.p.labS a.SA (emb q)
    labB := fun q => a.p.labS a.SB (emb q)
    labF := fun q => a.p.labS a.SF (emb q)
    cen := fun k => a.p.labS a.SA (reg k)
    z0 := GLab.lab a.p.h (a.p.tab.get 0)
    hz0 := by rw [G]; exact E.z0
    h0x := fun t => by
      show (GLab.lab a.p.h (a.p.tab.get (a.S0.get (emb (CR.lX t))))).dim = 1 ∧
        (GLab.lab a.p.h (a.p.tab.get (a.S0.get (emb (CR.lX t))))).Mem _
      rw [Ro.eX t, G]
      exact ⟨(E.port t.val t.isLt).x0d, (E.port t.val t.isLt).x0m⟩
    h0y := fun t => by
      show (GLab.lab a.p.h (a.p.tab.get (a.S0.get (emb (CR.lY t))))).dim = 0
      rw [Ro.eY t, (E.port t.val t.isLt).y0, G]; exact E.z0
    h0s := fun q => by
      show (GLab.lab a.p.h (a.p.tab.get (a.S0.get (emb (CR.lS q))))).dim = 0
      rw [Ro.eS q, (E.slot q.val (by have := V.hn; have := q.isLt; omega)).1, G]; exact E.z0
    hAy := fun t => by
      show GLab.lab a.p.h (a.p.tab.get (a.SA.get (emb (CR.lY t)))) = GLab.lab a.p.h (a.p.tab.get 0)
      rw [Ro.eY t, (E.port t.val t.isLt).yA]
    hAc := fun k q h => by
      show GLab.lab a.p.h (a.p.tab.get (a.SA.get (reg k)))
        = GLab.lab a.p.h (a.p.tab.get (a.SA.get (emb (CR.lS q))))
      rw [Ro.eS q, hCc k q h]
    hcen := fun k => by
      show 0 < (GLab.lab a.p.h (a.p.tab.get (a.SA.get (reg k)))).dim
      rw [G]; exact E.ret _ (hreg k)
    hFx := fun t => by
      show (GLab.lab a.p.h (a.p.tab.get (a.SF.get (emb (CR.lX t))))).dim = Fintype.card (Fin a.p.h)
      rw [Ro.eX t, G, Fintype.card_fin]; exact (E.port t.val t.isLt).xF
    hFs := fun q => by
      show (GLab.lab a.p.h (a.p.tab.get (a.SF.get (emb (CR.lS q))))).dim = Fintype.card (Fin a.p.h)
      rw [Ro.eS q, G, Fintype.card_fin]
      exact (E.slot q.val (by have := V.hn; have := q.isLt; omega)).2
    hFy := fun t => by
      show (GLab.lab a.p.h (a.p.tab.get (a.SF.get (emb (CR.lY t))))).dim + 1
          = Fintype.card (Fin a.p.h) ∧
        ∀ x, (GLab.lab a.p.h (a.p.tab.get (a.SF.get (emb (CR.lY t))))).Mem x → dot _ x = 0
      rw [Ro.eY t, G, Fintype.card_fin]
      exact ⟨(E.port t.val t.isLt).yFd, (E.port t.val t.isLt).yFm⟩
    rA := a.rA
    rB := a.rB
    rF := a.rF
    pA := fun {α} _ _ X hα => by
      have hα' : a.p.h < Fintype.card α := by rwa [Fintype.card_fin] at hα
      rw [hMA, hMAi]
      exact (V.runA.route C0 X hα' cf E.w0).1
    pB := fun {α} _ _ X hα => by
      have hα' : a.p.h < Fintype.card α := by rwa [Fintype.card_fin] at hα
      rw [hMB, hMBi]
      exact (V.runB.route C0 X hα' cf wA).1
    pF := fun {α} _ _ X hα => by
      have hα' : a.p.h < Fintype.card α := by rwa [Fintype.card_fin] at hα
      exact V.runF.route_id C0 X hα' wB (noAdds_sound _ V.fin) }

/-- the ranks and the copy dimensions of the label half (for the price) -/
theorem Valid.lab_ranks {c : Raw} {a : Aux} (V : Valid c a) {C : Type} [Fintype C]
    [DecidableEq C] (S : GX.Scal (Fin c.v) (Fin c.R) C)
    {emb : CR.L3 (Fin c.v) (Fin c.R) → Nat} {un : Nat → CR.L3 (Fin c.v) (Fin c.R)}
    (Ro : Roles c.v c.R emb un) (cf : Co → Coef) (hMA) (hMAi) (hMB) (hMBi)
    (reg : C → Nat) (hCc) (hreg) :
    (V.lab S Ro cf hMA hMAi hMB hMBi reg hCc hreg).rA = a.rA ∧
    (V.lab S Ro cf hMA hMAi hMB hMBi reg hCc hreg).rB = a.rB ∧
    (V.lab S Ro cf hMA hMAi hMB hMBi reg hCc hreg).rF = a.rF ∧
    ∀ k, ((V.lab S Ro cf hMA hMAi hMB hMBi reg hCc hreg).cen k).dim
      = cdim (a.p.tab.get (a.SA.get (reg k))) :=
  ⟨rfl, rfl, rfl, fun k => lab_dim (tabK_good _ _ V.tab _)⟩

end GLab

#print axioms GLab.Valid.lab
#print axioms GLab.Valid.lab_ranks
