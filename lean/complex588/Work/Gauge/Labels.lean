import Work.GCert.Labels.Main
import Work.Gauge.Defs

/-!
# (key: gauge-401) The label half of a GAUGED certificate: `ValidE.glab : GX.GLab`

DFT Bridge3, 2026-10-11.  Jacob Sussman's label check (`Work/GCert/Labels/{EndDef,EndSound,Main}.lean`, Apache-2.0)
already replays the labels from ANY start state `S0`; only the end check asks every slot to start at frame id 0.
`endKE … gl …` asks it only for the slots whose register is NOT in the gauge list `gl` (entrance gauges, Dugongue
PR #401); `ValidE.glab` builds `GX.GLab` with `ent q` = the start label of slot `q`.  No `sorry`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace GLab
open SSC GXD OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.GF OAI.PowerSaving.RAM
  OAI.PowerSaving.CB Finset Matrix

/-- `r ∈ gl`, as a kernel term -/
noncomputable def memK (r : Nat) (gl : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun x _ ih => Bool.rec (motive := fun _ => Bool) ih true (Nat.beq x r)) gl

theorem memK_sound (r : Nat) : ∀ gl : List Nat, memK r gl = true → r ∈ gl := by
  intro gl
  induction gl with
  | nil => intro h; exact absurd h Bool.false_ne_true
  | cons x gl ih =>
    intro h
    have h' : Bool.rec (motive := fun _ => Bool) (memK r gl) true (Nat.beq x r) = true := h
    cases e : Nat.beq x r with
    | true => rw [← beq_true e]; exact List.mem_cons_self
    | false => rw [e] at h'; exact List.mem_cons_of_mem _ (ih h')

/-- slots: start at frame id 0 or are gauged (register in `gl`); end at full dimension -/
noncomputable def slotsKE (p : Par) (v2 : Nat) (gl : List Nat) (S0 SF : Trie) : Nat → Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun q ih => S0.getK (Nat.add v2 q) fun a =>
      guard (Bool.rec (motive := fun _ => Bool) (memK (Nat.add v2 q) gl) true (Nat.beq a 0)) <|
      SF.getK (Nat.add v2 q) fun b => p.tab.getK b fun cb =>
      guard (Nat.beq (Nat.land cb 255) p.h) ih)

/-- **the end check with entrance gauges** (`endK` with `slotsKE`) -/
noncomputable def endKE (p : Par) (v : Nat) (ports rets gl : List Nat) (S0 SA SF : Trie) : Bool :=
  guard (Nat.ble 1 p.h) <|
  guard (wfK S0 p.d) <|
  guard (Nat.ble p.n (Nat.pow 2 p.d)) <|
  guard (Nat.ble (Nat.mul 2 v) p.n) <|
  p.tab.getK 0 fun c0 => guard (Nat.beq (Nat.land c0 255) 0) <|
  forceN (Nat.sub (Nat.pow 2 p.h) 1) fun hm =>
  forceN (Nat.div (Nat.sub (Nat.pow 2 (Nat.mul p.h p.h)) 1) hm) fun Oh =>
  guard (Nat.beq (Nat.mul Oh hm) (Nat.sub (Nat.pow 2 (Nat.mul p.h p.h)) 1)) <|
  guard (portsK p hm Oh (Nat.add 8 p.h) v S0 SA SF ports 0) <|
  guard (slotsKE p (Nat.mul 2 v) gl S0 SF (Nat.sub p.n (Nat.mul 2 v))) (retsK p SA rets)

theorem slotsKE_sound (p : Par) (v2 : Nat) (gl : List Nat) (S0 SF : Trie) : ∀ n, slotsKE p v2 gl S0 SF n = true →
    ∀ q, q < n → (S0.get (v2 + q) = 0 ∨ v2 + q ∈ gl) ∧ cdim (p.tab.get (SF.get (v2 + q))) = p.h := by
  intro n
  induction n with
  | zero => intro _ q hq; exact absurd hq (Nat.not_lt_zero q)
  | succ n ih =>
    intro H q hq
    have H := getK_true _ _ _ H
    obtain ⟨g1, H⟩ := guard_true H
    have H := getK_true _ _ _ H
    have H := getK_true _ _ _ H
    obtain ⟨g2, H⟩ := guard_true H
    rcases Nat.lt_succ_iff_lt_or_eq.mp hq with h1 | h1
    · exact ih H q h1
    · rw [h1]
      refine ⟨?_, beq_true g2⟩
      cases e : Nat.beq (S0.get (Nat.add v2 n)) 0 with
      | true => exact Or.inl (beq_true e)
      | false => rw [e] at g1; exact Or.inr (memK_sound _ gl g1)

/-- everything the gauged end check proves -/
structure EndsE (p : Par) (v : Nat) (ports rets gl : List Nat) (S0 SA SF : Trie) : Prop where
  hh : 0 < p.h
  w0 : S0.wf p.d
  hn : p.n ≤ 2 ^ p.d
  hv : 2 * v ≤ p.n
  z0 : cdim (p.tab.get 0) = 0
  len : ports.length = v
  port : ∀ t, t < v → PortOK p v S0 SA SF t (ports.getD t 0)
  slot : ∀ q, q < p.n - 2 * v →
    (S0.get (2 * v + q) = 0 ∨ 2 * v + q ∈ gl) ∧ cdim (p.tab.get (SF.get (2 * v + q))) = p.h
  ret : ∀ r ∈ rets, 0 < cdim (p.tab.get (SA.get r))

theorem endKE_sound {p : Par} {v : Nat} {ports rets gl : List Nat} {S0 SA SF : Trie}
    (hT : tabK p.h p.tab = true) (H : endKE p v ports rets gl S0 SA SF = true) :
    EndsE p v ports rets gl S0 SA SF := by
  unfold endKE at H
  obtain ⟨g0, H⟩ := guard_true H
  obtain ⟨g1, H⟩ := guard_true H
  obtain ⟨g2, H⟩ := guard_true H
  obtain ⟨g3, H⟩ := guard_true H
  have H := getK_true _ _ _ H
  obtain ⟨g4, H⟩ := guard_true H
  rw [forceN_eq] at H
  rw [forceN_eq] at H
  obtain ⟨g5, H⟩ := guard_true H
  have hh : 0 < p.h := ble_true g0
  have eO : Nat.div (Nat.sub (Nat.pow 2 (Nat.mul p.h p.h)) 1) (Nat.sub (Nat.pow 2 p.h) 1)
      = rep p.h p.h := rep_of_mul p.h p.h _ hh (beq_true g5)
  rw [eO] at H
  obtain ⟨g6, H⟩ := guard_true H
  obtain ⟨g7, g8⟩ := guard_true H
  obtain ⟨a, b⟩ := portsK_sound p hT hh v S0 SA SF ports 0 g6
  have len : ports.length = v := by omega
  exact
    { hh := hh
      w0 := wfK_sound _ _ g1
      hn := ble_true g2
      hv := ble_true g3
      z0 := beq_true g4
      len := len
      port := fun t ht => by
        have := b t (by omega)
        rw [Nat.zero_add] at this
        exact this
      slot := slotsKE_sound p _ gl S0 SF _ g7
      ret := retsK_sound p SA rets g8 }

/-- **the kernel-checked label facts of a gauged certificate** (`Valid` with `endKE`) -/
structure ValidE (c : Raw) (a : Aux) (gl : List Nat) : Prop where
  hn : a.p.n = 2 * c.v + c.R
  tab : tabK a.p.h a.p.tab = true
  runA : Run a.p a.S0 c.gatesA a.SA a.rA
  runB : Run a.p a.SA c.gatesB a.SB a.rB
  runF : Run a.p a.SB a.fins a.SF a.rF
  fin : noAdds a.fins = true
  ends : endKE a.p c.v c.ports (c.ret.map Prod.fst) gl a.S0 a.SA a.SF = true

/-- **THE LABEL HALF of a gauged certificate**: `GX.GLab` for its gauged scalar half; the entrance label of slot
`q` is its label in the start state.  `hg`: every slot in the gauge list is gauged in `S`. -/
noncomputable def ValidE.glab {c : Raw} {a : Aux} {gl : List Nat} (V : ValidE c a gl) {C : Type} [Fintype C]
    [DecidableEq C] (S : OAI.PowerSaving.GX.GScal (Fin c.v) (Fin c.R) C)
    {emb : CR.L3 (Fin c.v) (Fin c.R) → Nat} {un : Nat → CR.L3 (Fin c.v) (Fin c.R)}
    (Ro : Roles c.v c.R emb un) (cf : Co → Coef)
    (hMA : S.MA = matP un (mic cf (c.gatesA.flatMap Gate.adds)))
    (hMAi : S.MAi = matPinv un (mic cf (c.gatesA.flatMap Gate.adds)))
    (hMB : S.MB = matP un (mic cf (c.gatesB.flatMap Gate.adds)))
    (hMBi : S.MBi = matPinv un (mic cf (c.gatesB.flatMap Gate.adds)))
    (reg : C → Nat) (hCc : ∀ k (q : Fin c.R), S.Cc k q ≠ 0 → reg k = 2 * c.v + q.val)
    (hreg : ∀ k, reg k ∈ c.ret.map Prod.fst)
    (hg : ∀ q : Fin c.R, 2 * c.v + q.val ∈ gl → q ∈ S.gauged) : OAI.PowerSaving.GX.GLab (Fin a.p.h) S :=
  have E := endKE_sound V.tab V.ends
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
    ent := fun q => a.p.labS a.S0 (emb (CR.lS q))
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
    h0s' := fun q => rfl
    hent := fun q hq => by
      show (GLab.lab a.p.h (a.p.tab.get (a.S0.get (emb (CR.lS q))))).dim = 0
      rw [Ro.eS q]
      rcases (E.slot q.val (by have := V.hn; have := q.isLt; omega)).1 with h0 | hm
      · rw [h0, G]; exact E.z0
      · exact absurd (hg q hm) hq
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

/-- the ranks and the copy dimensions of the gauged label half (for the price) -/
theorem ValidE.glab_ranks {c : Raw} {a : Aux} {gl : List Nat} (V : ValidE c a gl) {C : Type} [Fintype C]
    [DecidableEq C] (S : OAI.PowerSaving.GX.GScal (Fin c.v) (Fin c.R) C)
    {emb : CR.L3 (Fin c.v) (Fin c.R) → Nat} {un : Nat → CR.L3 (Fin c.v) (Fin c.R)}
    (Ro : Roles c.v c.R emb un) (cf : Co → Coef) (hMA) (hMAi) (hMB) (hMBi)
    (reg : C → Nat) (hCc) (hreg) (hg) :
    (V.glab S Ro cf hMA hMAi hMB hMBi reg hCc hreg hg).rA = a.rA ∧
    (V.glab S Ro cf hMA hMAi hMB hMBi reg hCc hreg hg).rB = a.rB ∧
    (V.glab S Ro cf hMA hMAi hMB hMBi reg hCc hreg hg).rF = a.rF ∧
    ∀ k, ((V.glab S Ro cf hMA hMAi hMB hMBi reg hCc hreg hg).cen k).dim
      = cdim (a.p.tab.get (a.SA.get (reg k))) :=
  ⟨rfl, rfl, rfl, fun k => lab_dim (tabK_good _ _ V.tab _)⟩

end GLab

#print axioms GLab.endKE_sound
#print axioms GLab.ValidE.glab
#print axioms GLab.ValidE.glab_ranks
