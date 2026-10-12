import Work.CarrierCheck.Mat

/-!
# (key: carrier-check) The phases of a checked carrier certificate as exact block routes

For every block frame map `Xm`, on the live roles `c.Rl` (x, y, slots; all on the same footing):

* `Valid.route_ops`   a list of carrier ops, as a contiguous part of the micro-program, is an
                      exact block route between the labels before and after it, with the ordered
                      product of its gates as scalar map (and with the transposed inverse), one
                      block per frame change written in the certificate;
* `Valid.route_fin`   the real final entries: every x role and every slot climbs to the full
                      label.

Everything comes from `SSC.Complete.xpath` (`Work.Combine.Chunks`), which never asked which roles
are banks.  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace SSC
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM OAI.PowerSaving.SS
  OAI.PowerSaving.CB Finset Matrix

namespace CCert
variable {c : CCert}

/-- label of a live role after the micro-prefix `a` -/
def labAt (c : CCert) (a : List Micro) (q : c.Rl) : Lbl (Fin c.p.h) :=
  Lb c.p (runLab c.p c.lab0 a (c.emb3 q))

/-- the gates of carrier ops: `t < n`, `s` not a y role, `t` not an x role, `s ≠ t` -/
theorem adds_of_carrier (c : CCert) (ops : List Op)
    (hops : ∀ op ∈ ops, op.carrier c.v c.R = true) (t s : Nat) (cf : Coef)
    (h : Micro.add t s cf ∈ ops.flatMap Op.micro) :
    t < c.n ∧ s < c.v + c.R ∧ c.v ≤ t ∧ s ≠ t := by
  obtain ⟨op, hop, hmop⟩ := List.mem_flatMap.mp h
  rcases carrier_micro c.v c.R op (hops op hop) _ hmop with
    ⟨r, z, e | e, _⟩ | ⟨t', s', cf', e, h1, h2, h3, h4⟩
  · exact absurd e (by simp)
  · exact absurd e (by simp)
  · injection e with e1 e2 e3
    subst e1; subst e2
    exact ⟨h1, h2, h3, h4⟩

theorem Valid.seg_ops (V : c.Valid) (ops : List Op)
    (hops : ∀ op ∈ ops, op.carrier c.v c.R = true) :
    ∀ m ∈ ops.flatMap Op.micro, segOK c.emb3 (c.unemb3 V.hv V.hR) m := by
  intro m hm
  obtain ⟨op, hop, hmop⟩ := List.mem_flatMap.mp hm
  rcases carrier_micro c.v c.R op (hops op hop) m hmop with
    ⟨r, z, e | e, hr⟩ | ⟨t, s, cf, e, ht, hs, _, _⟩
  · rw [e]
    exact c.emb3_unemb3 V.hv V.hR r hr
  · rw [e]
    exact trivial
  · rw [e]
    have hs' : s < c.n := by unfold n; omega
    exact ⟨c.emb3_unemb3 V.hv V.hR t ht, c.emb3_unemb3 V.hv V.hR s hs'⟩

section
variable {α : Type} [Fintype α] [DecidableEq α]

/-- **a list of carrier ops is an exact block route**, for the product of its gates and for the
transposed inverse; one block per frame change. -/
theorem Valid.route_ops (V : c.Valid) (Xm : XMap (Fin c.p.h) α) (ops : List Op)
    (hops : ∀ op ∈ ops, op.carrier c.v c.R = true) (a rest : List Micro)
    (htot : c.tot = a ++ ops.flatMap Op.micro ++ rest) :
    XRoute (fun q => Xm.Φ (c.labAt a q).P)
        (fun q => Xm.Φ (c.labAt (a ++ ops.flatMap Op.micro) q).P)
        (actPoint (matP (c.unemb3 V.hv V.hR) (ops.flatMap Op.micro)))
        (fun φ => rcost φ (opsRanks 0 c.n ops)) ∧
    XRoute (fun q => Xm.Φ (c.labAt a q).P)
        (fun q => Xm.Φ (c.labAt (a ++ ops.flatMap Op.micro) q).P)
        (actPoint (matPinv (c.unemb3 V.hv V.hR) (ops.flatMap Op.micro))ᵀ)
        (fun φ => rcost φ (opsRanks 0 c.n ops)) := by
  have C := V.complete3
  have hun := c.unemb3_emb3 V.hv V.hR
  have hmic : chunksMicro (opsChunks 0 c.n true ops) = ops.flatMap Op.micro :=
    opsChunks_micro _ _ _ _
  have hseg := V.seg_ops ops hops
  have hin : ∀ r, 0 ≤ r → r < 0 + c.n → c.emb3 (c.unemb3 V.hv V.hR r) = r :=
    fun r _ hr => c.emb3_unemb3 V.hv V.hR r (by omega)
  have hout : ∀ q : c.Rl, 0 ≤ c.emb3 q ∧ c.emb3 q < 0 + c.n :=
    fun q => ⟨Nat.zero_le _, by have := c.emb3_lt q; omega⟩
  have hok : ∀ ch ∈ opsChunks 0 c.n true ops, ch.ok c.emb3 (c.unemb3 V.hv V.hR) :=
    opsChunks_ok c.emb3 (c.unemb3 V.hv V.hR) 0 c.n hin hout true ops
      (fun op h => carrier_plain _ _ op (hops op h)) (fun _ => hseg)
  have hna := opsChunks_noAdd 0 c.n ops
  constructor
  · have h := C.xpath (c.unemb3 V.hv V.hR) hun Xm _ a rest (by rw [hmic]; exact htot) hok
    rw [matC_eq_matP _ _ hna, hmic] at h
    exact h.cast (fun φ => by rw [opsChunks_ranks])
  · have C' : Complete c.p c.lab0 c.H0 (a ++ ops.flatMap Op.micro ++ rest) c.emb3 := htot ▸ C
    have hmic' : chunksMicro ((opsChunks 0 c.n true ops).map Chunk.swap)
        = (ops.flatMap Op.micro).map swapNeg := by
      rw [chunksMicro_swap, hmic]
    have hna' : ∀ ch ∈ (opsChunks 0 c.n true ops).map Chunk.swap, ch.noAdd := by
      intro ch hch
      obtain ⟨ch', h', rfl⟩ := List.mem_map.mp hch
      exact Chunk.noAdd_swap ch' (hna ch' h')
    have h := (C'.swap).xpath (c.unemb3 V.hv V.hR) hun Xm
      ((opsChunks 0 c.n true ops).map Chunk.swap) a rest (by rw [hmic'])
      (by
        intro ch hch
        obtain ⟨ch', h', rfl⟩ := List.mem_map.mp hch
        exact Chunk.ok_swap _ _ ch' (hok ch' h'))
    rw [matC_eq_matP _ _ hna', hmic', matP_swap] at h
    have e : (fun q => Xm.Φ (Lb c.p (runLab c.p c.lab0
          (a ++ (ops.flatMap Op.micro).map swapNeg) (c.emb3 q))).P)
        = fun q => Xm.Φ (c.labAt (a ++ ops.flatMap Op.micro) q).P := by
      funext q
      show Xm.Φ (Lb c.p (runLab c.p c.lab0 (a ++ (ops.flatMap Op.micro).map swapNeg)
          (c.emb3 q))).P
        = Xm.Φ (Lb c.p (runLab c.p c.lab0 (a ++ ops.flatMap Op.micro) (c.emb3 q))).P
      rw [runLab_append, runLab_swap, ← runLab_append]
    rw [e] at h
    exact h.cast (fun φ => by rw [chunksRanks_swap, opsChunks_ranks])

/-- **the real final entries**: every x role and every slot climbs to the full label. -/
theorem Valid.route_fin (V : c.Valid) (Xm : XMap (Fin c.p.h) α) :
    XRoute (fun q => Xm.Φ (c.labAt c.aB q).P) (fun q => Xm.Φ (c.labAt (c.aB ++ c.mF) q).P) id
      (fun φ => rcost φ (finsRanks 0 c.n c.fins.flatten)) := by
  have C := V.complete3
  have hmic : chunksMicro (finsChunks 0 c.n c.fins.flatten) = c.mF := finsChunks_micro _ _ _
  have htot : c.tot = c.aB ++ chunksMicro (finsChunks 0 c.n c.fins.flatten) ++ c.mY := by
    rw [hmic]; rfl
  have hin : ∀ r, 0 ≤ r → r < 0 + c.n → c.emb3 (c.unemb3 V.hv V.hR r) = r :=
    fun r _ hr => c.emb3_unemb3 V.hv V.hR r (by omega)
  have hout : ∀ q : c.Rl, 0 ≤ c.emb3 q ∧ c.emb3 q < 0 + c.n :=
    fun q => ⟨Nat.zero_le _, by have := c.emb3_lt q; omega⟩
  have hng : ∀ ch ∈ finsChunks 0 c.n c.fins.flatten, ch.noGate := finsChunks_noGate 0 c.n _
  have h := C.xpath (c.unemb3 V.hv V.hR) (c.unemb3_emb3 V.hv V.hR) Xm _ c.aB c.mY htot
    (finsChunks_ok c.emb3 (c.unemb3 V.hv V.hR) 0 c.n hin hout _)
  rw [matC_noGate _ _ hng, actPoint_one', hmic] at h
  exact h.cast (fun φ => by rw [finsChunks_ranks])

end

end CCert

end SSC
