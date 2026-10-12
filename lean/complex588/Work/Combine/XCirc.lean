import Work.Combine.Chunks
import Work.Combine.XNetwork
import Work.SharedSumChecker.Net

/-!
# (key: combine) A kernel-checked certificate as a BLOCK circuit, and its two-stage network

`PCert.Valid.xcircuit`: an accepted certificate of a helper circuit (the same `PCert` and the
same three kernel checks as `Work.SharedSumChecker`) is an `XCircuit` of `Work.Combine.XInvocation`:
every frame change of a helper slot written in the certificate (one part of a gate op, one final
entry) is ONE block, whose rank is the number of kernel moves of that frame change.

`PCert.Valid.xcertificate`: the two-stage network of that circuit as a proper BLOCK word with
`LiveKernel` and the exact price, for every price list `φ`,

    2 v (rcost φ c.invRanks + 2 v bcost φ (h-1))       -- the 2v invocations
    + 2 v^2 bcost φ ((h-1)^2) + 2 v R bcost φ ((h-1) h) + pad (φ (h^2-1) + φ 1)
    + v^2 φ 1

where `c.invRanks` (plain data, read off the certificate) lists the ranks of the blocks of the
helper slots and of the scratch copies of ONE invocation.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace SSC
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM OAI.PowerSaving.SS
  OAI.PowerSaving.CB Finset Matrix

namespace PCert
variable (c : PCert)

variable {c}

theorem embS_out (q : Fin c.R) : c.v ≤ c.embS q ∧ c.embS q < c.v + c.R :=
  ⟨Nat.le_add_right _ _, by show c.v + q.val < _; have := q.isLt; omega⟩

theorem Valid.plain_of (V : c.Valid) (L : List (List Op)) (hL : ∀ l ∈ L, l ∈ c.cs) :
    ∀ op ∈ L.flatten, op.plain = true := by
  intro op hop
  obtain ⟨l, hl, hop'⟩ := List.mem_flatten.mp hop
  exact List.all_eq_true.mp V.hplain op (List.mem_flatten.mpr ⟨l, hL l hl, hop'⟩)

theorem Valid.plain4 (V : c.Valid) : ∀ op ∈ c.F4.flatten, op.plain = true :=
  V.plain_of c.F4 (fun l hl => by simp [cs, hl])
theorem Valid.plain5 (V : c.Valid) : ∀ op ∈ c.F5.flatten, op.plain = true :=
  V.plain_of c.F5 (fun l hl => by simp [cs, hl])
theorem Valid.plain7 (V : c.Valid) : ∀ op ∈ c.F7.flatten, op.plain = true :=
  V.plain_of c.F7 (fun l hl => by simp [cs, hl])

theorem Valid.completeS (V : c.Valid) : Complete c.p c.lab0 c.H0 c.tot c.embS :=
  V.complete c.embS (fun q => by have := q.isLt; show c.v + q.val < _; omega)

/-! ### single climbs of the banks and the copies -/

theorem Valid.kx (V : c.Valid) (t : Fin c.v) : Climb (lineL (c.tv t)) fullL := by
  have C := V.complete (fun t : Fin c.v => t.val) (fun t => by have := t.isLt; omega)
  have h := C.climb t [] c.tot [] (by simp)
  rw [List.nil_append] at h
  have e : runLab c.p c.lab0 [] t.val = c.lab0 t.val := rfl
  rw [e, V.line t, V.fullLb t.val (by have := t.isLt; omega)] at h
  exact h

theorem Valid.ky (V : c.Valid) (t : Fin c.v) : Climb zeroL (perpL (c.tv t)) := by
  have C := V.complete (fun t : Fin c.v => t.val) (fun t => by have := t.isLt; omega)
  obtain ⟨A, hA⟩ := C.base t
  obtain ⟨l, hl⟩ := hist_prefix c.H0 c.tot t.val
  have h0 : A.v ⟨0, V.hh⟩ = c.tv t := by
    rw [hA, hl]
    show vecF c.p (((if t.val < c.v then [c.trips.getD t.val 0] else []) ++ l).getD 0 0) = _
    rw [if_pos t.isLt]
    rfl
  have h := climb_zero_perp A ⟨0, V.hh⟩
  rw [h0] at h
  exact h

theorem Valid.kc (V : c.Valid) (k : Fin c.p.h) : Climb zeroL (c.phi5 (c.retq V.hR k)) := by
  have C := V.completeS
  have h := C.climb (c.retq V.hR k) [] c.a5 ((expM c.e5 ++ c.m7) ++ expM c.e7 ++ c.mfin)
    (by simp only [tot, opsM, a7, List.nil_append, List.append_assoc])
  rw [List.nil_append] at h
  have e : runLab c.p c.lab0 [] (c.embS (c.retq V.hR k)) = 0 :=
    V.lab0_ge _ (Nat.le_add_right _ _)
  rw [e, Lb_zero] at h
  exact h

/-! ### the four phases of the helper slots as exact block routes -/

section Phases
variable {α : Type} [Fintype α] [DecidableEq α]

/-- loading: every slot from the zero label to its loading label. -/
theorem Valid.x4 (V : c.Valid) (Xm : XMap (Fin c.p.h) α) :
    XRoute (fun _ : Fin c.R => Xm.Φ 0) (fun q => Xm.Φ (c.phi4 q).P) id
      (fun φ => rcost φ c.ranks4) := by
  have C := V.completeS
  have hmic : chunksMicro (opsChunks c.v c.R false c.F4.flatten ++ [.skip (expM c.e4)]) = c.a4 := by
    rw [chunksMicro_append, opsChunks_micro]
    simp [a4, m4, chunksMicro, Chunk.micro]
  have htot : c.tot = [] ++ chunksMicro (opsChunks c.v c.R false c.F4.flatten ++ [.skip (expM c.e4)])
      ++ (c.m5 ++ (expM c.e5 ++ c.m7) ++ expM c.e7 ++ c.mfin) := by
    rw [hmic]
    simp only [tot, opsM, a7, a5, List.nil_append, List.append_assoc]
  have hng : ∀ ch ∈ opsChunks c.v c.R false c.F4.flatten ++ [Chunk.skip (expM c.e4)], ch.noGate := by
    intro ch hch
    rcases List.mem_append.mp hch with h1 | h1
    · exact opsChunks_noGate c.v c.R _ ch h1
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
      rw [h1]; exact trivial
  have h := C.xpath (c.unembS V.hR) (c.unembS_embS V.hR) Xm _ [] _ htot (by
    intro ch hch
    rcases List.mem_append.mp hch with h1 | h1
    · exact opsChunks_ok c.embS (c.unembS V.hR) c.v c.R (c.embS_unembS V.hR) embS_out false _
        V.plain4 (fun e => absurd e (by simp)) ch h1
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
      rw [h1]; exact expM_quiet _ _)
  rw [matC_noGate _ _ hng, actPoint_one', List.nil_append, hmic] at h
  have es : (fun q : Fin c.R => Xm.Φ (Lb c.p (runLab c.p c.lab0 [] (c.embS q))).P)
      = fun _ => Xm.Φ 0 := by
    funext q
    have e : runLab c.p c.lab0 [] (c.embS q) = 0 := V.lab0_ge _ (Nat.le_add_right _ _)
    rw [e, Lb_zero]; rfl
  rw [es] at h
  refine h.cast (fun φ => ?_)
  rw [chunksRanks_append, opsChunks_ranks]
  simp [chunksRanks, Chunk.ranks, ranks4]

/-- the addition circuit: for `L` and for the transposed inverse. -/
theorem Valid.x5 (V : c.Valid) (Xm : XMap (Fin c.p.h) α) :
    XRoute (fun q => Xm.Φ (c.phi4 q).P) (fun q => Xm.Φ (c.phi5 q).P) (actPoint (c.Lm V.hR))
        (fun φ => rcost φ c.ranks5) ∧
    XRoute (fun q => Xm.Φ (c.phi4 q).P) (fun q => Xm.Φ (c.phi5 q).P) (actPoint (c.Linvm V.hR)ᵀ)
        (fun φ => rcost φ c.ranks5) := by
  have C := V.completeS
  have hmic : chunksMicro (opsChunks c.v c.R true c.F5.flatten) = c.m5 := opsChunks_micro _ _ _ _
  have htot0 : c.tot = c.a4 ++ c.m5 ++ ((expM c.e5 ++ c.m7) ++ expM c.e7 ++ c.mfin) := by
    simp only [tot, opsM, a7, a5, List.append_assoc]
  have hok : ∀ ch ∈ opsChunks c.v c.R true c.F5.flatten, ch.ok c.embS (c.unembS V.hR) :=
    opsChunks_ok c.embS (c.unembS V.hR) c.v c.R (c.embS_unembS V.hR) embS_out true _
      V.plain5 (fun _ => V.seg5.1)
  have hna := opsChunks_noAdd c.v c.R c.F5.flatten
  constructor
  · have h := C.xpath (c.unembS V.hR) (c.unembS_embS V.hR) Xm _ c.a4 _
      (by rw [hmic]; exact htot0) hok
    rw [matC_eq_matP _ _ hna, hmic] at h
    exact h.cast (fun φ => by rw [opsChunks_ranks]; rfl)
  · have C' : Complete c.p c.lab0 c.H0
        (c.a4 ++ c.m5 ++ ((expM c.e5 ++ c.m7) ++ expM c.e7 ++ c.mfin)) c.embS := htot0 ▸ C
    have hmic' : chunksMicro ((opsChunks c.v c.R true c.F5.flatten).map Chunk.swap)
        = c.m5.map swapNeg := by
      rw [chunksMicro_swap, hmic]
    have hna' : ∀ ch ∈ (opsChunks c.v c.R true c.F5.flatten).map Chunk.swap, ch.noAdd := by
      intro ch hch
      obtain ⟨ch', h', rfl⟩ := List.mem_map.mp hch
      exact Chunk.noAdd_swap ch' (hna ch' h')
    have h := (C'.swap).xpath (c.unembS V.hR) (c.unembS_embS V.hR) Xm
      ((opsChunks c.v c.R true c.F5.flatten).map Chunk.swap) c.a4 _ (by rw [hmic'])
      (by
        intro ch hch
        obtain ⟨ch', h', rfl⟩ := List.mem_map.mp hch
        exact Chunk.ok_swap _ _ ch' (hok ch' h'))
    rw [matC_eq_matP _ _ hna', hmic', matP_swap] at h
    have e : (fun q => Xm.Φ (Lb c.p (runLab c.p c.lab0 (c.a4 ++ c.m5.map swapNeg) (c.embS q))).P)
        = fun q => Xm.Φ (c.phi5 q).P := by
      funext q
      show Xm.Φ (Lb c.p (runLab c.p c.lab0 (c.a4 ++ c.m5.map swapNeg) (c.embS q))).P
        = Xm.Φ (Lb c.p (runLab c.p c.lab0 (c.a4 ++ c.m5) (c.embS q))).P
      rw [runLab_append, runLab_swap, ← runLab_append]
    rw [e] at h
    exact h.cast (fun φ => by rw [chunksRanks_swap, opsChunks_ranks]; rfl)

/-- the piece phase: every slot from its label after the circuit to its label as a piece. -/
theorem Valid.x7 (V : c.Valid) (Xm : XMap (Fin c.p.h) α) :
    XRoute (fun q => Xm.Φ (c.phi5 q).P) (fun q => Xm.Φ (c.phi7 q).P) id
      (fun φ => rcost φ c.ranks7) := by
  have C := V.completeS
  have hmic : chunksMicro (Chunk.skip (expM c.e5) :: opsChunks c.v c.R false c.F7.flatten)
      = expM c.e5 ++ c.m7 := by
    rw [chunksMicro_cons, opsChunks_micro]; rfl
  have htot : c.tot = c.a5 ++ chunksMicro (Chunk.skip (expM c.e5) :: opsChunks c.v c.R false c.F7.flatten)
      ++ (expM c.e7 ++ c.mfin) := by
    rw [hmic]
    simp only [tot, opsM, a7, List.append_assoc]
  have hng : ∀ ch ∈ Chunk.skip (expM c.e5) :: opsChunks c.v c.R false c.F7.flatten, ch.noGate := by
    intro ch hch
    rcases List.mem_cons.mp hch with h1 | h1
    · rw [h1]; exact trivial
    · exact opsChunks_noGate c.v c.R _ ch h1
  have h := C.xpath (c.unembS V.hR) (c.unembS_embS V.hR) Xm _ c.a5 _ htot (by
    intro ch hch
    rcases List.mem_cons.mp hch with h1 | h1
    · rw [h1]; exact expM_quiet _ _
    · exact opsChunks_ok c.embS (c.unembS V.hR) c.v c.R (c.embS_unembS V.hR) embS_out false _
        V.plain7 (fun e => absurd e (by simp)) ch h1)
  rw [matC_noGate _ _ hng, actPoint_one', hmic] at h
  refine h.cast (fun φ => ?_)
  rw [chunksRanks_cons, opsChunks_ranks]
  rfl

/-- completion: every slot from its piece label to the full label. -/
theorem Valid.xF (V : c.Valid) (Xm : XMap (Fin c.p.h) α) :
    XRoute (fun q => Xm.Φ (c.phi7 q).P) (fun _ : Fin c.R => Xm.Φ 1) id
      (fun φ => rcost φ c.ranksF) := by
  have C := V.completeS
  have hmic : chunksMicro (Chunk.skip (expM c.e7) :: finsChunks c.v c.R c.fins.flatten)
      = expM c.e7 ++ c.mfin := by
    rw [chunksMicro_cons, finsChunks_micro]; rfl
  have htot : c.tot = c.a7 ++ chunksMicro (Chunk.skip (expM c.e7) :: finsChunks c.v c.R c.fins.flatten)
      ++ [] := by
    rw [hmic]
    simp only [tot, opsM, List.append_assoc, List.append_nil]
  have hng : ∀ ch ∈ Chunk.skip (expM c.e7) :: finsChunks c.v c.R c.fins.flatten, ch.noGate := by
    intro ch hch
    rcases List.mem_cons.mp hch with h1 | h1
    · rw [h1]; exact trivial
    · exact finsChunks_noGate c.v c.R _ ch h1
  have h := C.xpath (c.unembS V.hR) (c.unembS_embS V.hR) Xm _ c.a7 _ htot (by
    intro ch hch
    rcases List.mem_cons.mp hch with h1 | h1
    · rw [h1]; exact expM_quiet _ _
    · exact finsChunks_ok c.embS (c.unembS V.hR) c.v c.R (c.embS_unembS V.hR) embS_out _ ch h1)
  rw [matC_noGate _ _ hng, actPoint_one', hmic] at h
  have et : (fun q : Fin c.R => Xm.Φ (Lb c.p (runLab c.p c.lab0 (c.a7 ++ (expM c.e7 ++ c.mfin))
      (c.embS q))).P) = fun _ => Xm.Φ 1 := by
    funext q
    have e : c.a7 ++ (expM c.e7 ++ c.mfin) = c.tot := by
      simp only [tot, opsM, List.append_assoc]
    rw [e, V.fullLb _ (by have := q.isLt; show c.v + q.val < _; omega)]
    rfl
  rw [et] at h
  refine h.cast (fun φ => ?_)
  rw [chunksRanks_cons, finsChunks_ranks]
  rfl

end Phases

/-! ### the block circuit and its network -/

/-- **The block circuit of a checked certificate.** -/
noncomputable def Valid.xcircuit (V : c.Valid) (hid : c.ScalarId V.hR) :
    XCircuit (Fin c.p.h) (Fin c.v) (Fin c.R) (Fin c.p.h) where
  K := V.circuit hid
  kx := V.kx
  ky := V.ky
  kc := V.kc
  r4 := c.ranks4
  r5 := c.ranks5
  r7 := c.ranks7
  rF := c.ranksF
  p4 := fun Xm => V.x4 Xm
  p5 := fun Xm => V.x5 Xm
  p7 := fun Xm => V.x7 Xm
  pF := fun Xm => V.xF Xm

/-- the block network data of a checked certificate -/
noncomputable def Valid.xnetdata (V : c.Valid) (hid : c.ScalarId V.hR) (pad : ℕ)
    (h2 : 2 ≤ c.p.h) : XNetData (Fin c.p.h) (Fin c.v) (Fin c.R) (Fin c.p.h) where
  X := V.xcircuit hid
  base := fun t => Classical.choose (V.base_ex t)
  piv := fun _ => ⟨0, V.hh⟩
  hbase := fun t => Classical.choose_spec (V.base_ex t)
  pad := pad
  hH := by rw [Fintype.card_fin]; exact h2

/-- the copies cost the dimensions of the labels of the retained totals -/
theorem Valid.cen_cost (V : c.Valid) (φ : ℕ → ℝ) :
    ∑ k : Fin c.p.h, bcost φ (c.phi5 (c.retq V.hR k)).d = rcost φ c.cenRanks := by
  have hterm : ∀ k : Fin c.p.h,
      (c.phi5 (c.retq V.hR k)).d = cntOf c.p (dec (c.retLab.getD k.val 0)) := by
    intro k
    obtain ⟨_, p5, _, _⟩ := V.points
    have hmem : (c.v + c.ret.getD k.val 0, c.retLab.getD k.val 0) ∈ c.e5 :=
      List.mem_map.mpr ⟨(c.ret.getD k.val 0, c.retLab.getD k.val 0),
        zip_getD_mem _ _ _ _ _ (by rw [V.hrl]; exact k.isLt) (by rw [V.hrl']; exact k.isLt), rfl⟩
    have h := p5 _ hmem
    show cntOf c.p (runLab c.p c.lab0 c.a5 (c.embS (c.retq V.hR k))) = _
    have e : c.embS (c.retq V.hR k) = c.v + c.ret.getD k.val 0 := by
      show c.v + c.ret.getD k.val 0 % c.R = _
      rw [Nat.mod_eq_of_lt (V.all_ret k)]
    rw [e, h]
  rw [Finset.sum_congr rfl (fun k _ => by rw [hterm k])]
  have e : rcost φ c.cenRanks = (c.retLab.map (fun L => bcost φ (cntOf c.p (dec L)))).sum := by
    unfold cenRanks rcost
    rw [List.map_map]
    rfl
  rw [e, list_sum_range (fun L => bcost φ (cntOf c.p (dec L))) c.retLab, V.hrl']
  exact Fin.sum_univ_eq_sum_range (fun k => bcost φ (cntOf c.p (dec (c.retLab.getD k 0)))) c.p.h

/-- price of one invocation of the block circuit of a certificate -/
theorem Valid.xcost (V : c.Valid) (hid : c.ScalarId V.hR) (φ : ℕ → ℝ) :
    (V.xcircuit hid).cost φ = rcost φ c.invRanks + 2 * ((c.v : ℝ) * bcost φ (c.p.h - 1)) := by
  show rcost φ c.ranks4 + rcost φ c.ranks5 + rcost φ c.ranks7 + rcost φ c.ranksF
      + (∑ k : Fin c.p.h, bcost φ (c.phi5 (c.retq V.hR k)).d)
      + 2 * ((Fintype.card (Fin c.v) : ℝ) * bcost φ (Fintype.card (Fin c.p.h) - 1)) = _
  rw [V.cen_cost φ, Fintype.card_fin, Fintype.card_fin]
  simp only [invRanks, rcost_append]

/-- **The two-stage network of a checked helper circuit, in WHOLE BLOCKS**: a proper block
word with `LiveKernel` and the exact price for every price list. -/
theorem Valid.xcertificate (V : c.Valid) (hid : c.ScalarId V.hR) (pad : ℕ) (h2 : 2 ≤ c.p.h) :
    ∃ w : BWord (Fin c.p.h × Fin c.p.h) (Role (Fin c.v) (Fin c.R) (Fin c.p.h) pad),
      w.Proper (c.p.h * c.p.h) ∧
      (∀ φ : ℕ → ℝ, w.costR φ
        = 2 * ((c.v : ℝ) * (rcost φ c.invRanks + 2 * ((c.v : ℝ) * bcost φ (c.p.h - 1))))
          + (2 * ((c.v : ℝ) * (c.v : ℝ) * bcost φ ((c.p.h - 1) * (c.p.h - 1)))
            + 2 * ((c.v : ℝ) * (c.R : ℝ) * bcost φ ((c.p.h - 1) * c.p.h))
            + (pad : ℝ) * (φ (c.p.h * c.p.h - 1) + φ 1))
          + (c.v : ℝ) * (c.v : ℝ) * φ 1) ∧
      LiveKernel (Sum.inl : Live (Fin c.v) (Fin c.R) pad →
        Role (Fin c.v) (Fin c.R) (Fin c.p.h) pad) w.flat := by
  obtain ⟨w, hP, hc, hw⟩ := xnetwork_certificate (V.xnetdata hid pad h2)
  refine ⟨w, ?_, ?_, hw⟩
  · have e : Fintype.card (Fin c.p.h × Fin c.p.h) = c.p.h * c.p.h := by
      rw [Fintype.card_prod, Fintype.card_fin]
    rw [← e]; exact hP
  · intro φ
    refine (hc φ).trans ?_
    show 2 * ((Fintype.card (Fin c.v) : ℝ) * (V.xcircuit hid).cost φ)
        + (2 * ((Fintype.card (Fin c.v) : ℝ) * (Fintype.card (Fin c.v) : ℝ)
              * bcost φ ((Fintype.card (Fin c.p.h) - 1) * (Fintype.card (Fin c.p.h) - 1)))
          + 2 * ((Fintype.card (Fin c.v) : ℝ) * (Fintype.card (Fin c.R) : ℝ)
              * bcost φ ((Fintype.card (Fin c.p.h) - 1) * Fintype.card (Fin c.p.h)))
          + (pad : ℝ) * (φ (Fintype.card (Fin c.p.h × Fin c.p.h) - 1) + φ 1))
        + (Fintype.card (Fin c.v) : ℝ) * (Fintype.card (Fin c.v) : ℝ) * φ 1 = _
    rw [V.xcost hid φ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin]

end PCert

end SSC

#print axioms SSC.PCert.Valid.xcircuit
#print axioms SSC.PCert.Valid.xcertificate
