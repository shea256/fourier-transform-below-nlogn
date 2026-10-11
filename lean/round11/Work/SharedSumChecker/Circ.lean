import Work.SharedSumChecker.Mats
import Work.SharedSumChecker.PCert

/-!
# Shared-sum checker: a kernel-checked certificate gives a `Circuit` of
`Work.SharedSumStructured`

`PCert` is the data of the helper circuit of ONE invocation: the triples, the labelled
programs of the loading phase (`F4`), of the addition circuit (`F5`), of the piece phase
(`F7`), the final frame changes, and the tables of the scalar read-out (`src`, `ret`,
`pieces`, `scat`).  `PValid c` collects what the kernel has to check (`check ... = true` plus a
few shape tests).  `PCert.circuit` then is a `Circuit (Fin h) (Fin v) (Fin R) (Fin h)` of the
structured development, PROVIDED the scalar identity `J L V = 1` (`hid`) holds; that identity
is checked separately (Work.SharedSumChecker.Scalar).

Roles of the certificate: `0 .. v-1` = the inputs `X_t` (first label: the line of `t`),
`v .. v+R-1` = the helper slots, `v+R+S` = a reference role per target `S` (it only serves to
compute the label of `t_S^⊥`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace SSC
open OAI.PowerSaving.Binary OAI.PowerSaving.RAM OAI.PowerSaving.SS Finset Matrix

/-! ## list helpers -/

def expM (l : List (Nat × Nat)) : List Micro := l.map fun x => Micro.expect x.1 x.2

theorem expOps_micro (l : List (Nat × Nat)) : (expOps l).flatMap Op.micro = expM l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    show Op.micro (Op.expect x.1 x.2) ++ (expOps l).flatMap Op.micro = _
    rw [ih]; rfl

theorem expM_ok (p : Par) (lab : Nat → Nat) (l : List (Nat × Nat)) (h : Ok p lab (expM l)) :
    (∀ x ∈ l, lab x.1 = dec x.2) ∧ runLab p lab (expM l) = lab := by
  induction l with
  | nil => exact ⟨by simp, rfl⟩
  | cons x l ih =>
    have h' : Ok p lab (Micro.expect x.1 x.2 :: expM l) := h
    obtain ⟨h1, h2⟩ := h'
    obtain ⟨a, b⟩ := ih h2
    refine ⟨fun y hy => ?_, b⟩
    rcases List.mem_cons.mp hy with e | e
    · rw [e]; exact h1.2
    · exact a y e

theorem zip_getD_mem {α β : Type} (l1 : List α) (l2 : List β) (d1 : α) (d2 : β) (t : Nat)
    (h1 : t < l1.length) (h2 : t < l2.length) : (l1.getD t d1, l2.getD t d2) ∈ l1.zip l2 := by
  induction l1 generalizing l2 t with
  | nil => simp at h1
  | cons a l1 ih =>
    cases l2 with
    | nil => simp at h2
    | cons b l2 =>
      cases t with
      | zero => simp
      | succ t =>
        simp only [List.getD_cons_succ, List.zip_cons_cons, List.mem_cons]
        right
        exact ih l2 t (by simpa using h1) (by simpa using h2)

theorem getD_map_lt {α β : Type} (f : α → β) (l : List α) (d : α) (e : β) (t : Nat)
    (h : t < l.length) : (l.map f).getD t e = f (l.getD t d) := by
  induction l generalizing t with
  | nil => simp at h
  | cons a l ih =>
    cases t with
    | zero => rfl
    | succ t => simp only [List.map_cons, List.getD_cons_succ]; exact ih t (by simpa using h)

theorem getD_mem_lt {α : Type} (l : List α) (d : α) (t : Nat) (h : t < l.length) :
    l.getD t d ∈ l := by
  induction l generalizing t with
  | nil => simp at h
  | cons a l ih =>
    cases t with
    | zero => simp
    | succ t =>
      simp only [List.getD_cons_succ, List.mem_cons]
      right; exact ih t (by simpa using h)

/-! ## what the micro-ops of a gate op are -/

theorem mem_part_micro (pt : Part) (m : Micro) (h : m ∈ pt.micro) :
    ∃ z, m = .dir pt.role z ∨ m = .shift pt.role z := by
  cases pt with
  | old r dirs sh =>
    rcases List.mem_append.mp h with h | h
    · obtain ⟨z, _, rfl⟩ := List.mem_map.mp h; exact ⟨z, Or.inl rfl⟩
    · rw [List.mem_singleton] at h; exact ⟨sh, Or.inr h⟩
  | new r dirs sh =>
    rcases List.mem_append.mp h with h | h
    · obtain ⟨z, _, rfl⟩ := List.mem_map.mp h; exact ⟨z, Or.inl rfl⟩
    · rw [List.mem_singleton] at h; exact ⟨sh, Or.inr h⟩
  | stay r => exact absurd h (by simp [Part.micro])

theorem mem_gatesRow (t : Nat) (srcs : List Part) (row : List Coef) (m : Micro)
    (h : m ∈ gatesRow t srcs row) : ∃ s ∈ srcs, ∃ cf, m = .add t s.role cf := by
  induction srcs generalizing row with
  | nil => exact absurd h (by simp [gatesRow])
  | cons s ss ih =>
    cases row with
    | nil =>
      rcases List.mem_cons.mp h with h | h
      · exact ⟨s, List.mem_cons_self .., _, h⟩
      · obtain ⟨s', hs', cf, e⟩ := ih [] h
        exact ⟨s', List.mem_cons_of_mem _ hs', cf, e⟩
    | cons c cs =>
      rcases List.mem_cons.mp h with h | h
      · exact ⟨s, List.mem_cons_self .., _, h⟩
      · obtain ⟨s', hs', cf, e⟩ := ih cs h
        exact ⟨s', List.mem_cons_of_mem _ hs', cf, e⟩

theorem mem_gatesM (srcs tgts : List Part) (coefs : List (List Coef)) (m : Micro)
    (h : m ∈ gatesM srcs tgts coefs) :
    ∃ t ∈ tgts, ∃ s ∈ srcs, ∃ cf, m = .add t.role s.role cf := by
  induction tgts generalizing coefs with
  | nil => exact absurd h (by simp [gatesM])
  | cons t ts ih =>
    cases coefs with
    | nil =>
      rcases List.mem_append.mp h with h | h
      · obtain ⟨s, hs, cf, e⟩ := mem_gatesRow _ _ _ _ h
        exact ⟨t, List.mem_cons_self .., s, hs, cf, e⟩
      · obtain ⟨t', ht', r⟩ := ih [] h
        exact ⟨t', List.mem_cons_of_mem _ ht', r⟩
    | cons row rows =>
      rcases List.mem_append.mp h with h | h
      · obtain ⟨s, hs, cf, e⟩ := mem_gatesRow _ _ _ _ h
        exact ⟨t, List.mem_cons_self .., s, hs, cf, e⟩
      · obtain ⟨t', ht', r⟩ := ih rows h
        exact ⟨t', List.mem_cons_of_mem _ ht', r⟩

theorem plain_noCopy (op : Op) (h : op.plain = true) (m : Micro) (hm : m ∈ op.micro) :
    isCopy m = false := by
  cases op with
  | bip srcs tgts coefs =>
    rcases List.mem_append.mp hm with h1 | h1
    · obtain ⟨pt, _, hpt⟩ := List.mem_flatMap.mp h1
      obtain ⟨z, e | e⟩ := mem_part_micro pt m hpt <;> rw [e] <;> rfl
    · obtain ⟨t, _, s, _, cf, e⟩ := mem_gatesM _ _ _ _ h1
      rw [e]; rfl
  | copy _ _ => exact absurd h (by simp [Op.plain])
  | copyNew _ _ => exact absurd h (by simp [Op.plain])
  | erase _ => exact absurd h (by simp [Op.plain])
  | expect r e =>
    have : m = .expect r e := by simpa [Op.micro] using hm
    rw [this]; rfl

theorem fin_noCopy (fe : FinE) (m : Micro) (hm : m ∈ fe.micro) : isCopy m = false := by
  rcases List.mem_append.mp hm with h | h
  · obtain ⟨z, _, rfl⟩ := List.mem_map.mp h; rfl
  · rw [List.mem_singleton] at h; rw [h]; rfl

/-! ## final entries -/

theorem covB_mem (fs : List FinE) (r n e : Nat) (h : covB fs r n e = true) (k : Nat) (hk : k < n) :
    ∃ fe ∈ fs, fe.r = r + k ∧ fe.e = e := by
  induction n generalizing fs r k with
  | zero => omega
  | succ n ih =>
    cases fs with
    | nil => exact absurd h (by simp [covB])
    | cons fe fs =>
      simp only [covB, Bool.and_eq_true, decide_eq_true_eq] at h
      cases k with
      | zero => exact ⟨fe, List.mem_cons_self .., h.1.1, h.1.2⟩
      | succ k =>
        obtain ⟨fe', hfe', a, b⟩ := ih fs (r+1) h.2 k (by omega)
        exact ⟨fe', List.mem_cons_of_mem _ hfe', by omega, b⟩

theorem refB_mem (fs : List FinE) (r : Nat) (zs : List Nat) (e : Nat) (h : refB fs r zs e = true)
    (k : Nat) (hk : k < zs.length) :
    ∃ fe ∈ fs, fe.r = r + k ∧ fe.dirs = [zs.getD k 0] ∧ fe.e = e := by
  induction zs generalizing fs r k with
  | nil => simp at hk
  | cons z zs ih =>
    cases fs with
    | nil => exact absurd h (by simp [refB])
    | cons fe fs =>
      simp only [refB, Bool.and_eq_true, decide_eq_true_eq] at h
      cases k with
      | zero => exact ⟨fe, List.mem_cons_self .., h.1.1.1, h.1.1.2, h.1.2⟩
      | succ k =>
        obtain ⟨fe', hfe', a, b, c⟩ := ih fs (r+1) h.2 k (by simpa using hk)
        exact ⟨fe', List.mem_cons_of_mem _ hfe', by omega, by simpa using b, c⟩

/-! ## the certificate -/

theorem refE_mem (r : Nat) (ps : List Nat) (k : Nat) (hk : k < ps.length) :
    (r + k, ps.getD k 0) ∈ refE r ps := by
  induction ps generalizing r k with
  | nil => simp at hk
  | cons P ps ih =>
    cases k with
    | zero => exact List.mem_cons_self ..
    | succ k =>
      have := ih (r+1) k (by simpa using hk)
      refine List.mem_cons_of_mem _ ?_
      have e : r + (k + 1) = r + 1 + k := by omega
      rw [e]; exact this

namespace PCert
variable (c : PCert)

def m4 : List Micro := c.F4.flatten.flatMap Op.micro
def m5 : List Micro := c.F5.flatten.flatMap Op.micro
def m7 : List Micro := c.F7.flatten.flatMap Op.micro
def mfin : List Micro := c.fins.flatten.flatMap FinE.micro
def a4 : List Micro := c.m4 ++ expM c.e4
def a5 : List Micro := c.a4 ++ c.m5
def a7 : List Micro := c.a5 ++ (expM c.e5 ++ c.m7)
def opsM : List Micro := c.a7 ++ expM c.e7
def tot : List Micro := c.opsM ++ c.mfin
def lab0 : Nat → Nat := fun r => dec (c.inits.getD r 0)
def H0 : Nat → List Nat := fun r => if r < c.v then [c.trips.getD r 0] else []

theorem opsM_eq : c.cs.flatten.flatMap Op.micro = c.opsM := by
  simp only [cs, List.flatten_append, List.flatMap_append, List.flatten_cons, List.flatten_nil,
    List.append_nil, expOps_micro, opsM, a7, a5, a4, m4, m5, m7, List.append_assoc]

theorem tot_eq : expand c.cs c.fins = c.tot := by
  unfold expand
  rw [opsM_eq]; rfl

/-- what the kernel has to check (unpacked) -/
structure Valid : Prop where
  hchk : check c.p c.inits c.cs c.fins c.N = true
  hh : 0 < c.p.h
  hw : c.p.h < c.p.w
  hc : c.p.cnt = 1
  hR : 0 < c.R
  htl : c.trips.length = c.v
  hsl : c.src.length = c.v
  hrl : c.ret.length = c.p.h
  hrl' : c.retLab.length = c.p.h
  hpl : c.pieces.length = c.v
  hql : c.perps.length = c.v
  hplain : c.cs.flatten.all Op.plain = true
  h5 : c.F5.flatten.all (Op.slotGate c.v c.R) = true
  hsrc : c.src.all (fun x => decide (x < c.R)) = true
  hret : c.ret.all (fun x => decide (x < c.R)) = true
  hpc : c.pieces.all (fun l => l.all fun x => decide (x.1 < c.R)) = true
  hcov : covB c.fins.flatten 0 (c.v + c.R) c.eF = true
  href : refB (c.fins.flatten.drop (c.v + c.R)) (c.v + c.R) c.trips c.eF = true
  hfB : fullB c.p (dec c.eF) = true

theorem fullB_spec (p : Par) (L : Nat) (h : fullB p L = true) :
    pmat p L = 1 ∧ cntOf p L = p.h := by
  simp only [fullB, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, h2⟩
  funext i j
  show (if L.testBit (p.K2 + p.w * i.val + j.val) then (1:F) else 0) = (1 : Matrix _ _ F) i j
  rw [h1 i.val i.isLt j.val j.isLt, Matrix.one_apply]
  by_cases e : i = j
  · subst e; simp
  · have e' : i.val ≠ j.val := fun h => e (Fin.ext h)
    simp [e, e']

theorem Valid.hF {c : PCert} (V : c.Valid) :
    pmat c.p (dec c.eF) = 1 ∧ cntOf c.p (dec c.eF) = c.p.h := fullB_spec _ _ V.hfB

/-- **the two kernel checks give validity** -/
theorem Valid.of_checks {c : PCert} (h1 : c.labelCheck = true) (h2 : c.shapeCheck = true) :
    c.Valid := by
  simp only [shapeCheck, Bool.and_eq_true, decide_eq_true_eq] at h2
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hh, hw⟩, hc⟩, hR⟩, htl⟩, hsl⟩, hrl⟩, hrl'⟩, hpl⟩, hql⟩, hplain⟩, h5⟩, hsrc⟩, hret⟩, hpc⟩, hcov⟩, href⟩, hfB⟩ := h2
  exact ⟨h1, hh, hw, hc, hR, htl, hsl, hrl, hrl', hpl, hql, hplain, h5, hsrc, hret, hpc, hcov, href, hfB⟩

variable {c}

/-! ### consequences of validity -/

theorem Valid.micro (V : c.Valid) :
    Ok c.p c.lab0 c.tot ∧ countM c.tot = c.N ∧
      ∀ fl ∈ c.fins, ∀ fe ∈ fl, fe.r < c.p.n ∧ runLab c.p c.lab0 c.tot fe.r = dec fe.e ∧
        dec fe.e = updS c.p (foldU c.p (runLab c.p c.lab0 c.opsM fe.r) fe.dirs) fe.sh := by
  obtain ⟨_, h1, h2, h3⟩ := check_micro c.p c.inits c.cs c.fins c.N V.hchk
  rw [tot_eq] at h1 h2 h3
  rw [opsM_eq] at h3
  exact ⟨h1, h2, h3⟩

theorem Valid.inits_len (V : c.Valid) : c.inits.length = c.v := by
  unfold inits; rw [List.length_map, V.htl]

theorem Valid.lab0_lt (V : c.Valid) (t : Nat) (ht : t < c.v) :
    c.lab0 t = upd c.p 0 (spread c.p (c.trips.getD t 0)) (c.trips.getD t 0) := by
  show dec (c.inits.getD t 0) = _
  unfold inits
  rw [getD_map_lt _ _ 0 0 t (by rw [V.htl]; exact ht), dec_enc]

theorem Valid.lab0_ge (V : c.Valid) (r : Nat) (hr : c.v ≤ r) : c.lab0 r = 0 := by
  show dec (c.inits.getD r 0) = 0
  rw [List.getD_eq_default _ _ (by rw [V.inits_len]; exact hr)]
  rfl

theorem Valid.hinv (V : c.Valid) : HInv c.p c.lab0 c.H0 := by
  intro r
  by_cases hr : r < c.v
  · rw [V.lab0_lt r hr, pmat_upd c.p V.hh V.hw, cnt_upd c.p V.hh V.hw, pmat_zero, cnt_zero, V.hc]
    show _ = psum c.p (if r < c.v then [c.trips.getD r 0] else []) ∧
      _ = (if r < c.v then [c.trips.getD r 0] else []).length
    rw [if_pos hr, psum_single, zero_add]
    exact ⟨rfl, rfl⟩
  · rw [V.lab0_ge r (by omega), pmat_zero, cnt_zero]
    show _ = psum c.p (if r < c.v then [c.trips.getD r 0] else []) ∧
      _ = (if r < c.v then [c.trips.getD r 0] else []).length
    rw [if_neg hr]
    exact ⟨rfl, rfl⟩

theorem Valid.noCopy (V : c.Valid) : ∀ m ∈ c.tot, isCopy m = false := by
  intro m hm
  have hp := List.all_eq_true.mp V.hplain
  rcases List.mem_append.mp hm with h | h
  · rw [← opsM_eq] at h
    obtain ⟨op, hop, hmop⟩ := List.mem_flatMap.mp h
    exact plain_noCopy op (hp op hop) m hmop
  · obtain ⟨fe, _, hmfe⟩ := List.mem_flatMap.mp h
    exact fin_noCopy fe m hmfe

theorem Valid.full (V : c.Valid) (r : Nat) (hr : r < c.v + c.R) :
    pmat c.p (runLab c.p c.lab0 c.tot r) = 1 ∧ cntOf c.p (runLab c.p c.lab0 c.tot r) = c.p.h := by
  obtain ⟨fe, hfe, h1, h2⟩ := covB_mem _ _ _ _ V.hcov r hr
  obtain ⟨fl, hfl, hfe'⟩ := List.mem_flatten.mp hfe
  obtain ⟨_, hrun, _⟩ := V.micro.2.2 fl hfl fe hfe'
  rw [Nat.zero_add] at h1
  rw [← h1, hrun, h2]
  exact V.hF

/-- the certificate is complete on any family of roles below `v + R` -/
theorem Valid.complete (V : c.Valid) {ρ : Type} (emb : ρ → Nat) (hemb : ∀ q, emb q < c.v + c.R) :
    Complete c.p c.lab0 c.H0 c.tot emb :=
  ⟨V.hh, V.hw, V.hc, V.hinv, V.micro.1, V.noCopy, fun q => V.full (emb q) (hemb q)⟩

/-- labels do not change at the `expect`s; the expected labels hold -/
theorem Valid.points (V : c.Valid) :
    (∀ x ∈ c.e4, runLab c.p c.lab0 c.a4 x.1 = dec x.2) ∧
    (∀ x ∈ c.e5, runLab c.p c.lab0 c.a5 x.1 = dec x.2) ∧
    (∀ x ∈ c.e7, runLab c.p c.lab0 c.a7 x.1 = dec x.2) ∧
    runLab c.p c.lab0 c.opsM = runLab c.p c.lab0 c.a7 := by
  have hok := V.micro.1
  have e : c.tot = c.m4 ++ (expM c.e4 ++ (c.m5 ++ (expM c.e5 ++ (c.m7 ++ (expM c.e7 ++ c.mfin))))) := by
    simp only [tot, opsM, a7, a5, a4, List.append_assoc]
  rw [e, Ok_append, Ok_append, Ok_append, Ok_append, Ok_append, Ok_append] at hok
  obtain ⟨_, h4, _, h5, _, h7, _⟩ := hok
  obtain ⟨p4, r4⟩ := expM_ok c.p _ _ h4
  rw [r4] at h5 h7
  obtain ⟨p5, r5⟩ := expM_ok c.p _ _ h5
  rw [r5] at h7
  obtain ⟨p7, r7⟩ := expM_ok c.p _ _ h7
  have e4' : runLab c.p c.lab0 c.a4 = runLab c.p c.lab0 c.m4 := by
    rw [a4, runLab_append, r4]
  have e5' : runLab c.p c.lab0 c.a5 = runLab c.p (runLab c.p c.lab0 c.m4) c.m5 := by
    rw [a5, runLab_append, e4']
  have e7' : runLab c.p c.lab0 c.a7
      = runLab c.p (runLab c.p (runLab c.p c.lab0 c.m4) c.m5) c.m7 := by
    rw [a7, runLab_append, runLab_append, e5', r5]
  refine ⟨fun x hx => by rw [e4']; exact p4 x hx, fun x hx => by rw [e5']; exact p5 x hx,
    fun x hx => by rw [e7']; exact p7 x hx, ?_⟩
  rw [opsM, runLab_append, e7', r7]

/-! ### the roles -/

variable (c)

/-- the input vectors (triple indicators) -/
def tv (t : Fin c.v) : Space (Fin c.p.h) := vecF c.p (c.trips.getD t.val 0)

def embS (q : Fin c.R) : Nat := c.v + q.val
def unembS (hR : 0 < c.R) (r : Nat) : Fin c.R := ⟨(r - c.v) % c.R, Nat.mod_lt _ hR⟩

theorem unembS_embS (hR : 0 < c.R) (q : Fin c.R) : c.unembS hR (c.embS q) = q := by
  apply Fin.ext
  show (c.v + q.val - c.v) % c.R = q.val
  rw [Nat.add_sub_cancel_left, Nat.mod_eq_of_lt q.isLt]

theorem embS_unembS (hR : 0 < c.R) (r : Nat) (h1 : c.v ≤ r) (h2 : r < c.v + c.R) :
    c.embS (c.unembS hR r) = r := by
  show c.v + (r - c.v) % c.R = r
  rw [Nat.mod_eq_of_lt (by omega)]; omega

def srcq (hR : 0 < c.R) (t : Fin c.v) : Fin c.R := ⟨c.src.getD t.val 0 % c.R, Nat.mod_lt _ hR⟩
def retq (hR : 0 < c.R) (k : Fin c.p.h) : Fin c.R := ⟨c.ret.getD k.val 0 % c.R, Nat.mod_lt _ hR⟩

/-! ### the matrices -/

noncomputable def Lm (hR : 0 < c.R) : Matrix (Fin c.R) (Fin c.R) ℚ := matP (c.unembS hR) c.m5
noncomputable def Linvm (hR : 0 < c.R) : Matrix (Fin c.R) (Fin c.R) ℚ := matPinv (c.unembS hR) c.m5
def Vm (hR : 0 < c.R) : Matrix (Fin c.R) (Fin c.v) ℚ := fun q t => if q = c.srcq hR t then 1 else 0
def Ccm (hR : 0 < c.R) : Matrix (Fin c.p.h) (Fin c.R) ℚ := fun k q => if q = c.retq hR k then 1 else 0
noncomputable def Jpm : Matrix (Fin c.v) (Fin c.R) ℚ := fun t q => rowOf (c.pieces.getD t.val []) q
noncomputable def Jrm : Matrix (Fin c.v) (Fin c.p.h) ℚ := fun t k => rowOf (c.scat.getD t.val []) k

/-! ### the labels -/

def phi4 (q : Fin c.R) : Lbl (Fin c.p.h) := Lb c.p (runLab c.p c.lab0 c.a4 (c.embS q))
def phi5 (q : Fin c.R) : Lbl (Fin c.p.h) := Lb c.p (runLab c.p c.lab0 c.a5 (c.embS q))
def phi7 (q : Fin c.R) : Lbl (Fin c.p.h) := Lb c.p (runLab c.p c.lab0 c.a7 (c.embS q))

variable {c}

theorem Valid.line (V : c.Valid) (t : Fin c.v) : Lb c.p (c.lab0 t.val) = lineL (c.tv t) := by
  obtain ⟨h1, h2⟩ := V.hinv t.val
  show (⟨pmat c.p (c.lab0 t.val), cntOf c.p (c.lab0 t.val)⟩ : Lbl (Fin c.p.h)) = ⟨tt (c.tv t), 1⟩
  rw [h1, h2]
  show (⟨psum c.p (if t.val < c.v then [c.trips.getD t.val 0] else []),
    (if t.val < c.v then [c.trips.getD t.val 0] else []).length⟩ : Lbl (Fin c.p.h)) = _
  rw [if_pos t.isLt, psum_single]
  rfl

theorem Valid.fullLb (V : c.Valid) (r : Nat) (hr : r < c.v + c.R) :
    Lb c.p (runLab c.p c.lab0 c.tot r) = fullL := by
  obtain ⟨h1, h2⟩ := V.full r hr
  show (⟨pmat c.p _, cntOf c.p _⟩ : Lbl (Fin c.p.h)) = ⟨1, Fintype.card (Fin c.p.h)⟩
  rw [h1, h2, Fintype.card_fin]

theorem tt_cancel {H : Type} (z : Space H) : tt z + tt z = 0 := by
  funext i j
  show z i * z j + z i * z j = 0
  exact cancel _

theorem Valid.perp (V : c.Valid) (S : Fin c.v) :
    Lb c.p (dec (c.perps.getD S.val 0)) = perpL (c.tv S) := by
  obtain ⟨fe, hfe, h1, h2, h3⟩ := refB_mem _ _ _ _ V.href S.val (by rw [V.htl]; exact S.isLt)
  have hfe2 : fe ∈ c.fins.flatten := List.mem_of_mem_drop hfe
  obtain ⟨fl, hfl, hfe'⟩ := List.mem_flatten.mp hfe2
  obtain ⟨_, _, hrel⟩ := V.micro.2.2 fl hfl fe hfe'
  obtain ⟨_, _, p7, hops⟩ := V.points
  have hmem : (c.v + c.R + S.val, c.perps.getD S.val 0) ∈ c.e7 :=
    List.mem_append_right _ (refE_mem _ _ _ (by rw [V.hql]; exact S.isLt))
  have hl := p7 _ hmem
  rw [hops, h1, hl, h2, h3] at hrel
  have hrel' : dec c.eF = updS c.p (upd c.p (dec (c.perps.getD S.val 0))
      (spread c.p (c.trips.getD S.val 0)) (c.trips.getD S.val 0)) fe.sh := hrel
  have hP := congrArg (pmat c.p) hrel'
  have hC := congrArg (cntOf c.p) hrel'
  rw [pmat_updS c.p V.hh V.hw, pmat_upd c.p V.hh V.hw, V.hF.1] at hP
  rw [cnt_updS c.p V.hh V.hw, cnt_upd c.p V.hh V.hw, V.hF.2, V.hc] at hC
  have hP' : pmat c.p (dec (c.perps.getD S.val 0)) = 1 + tt (c.tv S) := by
    have h := tt_cancel (c.tv S)
    calc pmat c.p (dec (c.perps.getD S.val 0))
        = pmat c.p (dec (c.perps.getD S.val 0)) + (tt (c.tv S) + tt (c.tv S)) := by rw [h, add_zero]
      _ = 1 + tt (c.tv S) := by rw [← add_assoc]; exact congrArg (· + tt (c.tv S)) hP.symm
  show (⟨pmat c.p _, cntOf c.p _⟩ : Lbl (Fin c.p.h)) = ⟨1 + tt (c.tv S), Fintype.card (Fin c.p.h) - 1⟩
  rw [hP', Fintype.card_fin]
  congr 1
  omega

theorem Valid.all_src (V : c.Valid) (t : Fin c.v) : c.src.getD t.val 0 < c.R := by
  have h := List.all_eq_true.mp V.hsrc _ (getD_mem_lt c.src 0 t.val (by rw [V.hsl]; exact t.isLt))
  simpa using h

theorem Valid.all_ret (V : c.Valid) (k : Fin c.p.h) : c.ret.getD k.val 0 < c.R := by
  have h := List.all_eq_true.mp V.hret _ (getD_mem_lt c.ret 0 k.val (by rw [V.hrl]; exact k.isLt))
  simpa using h

/-- the loading label of a source slot is the line of its triple -/
theorem Valid.phi4_src (V : c.Valid) (t : Fin c.v) : c.phi4 (c.srcq V.hR t) = lineL (c.tv t) := by
  obtain ⟨p4, _, _, _⟩ := V.points
  have hmem : (c.v + c.src.getD t.val 0, c.inits.getD t.val 0) ∈ c.e4 := by
    refine List.mem_map.mpr ⟨(c.src.getD t.val 0, c.inits.getD t.val 0), ?_, rfl⟩
    exact zip_getD_mem _ _ _ _ _ (by rw [V.hsl]; exact t.isLt) (by rw [V.inits_len]; exact t.isLt)
  have h := p4 _ hmem
  have e : c.embS (c.srcq V.hR t) = c.v + c.src.getD t.val 0 := by
    show c.v + c.src.getD t.val 0 % c.R = _
    rw [Nat.mod_eq_of_lt (V.all_src t)]
  show Lb c.p (runLab c.p c.lab0 c.a4 (c.embS (c.srcq V.hR t))) = _
  rw [e, h]
  exact V.line t

/-- the label of a piece slot when it is read is `t_S^⊥` -/
theorem Valid.phi7_piece (V : c.Valid) (S : Fin c.v) (q : Fin c.R)
    (h : c.Jpm S q ≠ 0) : c.phi7 q = perpL (c.tv S) := by
  obtain ⟨x, hx, hxq⟩ := rowOf_ne_zero _ _ h
  obtain ⟨_, _, p7, _⟩ := V.points
  have hz : (c.pieces.getD S.val [], c.perps.getD S.val 0) ∈ c.pieces.zip c.perps :=
    zip_getD_mem _ _ _ _ _ (by rw [V.hpl]; exact S.isLt) (by rw [V.hql]; exact S.isLt)
  have hmem : (c.v + x.1, c.perps.getD S.val 0) ∈ c.e7 :=
    List.mem_append_left _ (List.mem_flatMap.mpr ⟨_, hz, List.mem_map.mpr ⟨x, hx, rfl⟩⟩)
  have hl := p7 _ hmem
  show Lb c.p (runLab c.p c.lab0 c.a7 (c.v + q.val)) = _
  rw [← hxq, hl]
  exact V.perp S

/-! ### the gates of the circuit phase -/

theorem Valid.seg5 (V : c.Valid) :
    (∀ m ∈ c.m5, segOK c.embS (c.unembS V.hR) m) ∧ gatesDistinct (c.unembS V.hR) c.m5 := by
  have h5 := List.all_eq_true.mp V.h5
  have key : ∀ m ∈ c.m5, (∃ r z, (m = .dir r z ∨ m = .shift r z) ∧ c.v ≤ r ∧ r < c.v + c.R) ∨
      (∃ t s cf, m = .add t s cf ∧ c.v ≤ t ∧ t < c.v + c.R ∧ c.v ≤ s ∧ s < c.v + c.R ∧ s ≠ t) := by
    intro m hm
    obtain ⟨op, hop, hmop⟩ := List.mem_flatMap.mp hm
    have hg := h5 op hop
    cases op with
    | bip srcs tgts coefs =>
      simp only [Op.slotGate, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hg
      obtain ⟨hr, hd⟩ := hg
      rcases List.mem_append.mp hmop with h1 | h1
      · obtain ⟨pt, hpt, hm'⟩ := List.mem_flatMap.mp h1
        obtain ⟨z, e⟩ := mem_part_micro pt m hm'
        exact Or.inl ⟨pt.role, z, e, hr pt hpt⟩
      · obtain ⟨t, ht, s, hs, cf, e⟩ := mem_gatesM _ _ _ _ h1
        exact Or.inr ⟨t.role, s.role, cf, e, (hr t (List.mem_append_right _ ht)).1,
          (hr t (List.mem_append_right _ ht)).2, (hr s (List.mem_append_left _ hs)).1,
          (hr s (List.mem_append_left _ hs)).2, hd s hs t ht⟩
    | copy _ _ => exact absurd hg (by simp [Op.slotGate])
    | copyNew _ _ => exact absurd hg (by simp [Op.slotGate])
    | erase _ => exact absurd hg (by simp [Op.slotGate])
    | expect _ _ => exact absurd hg (by simp [Op.slotGate])
  constructor
  · intro m hm
    rcases key m hm with ⟨r, z, e | e, h1, h2⟩ | ⟨t, s, cf, e, h1, h2, h3, h4, _⟩
    · rw [e]; exact c.embS_unembS V.hR r h1 h2
    · rw [e]; exact trivial
    · rw [e]; exact ⟨c.embS_unembS V.hR t h1 h2, c.embS_unembS V.hR s h3 h4⟩
  · have gen : ∀ ms : List Micro, (∀ m ∈ ms, m ∈ c.m5) → gatesDistinct (c.unembS V.hR) ms := by
      intro ms
      induction ms with
      | nil => intro _; exact trivial
      | cons m ms ih =>
        intro hsub
        have ih' := ih (fun m' h' => hsub m' (List.mem_cons_of_mem _ h'))
        have hm := hsub m (List.mem_cons_self ..)
        cases m with
        | add t s cf =>
          refine ⟨?_, ih'⟩
          rcases key _ hm with ⟨r, z, e | e, _⟩ | ⟨t', s', cf', e, h1, h2, h3, h4, hne⟩
          · exact absurd e (by simp)
          · exact absurd e (by simp)
          · injection e with e1 e2 e3
            subst e1; subst e2
            intro heq
            apply hne
            have a := c.embS_unembS V.hR t h1 h2
            have b := c.embS_unembS V.hR s h3 h4
            rw [← b, ← a, heq]
        | dir _ _ => exact ih'
        | shift _ _ => exact ih'
        | copy _ _ => exact ih'
        | erase _ => exact ih'
        | expect _ _ => exact ih'
    exact gen c.m5 (fun m h => h)

/-! ### the circuit -/

variable (c)

/-- the scalar identity `J L V = 1` of the certificate (checked in `Scalar.lean`) -/
def ScalarId (hR : 0 < c.R) : Prop :=
  (c.Jrm * c.Ccm hR + c.Jpm) * c.Lm hR * c.Vm hR = 1

variable {c}

/-- **The circuit certificate of the structured development, from a checked certificate.** -/
noncomputable def Valid.circuit (V : c.Valid) (hid : c.ScalarId V.hR) :
    Circuit (Fin c.p.h) (Fin c.v) (Fin c.R) (Fin c.p.h) where
  tv := c.tv
  L := c.Lm V.hR
  Linv := c.Linvm V.hR
  V := c.Vm V.hR
  Jp := c.Jpm
  Jr := c.Jrm
  Cc := c.Ccm V.hR
  φ4 := c.phi4
  φ5 := c.phi5
  φ7 := c.phi7
  cen := fun k => c.phi5 (c.retq V.hR k)
  hLL := matP_inv _ _ V.seg5.2
  hLL' := mul_eq_one_comm.mp (matP_inv _ _ V.seg5.2)
  hid := hid
  cx := fun t => by
    have C := V.complete (fun t : Fin c.v => t.val) (fun t => by have := t.isLt; omega)
    have h := C.climb t [] c.tot [] (by simp)
    rw [List.nil_append] at h
    have e : runLab c.p c.lab0 [] t.val = c.lab0 t.val := rfl
    rw [e, V.line t, V.fullLb t.val (by have := t.isLt; omega)] at h
    exact h.climbs
  cy := fun t => by
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
    exact h.climbs
  c04 := fun q => by
    have C := V.complete c.embS (fun q => by have := q.isLt; show c.v + q.val < _; omega)
    have h := C.climb q [] c.a4 (c.m5 ++ (expM c.e5 ++ c.m7) ++ expM c.e7 ++ c.mfin)
      (by simp only [tot, opsM, a7, a5, List.nil_append, List.append_assoc])
    rw [List.nil_append] at h
    have e : runLab c.p c.lab0 [] (c.embS q) = 0 := V.lab0_ge _ (Nat.le_add_right _ _)
    rw [e, Lb_zero] at h
    exact h.climbs
  c57 := fun q => by
    have C := V.complete c.embS (fun q => by have := q.isLt; show c.v + q.val < _; omega)
    exact (C.climb q c.a5 (expM c.e5 ++ c.m7) (expM c.e7 ++ c.mfin)
      (by simp only [tot, opsM, a7, List.append_assoc])).climbs
  c7F := fun q => by
    have C := V.complete c.embS (fun q => by have := q.isLt; show c.v + q.val < _; omega)
    have h := C.climb q c.a7 (expM c.e7 ++ c.mfin) []
      (by simp only [tot, opsM, List.append_nil, List.append_assoc])
    have e : c.a7 ++ (expM c.e7 ++ c.mfin) = c.tot := by
      simp only [tot, opsM, List.append_assoc]
    rw [e, V.fullLb _ (by have := q.isLt; show c.v + q.val < _; omega)] at h
    exact h.climbs
  cc := fun k => by
    have C := V.complete c.embS (fun q => by have := q.isLt; show c.v + q.val < _; omega)
    have h := C.climb (c.retq V.hR k) [] c.a5 ((expM c.e5 ++ c.m7) ++ expM c.e7 ++ c.mfin)
      (by simp only [tot, opsM, a7, List.nil_append, List.append_assoc])
    rw [List.nil_append] at h
    have e : runLab c.p c.lab0 [] (c.embS (c.retq V.hR k)) = 0 :=
      V.lab0_ge _ (Nat.le_add_right _ _)
    rw [e, Lb_zero] at h
    exact h.climbs
  sV := fun q t h => by
    have hq : q = c.srcq V.hR t := by
      by_contra hne
      exact h (by simp [Vm, hne])
    rw [hq]
    exact V.phi4_src t
  sC := fun k q h => by
    have hq : q = c.retq V.hR k := by
      by_contra hne
      exact h (by simp [Ccm, hne])
    rw [hq]
  sJ := fun t q h => V.phi7_piece t q h
  circ := fun Fm => by
    have C := V.complete c.embS (fun q => by have := q.isLt; show c.v + q.val < _; omega)
    have htot : c.tot = c.a4 ++ c.m5 ++ ((expM c.e5 ++ c.m7) ++ expM c.e7 ++ c.mfin) := by
      simp only [tot, opsM, a7, a5, List.append_assoc]
    constructor
    · exact C.path (c.unembS V.hR) (c.unembS_embS V.hR) Fm c.m5 c.a4 _ htot V.seg5.1
    · have C' : Complete c.p c.lab0 c.H0
          (c.a4 ++ c.m5 ++ ((expM c.e5 ++ c.m7) ++ expM c.e7 ++ c.mfin)) c.embS := htot ▸ C
      have h := (C'.swap).path (c.unembS V.hR) (c.unembS_embS V.hR) Fm (c.m5.map swapNeg) c.a4 _ rfl
        (fun m hm => by
          obtain ⟨m', hm', rfl⟩ := List.mem_map.mp hm
          exact segOK_swap _ _ _ (V.seg5.1 m' hm'))
      rw [matP_swap] at h
      have e : (fun q => Fm.lab (Lb c.p (runLab c.p c.lab0 (c.a4 ++ c.m5.map swapNeg) (c.embS q))))
          = fun q => Fm.lab (c.phi5 q) := by
        funext q
        show Fm.lab (Lb c.p (runLab c.p c.lab0 (c.a4 ++ c.m5.map swapNeg) (c.embS q)))
          = Fm.lab (Lb c.p (runLab c.p c.lab0 (c.a4 ++ c.m5) (c.embS q)))
        rw [runLab_append, runLab_swap, ← runLab_append]
      rw [e] at h
      exact h

end PCert

end SSC
