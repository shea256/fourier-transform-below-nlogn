import Work.CarrierCheck.CCert
import Work.Combine.Chunks

/-!
# (key: carrier-check) What the label check and the shape check of a carrier certificate give

`CCert.Valid c` collects the kernel checks (`Valid.of_checks`).  From it, at the level of the
micro-program `tot = mA ++ mE ++ mB ++ mF ++ mY` (phase A, the expects at the scatter, phase B,
the real final entries, the fictitious completions of the y roles):

* `Valid.complete`   every role below `n = v + R + v` makes exactly `h` moves and ends with
                     projector `1` (`SSC.Complete`), hence a `Climb` between any two of its labels;
* `Valid.line`, `Valid.cut_ret`, `Valid.cut_y`, `Valid.yB`, `Valid.fullLb`   the labels at the
                     start, at the scatter, after phase B and at the end;
* `carrier_micro`    every gate `t += c * s` of a carrier op has `t, s < n`, `s` not a y role,
                     `t` not an x role, `s ≠ t`.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace SSC
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM OAI.PowerSaving.SS
  OAI.PowerSaving.CB Finset Matrix

/-! ## list helpers -/

theorem getD_replicate_zero (k m : Nat) : (List.replicate k 0).getD m 0 = 0 := by
  induction k generalizing m with
  | zero => cases m <;> rfl
  | succ k ih =>
    cases m with
    | zero => rfl
    | succ m => exact ih m

theorem getD_app_left {α : Type} (l l' : List α) (d : α) (n : Nat) (h : n < l.length) :
    (l ++ l').getD n d = l.getD n d := by
  induction l generalizing n with
  | nil => simp at h
  | cons a l ih =>
    cases n with
    | zero => rfl
    | succ n => exact ih n (by simpa using h)

theorem getD_app_rep (l : List Nat) (k n : Nat) (h : l.length ≤ n) :
    (l ++ List.replicate k 0).getD n 0 = 0 := by
  induction l generalizing n with
  | nil => exact getD_replicate_zero k n
  | cons a l ih =>
    cases n with
    | zero => simp at h
    | succ n => exact ih n (by simpa using h)

/-! ## the fictitious completions -/

theorem yfinsFrom_mem (e : Nat) (zs : List Nat) : ∀ (r : Nat) (ss : List Nat) (k : Nat),
    k < zs.length → ∃ sh, (⟨r + k, [zs.getD k 0], sh, e⟩ : FinE) ∈ yfinsFrom e r zs ss := by
  induction zs with
  | nil => intro r ss k hk; simp at hk
  | cons z zs ih =>
    intro r ss k hk
    cases ss with
    | nil =>
      cases k with
      | zero =>
        exact ⟨0, (List.mem_cons_self .. : (⟨r, [z], 0, e⟩ : FinE) ∈
          (⟨r, [z], 0, e⟩ : FinE) :: yfinsFrom e (r+1) zs [])⟩
      | succ k =>
        obtain ⟨sh, h⟩ := ih (r+1) [] k (by simpa using hk)
        have e1 : r + (k + 1) = r + 1 + k := by omega
        rw [e1]
        exact ⟨sh, (List.mem_cons_of_mem _ h : (⟨r + 1 + k, [zs.getD k 0], sh, e⟩ : FinE) ∈
          (⟨r, [z], 0, e⟩ : FinE) :: yfinsFrom e (r+1) zs [])⟩
    | cons s ss =>
      cases k with
      | zero =>
        exact ⟨s, (List.mem_cons_self .. : (⟨r, [z], s, e⟩ : FinE) ∈
          (⟨r, [z], s, e⟩ : FinE) :: yfinsFrom e (r+1) zs ss)⟩
      | succ k =>
        obtain ⟨sh, h⟩ := ih (r+1) ss k (by simpa using hk)
        have e1 : r + (k + 1) = r + 1 + k := by omega
        rw [e1]
        exact ⟨sh, (List.mem_cons_of_mem _ h : (⟨r + 1 + k, [zs.getD k 0], sh, e⟩ : FinE) ∈
          (⟨r, [z], s, e⟩ : FinE) :: yfinsFrom e (r+1) zs ss)⟩

theorem yfinsFrom_ge (e : Nat) (zs : List Nat) : ∀ (r : Nat) (ss : List Nat),
    ∀ fe ∈ yfinsFrom e r zs ss, r ≤ fe.r := by
  induction zs with
  | nil => intro r ss fe h; simp [yfinsFrom] at h
  | cons z zs ih =>
    intro r ss fe h
    cases ss with
    | nil =>
      have h' : fe ∈ (⟨r, [z], 0, e⟩ : FinE) :: yfinsFrom e (r+1) zs [] := h
      rcases List.mem_cons.mp h' with h1 | h1
      · subst h1; exact Nat.le_refl _
      · have := ih (r+1) [] fe h1; omega
    | cons s ss =>
      have h' : fe ∈ (⟨r, [z], s, e⟩ : FinE) :: yfinsFrom e (r+1) zs ss := h
      rcases List.mem_cons.mp h' with h1 | h1
      · subst h1; exact Nat.le_refl _
      · have := ih (r+1) ss fe h1; omega

/-! ## carrier ops -/

theorem carrier_plain (v R : Nat) (op : Op) (h : op.carrier v R = true) : op.plain = true := by
  cases op with
  | bip _ _ _ => rfl
  | copy _ _ => exact absurd h (by simp [Op.carrier])
  | copyNew _ _ => exact absurd h (by simp [Op.carrier])
  | erase _ => exact absurd h (by simp [Op.carrier])
  | expect _ _ => exact absurd h (by simp [Op.carrier])

/-- the micro-ops of a carrier op: moves of roles below `n`, and gates `t += c * s` with
`t, s < n`, `s` not a y role, `t` not an x role, `s ≠ t` -/
theorem carrier_micro (v R : Nat) (op : Op) (h : op.carrier v R = true) (m : Micro)
    (hm : m ∈ op.micro) :
    (∃ r z, (m = .dir r z ∨ m = .shift r z) ∧ r < v + R + v) ∨
    (∃ t s cf, m = .add t s cf ∧ t < v + R + v ∧ s < v + R ∧ v ≤ t ∧ s ≠ t) := by
  cases op with
  | bip srcs tgts coefs =>
    simp only [Op.carrier, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    obtain ⟨hr, hp⟩ := h
    rcases List.mem_append.mp hm with h1 | h1
    · obtain ⟨pt, hpt, hm'⟩ := List.mem_flatMap.mp h1
      obtain ⟨z, e⟩ := mem_part_micro pt m hm'
      exact Or.inl ⟨pt.role, z, e, hr pt hpt⟩
    · obtain ⟨t, ht, s, hs, cf, e⟩ := mem_gatesM _ _ _ _ h1
      obtain ⟨a, b, d⟩ := hp s hs t ht
      exact Or.inr ⟨t.role, s.role, cf, e, hr t (List.mem_append_right _ ht), a, b, d⟩
  | copy _ _ => exact absurd h (by simp [Op.carrier])
  | copyNew _ _ => exact absurd h (by simp [Op.carrier])
  | erase _ => exact absurd h (by simp [Op.carrier])
  | expect _ _ => exact absurd h (by simp [Op.carrier])

/-- final entries of other roles are quiet for the role `r` -/
theorem fins_quiet (fs : List FinE) (r : Nat) (h : ∀ fe ∈ fs, fe.r ≠ r) :
    ∀ m ∈ fs.flatMap FinE.micro, quiet (fun _ : Unit => r) m := by
  intro m hm
  obtain ⟨fe, hfe, hmf⟩ := List.mem_flatMap.mp hm
  rcases List.mem_append.mp hmf with h1 | h1
  · obtain ⟨z, _, rfl⟩ := List.mem_map.mp h1
    intro _ e
    exact h fe hfe e.symm
  · rw [List.mem_singleton] at h1
    rw [h1]; exact trivial

namespace CCert
variable (c : CCert)

def mA : List Micro := c.A.flatten.flatMap Op.micro
def mB : List Micro := c.B.flatten.flatMap Op.micro
def mE : List Micro := expM c.eA
def mF : List Micro := c.fins.flatten.flatMap FinE.micro
def mY : List Micro := c.yfins.flatMap FinE.micro
/-- the micro-program up to the end of phase B -/
def aB : List Micro := c.mA ++ c.mE ++ c.mB
def tot : List Micro := c.aB ++ c.mF ++ c.mY
def lab0 : Nat → Nat := fun r => dec (c.inits.getD r 0)
def H0 : Nat → List Nat := fun r => if r < c.v then [c.trips.getD r 0] else []

theorem opsM_eq : c.cs.flatten.flatMap Op.micro = c.aB := by
  simp only [cs, List.flatten_append, List.flatMap_append, List.flatten_cons, List.flatten_nil,
    List.append_nil, expOps_micro, aB, mA, mB, mE, List.append_assoc]

theorem tot_eq : expand c.cs (c.fins ++ [c.yfins]) = c.tot := by
  unfold expand
  rw [opsM_eq]
  simp only [tot, mF, mY, List.flatten_append, List.flatMap_append, List.flatten_cons,
    List.flatten_nil, List.append_nil, List.append_assoc]

/-- what the kernel has to check (unpacked) -/
structure Valid : Prop where
  hchk : check c.p c.inits c.cs (c.fins ++ [c.yfins]) c.N = true
  hh : 0 < c.p.h
  hw : c.p.h < c.p.w
  hc : c.p.cnt = 1
  hv : 0 < c.v
  hR : 0 < c.R
  htl : c.trips.length = c.v
  hyl : c.ysh.length = c.v
  hrl : c.retLab.length = c.ret.length
  hsl : c.scat.length = c.v
  hA : c.A.flatten.all (Op.carrier c.v c.R) = true
  hB : c.B.flatten.all (Op.carrier c.v c.R) = true
  hret : c.ret.all (fun x => decide (x < c.R)) = true
  hsc : c.scat.all (fun l => l.all fun x => decide (x.1 < c.ret.length)) = true
  hcov : covB c.fins.flatten 0 (c.v + c.R) c.eF = true
  hfr : c.fins.flatten.all (fun fe => decide (fe.r < c.v + c.R)) = true
  hfB : fullB c.p (dec c.eF) = true

/-- **the two kernel checks give validity** -/
theorem Valid.of_checks {c : CCert} (h1 : c.labelCheck = true) (h2 : c.shapeCheck = true) :
    c.Valid := by
  simp only [shapeCheck, Bool.and_eq_true, decide_eq_true_eq] at h2
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hh, hw⟩, hc⟩, hv⟩, hR⟩, htl⟩, hyl⟩, hrl⟩, hsl⟩, hA⟩, hB⟩, hret⟩, hsc⟩, hcov⟩, hfr⟩, hfB⟩ := h2
  exact ⟨h1, hh, hw, hc, hv, hR, htl, hyl, hrl, hsl, hA, hB, hret, hsc, hcov, hfr, hfB⟩

variable {c}

theorem Valid.hF (V : c.Valid) :
    pmat c.p (dec c.eF) = 1 ∧ cntOf c.p (dec c.eF) = c.p.h := PCert.fullB_spec _ _ V.hfB

theorem Valid.hn (V : c.Valid) : 0 < c.n := by
  have := V.hv
  unfold n; omega

theorem Valid.micro (V : c.Valid) :
    Ok c.p c.lab0 c.tot ∧ countM c.tot = c.N ∧
      ∀ fl ∈ c.fins ++ [c.yfins], ∀ fe ∈ fl, fe.r < c.p.n ∧
        runLab c.p c.lab0 c.tot fe.r = dec fe.e ∧
        dec fe.e = updS c.p (foldU c.p (runLab c.p c.lab0 c.aB fe.r) fe.dirs) fe.sh := by
  obtain ⟨_, h1, h2, h3⟩ := check_micro c.p c.inits c.cs (c.fins ++ [c.yfins]) c.N V.hchk
  rw [tot_eq] at h1 h2 h3
  rw [opsM_eq] at h3
  exact ⟨h1, h2, h3⟩

theorem Valid.lab0_lt (V : c.Valid) (t : Nat) (ht : t < c.v) :
    c.lab0 t = upd c.p 0 (spread c.p (c.trips.getD t 0)) (c.trips.getD t 0) := by
  show dec (c.inits.getD t 0) = _
  unfold inits
  rw [getD_app_left _ _ _ _ (by rw [List.length_map, V.htl]; exact ht),
    getD_map_lt _ _ 0 0 t (by rw [V.htl]; exact ht), dec_enc]

theorem Valid.lab0_ge (V : c.Valid) (r : Nat) (hr : c.v ≤ r) : c.lab0 r = 0 := by
  show dec (c.inits.getD r 0) = 0
  unfold inits
  rw [getD_app_rep _ _ _ (by rw [List.length_map, V.htl]; exact hr)]
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
  have key : ∀ ops : List Op, (∀ op ∈ ops, op.carrier c.v c.R = true) →
      ∀ m ∈ ops.flatMap Op.micro, isCopy m = false := fun ops h m hm => by
    obtain ⟨op, hop, hmop⟩ := List.mem_flatMap.mp hm
    exact plain_noCopy op (carrier_plain _ _ op (h op hop)) m hmop
  have keyF : ∀ fs : List FinE, ∀ m ∈ fs.flatMap FinE.micro, isCopy m = false := fun fs m hm => by
    obtain ⟨fe, _, h⟩ := List.mem_flatMap.mp hm
    exact fin_noCopy fe m h
  have hm' : m ∈ (((c.mA ++ c.mE) ++ c.mB) ++ c.mF) ++ c.mY := hm
  rcases List.mem_append.mp hm' with h | h
  · rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · rcases List.mem_append.mp h with h | h
        · exact key _ (List.all_eq_true.mp V.hA) m h
        · obtain ⟨x, _, rfl⟩ := List.mem_map.mp h
          rfl
      · exact key _ (List.all_eq_true.mp V.hB) m h
    · exact keyF _ m h
  · exact keyF _ m h

/-- every role below `n` ends with projector `1` after exactly `h` moves -/
theorem Valid.full (V : c.Valid) (r : Nat) (hr : r < c.n) :
    pmat c.p (runLab c.p c.lab0 c.tot r) = 1 ∧ cntOf c.p (runLab c.p c.lab0 c.tot r) = c.p.h := by
  by_cases h1 : r < c.v + c.R
  · obtain ⟨fe, hfe, e1, e2⟩ := covB_mem _ _ _ _ V.hcov r h1
    obtain ⟨fl, hfl, hfe'⟩ := List.mem_flatten.mp hfe
    obtain ⟨_, hrun, _⟩ := V.micro.2.2 fl (List.mem_append_left _ hfl) fe hfe'
    rw [Nat.zero_add] at e1
    rw [← e1, hrun, e2]
    exact V.hF
  · have hk : r - (c.v + c.R) < c.trips.length := by
      rw [V.htl]; unfold n at hr; omega
    obtain ⟨sh, hmem⟩ := yfinsFrom_mem c.eF c.trips (c.v + c.R) c.ysh _ hk
    obtain ⟨_, hrun, _⟩ := V.micro.2.2 c.yfins
      (List.mem_append_right _ (List.mem_singleton.mpr rfl)) _ hmem
    have hrun' : runLab c.p c.lab0 c.tot (c.v + c.R + (r - (c.v + c.R))) = dec c.eF := hrun
    have e : c.v + c.R + (r - (c.v + c.R)) = r := by omega
    rw [e] at hrun'
    rw [hrun']
    exact V.hF

/-- the certificate is complete on any family of roles below `n` -/
theorem Valid.complete (V : c.Valid) {ρ : Type} (emb : ρ → Nat) (hemb : ∀ q, emb q < c.n) :
    Complete c.p c.lab0 c.H0 c.tot emb :=
  ⟨V.hh, V.hw, V.hc, V.hinv, V.micro.1, V.noCopy, fun q => V.full (emb q) (hemb q)⟩

/-- at the scatter the expected labels hold, and the expects change nothing -/
theorem Valid.cut (V : c.Valid) :
    (∀ x ∈ c.eA, runLab c.p c.lab0 c.mA x.1 = dec x.2) ∧
    runLab c.p c.lab0 (c.mA ++ c.mE) = runLab c.p c.lab0 c.mA := by
  have hok := V.micro.1
  have e : c.tot = c.mA ++ (c.mE ++ (c.mB ++ (c.mF ++ c.mY))) := by
    simp only [tot, aB, List.append_assoc]
  rw [e, Ok_append, Ok_append] at hok
  obtain ⟨_, hE, _⟩ := hok
  obtain ⟨pE, rE⟩ := expM_ok c.p _ _ hE
  exact ⟨pE, by rw [runLab_append]; exact rE⟩

theorem Valid.cut_ret (V : c.Valid) (k : Nat) (hk : k < c.ret.length) :
    runLab c.p c.lab0 c.mA (c.v + c.ret.getD k 0) = dec (c.retLab.getD k 0) := by
  have hmem : (c.v + c.ret.getD k 0, c.retLab.getD k 0) ∈ c.eA := by
    refine List.mem_append_left _ (List.mem_map.mpr ⟨(c.ret.getD k 0, c.retLab.getD k 0), ?_, rfl⟩)
    exact zip_getD_mem _ _ _ _ _ hk (by rw [V.hrl]; exact hk)
  exact V.cut.1 _ hmem

theorem Valid.cut_y (V : c.Valid) (S : Nat) (hS : S < c.v) :
    runLab c.p c.lab0 c.mA (c.v + c.R + S) = 0 := by
  have hmem : (c.v + c.R + S, 0) ∈ c.eA :=
    List.mem_append_right _ (List.mem_map.mpr ⟨S, List.mem_range.mpr hS, rfl⟩)
  have h := V.cut.1 _ hmem
  have h2 : runLab c.p c.lab0 c.mA (c.v + c.R + S) = dec 0 := h
  exact h2.trans dec_zero

/-! ### the roles and their labels -/

variable (c)

/-- the input vectors (triple indicators) -/
def tv (t : Fin c.v) : Space (Fin c.p.h) := vecF c.p (c.trips.getD t.val 0)

variable {c}

theorem Valid.line (V : c.Valid) (t : Fin c.v) : Lb c.p (c.lab0 t.val) = lineL (c.tv t) := by
  obtain ⟨h1, h2⟩ := V.hinv t.val
  show (⟨pmat c.p (c.lab0 t.val), cntOf c.p (c.lab0 t.val)⟩ : Lbl (Fin c.p.h)) = ⟨tt (c.tv t), 1⟩
  rw [h1, h2]
  show (⟨psum c.p (if t.val < c.v then [c.trips.getD t.val 0] else []),
    (if t.val < c.v then [c.trips.getD t.val 0] else []).length⟩ : Lbl (Fin c.p.h)) = _
  rw [if_pos t.isLt, psum_single]
  rfl

theorem Valid.fullLb (V : c.Valid) (r : Nat) (hr : r < c.n) :
    Lb c.p (runLab c.p c.lab0 c.tot r) = fullL := by
  obtain ⟨h1, h2⟩ := V.full r hr
  show (⟨pmat c.p _, cntOf c.p _⟩ : Lbl (Fin c.p.h)) = ⟨1, Fintype.card (Fin c.p.h)⟩
  rw [h1, h2, Fintype.card_fin]

/-- after phase B the role `y_S` stands at `t_S^⊥` -/
theorem Valid.yB (V : c.Valid) (S : Fin c.v) :
    Lb c.p (runLab c.p c.lab0 c.aB (c.v + c.R + S.val)) = perpL (c.tv S) := by
  obtain ⟨sh, hmem⟩ := yfinsFrom_mem c.eF c.trips (c.v + c.R) c.ysh S.val
    (by rw [V.htl]; exact S.isLt)
  obtain ⟨_, _, hrel⟩ := V.micro.2.2 c.yfins
    (List.mem_append_right _ (List.mem_singleton.mpr rfl)) _ hmem
  have hrel' : dec c.eF = updS c.p (upd c.p (runLab c.p c.lab0 c.aB (c.v + c.R + S.val))
      (spread c.p (c.trips.getD S.val 0)) (c.trips.getD S.val 0)) sh := hrel
  have hP := congrArg (pmat c.p) hrel'
  have hC := congrArg (cntOf c.p) hrel'
  rw [pmat_updS c.p V.hh V.hw, pmat_upd c.p V.hh V.hw, V.hF.1] at hP
  rw [cnt_updS c.p V.hh V.hw, cnt_upd c.p V.hh V.hw, V.hF.2, V.hc] at hC
  have hP' : pmat c.p (runLab c.p c.lab0 c.aB (c.v + c.R + S.val)) = 1 + tt (c.tv S) := by
    have h := PCert.tt_cancel (c.tv S)
    calc pmat c.p (runLab c.p c.lab0 c.aB (c.v + c.R + S.val))
        = pmat c.p (runLab c.p c.lab0 c.aB (c.v + c.R + S.val)) + (tt (c.tv S) + tt (c.tv S)) := by
          rw [h, add_zero]
      _ = 1 + tt (c.tv S) := by rw [← add_assoc]; exact congrArg (· + tt (c.tv S)) hP.symm
  show (⟨pmat c.p _, cntOf c.p _⟩ : Lbl (Fin c.p.h)) = ⟨1 + tt (c.tv S), Fintype.card (Fin c.p.h) - 1⟩
  rw [hP', Fintype.card_fin]
  congr 1
  omega

/-- the real final entries do not move the y roles -/
theorem Valid.yF (V : c.Valid) (S : Fin c.v) :
    Lb c.p (runLab c.p c.lab0 (c.aB ++ c.mF) (c.v + c.R + S.val)) = perpL (c.tv S) := by
  have hq := fins_quiet c.fins.flatten (c.v + c.R + S.val) (fun fe hfe e => by
    have h := List.all_eq_true.mp V.hfr fe hfe
    simp only [decide_eq_true_eq] at h
    omega)
  have h : Lb c.p (runLab c.p (runLab c.p c.lab0 c.aB) c.mF (c.v + c.R + S.val))
      = Lb c.p (runLab c.p c.lab0 c.aB (c.v + c.R + S.val)) :=
    Lb_quiet c.p V.hh V.hw (fun _ : Unit => c.v + c.R + S.val) c.mF
      (runLab c.p c.lab0 c.aB) hq ()
  rw [runLab_append, h]
  exact V.yB S

/-- after the real final entries every x role and every slot stands at the full label -/
theorem Valid.xsF (V : c.Valid) (r : Nat) (hr : r < c.v + c.R) :
    Lb c.p (runLab c.p c.lab0 (c.aB ++ c.mF) r) = fullL := by
  have hq := fins_quiet c.yfins r (fun fe hfe e => by
    have h := yfinsFrom_ge c.eF c.trips (c.v + c.R) c.ysh fe hfe
    omega)
  have h : Lb c.p (runLab c.p (runLab c.p c.lab0 (c.aB ++ c.mF)) c.mY r)
      = Lb c.p (runLab c.p c.lab0 (c.aB ++ c.mF) r) :=
    Lb_quiet c.p V.hh V.hw (fun _ : Unit => r) c.mY
      (runLab c.p c.lab0 (c.aB ++ c.mF)) hq ()
  have e : runLab c.p (runLab c.p c.lab0 (c.aB ++ c.mF)) c.mY = runLab c.p c.lab0 c.tot :=
    (runLab_append c.p c.lab0 (c.aB ++ c.mF) c.mY).symm
  rw [e] at h
  rw [← h]
  exact V.fullLb r (by unfold n; omega)

end CCert

end SSC
