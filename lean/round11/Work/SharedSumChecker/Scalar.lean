import Work.SharedSumChecker.Circ
import Work.SharedSumChecker.ScalarDef

/-!
# Shared-sum checker: soundness of the scalar check

`PCert.Valid.scalar`: if the certificate is valid and `scalarCheck` accepts, the matrices of
the certificate satisfy `(Jr * Cc + Jp) * L * V = 1` (`PCert.ScalarId`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace SSC
open OAI.PowerSaving.Binary OAI.PowerSaving.RAM OAI.PowerSaving.SS Finset Matrix

/-! ## supports, abstractly -/

def supStep : Micro → (Nat → Nat) → (Nat → Nat)
  | .add t s _, sup => Function.update sup t (sup t ||| sup s)
  | _, sup => sup

def okSup1 : Micro → (Nat → Nat) → Prop
  | .add t s cf, sup => sup t &&& sup s = 0 ∧ cf.val = 1
  | _, _ => True

def runSup (sup : Nat → Nat) (ms : List Micro) : Nat → Nat :=
  ms.foldl (fun s m => supStep m s) sup

def okSup : (Nat → Nat) → List Micro → Prop
  | _, [] => True
  | sup, m :: ms => okSup1 m sup ∧ okSup (supStep m sup) ms

theorem runSup_cons (sup : Nat → Nat) (m : Micro) (ms : List Micro) :
    runSup sup (m :: ms) = runSup (supStep m sup) ms := rfl
theorem runSup_append (sup : Nat → Nat) (a b : List Micro) :
    runSup sup (a ++ b) = runSup (runSup sup a) b := by
  simp [runSup, List.foldl_append]

theorem okSup_append (sup : Nat → Nat) (a b : List Micro) :
    okSup sup (a ++ b) ↔ okSup sup a ∧ okSup (runSup sup a) b := by
  induction a generalizing sup with
  | nil => simp [okSup, runSup]
  | cons m ms ih => simp only [List.cons_append, okSup, runSup_cons, ih, and_assoc]

theorem sup_moves (sup : Nat → Nat) (ms : List Micro)
    (h : ∀ m ∈ ms, ∃ r z, m = .dir r z ∨ m = .shift r z) :
    okSup sup ms ∧ runSup sup ms = sup := by
  induction ms with
  | nil => exact ⟨trivial, rfl⟩
  | cons m ms ih =>
    obtain ⟨a, b⟩ := ih (fun m' h' => h m' (List.mem_cons_of_mem _ h'))
    obtain ⟨r, z, e | e⟩ := h m (List.mem_cons_self ..) <;> subst e <;> exact ⟨⟨trivial, a⟩, b⟩

theorem Coef.one_val : Coef.one.val = 1 := by simp [Coef.one, Coef.val]

/-! ## the support table -/

def absS (n : Nat) (t : Trie) : Nat → Nat := fun r => if r < n then t.get r else 0

theorem absS_apply (d : Nat) (t : Trie) (r : Nat) (hr : r < 2^d) : absS (2^d) t r = t.get r := by
  show (if r < 2^d then t.get r else 0) = _
  rw [if_pos hr]

theorem absS_set (d : Nat) (t : Trie) (hwf : t.wf d) (r x : Nat) (hr : r < 2^d) :
    absS (2^d) (t.set r x) = Function.update (absS (2^d) t) r x := by
  funext r'
  rw [Function.update_apply]
  show (if r' < 2^d then (t.set r x).get r' else 0) = if r' = r then x else (if r' < 2^d then t.get r' else 0)
  by_cases h : r' < 2^d
  · rw [if_pos h, Trie.get_set d t hwf r r' x hr h]
    by_cases e : r' = r
    · rw [if_pos e, if_pos e]
    · rw [if_neg e, if_neg e, if_pos h]
  · rw [if_neg h]
    have e : r' ≠ r := by omega
    rw [if_neg e, if_neg h]

theorem absS_mk (d r : Nat) : absS (2^d) (Trie.mk d) r = 0 := by
  show (if r < 2^d then (Trie.mk d).get r else 0) = 0
  rw [Trie.get_mk]; simp

theorem supTgts_nil (A : Nat) (t : Trie) (k : Trie → Bool) : supTgts A [] t k = k t := rfl
theorem supTgts_cons (A : Nat) (pt : Part) (tgts : List Part) (t : Trie) (k : Trie → Bool) :
    supTgts A (pt :: tgts) t k = t.getK pt.role fun B => guard (Nat.beq (Nat.land B A) 0)
      (forceN (Nat.lor B A) fun C => supTgts A tgts (t.set pt.role C) k) := rfl

theorem supTgts_sound (d A s : Nat) (tgts : List Part) (t : Trie) (k : Trie → Bool)
    (hwf : t.wf d) (hs : ∀ pt ∈ tgts, pt.role ≠ s) (hA : absS (2^d) t s = A)
    (h : supTgts A tgts t k = true) :
    ∃ t', t'.wf d ∧ k t' = true ∧
      okSup (absS (2^d) t) (tgts.map fun pt => Micro.add pt.role s Coef.one) ∧
      absS (2^d) t' = runSup (absS (2^d) t) (tgts.map fun pt => Micro.add pt.role s Coef.one) := by
  induction tgts generalizing t with
  | nil => exact ⟨t, hwf, h, trivial, rfl⟩
  | cons pt tgts ih =>
    rw [supTgts_cons, Trie.getK_eq d t hwf] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hr, h2⟩ := h
    obtain ⟨hb, h3⟩ := guard_true h2
    rw [forceN_eq] at h3
    have hne : pt.role ≠ s := hs pt (List.mem_cons_self ..)
    have hset := absS_set d t hwf pt.role (Nat.lor (t.get pt.role) A) hr
    have hA' : absS (2^d) (t.set pt.role (Nat.lor (t.get pt.role) A)) s = A := by
      rw [hset, Function.update_of_ne (Ne.symm hne), hA]
    obtain ⟨t', hwf', hk, hok, hrun⟩ := ih _ (Trie.wf_set d t hwf _ _)
      (fun pt' h' => hs pt' (List.mem_cons_of_mem _ h')) hA' h3
    have hval : absS (2^d) t pt.role ||| absS (2^d) t s = Nat.lor (t.get pt.role) A := by
      show absS (2^d) t pt.role ||| absS (2^d) t s = t.get pt.role ||| A
      rw [hA, absS_apply d t pt.role hr]
    have hstep : supStep (Micro.add pt.role s Coef.one) (absS (2^d) t)
        = absS (2^d) (t.set pt.role (Nat.lor (t.get pt.role) A)) := by
      rw [hset]
      exact congrArg (Function.update (absS (2^d) t) pt.role) hval
    refine ⟨t', hwf', hk, ?_, ?_⟩
    · refine ⟨⟨?_, Coef.one_val⟩, ?_⟩
      · rw [hA, absS_apply d t pt.role hr]; exact beq_true hb
      · rw [hstep]; exact hok
    · rw [List.map_cons, runSup_cons, hstep]; exact hrun

theorem gatesM_single (s : Part) (tgts : List Part) :
    gatesM [s] tgts [] = tgts.map fun pt => Micro.add pt.role s.role Coef.one := by
  induction tgts with
  | nil => rfl
  | cons t ts ih =>
    show gatesRow t.role [s] [] ++ gatesM [s] ts [] = _
    rw [ih]; rfl

theorem supOp_sound (d v R : Nat) (op : Op) (hop : op.slotGate v R = true) (t : Trie)
    (k : Trie → Bool) (hwf : t.wf d) (h : supOp op t k = true) :
    ∃ t', t'.wf d ∧ k t' = true ∧ okSup (absS (2^d) t) op.micro ∧
      absS (2^d) t' = runSup (absS (2^d) t) op.micro := by
  cases op with
  | bip srcs tgts coefs =>
    cases srcs with
    | nil => exact absurd h Bool.false_ne_true
    | cons s rest =>
      cases rest with
      | cons s2 rest2 => exact absurd h Bool.false_ne_true
      | nil =>
        cases coefs with
        | cons c0 cs0 => exact absurd h Bool.false_ne_true
        | nil =>
          have h' : (t.getK s.role fun A => supTgts A tgts t k) = true := h
          rw [Trie.getK_eq d t hwf] at h'
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
          obtain ⟨hr, h2⟩ := h'
          simp only [Op.slotGate, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hop
          have hs : ∀ pt ∈ tgts, pt.role ≠ s.role :=
            fun pt hpt => Ne.symm (hop.2 s (List.mem_cons_self ..) pt hpt)
          obtain ⟨t', hwf', hk, hok, hrun⟩ :=
            supTgts_sound d _ s.role tgts t k hwf hs (absS_apply d t s.role hr) h2
          have hmv : ∀ m ∈ ([s] ++ tgts).flatMap Part.micro, ∃ r z, m = .dir r z ∨ m = .shift r z := by
            intro m hm
            obtain ⟨pt, _, hpt⟩ := List.mem_flatMap.mp hm
            obtain ⟨z, e⟩ := mem_part_micro pt m hpt
            exact ⟨pt.role, z, e⟩
          obtain ⟨m1, m2⟩ := sup_moves (absS (2^d) t) _ hmv
          refine ⟨t', hwf', hk, ?_, ?_⟩
          · show okSup _ (([s] ++ tgts).flatMap Part.micro ++ gatesM [s] tgts [])
            rw [okSup_append, m2, gatesM_single]; exact ⟨m1, hok⟩
          · show _ = runSup _ (([s] ++ tgts).flatMap Part.micro ++ gatesM [s] tgts [])
            rw [runSup_append, m2, gatesM_single]; exact hrun
  | copy _ _ => exact absurd h Bool.false_ne_true
  | copyNew _ _ => exact absurd h Bool.false_ne_true
  | erase _ => exact absurd h Bool.false_ne_true
  | expect _ _ => exact absurd h Bool.false_ne_true

theorem supOps_sound (d v R : Nat) (ops : List Op) (hop : ∀ op ∈ ops, op.slotGate v R = true)
    (t : Trie) (k : Trie → Bool) (hwf : t.wf d) (h : supOps ops t k = true) :
    ∃ t', t'.wf d ∧ k t' = true ∧ okSup (absS (2^d) t) (ops.flatMap Op.micro) ∧
      absS (2^d) t' = runSup (absS (2^d) t) (ops.flatMap Op.micro) := by
  induction ops generalizing t with
  | nil => exact ⟨t, hwf, h, trivial, rfl⟩
  | cons op ops ih =>
    have h' : (supOp op t fun t' => supOps ops t' k) = true := h
    obtain ⟨t1, hwf1, hk1, hok1, hrun1⟩ :=
      supOp_sound d v R op (hop op (List.mem_cons_self ..)) t _ hwf h'
    obtain ⟨t2, hwf2, hk2, hok2, hrun2⟩ :=
      ih (fun op' h' => hop op' (List.mem_cons_of_mem _ h')) t1 hwf1 hk1
    refine ⟨t2, hwf2, hk2, ?_, ?_⟩
    · rw [List.flatMap_cons, okSup_append, ← hrun1]; exact ⟨hok1, hok2⟩
    · rw [List.flatMap_cons, runSup_append, ← hrun1]; exact hrun2

theorem supChunks_sound (d v R : Nat) (cs : List (List Op))
    (hop : ∀ op ∈ cs.flatten, op.slotGate v R = true)
    (t : Trie) (k : Trie → Bool) (hwf : t.wf d) (h : supChunks cs t k = true) :
    ∃ t', t'.wf d ∧ k t' = true ∧ okSup (absS (2^d) t) (cs.flatten.flatMap Op.micro) ∧
      absS (2^d) t' = runSup (absS (2^d) t) (cs.flatten.flatMap Op.micro) := by
  induction cs generalizing t with
  | nil => exact ⟨t, hwf, h, trivial, rfl⟩
  | cons ops cs ih =>
    have h' : (supOps ops t fun t' => supChunks cs t' k) = true := h
    obtain ⟨t1, hwf1, hk1, hok1, hrun1⟩ :=
      supOps_sound d v R ops (fun op h' => hop op (by simp [h'])) t _ hwf h'
    obtain ⟨t2, hwf2, hk2, hok2, hrun2⟩ :=
      ih (fun op' h' => hop op' (by
        rw [List.flatten_cons]; exact List.mem_append_right _ h')) t1 hwf1 hk1
    refine ⟨t2, hwf2, hk2, ?_, ?_⟩
    · rw [List.flatten_cons, List.flatMap_append, okSup_append, ← hrun1]; exact ⟨hok1, hok2⟩
    · rw [List.flatten_cons, List.flatMap_append, runSup_append, ← hrun1]; exact hrun2

theorem supInit_nil (v i : Nat) (t : Trie) (k : Trie → Bool) : supInit v [] i t k = k t := rfl
theorem supInit_cons (v s : Nat) (l : List Nat) (i : Nat) (t : Trie) (k : Trie → Bool) :
    supInit v (s :: l) i t k = t.getK (Nat.add v s) fun B => guard (Nat.beq B 0)
      (forceN (Nat.shiftLeft 1 i) fun bit => forceN (Nat.succ i) fun i2 =>
        supInit v l i2 (t.set (Nat.add v s) bit) k) := rfl

theorem supInit_sound (d v : Nat) (l : List Nat) (i : Nat) (t : Trie) (k : Trie → Bool)
    (hwf : t.wf d) (h : supInit v l i t k = true) :
    ∃ t', t'.wf d ∧ k t' = true ∧
      (∀ j, j < l.length → absS (2^d) t (v + l.getD j 0) = 0 ∧
        absS (2^d) t' (v + l.getD j 0) = 2^(i + j)) ∧
      (∀ r, (∀ j, j < l.length → v + l.getD j 0 ≠ r) → absS (2^d) t' r = absS (2^d) t r) := by
  induction l generalizing i t with
  | nil => exact ⟨t, hwf, h, fun j hj => absurd hj (by simp), fun r _ => rfl⟩
  | cons s l ih =>
    rw [supInit_cons, Trie.getK_eq d t hwf] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.add_eq] at h
    obtain ⟨hr, h2⟩ := h
    have hr' : v + s < 2^d := hr
    obtain ⟨hb, h3⟩ := guard_true h2
    rw [forceN_eq, forceN_eq] at h3
    have h0 : absS (2^d) t (v + s) = 0 := by rw [absS_apply d t _ hr']; exact beq_true hb
    have hbit : Nat.shiftLeft 1 i = 2^i := by
      show 1 <<< i = 2^i
      rw [Nat.shiftLeft_eq, Nat.one_mul]
    have hset : absS (2^d) (t.set (v + s) (2^i)) = Function.update (absS (2^d) t) (v + s) (2^i) :=
      absS_set d t hwf (v + s) (2^i) hr'
    rw [hbit] at h3
    obtain ⟨t', hwf', hk, ha, hb'⟩ := ih (Nat.succ i) _ (Trie.wf_set d t hwf _ _) h3
    have hne : ∀ j, j < l.length → v + l.getD j 0 ≠ v + s := by
      intro j hj e
      have h1 := (ha j hj).1
      rw [e, hset, Function.update_self] at h1
      exact absurd h1 (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos i))
    refine ⟨t', hwf', hk, ?_, ?_⟩
    · intro j hj
      cases j with
      | zero =>
        refine ⟨h0, ?_⟩
        show absS (2^d) t' (v + s) = 2^(i + 0)
        rw [hb' (v + s) hne, hset, Function.update_self]; rfl
      | succ j =>
        have hj' : j < l.length := by simpa using hj
        obtain ⟨a1, a2⟩ := ha j hj'
        show absS (2^d) t (v + l.getD j 0) = 0 ∧ absS (2^d) t' (v + l.getD j 0) = 2^(i + (j+1))
        rw [hset, Function.update_of_ne (hne j hj')] at a1
        refine ⟨a1, ?_⟩
        rw [a2]; congr 1; omega
    · intro r hr2
      have h1 : ∀ j, j < l.length → v + l.getD j 0 ≠ r := fun j hj => hr2 (j+1) (by simpa using hj)
      have h2' : r ≠ v + s := fun e => hr2 0 (by simp) e.symm
      rw [hb' r h1, hset, Function.update_of_ne h2']

/-! ## the matrix of the supports -/

section
variable {ρ m : Type} [Fintype ρ] [DecidableEq ρ]

theorem eMat_mul_apply (a b : ρ) (M : Matrix ρ m ℚ) (i : ρ) (j : m) :
    (eMat a b * M) i j = if i = a then M b j else 0 := by
  rw [Matrix.mul_apply]
  by_cases h : i = a
  · rw [if_pos h, Finset.sum_eq_single b]
    · simp [eMat, h]
    · intro k _ hk; simp [eMat, hk]
    · intro hb; exact absurd (Finset.mem_univ _) hb
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro k _
    simp [eMat, h]

theorem addMat_mul_apply (a b : ρ) (cf : ℚ) (M : Matrix ρ m ℚ) (i : ρ) (j : m) :
    (addMat a b cf * M) i j = M i j + (if i = a then cf * M b j else 0) := by
  rw [addMat_eq, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, Matrix.smul_mul,
    Matrix.smul_apply, eMat_mul_apply]
  split <;> simp

end

namespace PCert
variable (c : PCert)

/-- `1` if the input belongs to the support of the slot -/
def Wm (sup : Nat → Nat) : Matrix (Fin c.R) (Fin c.v) ℚ :=
  fun q t => if (sup (c.v + q.val)).testBit t.val then 1 else 0

theorem Wm_add (hR : 0 < c.R) (sup : Nat → Nat) (t s : Nat)
    (ht : c.embS (c.unembS hR t) = t) (hs : c.embS (c.unembS hR s) = s)
    (hd : sup t &&& sup s = 0) :
    c.Wm (Function.update sup t (sup t ||| sup s))
      = addMat (c.unembS hR t) (c.unembS hR s) 1 * c.Wm sup := by
  ext q tr
  rw [addMat_mul_apply]
  have hs' : c.v + (c.unembS hR s).val = s := hs
  show (if (Function.update sup t (sup t ||| sup s) (c.v + q.val)).testBit tr.val then (1:ℚ) else 0)
    = (if (sup (c.v + q.val)).testBit tr.val then 1 else 0)
      + (if q = c.unembS hR t then
          1 * (if (sup (c.v + (c.unembS hR s).val)).testBit tr.val then 1 else 0) else 0)
  rw [hs']
  have hbit : ¬ ((sup t).testBit tr.val = true ∧ (sup s).testBit tr.val = true) := by
    intro ⟨a, b⟩
    have h := congrArg (fun x => x.testBit tr.val) hd
    simp [Nat.testBit_and, a, b] at h
  by_cases e : c.v + q.val = t
  · have hq : q = c.unembS hR t := by rw [← e]; exact (c.unembS_embS hR q).symm
    rw [e, Function.update_self, if_pos hq, Nat.testBit_or]
    cases h1 : (sup t).testBit tr.val <;> cases h2 : (sup s).testBit tr.val <;> simp_all
  · have hq : q ≠ c.unembS hR t := fun h => e (by rw [h]; exact ht)
    rw [Function.update_of_ne e, if_neg hq, add_zero]

theorem Wm_run (hR : 0 < c.R) (ms : List Micro)
    (hseg : ∀ m ∈ ms, segOK c.embS (c.unembS hR) m) (sup : Nat → Nat) (hok : okSup sup ms) :
    c.Wm (runSup sup ms) = matP (c.unembS hR) ms * c.Wm sup := by
  induction ms generalizing sup with
  | nil =>
    show c.Wm sup = 1 * c.Wm sup
    rw [Matrix.one_mul]
  | cons m ms ih =>
    obtain ⟨h1, h2⟩ := hok
    have hm := hseg m (List.mem_cons_self ..)
    have ih' := ih (fun m' h' => hseg m' (List.mem_cons_of_mem _ h')) _ h2
    cases m with
    | add t s cf =>
      obtain ⟨hd, hcf⟩ := h1
      show c.Wm (runSup (supStep (.add t s cf) sup) ms)
        = matP (c.unembS hR) ms * addMat (c.unembS hR t) (c.unembS hR s) cf.val * c.Wm sup
      rw [ih', hcf, Matrix.mul_assoc]
      congr 1
      exact c.Wm_add hR sup t s hm.1 hm.2 hd
    | dir _ _ => exact ih'
    | shift _ _ => exact ih'
    | copy _ _ => exact ih'
    | erase _ => exact ih'
    | expect _ _ => exact ih'

end PCert

/-! ## bit-sliced counters -/

/-- the count of the input `t` in the counters -/
def pval : List Nat → Nat → Nat
  | [], _ => 0
  | p :: ps, t => (p.testBit t).toNat + 2 * pval ps t

theorem pval_replicate (n t : Nat) : pval (List.replicate n 0) t = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, pval, ih]

theorem addPK_sound (ps : List Nat) (c : Nat) (k : List Nat → Bool) (h : addPK ps c k = true) :
    ∃ ps', (∀ t, pval ps' t = pval ps t + (c.testBit t).toNat) ∧ k ps' = true := by
  induction ps generalizing c k with
  | nil =>
    have h' : guard (Nat.beq c 0) (k []) = true := h
    obtain ⟨hb, hk⟩ := guard_true h'
    have hc : c = 0 := beq_true hb
    subst hc
    exact ⟨[], fun t => by simp [pval], hk⟩
  | cons p ps ih =>
    have h' : (forceN (Nat.xor p c) fun p' => forceN (Nat.land p c) fun c' =>
        addPK ps c' fun ps' => k (p' :: ps')) = true := h
    rw [forceN_eq, forceN_eq] at h'
    obtain ⟨ps', hv, hk⟩ := ih _ _ h'
    refine ⟨(p ^^^ c) :: ps', fun t => ?_, hk⟩
    show ((p ^^^ c).testBit t).toNat + 2 * pval ps' t
      = (p.testBit t).toNat + 2 * pval ps t + (c.testBit t).toNat
    have hv' : pval ps' t = pval ps t + ((p &&& c).testBit t).toNat := hv t
    rw [hv', Nat.testBit_xor, Nat.testBit_and]
    cases p.testBit t <;> cases c.testBit t <;> simp <;> omega

theorem addNK_zero (ps : List Nat) (c : Nat) (k : List Nat → Bool) : addNK 0 ps c k = k ps := rfl
theorem addNK_succ (n : Nat) (ps : List Nat) (c : Nat) (k : List Nat → Bool) :
    addNK (n+1) ps c k = addPK ps c fun ps' => addNK n ps' c k := rfl

theorem addNK_sound (n : Nat) (ps : List Nat) (c : Nat) (k : List Nat → Bool)
    (h : addNK n ps c k = true) :
    ∃ ps', (∀ t, pval ps' t = pval ps t + n * (c.testBit t).toNat) ∧ k ps' = true := by
  induction n generalizing ps with
  | zero => exact ⟨ps, fun t => by simp, h⟩
  | succ n ih =>
    rw [addNK_succ] at h
    obtain ⟨ps1, hv1, hk1⟩ := addPK_sound ps c _ h
    obtain ⟨ps2, hv2, hk2⟩ := ih ps1 hk1
    refine ⟨ps2, fun t => ?_, hk2⟩
    rw [hv2 t, hv1 t, Nat.succ_mul]; omega

theorem weightK_sound (cf : Coef) (k : Bool → Nat → Bool) (h : weightK cf k = true) :
    ∃ w : Nat, k cf.neg w = true ∧ cf.val = (if cf.neg then -(w:ℚ) else (w:ℚ)) / 2 := by
  obtain ⟨ng, num, den⟩ := cf
  have h' : Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) false (k ng (Nat.mul 2 num)) (Nat.beq den 1)) (k ng num)
      (Nat.beq den 2) = true := h
  cases h2 : Nat.beq den 2 with
  | true =>
    rw [h2] at h'
    have e : den = 2 := beq_true h2
    subst e
    exact ⟨num, h', by simp [Coef.val]⟩
  | false =>
    rw [h2] at h'
    cases h1 : Nat.beq den 1 with
    | true =>
      rw [h1] at h'
      have e : den = 1 := beq_true h1
      subst e
      refine ⟨2 * num, h', ?_⟩
      show (if ng then -(num:ℚ) else (num:ℚ)) / ((1:ℕ):ℚ) = (if ng then -((2 * num : ℕ):ℚ) else ((2 * num : ℕ):ℚ)) / 2
      cases ng <;> simp <;> ring
    | false =>
      rw [h1] at h'
      exact absurd h' Bool.false_ne_true

/-- `1` if the bit is set -/
def bq (A t : Nat) : ℚ := if A.testBit t then 1 else 0

theorem bq_toNat (A t : Nat) : ((A.testBit t).toNat : ℚ) = bq A t := by
  unfold bq; cases A.testBit t <;> simp

theorem accK_nil (v : Nat) (tS : Trie) (look : Nat → Nat) (pos neg : List Nat)
    (k : List Nat → List Nat → Bool) : accK v tS look [] pos neg k = k pos neg := rfl

theorem accK_cons (v : Nat) (tS : Trie) (look : Nat → Nat) (x : Nat × Coef)
    (l : List (Nat × Coef)) (pos neg : List Nat) (k : List Nat → List Nat → Bool) :
    accK v tS look (x :: l) pos neg k = tS.getK (Nat.add v (look x.1)) fun A =>
      weightK x.2 fun ng w => Bool.rec (motive := fun _ => Bool)
        (addNK w pos A fun pos' => accK v tS look l pos' neg k)
        (addNK w neg A fun neg' => accK v tS look l pos neg' k) ng := rfl

theorem accK_sound (d v : Nat) (tS : Trie) (hwf : tS.wf d) (look : Nat → Nat)
    (l : List (Nat × Coef)) (pos neg : List Nat) (k : List Nat → List Nat → Bool)
    (h : accK v tS look l pos neg k = true) :
    ∃ pos' neg', k pos' neg' = true ∧ ∀ t, ((pval pos' t : ℚ) - pval neg' t)
      = (pval pos t : ℚ) - pval neg t
        + 2 * (l.map fun x => x.2.val * bq (absS (2^d) tS (v + look x.1)) t).sum := by
  induction l generalizing pos neg with
  | nil => exact ⟨pos, neg, h, fun t => by simp⟩
  | cons x l ih =>
    rw [accK_cons, Trie.getK_eq d tS hwf] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hr, h2⟩ := h
    have hr' : v + look x.1 < 2^d := hr
    obtain ⟨w, hk, hval⟩ := weightK_sound x.2 _ h2
    have hA : tS.get (Nat.add v (look x.1)) = absS (2^d) tS (v + look x.1) :=
      (absS_apply d tS _ hr').symm
    cases hng : x.2.neg with
    | false =>
      rw [hng] at hk hval
      have hk' : (addNK w pos (tS.get (Nat.add v (look x.1))) fun pos' =>
          accK v tS look l pos' neg k) = true := hk
      obtain ⟨pos1, hv1, hk1⟩ := addNK_sound _ _ _ _ hk'
      obtain ⟨pos', neg', hkk, hrel⟩ := ih pos1 neg hk1
      refine ⟨pos', neg', hkk, fun t => ?_⟩
      rw [hrel t, hv1 t, List.map_cons, List.sum_cons, hval, hA, Nat.cast_add, Nat.cast_mul,
        bq_toNat]
      simp only [Bool.false_eq_true, if_false]
      ring
    | true =>
      rw [hng] at hk hval
      have hk' : (addNK w neg (tS.get (Nat.add v (look x.1))) fun neg' =>
          accK v tS look l pos neg' k) = true := hk
      obtain ⟨neg1, hv1, hk1⟩ := addNK_sound _ _ _ _ hk'
      obtain ⟨pos', neg', hkk, hrel⟩ := ih pos neg1 hk1
      refine ⟨pos', neg', hkk, fun t => ?_⟩
      rw [hrel t, hv1 t, List.map_cons, List.sum_cons, hval, hA, Nat.cast_add, Nat.cast_mul,
        bq_toNat]
      simp only [if_true]
      ring

theorem eqK_sound (a b : List Nat) (h : eqK a b = true) : a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons y ys => exact absurd h Bool.false_ne_true
  | cons x xs ih =>
    cases b with
    | nil => exact absurd h Bool.false_ne_true
    | cons y ys =>
      have h' : guard (Nat.beq x y) (eqK xs ys) = true := h
      obtain ⟨hb, h2⟩ := guard_true h'
      rw [beq_true hb, ih ys h2]

theorem rowK_sound (d v : Nat) (tS : Trie) (hwf : tS.wf d) (ret zeros : List Nat)
    (hz : ∀ t, pval zeros t = 0) (S : Nat) (pc sc : List (Nat × Coef))
    (h : rowK v tS ret zeros S pc sc = true) (t : Nat) :
    (pc.map fun x => x.2.val * bq (absS (2^d) tS (v + x.1)) t).sum
      + (sc.map fun x => x.2.val * bq (absS (2^d) tS (v + ret.getD x.1 0)) t).sum
      = if S = t then 1 else 0 := by
  have h' : (accK v tS (fun q => q) pc zeros zeros fun pos neg =>
      accK v tS (fun k => ret.getD k 0) sc pos neg fun pos' neg' =>
        addNK 2 neg' (Nat.shiftLeft 1 S) fun neg'' => eqK pos' neg'') = true := h
  obtain ⟨pos, neg, hk, hrel⟩ := accK_sound d v tS hwf _ pc zeros zeros _ h'
  obtain ⟨pos', neg', hk', hrel'⟩ := accK_sound d v tS hwf _ sc pos neg _ hk
  obtain ⟨neg'', hv, he⟩ := addNK_sound 2 neg' _ _ hk'
  have heq := eqK_sound _ _ he
  have h1 := hrel t
  have h2 := hrel' t
  have h3 := hv t
  rw [hz t] at h1
  rw [heq] at h2
  have hbit : ((Nat.shiftLeft 1 S).testBit t).toNat = if S = t then 1 else 0 := by
    show ((1 <<< S).testBit t).toNat = _
    rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]
    by_cases e : S = t <;> simp [e]
  rw [hbit] at h3
  have h3' : (pval neg'' t : ℚ) = pval neg' t + 2 * (if S = t then 1 else 0) := by
    rw [h3]
    by_cases e : S = t <;> simp [e]
  rw [h3'] at h2
  simp only [Nat.cast_zero, sub_self, zero_add] at h1
  linarith

theorem rowsK_nil (v : Nat) (tS : Trie) (ret zeros : List Nat) (S : Nat) :
    rowsK v tS ret zeros [] S = true := rfl

theorem rowsK_cons (v : Nat) (tS : Trie) (ret zeros : List Nat)
    (x : List (Nat × Coef) × List (Nat × Coef)) (rows : List (List (Nat × Coef) × List (Nat × Coef)))
    (S : Nat) : rowsK v tS ret zeros (x :: rows) S
      = guard (rowK v tS ret zeros S x.1 x.2) (forceN (Nat.succ S) fun S2 => rowsK v tS ret zeros rows S2) :=
  rfl

theorem rowsK_sound (v : Nat) (tS : Trie) (ret zeros : List Nat)
    (rows : List (List (Nat × Coef) × List (Nat × Coef))) (S : Nat)
    (h : rowsK v tS ret zeros rows S = true) (j : Nat) (hj : j < rows.length) :
    rowK v tS ret zeros (S + j) (rows.getD j ([], [])).1 (rows.getD j ([], [])).2 = true := by
  induction rows generalizing S j with
  | nil => simp at hj
  | cons x rows ih =>
    rw [rowsK_cons] at h
    obtain ⟨h1, h2⟩ := guard_true h
    rw [forceN_eq] at h2
    cases j with
    | zero => exact h1
    | succ j =>
      have := ih (Nat.succ S) h2 j (by simpa using hj)
      have e : S + (j + 1) = Nat.succ S + j := by omega
      rw [e]; exact this

theorem zip_getD {α β : Type} (l1 : List α) (l2 : List β) (d1 : α) (d2 : β) (t : Nat)
    (h1 : t < l1.length) (h2 : t < l2.length) :
    (l1.zip l2).getD t (d1, d2) = (l1.getD t d1, l2.getD t d2) := by
  induction l1 generalizing l2 t with
  | nil => simp at h1
  | cons a l1 ih =>
    cases l2 with
    | nil => simp at h2
    | cons b l2 =>
      cases t with
      | zero => rfl
      | succ t =>
        simp only [List.zip_cons_cons, List.getD_cons_succ]
        exact ih l2 t (by simpa using h1) (by simpa using h2)

/-! ## the scalar identity -/

namespace PCert
variable {c : PCert}

/-- **Soundness of the scalar check.** -/
theorem Valid.scalar (V : c.Valid) (h : c.scalarCheck = true) : c.ScalarId V.hR := by
  have h' : guard (decide (c.scat.length = c.v) &&
      c.scat.all (fun l => l.all fun x => decide (x.1 < c.p.h)))
    (supInit c.v c.src 0 (Trie.mk c.p.d) fun t0 => supChunks c.F5 t0 fun tS =>
      rowsK c.v tS c.ret (List.replicate 10 0) (c.pieces.zip c.scat) 0) = true := h
  obtain ⟨hg, h1⟩ := guard_true h'
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hg
  obtain ⟨hscl, hsc⟩ := hg
  obtain ⟨t0, hwf0, hk0, hin, hout⟩ := supInit_sound c.p.d c.v c.src 0 _ _ (Trie.wf_mk _) h1
  obtain ⟨tS, hwfS, hkS, hokS, hrunS⟩ :=
    supChunks_sound c.p.d c.v c.R c.F5 (List.all_eq_true.mp V.h5) t0 _ hwf0 hk0
  -- the initial supports are the loading matrix
  have hW0 : c.Wm (absS (2^c.p.d) t0) = c.Vm V.hR := by
    ext q t
    show (if (absS (2^c.p.d) t0 (c.v + q.val)).testBit t.val then (1:ℚ) else 0)
      = if q = c.srcq V.hR t then 1 else 0
    have hsrc : ∀ t' : Nat, t' < c.v → absS (2^c.p.d) t0 (c.v + c.src.getD t' 0) = 2^t' := by
      intro t' ht'
      have := (hin t' (by rw [V.hsl]; exact ht')).2
      rw [Nat.zero_add] at this
      exact this
    by_cases hq : q = c.srcq V.hR t
    · have e : c.v + q.val = c.v + c.src.getD t.val 0 := by
        rw [hq]
        show c.v + c.src.getD t.val 0 % c.R = _
        rw [Nat.mod_eq_of_lt (V.all_src t)]
      rw [e, hsrc t.val t.isLt, Nat.testBit_two_pow, if_pos hq]
      simp
    · rw [if_neg hq]
      by_cases hex : ∃ j, j < c.src.length ∧ c.v + c.src.getD j 0 = c.v + q.val
      · obtain ⟨j, hj, hjq⟩ := hex
        have hj' : j < c.v := by rw [← V.hsl]; exact hj
        rw [← hjq, hsrc j hj', Nat.testBit_two_pow]
        have hne : j ≠ t.val := by
          intro e
          apply hq
          apply Fin.ext
          show q.val = c.src.getD t.val 0 % c.R
          rw [Nat.mod_eq_of_lt (V.all_src t), ← e]
          omega
        simp [hne]
      · have h0 : absS (2^c.p.d) t0 (c.v + q.val) = 0 := by
          rw [hout _ (fun j hj e => hex ⟨j, hj, e⟩), absS_mk]
        rw [h0, Nat.zero_testBit]
        simp
  -- hence the final supports are `L * V`
  have hLV : c.Lm V.hR * c.Vm V.hR = c.Wm (absS (2^c.p.d) tS) := by
    rw [hrunS]
    show matP (c.unembS V.hR) c.m5 * c.Vm V.hR = c.Wm (runSup _ c.m5)
    rw [c.Wm_run V.hR c.m5 V.seg5.1 _ hokS, hW0]
  show (c.Jrm * c.Ccm V.hR + c.Jpm) * c.Lm V.hR * c.Vm V.hR = 1
  rw [Matrix.mul_assoc, hLV]
  ext S t
  have hrowlen : S.val < (c.pieces.zip c.scat).length := by
    rw [List.length_zip, V.hpl, hscl]; simp
  have hrow := rowsK_sound c.v tS c.ret _ _ 0 hkS S.val hrowlen
  rw [zip_getD _ _ _ _ _ (by rw [V.hpl]; exact S.isLt) (by rw [hscl]; exact S.isLt),
    Nat.zero_add] at hrow
  have hsum := rowK_sound c.p.d c.v tS hwfS c.ret _ (pval_replicate 10) S.val _ _ hrow t.val
  -- the matrix entry is the same sum
  have hC : ∀ k : Fin c.p.h, (c.Ccm V.hR * c.Wm (absS (2^c.p.d) tS)) k t
      = bq (absS (2^c.p.d) tS (c.v + c.ret.getD k.val 0)) t.val := by
    intro k
    rw [Matrix.mul_apply, Finset.sum_eq_single (c.retq V.hR k)]
    · show (if c.retq V.hR k = c.retq V.hR k then (1:ℚ) else 0)
        * (if (absS (2^c.p.d) tS (c.v + (c.retq V.hR k).val)).testBit t.val then 1 else 0) = _
      rw [if_pos rfl, one_mul]
      show _ = bq _ _
      have e : (c.retq V.hR k).val = c.ret.getD k.val 0 :=
        Nat.mod_eq_of_lt (V.all_ret k)
      rw [e]; rfl
    · intro q _ hq
      show (if q = c.retq V.hR k then (1:ℚ) else 0) * _ = 0
      rw [if_neg hq, zero_mul]
    · intro hb; exact absurd (Finset.mem_univ _) hb
  have hpcR : ∀ x ∈ c.pieces.getD S.val [], x.1 < c.R := by
    intro x hx
    have h1 := List.all_eq_true.mp V.hpc _ (getD_mem_lt c.pieces [] S.val (by rw [V.hpl]; exact S.isLt))
    have h2 := List.all_eq_true.mp h1 x hx
    simpa using h2
  have hscR : ∀ x ∈ c.scat.getD S.val [], x.1 < c.p.h := by
    intro x hx
    exact hsc _ (getD_mem_lt c.scat [] S.val (by rw [hscl]; exact S.isLt)) x hx
  rw [Matrix.add_mul, Matrix.add_apply, Matrix.mul_assoc, Matrix.mul_apply, Matrix.mul_apply,
    Matrix.one_apply]
  have e1 : ∑ k : Fin c.p.h, c.Jrm S k * (c.Ccm V.hR * c.Wm (absS (2^c.p.d) tS)) k t
      = ((c.scat.getD S.val []).map fun x =>
          x.2.val * bq (absS (2^c.p.d) tS (c.v + c.ret.getD x.1 0)) t.val).sum :=
    rowOf_sum _ hscR _ (fun k => bq (absS (2^c.p.d) tS (c.v + c.ret.getD k 0)) t.val) hC
  have e2 : ∑ q : Fin c.R, c.Jpm S q * c.Wm (absS (2^c.p.d) tS) q t
      = ((c.pieces.getD S.val []).map fun x =>
          x.2.val * bq (absS (2^c.p.d) tS (c.v + x.1)) t.val).sum :=
    rowOf_sum _ hpcR _ (fun r => bq (absS (2^c.p.d) tS (c.v + r)) t.val) (fun q => rfl)
  rw [e1, e2]
  by_cases e : S = t
  · have e' : S.val = t.val := congrArg Fin.val e
    rw [if_pos e'] at hsum
    rw [if_pos e]
    linarith
  · have e' : ¬ S.val = t.val := fun h => e (Fin.ext h)
    rw [if_neg e'] at hsum
    rw [if_neg e]
    linarith

end PCert

end SSC
