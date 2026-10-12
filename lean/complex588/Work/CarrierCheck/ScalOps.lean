import Work.CarrierCheck.ScalRun

/-!
# (key: carrier-check) The scalar check on ops, chunks and the scatter rows; the content matrix

* `sOps_sound`, `sChunks_sound`   the checker on a list of ops runs `SRun` on its micro-program;
* `sScat_sound`                   the checker on the scatter rows runs `SRun` on `scatFromM`;
* `SRun_Cm`                       `SRun a ms b → Cm b = matP unemb ms * Cm a`.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace SSC
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM OAI.PowerSaving.SS Finset Matrix

/-! ## unfolding lemmas -/

theorem sRow_nil (tm y0 : Nat) (t : Nat) (cfs : List Coef) (tP tN : Trie) (k : Trie → Trie → Bool) :
    sRow tm y0 t [] cfs tP tN k = k tP tN := rfl

theorem sRow_cons_nil (tm y0 : Nat) (t : Nat) (s : Part) (ss : List Part) (tP tN : Trie)
    (k : Trie → Trie → Bool) :
    sRow tm y0 t (s :: ss) [] tP tN k
      = sAdd tm y0 t s.role ⟨false, 1, 1⟩ tP tN fun tP' tN' => sRow tm y0 t ss [] tP' tN' k := rfl

theorem sRow_cons_cons (tm y0 : Nat) (t : Nat) (s : Part) (ss : List Part) (cf : Coef) (cs : List Coef)
    (tP tN : Trie) (k : Trie → Trie → Bool) :
    sRow tm y0 t (s :: ss) (cf :: cs) tP tN k
      = sAdd tm y0 t s.role cf tP tN fun tP' tN' => sRow tm y0 t ss cs tP' tN' k := rfl

theorem sGates_nil (tm y0 : Nat) (srcs : List Part) (rows : List (List Coef)) (tP tN : Trie)
    (k : Trie → Trie → Bool) : sGates tm y0 srcs [] rows tP tN k = k tP tN := rfl

theorem sGates_cons_nil (tm y0 : Nat) (srcs : List Part) (t : Part) (ts : List Part) (tP tN : Trie)
    (k : Trie → Trie → Bool) :
    sGates tm y0 srcs (t :: ts) [] tP tN k
      = sRow tm y0 t.role srcs [] tP tN fun tP' tN' => sGates tm y0 srcs ts [] tP' tN' k := rfl

theorem sGates_cons_cons (tm y0 : Nat) (srcs : List Part) (t : Part) (ts : List Part) (row : List Coef)
    (rs : List (List Coef)) (tP tN : Trie) (k : Trie → Trie → Bool) :
    sGates tm y0 srcs (t :: ts) (row :: rs) tP tN k
      = sRow tm y0 t.role srcs row tP tN fun tP' tN' => sGates tm y0 srcs ts rs tP' tN' k := rfl

theorem sOps_nil (tm y0 : Nat) (tP tN : Trie) (k : Trie → Trie → Bool) : sOps tm y0 [] tP tN k = k tP tN := rfl
theorem sOps_cons (tm y0 : Nat) (op : Op) (ops : List Op) (tP tN : Trie) (k : Trie → Trie → Bool) :
    sOps tm y0 (op :: ops) tP tN k
      = sOp tm y0 op tP tN fun tP' tN' => sOps tm y0 ops tP' tN' k := rfl

theorem sChunks_nil (tm y0 : Nat) (tP tN : Trie) (k : Trie → Trie → Bool) :
    sChunks tm y0 [] tP tN k = k tP tN := rfl
theorem sChunks_cons (tm y0 : Nat) (ops : List Op) (cs : List (List Op)) (tP tN : Trie)
    (k : Trie → Trie → Bool) :
    sChunks tm y0 (ops :: cs) tP tN k
      = sOps tm y0 ops tP tN fun tP' tN' => sChunks tm y0 cs tP' tN' k := rfl

/-- the gates of the scatter row of the target role `t` -/
def scatRowM (v : Nat) (ret : List Nat) (t : Nat) (l : List (Nat × Coef)) : List Micro :=
  l.map fun x => Micro.add t (v + ret.getD x.1 0) x.2

/-- the gates of the scatter rows of the target roles `t, t+1, ..` -/
def scatFromM (v : Nat) (ret : List Nat) : Nat → List (List (Nat × Coef)) → List Micro
  | _, [] => []
  | t, l :: rows => scatRowM v ret t l ++ scatFromM v ret (t+1) rows

theorem sScatRow_cons (tm y0 v : Nat) (ret : List Nat) (t : Nat) (x : Nat × Coef) (l : List (Nat × Coef))
    (tP tN : Trie) (k : Trie → Trie → Bool) :
    sScatRow tm y0 v ret t (x :: l) tP tN k
      = sAdd tm y0 t (Nat.add v (ret.getD x.1 0)) x.2 tP tN
          fun tP' tN' => sScatRow tm y0 v ret t l tP' tN' k := rfl

theorem sScat_cons (tm y0 v : Nat) (ret : List Nat) (l : List (Nat × Coef)) (rows : List (List (Nat × Coef)))
    (t : Nat) (tP tN : Trie) (k : Trie → Trie → Bool) :
    sScat tm y0 v ret (l :: rows) t tP tN k
      = sScatRow tm y0 v ret t l tP tN fun tP' tN' =>
          forceN (Nat.succ t) fun t2 => sScat tm y0 v ret rows t2 tP' tN' k := rfl

section
variable (d sw v tm y0 : Nat) (hsw : 1 ≤ sw) (htm : tm = rep sw v <<< (sw - 1))
include hsw htm

/-! ## one target row -/

theorem sRow_sound (t : Nat) (srcs : List Part) : ∀ (cfs : List Coef) (tP tN : Trie)
    (k : Trie → Trie → Bool), TOk d sw v tP tN → sRow tm y0 t srcs cfs tP tN k = true →
    ∃ tP' tN', TOk d sw v tP' tN' ∧ k tP' tN' = true ∧
      SRun sw v y0 (absT d tP tN) (gatesRow t srcs cfs) (absT d tP' tN') := by
  induction srcs with
  | nil =>
    intro cfs tP tN k hI h
    exact ⟨tP, tN, hI, h, rfl⟩
  | cons s ss ih =>
    intro cfs tP tN k hI h
    cases cfs with
    | nil =>
      rw [sRow_cons_nil] at h
      obtain ⟨tP1, tN1, hI1, hk1, hst⟩ := sAdd_sound d sw v tm y0 hsw htm t s.role _ tP tN hI _ h
      obtain ⟨tP2, tN2, hI2, hk2, hrun⟩ := ih [] tP1 tN1 k hI1 hk1
      exact ⟨tP2, tN2, hI2, hk2, ⟨absT d tP1 tN1, hst, hrun⟩⟩
    | cons cf cs =>
      rw [sRow_cons_cons] at h
      obtain ⟨tP1, tN1, hI1, hk1, hst⟩ := sAdd_sound d sw v tm y0 hsw htm t s.role cf tP tN hI _ h
      obtain ⟨tP2, tN2, hI2, hk2, hrun⟩ := ih cs tP1 tN1 k hI1 hk1
      exact ⟨tP2, tN2, hI2, hk2, ⟨absT d tP1 tN1, hst, hrun⟩⟩

/-! ## all gates of an op -/

theorem sGates_sound (srcs tgts : List Part) : ∀ (rows : List (List Coef)) (tP tN : Trie)
    (k : Trie → Trie → Bool), TOk d sw v tP tN → sGates tm y0 srcs tgts rows tP tN k = true →
    ∃ tP' tN', TOk d sw v tP' tN' ∧ k tP' tN' = true ∧
      SRun sw v y0 (absT d tP tN) (gatesM srcs tgts rows) (absT d tP' tN') := by
  induction tgts with
  | nil =>
    intro rows tP tN k hI h
    exact ⟨tP, tN, hI, h, rfl⟩
  | cons t ts ih =>
    intro rows tP tN k hI h
    cases rows with
    | nil =>
      rw [sGates_cons_nil] at h
      obtain ⟨tP1, tN1, hI1, hk1, hr1⟩ := sRow_sound d sw v tm y0 hsw htm t.role srcs [] tP tN _ hI h
      obtain ⟨tP2, tN2, hI2, hk2, hr2⟩ := ih [] tP1 tN1 k hI1 hk1
      exact ⟨tP2, tN2, hI2, hk2, SRun_append sw v y0 _ _ _ _ _ hr1 hr2⟩
    | cons row rs =>
      rw [sGates_cons_cons] at h
      obtain ⟨tP1, tN1, hI1, hk1, hr1⟩ := sRow_sound d sw v tm y0 hsw htm t.role srcs row tP tN _ hI h
      obtain ⟨tP2, tN2, hI2, hk2, hr2⟩ := ih rs tP1 tN1 k hI1 hk1
      exact ⟨tP2, tN2, hI2, hk2, SRun_append sw v y0 _ _ _ _ _ hr1 hr2⟩

/-! ## ops, lists of ops, chunks -/

theorem sOp_sound (op : Op) (tP tN : Trie) (k : Trie → Trie → Bool) (hI : TOk d sw v tP tN)
    (h : sOp tm y0 op tP tN k = true) :
    ∃ tP' tN', TOk d sw v tP' tN' ∧ k tP' tN' = true ∧
      SRun sw v y0 (absT d tP tN) op.micro (absT d tP' tN') := by
  cases op with
  | bip srcs tgts coefs =>
    have h' : sGates tm y0 srcs tgts coefs tP tN k = true := h
    obtain ⟨tP1, tN1, hI1, hk1, hr1⟩ := sGates_sound d sw v tm y0 hsw htm srcs tgts coefs tP tN k hI h'
    refine ⟨tP1, tN1, hI1, hk1, ?_⟩
    have hmv : SRun sw v y0 (absT d tP tN) ((srcs ++ tgts).flatMap Part.micro) (absT d tP tN) :=
      SRun_moves sw v y0 _ (fun m hm => by
        obtain ⟨pt, _, hpt⟩ := List.mem_flatMap.mp hm
        obtain ⟨z, e⟩ := mem_part_micro pt m hpt
        exact ⟨pt.role, z, e⟩) _
    exact SRun_append sw v y0 _ _ _ _ _ hmv hr1
  | copy _ _ => exact absurd h Bool.false_ne_true
  | copyNew _ _ => exact absurd h Bool.false_ne_true
  | erase _ => exact absurd h Bool.false_ne_true
  | expect r e => exact ⟨tP, tN, hI, h, rfl⟩

theorem sOps_sound (ops : List Op) : ∀ (tP tN : Trie) (k : Trie → Trie → Bool),
    TOk d sw v tP tN → sOps tm y0 ops tP tN k = true →
    ∃ tP' tN', TOk d sw v tP' tN' ∧ k tP' tN' = true ∧
      SRun sw v y0 (absT d tP tN) (ops.flatMap Op.micro) (absT d tP' tN') := by
  induction ops with
  | nil =>
    intro tP tN k hI h
    exact ⟨tP, tN, hI, h, rfl⟩
  | cons op ops ih =>
    intro tP tN k hI h
    rw [sOps_cons] at h
    obtain ⟨tP1, tN1, hI1, hk1, hr1⟩ := sOp_sound d sw v tm y0 hsw htm op tP tN _ hI h
    obtain ⟨tP2, tN2, hI2, hk2, hr2⟩ := ih tP1 tN1 k hI1 hk1
    refine ⟨tP2, tN2, hI2, hk2, ?_⟩
    rw [List.flatMap_cons]
    exact SRun_append sw v y0 _ _ _ _ _ hr1 hr2

theorem sChunks_sound (cs : List (List Op)) : ∀ (tP tN : Trie) (k : Trie → Trie → Bool),
    TOk d sw v tP tN → sChunks tm y0 cs tP tN k = true →
    ∃ tP' tN', TOk d sw v tP' tN' ∧ k tP' tN' = true ∧
      SRun sw v y0 (absT d tP tN) (cs.flatten.flatMap Op.micro) (absT d tP' tN') := by
  induction cs with
  | nil =>
    intro tP tN k hI h
    exact ⟨tP, tN, hI, h, rfl⟩
  | cons ops cs ih =>
    intro tP tN k hI h
    rw [sChunks_cons] at h
    obtain ⟨tP1, tN1, hI1, hk1, hr1⟩ := sOps_sound d sw v tm y0 hsw htm ops tP tN _ hI h
    obtain ⟨tP2, tN2, hI2, hk2, hr2⟩ := ih tP1 tN1 k hI1 hk1
    refine ⟨tP2, tN2, hI2, hk2, ?_⟩
    rw [List.flatten_cons, List.flatMap_append]
    exact SRun_append sw v y0 _ _ _ _ _ hr1 hr2

/-! ## the scatter rows -/

theorem sScatRow_sound (ret : List Nat) (t : Nat) (l : List (Nat × Coef)) :
    ∀ (tP tN : Trie) (k : Trie → Trie → Bool), TOk d sw v tP tN →
    sScatRow tm y0 v ret t l tP tN k = true →
    ∃ tP' tN', TOk d sw v tP' tN' ∧ k tP' tN' = true ∧
      SRun sw v y0 (absT d tP tN) (scatRowM v ret t l) (absT d tP' tN') := by
  induction l with
  | nil =>
    intro tP tN k hI h
    exact ⟨tP, tN, hI, h, rfl⟩
  | cons x l ih =>
    intro tP tN k hI h
    rw [sScatRow_cons] at h
    obtain ⟨tP1, tN1, hI1, hk1, hst⟩ :=
      sAdd_sound d sw v tm y0 hsw htm t (v + ret.getD x.1 0) x.2 tP tN hI _ h
    obtain ⟨tP2, tN2, hI2, hk2, hrun⟩ := ih tP1 tN1 k hI1 hk1
    exact ⟨tP2, tN2, hI2, hk2, ⟨absT d tP1 tN1, hst, hrun⟩⟩

theorem sScat_sound (ret : List Nat) (rows : List (List (Nat × Coef))) :
    ∀ (t : Nat) (tP tN : Trie) (k : Trie → Trie → Bool), TOk d sw v tP tN →
    sScat tm y0 v ret rows t tP tN k = true →
    ∃ tP' tN', TOk d sw v tP' tN' ∧ k tP' tN' = true ∧
      SRun sw v y0 (absT d tP tN) (scatFromM v ret t rows) (absT d tP' tN') := by
  induction rows with
  | nil =>
    intro t tP tN k hI h
    exact ⟨tP, tN, hI, h, rfl⟩
  | cons l rows ih =>
    intro t tP tN k hI h
    rw [sScat_cons] at h
    obtain ⟨tP1, tN1, hI1, hk1, hr1⟩ := sScatRow_sound d sw v tm y0 hsw htm ret t l tP tN _ hI h
    rw [forceN_eq] at hk1
    obtain ⟨tP2, tN2, hI2, hk2, hr2⟩ := ih (t+1) tP1 tN1 k hI1 hk1
    exact ⟨tP2, tN2, hI2, hk2, SRun_append sw v y0 _ _ _ _ _ hr1 hr2⟩

end

end SSC
