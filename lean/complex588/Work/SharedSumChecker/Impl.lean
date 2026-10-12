import Work.SharedSumChecker.Sound

/-!
# Shared-sum checker: the checker of `Check.lean` is sound

`check p inits cs fs N = true` implies that the micro-expansion of the certificate is `Ok`
(every gate at one common label), hence (`micro_sound`) the engine word is a `Route` with
exactly `N` paid moves.  Main result: `check_sound`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace SSC
open OAI.PowerSaving.Binary OAI.PowerSaving.RAM

/-! ## small facts -/

theorem beq_true {a b : Nat} (h : Nat.beq a b = true) : a = b := Eq.mp Nat.beq_eq h
theorem ble_true {a b : Nat} (h : Nat.ble a b = true) : a ≤ b := Eq.mp Nat.ble_eq h

theorem guard_true {b k : Bool} (h : guard b k = true) : b = true ∧ k = true := by
  cases b with
  | false => exact absurd h Bool.false_ne_true
  | true => exact ⟨rfl, h⟩

/-! ## the role table -/

def Trie.get : Trie → Nat → Nat
  | .leaf v, _ => v
  | .node l r, k => if k % 2 = 0 then l.get (k/2) else r.get (k/2)

def Trie.wf : Nat → Trie → Prop
  | 0, .leaf _ => True
  | d+1, .node l r => Trie.wf d l ∧ Trie.wf d r
  | _, _ => False

theorem Trie.getK_leaf (v key : Nat) (k : Nat → Bool) :
    (Trie.leaf v).getK key k = if key = 0 then k v else false := by
  cases key <;> rfl

theorem Trie.getK_node (l r : Trie) (key : Nat) (k : Nat → Bool) :
    (Trie.node l r).getK key k = if key % 2 = 0 then l.getK (key/2) k else r.getK (key/2) k := by
  have h1 : Nat.shiftRight key 1 = key / 2 := Nat.shiftRight_one key
  have h2 : Nat.land key 1 = key % 2 := Nat.and_one_is_mod key
  show Bool.rec (motive := fun _ => Bool) (r.getK (Nat.shiftRight key 1) k)
    (l.getK (Nat.shiftRight key 1) k) (Nat.beq (Nat.land key 1) 0) = _
  rw [h1, h2]
  rcases Nat.mod_two_eq_zero_or_one key with h | h <;> rw [h] <;> rfl

theorem Trie.set_leaf (v key x : Nat) : (Trie.leaf v).set key x = .leaf x := rfl

theorem Trie.set_node (l r : Trie) (key x : Nat) :
    (Trie.node l r).set key x =
      if key % 2 = 0 then .node (l.set (key/2) x) r else .node l (r.set (key/2) x) := by
  have h1 : Nat.shiftRight key 1 = key / 2 := Nat.shiftRight_one key
  have h2 : Nat.land key 1 = key % 2 := Nat.and_one_is_mod key
  show Bool.rec (motive := fun _ => Trie) (.node l (r.set (Nat.shiftRight key 1) x))
    (.node (l.set (Nat.shiftRight key 1) x) r) (Nat.beq (Nat.land key 1) 0) = _
  rw [h1, h2]
  rcases Nat.mod_two_eq_zero_or_one key with h | h <;> rw [h] <;> rfl

theorem Trie.getK_eq (d : Nat) (t : Trie) (hwf : t.wf d) (key : Nat) (k : Nat → Bool) :
    t.getK key k = (decide (key < 2^d) && k (t.get key)) := by
  induction d generalizing t key with
  | zero =>
    cases t with
    | leaf v =>
      rw [Trie.getK_leaf]
      by_cases h : key = 0
      · subst h; simp [Trie.get]
      · have h' : ¬ key < 2^0 := by simpa using h
        simp [h, h']
    | node l r => exact False.elim hwf
  | succ d ih =>
    cases t with
    | leaf v => exact False.elim hwf
    | node l r =>
      obtain ⟨hl, hr⟩ := hwf
      rw [Trie.getK_node]
      have hlt : (key / 2 < 2^d) ↔ (key < 2^(d+1)) := by rw [pow_succ]; omega
      by_cases h : key % 2 = 0
      · rw [if_pos h, ih l hl]; simp [Trie.get, h, hlt]
      · rw [if_neg h, ih r hr]; simp [Trie.get, h, hlt]

theorem Trie.wf_set (d : Nat) (t : Trie) (hwf : t.wf d) (key x : Nat) : (t.set key x).wf d := by
  induction d generalizing t key with
  | zero =>
    cases t with
    | leaf v => exact trivial
    | node l r => exact False.elim hwf
  | succ d ih =>
    cases t with
    | leaf v => exact False.elim hwf
    | node l r =>
      obtain ⟨hl, hr⟩ := hwf
      rw [Trie.set_node]
      by_cases h : key % 2 = 0
      · rw [if_pos h]; exact ⟨ih l hl _, hr⟩
      · rw [if_neg h]; exact ⟨hl, ih r hr _⟩

theorem Trie.get_set (d : Nat) (t : Trie) (hwf : t.wf d) (key key' x : Nat) (hk : key < 2^d)
    (hk' : key' < 2^d) : (t.set key x).get key' = if key' = key then x else t.get key' := by
  induction d generalizing t key key' with
  | zero =>
    cases t with
    | leaf v =>
      have h1 : key = 0 := by simpa using hk
      have h2 : key' = 0 := by simpa using hk'
      subst h1; subst h2; rfl
    | node l r => exact False.elim hwf
  | succ d ih =>
    cases t with
    | leaf v => exact False.elim hwf
    | node l r =>
      obtain ⟨hl, hr⟩ := hwf
      have hk2 : key / 2 < 2^d := by rw [pow_succ] at hk; omega
      have hk2' : key' / 2 < 2^d := by rw [pow_succ] at hk'; omega
      rw [Trie.set_node]
      by_cases h : key % 2 = 0 <;> by_cases h' : key' % 2 = 0
      · rw [if_pos h]
        simp only [Trie.get, h', ↓reduceIte]
        rw [ih l hl _ _ hk2 hk2']
        have e : (key'/2 = key/2) ↔ (key' = key) := by omega
        simp only [e]
      · rw [if_pos h]
        simp only [Trie.get, h', ↓reduceIte]
        have e : key' ≠ key := by omega
        rw [if_neg e]
      · rw [if_neg h]
        simp only [Trie.get, h', ↓reduceIte]
        have e : key' ≠ key := by omega
        rw [if_neg e]
      · rw [if_neg h]
        simp only [Trie.get, h', ↓reduceIte]
        rw [ih r hr _ _ hk2 hk2']
        have e : (key'/2 = key/2) ↔ (key' = key) := by omega
        simp only [e]

theorem Trie.wf_mk (d : Nat) : (Trie.mk d).wf d := by
  induction d with
  | zero => exact trivial
  | succ d ih => exact ⟨ih, ih⟩

theorem Trie.get_mk (d key : Nat) : (Trie.mk d).get key = 0 := by
  induction d generalizing key with
  | zero => rfl
  | succ d ih => simp [Trie.mk, Trie.get, ih]

/-- labels of the roles `< 2^d` as a function -/
def absL (p : Par) (t : Trie) : Nat → Nat := fun r => if r < p.n then dec (t.get r) else 0

theorem absL_apply (p : Par) (t : Trie) (r : Nat) (hr : r < p.n) : absL p t r = dec (t.get r) := by
  show (if r < p.n then dec (t.get r) else 0) = _
  rw [if_pos hr]

theorem absL_set (p : Par) (t : Trie) (hwf : t.wf p.d) (r P : Nat) (hr : r < p.n) :
    absL p (t.set r P) = Function.update (absL p t) r (dec P) := by
  funext r'
  rw [Function.update_apply]
  show (if r' < p.n then dec ((t.set r P).get r') else 0)
    = if r' = r then dec P else (if r' < p.n then dec (t.get r') else 0)
  by_cases h : r' < p.n
  · rw [if_pos h, Trie.get_set p.d t hwf r r' P hr h]
    by_cases e : r' = r
    · rw [if_pos e, if_pos e]
    · rw [if_neg e, if_neg e, if_pos h]
  · rw [if_neg h]
    have e : r' ≠ r := by omega
    rw [if_neg e, if_neg h]

/-! ## micro-expansion of a certificate -/

def dirsM (r : Nat) (dirs : List Nat) : List Micro := dirs.map (Micro.dir r)

def Part.micro : Part → List Micro
  | .old r dirs sh => dirsM r dirs ++ [.shift r sh]
  | .new r dirs sh => dirsM r dirs ++ [.shift r sh]
  | .stay _ => []

/-- coefficient `1` (default when the table of coefficients is shorter than the gate) -/
def Coef.one : Coef := ⟨false, 1, 1⟩

/-- gates `t += c_j * src_j` -/
def gatesRow (t : Nat) : List Part → List Coef → List Micro
  | [], _ => []
  | s :: ss, [] => .add t s.role Coef.one :: gatesRow t ss []
  | s :: ss, c :: cs => .add t s.role c :: gatesRow t ss cs

def gatesM (srcs : List Part) : List Part → List (List Coef) → List Micro
  | [], _ => []
  | t :: ts, [] => gatesRow t.role srcs [] ++ gatesM srcs ts []
  | t :: ts, row :: rows => gatesRow t.role srcs row ++ gatesM srcs ts rows

def Op.micro : Op → List Micro
  | .bip srcs tgts coefs => (srcs ++ tgts).flatMap Part.micro ++ gatesM srcs tgts coefs
  | .copy s d => [.copy s d]
  | .copyNew s d => [.copy s d]
  | .erase d => [.erase d]
  | .expect r e => [.expect r e]

def FinE.micro (fe : FinE) : List Micro := dirsM fe.r fe.dirs ++ [.shift fe.r fe.sh]

/-- the micro-program of a certificate -/
def expand (cs : List (List Op)) (fs : List (List FinE)) : List Micro :=
  cs.flatten.flatMap Op.micro ++ fs.flatten.flatMap FinE.micro

/-! ## frame changes -/

def foldU (p : Par) (L : Nat) (dirs : List Nat) : Nat :=
  dirs.foldl (fun L z => upd p L (spread p z) z) L

theorem applyDirs_nil (p : Par) (P c : Nat) (k : Nat → Nat → Bool) :
    applyDirs p [] P c k = k P c := rfl

theorem applyDirs_cons (p : Par) (z : Nat) (zs : List Nat) (P c : Nat) (k : Nat → Nat → Bool) :
    applyDirs p (z :: zs) P c k = Bool.rec (motive := fun _ => Bool)
      (forceN (updE p P z) fun P' => applyDirs p zs P' (Nat.succ c) k) false
      (Nat.beq (Nat.land z p.hm) 0) := rfl

theorem applyDirs_sound (p : Par) (dirs : List Nat) (P c : Nat) (k : Nat → Nat → Bool)
    (h : applyDirs p dirs P c k = true) :
    (∀ z ∈ dirs, z &&& p.hm ≠ 0) ∧
      ∃ P', dec P' = foldU p (dec P) dirs ∧ k P' (c + dirs.length) = true := by
  induction dirs generalizing P c with
  | nil => exact ⟨by simp, P, rfl, h⟩
  | cons z zs ih =>
    rw [applyDirs_cons] at h
    by_cases h0 : Nat.land z p.hm = 0
    · rw [h0] at h; exact absurd h Bool.false_ne_true
    · have hb : Nat.beq (Nat.land z p.hm) 0 = false := by
        cases hb : Nat.beq (Nat.land z p.hm) 0 with
        | false => rfl
        | true => exact absurd (beq_true hb) h0
      rw [hb, forceN_eq] at h
      obtain ⟨hz, P', hP', hk⟩ := ih _ _ h
      refine ⟨?_, P', ?_, ?_⟩
      · intro z' hz'
        rcases List.mem_cons.mp hz' with e | e
        · rw [e]; exact h0
        · exact hz z' e
      · rw [hP']
        show foldU p (dec (enc (upd p (dec P) (spread p z) z))) zs = _
        rw [dec_enc]; rfl
      · rw [List.length_cons]
        have e : c + (zs.length + 1) = Nat.succ c + zs.length := by omega
        rw [e]; exact hk

theorem dirs_ok (p : Par) (r : Nat) (hr : r < p.n) (dirs : List Nat)
    (hz : ∀ z ∈ dirs, z &&& p.hm ≠ 0) (lab : Nat → Nat) :
    Ok p lab (dirsM r dirs) ∧
      runLab p lab (dirsM r dirs) = Function.update lab r (foldU p (lab r) dirs) ∧
      countM (dirsM r dirs) = dirs.length := by
  induction dirs generalizing lab with
  | nil =>
    refine ⟨trivial, ?_, rfl⟩
    show lab = Function.update lab r (lab r)
    rw [Function.update_eq_self]
  | cons z zs ih =>
    obtain ⟨h1, h2, h3⟩ := ih (fun z' hz' => hz z' (List.mem_cons_of_mem _ hz'))
      (stepLab p (.dir r z) lab)
    refine ⟨⟨⟨hr, hz z (List.mem_cons_self ..)⟩, h1⟩, ?_, ?_⟩
    · show runLab p (stepLab p (.dir r z) lab) (dirsM r zs) = _
      rw [h2]
      show Function.update (Function.update lab r (upd p (lab r) (spread p z) z)) r
        (foldU p (Function.update lab r (upd p (lab r) (spread p z) z) r) zs) = _
      rw [Function.update_self, Function.update_idem]
      rfl
    · show countM (Micro.dir r z :: dirsM r zs) = _
      rw [countM_cons, h3, List.length_cons]
      show 1 + zs.length = zs.length + 1
      omega

/-- a role makes a frame change (kernel moves `dirs`, then the shift `sh`) -/
theorem move_ok (p : Par) (r : Nat) (hr : r < p.n) (dirs : List Nat) (sh : Nat)
    (hz : ∀ z ∈ dirs, z &&& p.hm ≠ 0) (lab : Nat → Nat) :
    Ok p lab (dirsM r dirs ++ [.shift r sh]) ∧
      runLab p lab (dirsM r dirs ++ [.shift r sh])
        = Function.update lab r (updS p (foldU p (lab r) dirs) sh) ∧
      countM (dirsM r dirs ++ [.shift r sh]) = dirs.length := by
  obtain ⟨h1, h2, h3⟩ := dirs_ok p r hr dirs hz lab
  refine ⟨(Ok_append p lab _ _).mpr ⟨h1, ⟨hr, trivial⟩⟩, ?_, ?_⟩
  · rw [runLab_append, h2]
    show Function.update (Function.update lab r (foldU p (lab r) dirs)) r
      (updS p (Function.update lab r (foldU p (lab r) dirs) r) sh) = _
    rw [Function.update_self, Function.update_idem]
  · rw [countM_append, h3]; rfl

/-! ## one part -/

/-- invariant of the role table: well formed, `f` = next unused role, unused roles at the
zero label -/
def Inv (p : Par) (t : Trie) (f : Nat) : Prop :=
  t.wf p.d ∧ f ≤ p.n ∧ ∀ r, f ≤ r → r < p.n → t.get r = 0

theorem onePart_sound (p : Par) (pt : Part) (t : Trie) (f c : Nat)
    (k : Nat → Trie → Nat → Nat → Bool) (hinv : Inv p t f) (h : onePart p pt t f c k = true) :
    ∃ L t' f', Inv p t' f' ∧ pt.role < p.n ∧ Ok p (absL p t) pt.micro ∧
      runLab p (absL p t) pt.micro = absL p t' ∧
      absL p t' = Function.update (absL p t) pt.role (dec L) ∧
      k L t' f' (c + countM pt.micro) = true := by
  obtain ⟨hwf, hf, hfr⟩ := hinv
  cases pt with
  | old r dirs sh =>
    have h' : guard (Nat.ble (Nat.succ r) f) (t.getK r fun L0 =>
        applyDirs p dirs L0 c fun L1 c1 =>
          forceN (updSE p L1 sh) fun L => forceN c1 fun c2 => k L (t.set r L) f c2) = true := h
    obtain ⟨hg, h1⟩ := guard_true h'
    have hrf : r < f := ble_true hg
    have hr : r < p.n := by omega
    rw [Trie.getK_eq p.d t hwf] at h1
    have h2 : (applyDirs p dirs (t.get r) c fun L1 c1 =>
          forceN (updSE p L1 sh) fun L => forceN c1 fun c2 => k L (t.set r L) f c2) = true := by
      simp only [Bool.and_eq_true] at h1; exact h1.2
    obtain ⟨hz, P', hP', hk⟩ := applyDirs_sound p dirs _ _ _ h2
    rw [forceN_eq, forceN_eq] at hk
    obtain ⟨m1, m2, m3⟩ := move_ok p r hr dirs sh hz (absL p t)
    have hdec : dec (updSE p P' sh) = updS p (foldU p (absL p t r) dirs) sh := by
      show dec (enc (updS p (dec P') sh)) = _
      rw [dec_enc, hP', absL_apply p t r hr]
    have hset : absL p (t.set r (updSE p P' sh))
        = Function.update (absL p t) r (dec (updSE p P' sh)) := absL_set p t hwf r _ hr
    refine ⟨updSE p P' sh, t.set r (updSE p P' sh), f, ⟨Trie.wf_set _ _ hwf _ _, hf, ?_⟩, hr, m1,
      ?_, hset, ?_⟩
    · intro r' h1' h2'
      rw [Trie.get_set p.d t hwf r r' _ hr h2', if_neg (by omega)]
      exact hfr r' h1' h2'
    · rw [hset, hdec]; exact m2
    · show k _ _ f (c + countM (dirsM r dirs ++ [.shift r sh])) = true
      rw [m3]; exact hk
  | new r dirs sh =>
    have h' : guard (Nat.beq r f) (guard (Nat.ble (Nat.succ f) p.n)
        (applyDirs p dirs 0 c fun L1 c1 =>
          forceN (updSE p L1 sh) fun L => forceN c1 fun c2 =>
            forceN (Nat.succ f) fun f2 => k L (t.set r L) f2 c2)) = true := h
    obtain ⟨hg, h1⟩ := guard_true h'
    obtain ⟨hg2, h2⟩ := guard_true h1
    have hrf : r = f := beq_true hg
    have hfn : f < p.n := ble_true hg2
    have hr : r < p.n := by omega
    obtain ⟨hz, P', hP', hk⟩ := applyDirs_sound p dirs _ _ _ h2
    rw [forceN_eq, forceN_eq, forceN_eq] at hk
    have hzero : absL p t r = 0 := by
      rw [absL_apply p t r hr, hfr r (by omega) hr]; rfl
    obtain ⟨m1, m2, m3⟩ := move_ok p r hr dirs sh hz (absL p t)
    have hdec : dec (updSE p P' sh) = updS p (foldU p (absL p t r) dirs) sh := by
      show dec (enc (updS p (dec P') sh)) = _
      rw [dec_enc, hP', hzero]; rfl
    have hset : absL p (t.set r (updSE p P' sh))
        = Function.update (absL p t) r (dec (updSE p P' sh)) := absL_set p t hwf r _ hr
    refine ⟨updSE p P' sh, t.set r (updSE p P' sh), Nat.succ f,
      ⟨Trie.wf_set _ _ hwf _ _, hfn, ?_⟩, hr, m1, ?_, hset, ?_⟩
    · intro r' h1' h2'
      rw [Trie.get_set p.d t hwf r r' _ hr h2', if_neg (by omega)]
      exact hfr r' (by omega) h2'
    · rw [hset, hdec]; exact m2
    · show k _ _ (Nat.succ f) (c + countM (dirsM r dirs ++ [.shift r sh])) = true
      rw [m3]; exact hk
  | stay r =>
    have h' : (t.getK r fun L => k L t f c) = true := h
    rw [Trie.getK_eq p.d t hwf] at h'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
    have hr : r < p.n := h'.1
    refine ⟨t.get r, t, f, ⟨hwf, hf, hfr⟩, hr, trivial, rfl, ?_, h'.2⟩
    show absL p t = Function.update (absL p t) r (dec (t.get r))
    rw [← absL_apply p t r hr, Function.update_eq_self]

/-! ## several parts at one label -/

theorem partsK_nil (p : Par) (l : Nat) (t : Trie) (f c : Nat) (k : Trie → Nat → Nat → Bool) :
    partsK p l [] t f c k = k t f c := rfl

theorem partsK_cons (p : Par) (l : Nat) (pt : Part) (pts : List Part) (t : Trie) (f c : Nat)
    (k : Trie → Nat → Nat → Bool) :
    partsK p l (pt :: pts) t f c k = onePart p pt t f c fun L t' f' c' =>
      guard (Nat.beq L l) (partsK p l pts t' f' c' k) := rfl

theorem partsK_sound (p : Par) (l : Nat) (pts : List Part) (t : Trie) (f c : Nat)
    (k : Trie → Nat → Nat → Bool) (hinv : Inv p t f) (h : partsK p l pts t f c k = true) :
    ∃ t' f', Inv p t' f' ∧ Ok p (absL p t) (pts.flatMap Part.micro) ∧
      runLab p (absL p t) (pts.flatMap Part.micro) = absL p t' ∧
      (∀ pt ∈ pts, pt.role < p.n ∧ absL p t' pt.role = dec l) ∧
      (∀ r, absL p t r = dec l → absL p t' r = dec l) ∧
      k t' f' (c + countM (pts.flatMap Part.micro)) = true := by
  induction pts generalizing t f c with
  | nil => exact ⟨t, f, hinv, trivial, rfl, by simp, fun _ h => h, h⟩
  | cons pt pts ih =>
    rw [partsK_cons] at h
    obtain ⟨L, t1, f1, hinv1, hr, hok1, hrun1, hupd1, hk1⟩ := onePart_sound p pt t f c _ hinv h
    obtain ⟨hb, hk2⟩ := guard_true hk1
    have hL : L = l := beq_true hb
    obtain ⟨t2, f2, hinv2, hok2, hrun2, hall2, hpres2, hk3⟩ := ih t1 f1 _ hinv1 hk2
    have hpt : absL p t1 pt.role = dec l := by rw [hupd1, Function.update_self, hL]
    refine ⟨t2, f2, hinv2, ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.flatMap_cons, Ok_append]; exact ⟨hok1, by rw [hrun1]; exact hok2⟩
    · rw [List.flatMap_cons, runLab_append, hrun1, hrun2]
    · intro q hq
      rcases List.mem_cons.mp hq with e | e
      · rw [e]; exact ⟨hr, hpres2 _ hpt⟩
      · exact hall2 q e
    · intro r hrl
      apply hpres2
      rw [hupd1, Function.update_apply]
      by_cases e : r = pt.role
      · rw [if_pos e, hL]
      · rw [if_neg e]; exact hrl
    · rw [List.flatMap_cons, countM_append, ← Nat.add_assoc]; exact hk3

/-! ## gates -/

theorem gatesRow_ok (p : Par) (lab : Nat → Nat) (x : Nat) (t : Nat) (ht : t < p.n) (hlt : lab t = x)
    (srcs : List Part) (hs : ∀ s ∈ srcs, s.role < p.n ∧ lab s.role = x) (row : List Coef) :
    Ok p lab (gatesRow t srcs row) ∧ runLab p lab (gatesRow t srcs row) = lab ∧
      countM (gatesRow t srcs row) = 0 := by
  induction srcs generalizing row with
  | nil => exact ⟨trivial, rfl, rfl⟩
  | cons s ss ih =>
    have hs0 := hs s (List.mem_cons_self ..)
    have ih' := fun row => ih (fun s' h' => hs s' (List.mem_cons_of_mem _ h')) row
    cases row with
    | nil =>
      obtain ⟨a, b, c⟩ := ih' []
      exact ⟨⟨⟨ht, hs0.1, hlt.trans hs0.2.symm⟩, a⟩, b, by
        show countM (Micro.add t s.role Coef.one :: gatesRow t ss []) = 0
        rw [countM_cons, c]; rfl⟩
    | cons cf cs =>
      obtain ⟨a, b, c⟩ := ih' cs
      exact ⟨⟨⟨ht, hs0.1, hlt.trans hs0.2.symm⟩, a⟩, b, by
        show countM (Micro.add t s.role cf :: gatesRow t ss cs) = 0
        rw [countM_cons, c]; rfl⟩

theorem gatesM_ok (p : Par) (lab : Nat → Nat) (x : Nat) (srcs : List Part)
    (hs : ∀ s ∈ srcs, s.role < p.n ∧ lab s.role = x) (tgts : List Part)
    (ht : ∀ s ∈ tgts, s.role < p.n ∧ lab s.role = x) (coefs : List (List Coef)) :
    Ok p lab (gatesM srcs tgts coefs) ∧ runLab p lab (gatesM srcs tgts coefs) = lab ∧
      countM (gatesM srcs tgts coefs) = 0 := by
  induction tgts generalizing coefs with
  | nil => exact ⟨trivial, rfl, rfl⟩
  | cons t ts ih =>
    have ht0 := ht t (List.mem_cons_self ..)
    have ih' := fun cf => ih (fun s' h' => ht s' (List.mem_cons_of_mem _ h')) cf
    cases coefs with
    | nil =>
      obtain ⟨a, b, c⟩ := gatesRow_ok p lab x t.role ht0.1 ht0.2 srcs hs []
      obtain ⟨a', b', c'⟩ := ih' []
      refine ⟨?_, ?_, ?_⟩
      · show Ok p lab (gatesRow t.role srcs [] ++ gatesM srcs ts [])
        rw [Ok_append, b]; exact ⟨a, a'⟩
      · show runLab p lab (gatesRow t.role srcs [] ++ gatesM srcs ts []) = lab
        rw [runLab_append, b, b']
      · show countM (gatesRow t.role srcs [] ++ gatesM srcs ts []) = 0
        rw [countM_append, c, c']
    | cons row rows =>
      obtain ⟨a, b, c⟩ := gatesRow_ok p lab x t.role ht0.1 ht0.2 srcs hs row
      obtain ⟨a', b', c'⟩ := ih' rows
      refine ⟨?_, ?_, ?_⟩
      · show Ok p lab (gatesRow t.role srcs row ++ gatesM srcs ts rows)
        rw [Ok_append, b]; exact ⟨a, a'⟩
      · show runLab p lab (gatesRow t.role srcs row ++ gatesM srcs ts rows) = lab
        rw [runLab_append, b, b']
      · show countM (gatesRow t.role srcs row ++ gatesM srcs ts rows) = 0
        rw [countM_append, c, c']

/-! ## ops -/

theorem opK_sound (p : Par) (op : Op) (t : Trie) (f c : Nat) (k : Trie → Nat → Nat → Bool)
    (hinv : Inv p t f) (h : opK p op t f c k = true) :
    ∃ t' f', Inv p t' f' ∧ Ok p (absL p t) op.micro ∧
      runLab p (absL p t) op.micro = absL p t' ∧ k t' f' (c + countM op.micro) = true := by
  cases op with
  | bip srcs tgts coefs =>
    cases srcs with
    | nil => exact absurd h Bool.false_ne_true
    | cons s0 rest =>
      have h' : (onePart p s0 t f c fun l t1 f1 c1 =>
          partsK p l rest t1 f1 c1 fun t2 f2 c2 => partsK p l tgts t2 f2 c2 k) = true := h
      obtain ⟨l, t1, f1, hinv1, hr0, hok1, hrun1, hupd1, hk1⟩ := onePart_sound p s0 t f c _ hinv h'
      obtain ⟨t2, f2, hinv2, hok2, hrun2, hall2, hpres2, hk2⟩ :=
        partsK_sound p l rest t1 f1 _ _ hinv1 hk1
      obtain ⟨t3, f3, hinv3, hok3, hrun3, hall3, hpres3, hk3⟩ :=
        partsK_sound p l tgts t2 f2 _ _ hinv2 hk2
      have h0 : absL p t1 s0.role = dec l := by rw [hupd1, Function.update_self]
      have hsrc : ∀ s ∈ s0 :: rest, s.role < p.n ∧ absL p t3 s.role = dec l := by
        intro s hs
        rcases List.mem_cons.mp hs with e | e
        · rw [e]; exact ⟨hr0, hpres3 _ (hpres2 _ h0)⟩
        · exact ⟨(hall2 s e).1, hpres3 _ (hall2 s e).2⟩
      obtain ⟨g1, g2, g3⟩ := gatesM_ok p (absL p t3) (dec l) (s0 :: rest) hsrc tgts hall3 coefs
      have hparts : runLab p (absL p t) ((s0 :: rest ++ tgts).flatMap Part.micro) = absL p t3 := by
        rw [List.cons_append, List.flatMap_cons, List.flatMap_append, runLab_append, hrun1,
          runLab_append, hrun2, hrun3]
      refine ⟨t3, f3, hinv3, ?_, ?_, ?_⟩
      · show Ok p (absL p t) ((s0 :: rest ++ tgts).flatMap Part.micro ++ gatesM (s0 :: rest) tgts coefs)
        rw [Ok_append, hparts]
        refine ⟨?_, g1⟩
        rw [List.cons_append, List.flatMap_cons, List.flatMap_append, Ok_append, hrun1, Ok_append,
          hrun2]
        exact ⟨hok1, hok2, hok3⟩
      · show runLab p (absL p t)
          ((s0 :: rest ++ tgts).flatMap Part.micro ++ gatesM (s0 :: rest) tgts coefs) = _
        rw [runLab_append, hparts, g2]
      · show k t3 f3 (c + countM
          ((s0 :: rest ++ tgts).flatMap Part.micro ++ gatesM (s0 :: rest) tgts coefs)) = true
        rw [countM_append, g3, Nat.add_zero, List.cons_append, List.flatMap_cons,
          List.flatMap_append, countM_append, countM_append, ← Nat.add_assoc, ← Nat.add_assoc]
        exact hk3
  | copy s d =>
    obtain ⟨hwf, hf, hfr⟩ := hinv
    have h' : guard (Nat.ble (Nat.succ d) f) (t.getK s fun L => k (t.set d L) f c) = true := h
    obtain ⟨hg, h1⟩ := guard_true h'
    have hdf : d < f := ble_true hg
    have hd : d < p.n := by omega
    rw [Trie.getK_eq p.d t hwf] at h1
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    have hs : s < p.n := h1.1
    refine ⟨t.set d (t.get s), f, ⟨Trie.wf_set _ _ hwf _ _, hf, ?_⟩, ⟨⟨hs, hd⟩, trivial⟩, ?_, h1.2⟩
    · intro r' h1' h2'
      rw [Trie.get_set p.d t hwf d r' _ hd h2', if_neg (by omega)]
      exact hfr r' h1' h2'
    · show Function.update (absL p t) d (absL p t s) = _
      rw [absL_set p t hwf d _ hd, absL_apply p t s hs]
  | copyNew s d =>
    obtain ⟨hwf, hf, hfr⟩ := hinv
    have h' : guard (Nat.beq d f) (guard (Nat.ble (Nat.succ f) p.n)
        (t.getK s fun L => forceN (Nat.succ f) fun f2 => k (t.set d L) f2 c)) = true := h
    obtain ⟨hg, h1⟩ := guard_true h'
    obtain ⟨hg2, h2⟩ := guard_true h1
    have hdf : d = f := beq_true hg
    have hfn : f < p.n := ble_true hg2
    have hd : d < p.n := by omega
    rw [Trie.getK_eq p.d t hwf] at h2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
    have hs : s < p.n := h2.1
    have hk := h2.2
    rw [forceN_eq] at hk
    refine ⟨t.set d (t.get s), Nat.succ f, ⟨Trie.wf_set _ _ hwf _ _, hfn, ?_⟩,
      ⟨⟨hs, hd⟩, trivial⟩, ?_, hk⟩
    · intro r' h1' h2'
      rw [Trie.get_set p.d t hwf d r' _ hd h2', if_neg (by omega)]
      exact hfr r' (by omega) h2'
    · show Function.update (absL p t) d (absL p t s) = _
      rw [absL_set p t hwf d _ hd, absL_apply p t s hs]
  | erase d =>
    exact ⟨t, f, hinv, ⟨trivial, trivial⟩, rfl, h⟩
  | expect r e =>
    have h' : (t.getK r fun L => guard (Nat.beq L e) (k t f c)) = true := h
    rw [Trie.getK_eq p.d t hinv.1] at h'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
    have hr : r < p.n := h'.1
    obtain ⟨hb, hk⟩ := guard_true h'.2
    have he : absL p t r = dec e := by rw [absL_apply p t r hr, beq_true hb]
    exact ⟨t, f, hinv, ⟨⟨hr, he⟩, trivial⟩, rfl, hk⟩

theorem opsK_nil (p : Par) (t : Trie) (f c : Nat) (k : Trie → Nat → Nat → Bool) :
    opsK p [] t f c k = k t f c := rfl

theorem opsK_cons (p : Par) (op : Op) (ops : List Op) (t : Trie) (f c : Nat)
    (k : Trie → Nat → Nat → Bool) :
    opsK p (op :: ops) t f c k = opK p op t f c fun t' f' c' => opsK p ops t' f' c' k := rfl

theorem opsK_sound (p : Par) (ops : List Op) (t : Trie) (f c : Nat) (k : Trie → Nat → Nat → Bool)
    (hinv : Inv p t f) (h : opsK p ops t f c k = true) :
    ∃ t' f', Inv p t' f' ∧ Ok p (absL p t) (ops.flatMap Op.micro) ∧
      runLab p (absL p t) (ops.flatMap Op.micro) = absL p t' ∧
      k t' f' (c + countM (ops.flatMap Op.micro)) = true := by
  induction ops generalizing t f c with
  | nil => exact ⟨t, f, hinv, trivial, rfl, h⟩
  | cons op ops ih =>
    rw [opsK_cons] at h
    obtain ⟨t1, f1, hinv1, hok1, hrun1, hk1⟩ := opK_sound p op t f c _ hinv h
    obtain ⟨t2, f2, hinv2, hok2, hrun2, hk2⟩ := ih t1 f1 _ hinv1 hk1
    refine ⟨t2, f2, hinv2, ?_, ?_, ?_⟩
    · rw [List.flatMap_cons, Ok_append, hrun1]; exact ⟨hok1, hok2⟩
    · rw [List.flatMap_cons, runLab_append, hrun1, hrun2]
    · rw [List.flatMap_cons, countM_append, ← Nat.add_assoc]; exact hk2

theorem chunksK_nil (p : Par) (t : Trie) (f c : Nat) (k : Trie → Nat → Nat → Bool) :
    chunksK p [] t f c k = k t f c := rfl

theorem chunksK_cons (p : Par) (ops : List Op) (cs : List (List Op)) (t : Trie) (f c : Nat)
    (k : Trie → Nat → Nat → Bool) :
    chunksK p (ops :: cs) t f c k = opsK p ops t f c fun t' f' c' => chunksK p cs t' f' c' k := rfl

theorem chunksK_sound (p : Par) (cs : List (List Op)) (t : Trie) (f c : Nat)
    (k : Trie → Nat → Nat → Bool) (hinv : Inv p t f) (h : chunksK p cs t f c k = true) :
    ∃ t' f', Inv p t' f' ∧ Ok p (absL p t) (cs.flatten.flatMap Op.micro) ∧
      runLab p (absL p t) (cs.flatten.flatMap Op.micro) = absL p t' ∧
      k t' f' (c + countM (cs.flatten.flatMap Op.micro)) = true := by
  induction cs generalizing t f c with
  | nil => exact ⟨t, f, hinv, trivial, rfl, h⟩
  | cons ops cs ih =>
    rw [chunksK_cons] at h
    obtain ⟨t1, f1, hinv1, hok1, hrun1, hk1⟩ := opsK_sound p ops t f c _ hinv h
    obtain ⟨t2, f2, hinv2, hok2, hrun2, hk2⟩ := ih t1 f1 _ hinv1 hk1
    refine ⟨t2, f2, hinv2, ?_, ?_, ?_⟩
    · rw [List.flatten_cons, List.flatMap_append, Ok_append, hrun1]; exact ⟨hok1, hok2⟩
    · rw [List.flatten_cons, List.flatMap_append, runLab_append, hrun1, hrun2]
    · rw [List.flatten_cons, List.flatMap_append, countM_append, ← Nat.add_assoc]; exact hk2

/-! ## final frame changes -/

theorem finK_nil (p : Par) (t : Trie) (lb c : Nat) (k : Nat → Nat → Bool) :
    finK p t [] lb c k = k lb c := rfl

theorem finK_cons (p : Par) (t : Trie) (r : Nat) (dirs : List Nat) (sh e : Nat) (fs : List FinE)
    (lb c : Nat) (k : Nat → Nat → Bool) :
    finK p t (⟨r, dirs, sh, e⟩ :: fs) lb c k = guard (Nat.ble lb r) (t.getK r fun L0 =>
      applyDirs p dirs L0 c fun L1 c1 => guard (Nat.beq (updSE p L1 sh) e)
        (forceN c1 fun c2 => forceN (Nat.succ r) fun lb2 => finK p t fs lb2 c2 k)) := rfl

theorem finK_sound (p : Par) (t : Trie) (hwf : t.wf p.d) (fs : List FinE) (lb c : Nat)
    (k : Nat → Nat → Bool) (lab : Nat → Nat) (hlab : ∀ r, lb ≤ r → lab r = absL p t r)
    (h : finK p t fs lb c k = true) :
    ∃ lb', lb ≤ lb' ∧ Ok p lab (fs.flatMap FinE.micro) ∧
      (∀ r, lb' ≤ r → runLab p lab (fs.flatMap FinE.micro) r = absL p t r) ∧
      (∀ r, r < lb → runLab p lab (fs.flatMap FinE.micro) r = lab r) ∧
      (∀ fe ∈ fs, fe.r < p.n ∧ fe.r < lb' ∧
        runLab p lab (fs.flatMap FinE.micro) fe.r = dec fe.e ∧
        dec fe.e = updS p (foldU p (absL p t fe.r) fe.dirs) fe.sh) ∧
      k lb' (c + countM (fs.flatMap FinE.micro)) = true := by
  induction fs generalizing lb c lab with
  | nil => exact ⟨lb, le_refl _, trivial, fun r hr => hlab r hr, fun _ _ => rfl, by simp, h⟩
  | cons fe fs ih =>
    obtain ⟨r, dirs, sh, e⟩ := fe
    rw [finK_cons] at h
    obtain ⟨hg, h1⟩ := guard_true h
    have hlr : lb ≤ r := ble_true hg
    rw [Trie.getK_eq p.d t hwf] at h1
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    have hr : r < p.n := h1.1
    obtain ⟨hz, P', hP', hk⟩ := applyDirs_sound p dirs _ _ _ h1.2
    obtain ⟨hb, hk2⟩ := guard_true hk
    rw [forceN_eq, forceN_eq] at hk2
    obtain ⟨m1, m2, m3⟩ := move_ok p r hr dirs sh hz lab
    have hdec : dec e = updS p (foldU p (lab r) dirs) sh := by
      rw [← beq_true hb]
      show dec (enc (updS p (dec P') sh)) = _
      rw [dec_enc, hP', hlab r hlr, absL_apply p t r hr]
    set lab1 := runLab p lab (dirsM r dirs ++ [.shift r sh]) with hlab1
    have hlab1' : lab1 = Function.update lab r (dec e) := by rw [m2, hdec]
    obtain ⟨lb', hle, hok, hhi, hlo, hall, hkk⟩ := ih (Nat.succ r) _ lab1
      (fun r' hr' => by rw [hlab1', Function.update_of_ne (by omega)]; exact hlab r' (by omega)) hk2
    have hmic : (({ r := r, dirs := dirs, sh := sh, e := e } : FinE) :: fs).flatMap FinE.micro
        = (dirsM r dirs ++ [.shift r sh]) ++ fs.flatMap FinE.micro := by
      rw [List.flatMap_cons]; rfl
    refine ⟨lb', by omega, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hmic, Ok_append]; exact ⟨m1, hok⟩
    · intro r' hr'; rw [hmic, runLab_append]; exact hhi r' hr'
    · intro r' hr'
      rw [hmic, runLab_append, hlo r' (by omega)]
      show lab1 r' = lab r'
      rw [hlab1', Function.update_of_ne (by omega)]
    · intro fe hfe
      rcases List.mem_cons.mp hfe with e' | e'
      · rw [e']
        refine ⟨hr, hle, ?_, ?_⟩
        · rw [hmic, runLab_append]
          show runLab p lab1 (fs.flatMap FinE.micro) r = dec e
          rw [hlo r (Nat.lt_succ_self r), hlab1', Function.update_self]
        · show dec e = updS p (foldU p (absL p t r) dirs) sh
          rw [hdec, hlab r hlr]
      · rw [hmic, runLab_append]; exact hall fe e'
    · rw [hmic, countM_append, m3, ← Nat.add_assoc]; exact hkk

theorem finsK_nil (p : Par) (t : Trie) (lb c : Nat) (k : Nat → Nat → Bool) :
    finsK p t [] lb c k = k lb c := rfl

theorem finsK_cons (p : Par) (t : Trie) (fl : List FinE) (fs : List (List FinE)) (lb c : Nat)
    (k : Nat → Nat → Bool) :
    finsK p t (fl :: fs) lb c k = finK p t fl lb c fun lb2 c2 => finsK p t fs lb2 c2 k := rfl

theorem finsK_sound (p : Par) (t : Trie) (hwf : t.wf p.d) (fs : List (List FinE)) (lb c : Nat)
    (k : Nat → Nat → Bool) (lab : Nat → Nat) (hlab : ∀ r, lb ≤ r → lab r = absL p t r)
    (h : finsK p t fs lb c k = true) :
    ∃ lb', lb ≤ lb' ∧ Ok p lab (fs.flatten.flatMap FinE.micro) ∧
      (∀ r, r < lb → runLab p lab (fs.flatten.flatMap FinE.micro) r = lab r) ∧
      (∀ fl ∈ fs, ∀ fe ∈ fl, fe.r < p.n ∧
        runLab p lab (fs.flatten.flatMap FinE.micro) fe.r = dec fe.e ∧
        dec fe.e = updS p (foldU p (absL p t fe.r) fe.dirs) fe.sh) ∧
      k lb' (c + countM (fs.flatten.flatMap FinE.micro)) = true := by
  induction fs generalizing lb c lab with
  | nil => exact ⟨lb, le_refl _, trivial, fun _ _ => rfl, by simp, h⟩
  | cons fl fs ih =>
    rw [finsK_cons] at h
    obtain ⟨lb1, hle1, hok1, hhi1, hlo1, hall1, hk1⟩ := finK_sound p t hwf fl lb c _ lab hlab h
    obtain ⟨lb2, hle2, hok2, hlo2, hall2, hk2⟩ :=
      ih lb1 _ (runLab p lab (fl.flatMap FinE.micro)) hhi1 hk1
    refine ⟨lb2, by omega, ?_, ?_, ?_, ?_⟩
    · rw [List.flatten_cons, List.flatMap_append, Ok_append]; exact ⟨hok1, hok2⟩
    · intro r hr
      rw [List.flatten_cons, List.flatMap_append, runLab_append, hlo2 r (by omega), hlo1 r hr]
    · intro fl' hfl' fe hfe
      rw [List.flatten_cons, List.flatMap_append, runLab_append]
      rcases List.mem_cons.mp hfl' with e' | e'
      · subst e'
        obtain ⟨a, hlt, b, d⟩ := hall1 fe hfe
        refine ⟨a, ?_, d⟩
        rw [hlo2 fe.r hlt]; exact b
      · exact hall2 fl' e' fe hfe
    · rw [List.flatten_cons, List.flatMap_append, countM_append, ← Nat.add_assoc]; exact hk2


/-! ## initial labels -/

noncomputable def initT : List Nat → Trie → Nat → Trie
  | [], t, _ => t
  | L :: ls, t, i => initT ls (t.set i L) (i+1)

theorem initK_eq (ls : List Nat) (t : Trie) (i : Nat) (k : Trie → Nat → Bool) :
    initK ls t i k = k (initT ls t i) (i + ls.length) := by
  induction ls generalizing t i with
  | nil => rfl
  | cons L ls ih =>
    show (forceN (Nat.succ i) fun i2 => initK ls (t.set i L) i2 k) = _
    rw [forceN_eq, ih, List.length_cons]
    have e : Nat.succ i + ls.length = i + (ls.length + 1) := by omega
    rw [e]; rfl

theorem initT_wf (d : Nat) (ls : List Nat) (t : Trie) (hwf : t.wf d) (i : Nat) :
    (initT ls t i).wf d := by
  induction ls generalizing t i with
  | nil => exact hwf
  | cons L ls ih => exact ih _ (Trie.wf_set d t hwf i L) _

theorem initT_get (d : Nat) (ls : List Nat) (t : Trie) (hwf : t.wf d) (i : Nat)
    (hb : i + ls.length ≤ 2^d) (r : Nat) (hr : r < 2^d) :
    (initT ls t i).get r = if i ≤ r ∧ r < i + ls.length then ls.getD (r - i) 0 else t.get r := by
  induction ls generalizing t i with
  | nil =>
    have h : ¬ (i ≤ r ∧ r < i + ([] : List Nat).length) := by simp
    rw [if_neg h]; rfl
  | cons L ls ih =>
    rw [List.length_cons] at hb
    have hi : i < 2^d := by omega
    show (initT ls (t.set i L) (i+1)).get r = _
    rw [ih (t.set i L) (Trie.wf_set d t hwf i L) (i+1) (by omega),
      Trie.get_set d t hwf i r L hi hr, List.length_cons]
    by_cases h1 : r = i
    · subst h1
      have a : ¬ (r + 1 ≤ r ∧ r < r + 1 + ls.length) := by omega
      have b : r ≤ r ∧ r < r + (ls.length + 1) := by omega
      rw [if_neg a, if_pos rfl, if_pos b, Nat.sub_self]
      rfl
    · by_cases h2 : i + 1 ≤ r ∧ r < i + 1 + ls.length
      · have b : i ≤ r ∧ r < i + (ls.length + 1) := by omega
        have e : r - i = (r - (i+1)) + 1 := by omega
        rw [if_pos h2, if_pos b, e]
        rfl
      · have b : ¬ (i ≤ r ∧ r < i + (ls.length + 1)) := by omega
        rw [if_neg h2, if_neg h1, if_neg b]

/-! ## the main theorems -/

/-- **What an accepted certificate says about its micro-program**: every gate is justified
(`Ok`), the number of paid moves is `N`, and every final entry is reached from the label after
the ops by its own kernel moves and shift. -/
theorem check_micro (p : Par) (inits : List Nat) (cs : List (List Op)) (fs : List (List FinE))
    (N : Nat) (hc : check p inits cs fs N = true) :
    inits.length ≤ p.n ∧ Ok p (fun r => dec (inits.getD r 0)) (expand cs fs) ∧
      countM (expand cs fs) = N ∧
      ∀ fl ∈ fs, ∀ fe ∈ fl, fe.r < p.n ∧
        runLab p (fun r => dec (inits.getD r 0)) (expand cs fs) fe.r = dec fe.e ∧
        dec fe.e = updS p (foldU p
          (runLab p (fun r => dec (inits.getD r 0)) (cs.flatten.flatMap Op.micro) fe.r) fe.dirs) fe.sh := by
  have h1 : (initK inits (Trie.mk p.d) 0 fun t0 f0 => guard (Nat.ble f0 p.n)
      (chunksK p cs t0 f0 0 fun t1 _ c1 => finsK p t1 fs 0 c1 fun _ c2 => Nat.beq c2 N)) = true := hc
  rw [initK_eq] at h1
  obtain ⟨hg, h2⟩ := guard_true h1
  have hlen : 0 + inits.length ≤ p.n := ble_true hg
  have hwf0 : (initT inits (Trie.mk p.d) 0).wf p.d := initT_wf _ _ _ (Trie.wf_mk _) _
  have hget0 : ∀ r, r < p.n → (initT inits (Trie.mk p.d) 0).get r = inits.getD r 0 := by
    intro r hr
    rw [initT_get p.d inits _ (Trie.wf_mk _) 0 hlen r hr]
    by_cases h : 0 ≤ r ∧ r < 0 + inits.length
    · rw [if_pos h, Nat.sub_zero]
    · rw [if_neg h, Trie.get_mk]
      have hle : inits.length ≤ r := by omega
      exact (List.getD_eq_default _ _ hle).symm
  have hinv0 : Inv p (initT inits (Trie.mk p.d) 0) (0 + inits.length) := by
    refine ⟨hwf0, hlen, fun r h1 h2 => ?_⟩
    rw [hget0 r h2]
    exact List.getD_eq_default _ _ (by omega)
  have hlab : absL p (initT inits (Trie.mk p.d) 0) = fun r => dec (inits.getD r 0) := by
    funext r
    by_cases hr : r < p.n
    · rw [absL_apply p _ r hr, hget0 r hr]
    · show (if r < p.n then _ else 0) = _
      rw [if_neg hr, List.getD_eq_default _ _ (by omega)]
      rfl
  obtain ⟨t1, f1, hinv1, hok1, hrun1, hk1⟩ := chunksK_sound p cs _ _ 0 _ hinv0 h2
  obtain ⟨lb', _, hok2, _, hall2, hk2⟩ :=
    finsK_sound p t1 hinv1.1 fs 0 _ _ (absL p t1) (fun r _ => rfl) hk1
  have hN : 0 + countM (cs.flatten.flatMap Op.micro) + countM (fs.flatten.flatMap FinE.micro) = N :=
    beq_true hk2
  rw [hlab] at hok1 hrun1
  refine ⟨by omega, ?_, ?_, ?_⟩
  · unfold expand
    rw [Ok_append, hrun1]
    exact ⟨hok1, hok2⟩
  · unfold expand; rw [countM_append]; omega
  · intro fl hfl fe hfe
    obtain ⟨a, b, d⟩ := hall2 fl hfl fe hfe
    refine ⟨a, ?_, ?_⟩
    · unfold expand
      rw [runLab_append, hrun1, b]
    · rw [hrun1]; exact d

/-- **Soundness of the certificate checker.**  If `check` accepts, then for EVERY lift of the
label space into the address space of the engine, every embedding of the certificate's roles
into the engine's roles, and every table of matrices `S` that has the certificate's initial
labels on those roles, the engine word of the certificate is a `Route` from `S` to a table
`T` that has the declared final labels, uses exactly `N` paid directional moves, and leaves
the matrices of all other roles alone. -/
theorem check_sound (p : Par) (hh : 0 < p.h) (hw : p.h < p.w) (inits : List Nat)
    (cs : List (List Op)) (fs : List (List FinE)) (N : Nat)
    (hc : check p inits cs fs N = true)
    {α ρ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
    (lf : Lift p α) (Base : CMat α) (emb : Nat → ρ)
    (hemb : ∀ i j, i < p.n → j < p.n → emb i = emb j → i = j)
    (S : ρ → CMat α) (hS : ∀ r, r < p.n → S (emb r) = lf.mat Base (dec (inits.getD r 0))) :
    ∃ T, Route S T (gsemM emb (expand cs fs)) N ∧
      (∀ fl ∈ fs, ∀ fe ∈ fl, T (emb fe.r) = lf.mat Base (dec fe.e)) ∧
      (∀ q, (∀ r, r < p.n → emb r ≠ q) → T q = S q) := by
  obtain ⟨_, hok, hcnt, hall⟩ := check_micro p inits cs fs N hc
  obtain ⟨T, hR, hT, hF⟩ :=
    micro_sound lf hh hw Base emb hemb (expand cs fs) _ S hok hS
  refine ⟨T, ?_, ?_, hF⟩
  · rw [← hcnt]; exact hR
  · intro fl hfl fe hfe
    obtain ⟨a, b, _⟩ := hall fl hfl fe hfe
    rw [hT fe.r a, b]

end SSC
