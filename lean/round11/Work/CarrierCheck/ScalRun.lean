import Work.CarrierCheck.ScalSound

/-!
# (key: carrier-check) The scalar check runs the gates of the micro-program

* `SSt`, `cont`      abstract state (two packed vectors per role) and the x-content it encodes;
* `SStep`, `SRun`    one gate / a micro-program on abstract states;
* `sAdd_sound`       the checker's gate step is an `SStep`;
* `SRun_Cm`          `SRun a ms b → Cm b = matP unemb ms * Cm a` (content matrix).

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace SSC
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM OAI.PowerSaving.SS Finset Matrix

/-- abstract state of the scalar check: positive and negative packed vector of every role -/
structure SSt where
  P : Nat → Nat
  N : Nat → Nat

/-- unit of the content of a role: halves for the y roles (`y0 ≤ r`), ones otherwise -/
def scl (y0 r : Nat) : ℚ := bif Nat.ble y0 r then (2:ℚ) else 1

/-- coefficient of `x_T` in the content of the role `r` -/
def cont (sw y0 : Nat) (a : SSt) (r T : Nat) : ℚ :=
  ((dg sw (a.P r) T : ℚ) - (dg sw (a.N r) T : ℚ)) / scl y0 r

def SmallSt (sw v : Nat) (a : SSt) : Prop := ∀ r, SmallV sw v (a.P r) ∧ SmallV sw v (a.N r)

/-- one gate `t += cf * s` on abstract states -/
def SStep (sw v y0 t s : Nat) (cf : Coef) (a b : SSt) : Prop :=
  s < y0 ∧ t ≠ s ∧ (∀ r, r ≠ t → b.P r = a.P r ∧ b.N r = a.N r) ∧
    ∀ T, T < v → cont sw y0 b t T = cont sw y0 a t T + cf.val * cont sw y0 a s T

/-- a micro-program on abstract states (moves, shifts and expects do nothing) -/
def SRun (sw v y0 : Nat) : SSt → List Micro → SSt → Prop
  | a, [], b => b = a
  | a, .add t s cf :: ms, b => ∃ m, SStep sw v y0 t s cf a m ∧ SRun sw v y0 m ms b
  | a, .dir _ _ :: ms, b => SRun sw v y0 a ms b
  | a, .shift _ _ :: ms, b => SRun sw v y0 a ms b
  | _, .copy _ _ :: _, _ => False
  | _, .erase _ :: _, _ => False
  | a, .expect _ _ :: ms, b => SRun sw v y0 a ms b

theorem SRun_append (sw v y0 : Nat) (l1 l2 : List Micro) : ∀ (a m b : SSt),
    SRun sw v y0 a l1 m → SRun sw v y0 m l2 b → SRun sw v y0 a (l1 ++ l2) b := by
  induction l1 with
  | nil =>
    intro a m b h1 h2
    have e : m = a := h1
    rw [e] at h2
    exact h2
  | cons x l1 ih =>
    intro a m b h1 h2
    cases x with
    | add t s cf =>
      obtain ⟨m1, hs, hr⟩ := h1
      exact ⟨m1, hs, ih m1 m b hr h2⟩
    | dir r z => exact ih a m b h1 h2
    | shift r z => exact ih a m b h1 h2
    | copy _ _ => exact False.elim h1
    | erase _ => exact False.elim h1
    | expect _ _ => exact ih a m b h1 h2

theorem SRun_moves (sw v y0 : Nat) (ms : List Micro)
    (h : ∀ m ∈ ms, ∃ r z, m = .dir r z ∨ m = .shift r z) (a : SSt) : SRun sw v y0 a ms a := by
  induction ms with
  | nil => exact rfl
  | cons m ms ih =>
    have ih' := ih (fun m' h' => h m' (List.mem_cons_of_mem _ h'))
    obtain ⟨r, z, e | e⟩ := h m (List.mem_cons_self ..) <;> subst e <;> exact ih'

/-! ## the checker state -/

def absT (d : Nat) (tP tN : Trie) : SSt := ⟨absS (2^d) tP, absS (2^d) tN⟩

/-- invariant of the checker state -/
structure TOk (d sw v : Nat) (tP tN : Trie) : Prop where
  wP : tP.wf d
  wN : tN.wf d
  sm : SmallSt sw v (absT d tP tN)

theorem scl_lt (y0 s : Nat) (h : s < y0) : scl y0 s = 1 := by
  unfold scl
  cases hb : Nat.ble y0 s with
  | true => exact absurd (ble_true hb) (by omega)
  | false => rfl

theorem scl_ge (y0 t : Nat) (h : y0 ≤ t) : scl y0 t = 2 := by
  unfold scl
  cases hb : Nat.ble y0 t with
  | true => rfl
  | false =>
    have h2 := Nat.ble_eq_true_of_le h
    rw [hb] at h2
    exact Bool.noConfusion h2

theorem brec_false_eq {a : Bool}
    (h : Bool.rec (motive := fun _ => Bool) a false false = true) : a = true := h

theorem scl_ne (y0 r : Nat) : scl y0 r ≠ 0 := by
  unfold scl
  cases Nat.ble y0 r <;> norm_num

/-- the two repeated additions of a gate -/
theorem sAdd_core (d sw v tm : Nat) (hsw : 1 ≤ sw) (htm : tm = rep sw v <<< (sw - 1))
    (t a b w : Nat) (tP tN : Trie) (ha : SmallV sw v a) (hb : SmallV sw v b)
    (hpt : SmallV sw v (tP.get t)) (hnt : SmallV sw v (tN.get t)) (k : Trie → Trie → Bool)
    (h : addNC tm a w (tP.get t) (fun pt' => addNC tm b w (tN.get t) fun nt' =>
      k (tP.set t pt') (tN.set t nt')) = true) :
    ∃ pt' nt', k (tP.set t pt') (tN.set t nt') = true ∧ SmallV sw v pt' ∧ SmallV sw v nt' ∧
      ∀ T, T < v → dg sw pt' T = dg sw (tP.get t) T + w * dg sw a T ∧
        dg sw nt' T = dg sw (tN.get t) T + w * dg sw b T := by
  obtain ⟨pt', hk1, hs1, hd1⟩ := addNC_sound sw v tm a hsw htm ha w (tP.get t) _ hpt h
  have hk1' : addNC tm b w (tN.get t) (fun nt' => k (tP.set t pt') (tN.set t nt')) = true := hk1
  obtain ⟨nt', hk2, hs2, hd2⟩ := addNC_sound sw v tm b hsw htm hb w (tN.get t) _ hnt hk1'
  exact ⟨pt', nt', hk2, hs1, hs2, fun T hT => ⟨hd1 T hT, hd2 T hT⟩⟩

/-- **one gate of the checker is a gate on abstract states** -/
theorem sAdd_sound (d sw v tm y0 : Nat) (hsw : 1 ≤ sw) (htm : tm = rep sw v <<< (sw - 1))
    (t s : Nat) (cf : Coef) (tP tN : Trie) (hI : TOk d sw v tP tN)
    (k : Trie → Trie → Bool) (h : sAdd tm y0 t s cf tP tN k = true) :
    ∃ tP' tN', TOk d sw v tP' tN' ∧ k tP' tN' = true ∧
      SStep sw v y0 t s cf (absT d tP tN) (absT d tP' tN') := by
  obtain ⟨hwP, hwN, hsm⟩ := hI
  have h0 : guard (Nat.ble (Nat.succ s) y0) (Bool.rec (motive := fun _ => Bool)
      (tP.getK s fun ps => tN.getK s fun ns => tP.getK t fun pt => tN.getK t fun nt =>
        wgtK (Nat.ble y0 t) cf fun ng w =>
          Bool.rec (motive := fun _ => Bool)
            (addNC tm ps w pt fun pt' => addNC tm ns w nt fun nt' =>
              k (tP.set t pt') (tN.set t nt'))
            (addNC tm ns w pt fun pt' => addNC tm ps w nt fun nt' =>
              k (tP.set t pt') (tN.set t nt'))
            ng)
      false (Nat.beq t s)) = true := h
  obtain ⟨hs, h1⟩ := guard_true h0
  have hsy : s < y0 := ble_true hs
  cases hts : Nat.beq t s with
  | true =>
    rw [hts] at h1
    exact absurd h1 Bool.false_ne_true
  | false =>
    rw [hts] at h1
    replace h1 := brec_false_eq h1
    have hne : t ≠ s := fun e => by
      rw [e, Nat.beq_refl] at hts
      exact Bool.noConfusion hts
    rw [Trie.getK_eq d tP hwP] at h1
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    obtain ⟨hs2, h2⟩ := h1
    rw [Trie.getK_eq d tN hwN] at h2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
    obtain ⟨_, h3⟩ := h2
    rw [Trie.getK_eq d tP hwP] at h3
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h3
    obtain ⟨ht2, h4⟩ := h3
    rw [Trie.getK_eq d tN hwN] at h4
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h4
    obtain ⟨_, h5⟩ := h4
    obtain ⟨ng, w, hk, hval⟩ := wgtK_sound _ _ _ h5
    have ePs : absS (2^d) tP s = tP.get s := absS_apply d tP s hs2
    have eNs : absS (2^d) tN s = tN.get s := absS_apply d tN s hs2
    have ePt : absS (2^d) tP t = tP.get t := absS_apply d tP t ht2
    have eNt : absS (2^d) tN t = tN.get t := absS_apply d tN t ht2
    have sPs : SmallV sw v (tP.get s) := by rw [← ePs]; exact (hsm s).1
    have sNs : SmallV sw v (tN.get s) := by rw [← eNs]; exact (hsm s).2
    have sPt : SmallV sw v (tP.get t) := by rw [← ePt]; exact (hsm t).1
    have sNt : SmallV sw v (tN.get t) := by rw [← eNt]; exact (hsm t).2
    have fin : ∀ (a b : Nat) (pt' nt' : Nat), k (tP.set t pt') (tN.set t nt') = true →
        SmallV sw v pt' → SmallV sw v nt' →
        (∀ T, T < v → dg sw pt' T = dg sw (tP.get t) T + w * dg sw a T ∧
          dg sw nt' T = dg sw (tN.get t) T + w * dg sw b T) →
        (∀ T, T < v → cf.val * cont sw y0 (absT d tP tN) s T
          = (w:ℚ) * ((dg sw a T : ℚ) - (dg sw b T : ℚ)) / scl y0 t) →
        ∃ tP' tN', TOk d sw v tP' tN' ∧ k tP' tN' = true ∧
          SStep sw v y0 t s cf (absT d tP tN) (absT d tP' tN') := by
      intro a b pt' nt' hk' hs1 hs2 hd hc
      have hsetP := absS_set d tP hwP t pt' ht2
      have hsetN := absS_set d tN hwN t nt' ht2
      refine ⟨tP.set t pt', tN.set t nt', ⟨Trie.wf_set d tP hwP _ _, Trie.wf_set d tN hwN _ _, ?_⟩,
        hk', hsy, hne, ?_, ?_⟩
      · intro r
        show SmallV sw v (absS (2^d) (tP.set t pt') r) ∧ SmallV sw v (absS (2^d) (tN.set t nt') r)
        rw [hsetP, hsetN]
        by_cases e : r = t
        · rw [e, Function.update_self, Function.update_self]
          exact ⟨hs1, hs2⟩
        · rw [Function.update_of_ne e, Function.update_of_ne e]
          exact hsm r
      · intro r hr
        show absS (2^d) (tP.set t pt') r = absS (2^d) tP r ∧
          absS (2^d) (tN.set t nt') r = absS (2^d) tN r
        rw [hsetP, hsetN, Function.update_of_ne hr, Function.update_of_ne hr]
        exact ⟨rfl, rfl⟩
      · intro T hT
        obtain ⟨d1, d2⟩ := hd T hT
        rw [hc T hT]
        show ((dg sw (absS (2^d) (tP.set t pt') t) T : ℚ) - (dg sw (absS (2^d) (tN.set t nt') t) T : ℚ))
            / scl y0 t
          = ((dg sw (absS (2^d) tP t) T : ℚ) - (dg sw (absS (2^d) tN t) T : ℚ)) / scl y0 t
            + (w:ℚ) * ((dg sw a T : ℚ) - (dg sw b T : ℚ)) / scl y0 t
        rw [hsetP, hsetN, Function.update_self, Function.update_self, ePt, eNt, d1, d2]
        push_cast
        ring
    have hcs : ∀ T, cont sw y0 (absT d tP tN) s T
        = (dg sw (tP.get s) T : ℚ) - (dg sw (tN.get s) T : ℚ) := by
      intro T
      show ((dg sw (absS (2^d) tP s) T : ℚ) - (dg sw (absS (2^d) tN s) T : ℚ)) / scl y0 s = _
      rw [scl_lt y0 s hsy, ePs, eNs, div_one]
    have hsc : scl y0 t = (bif Nat.ble y0 t then (2:ℚ) else 1) := rfl
    cases ng with
    | false =>
      have hk' : addNC tm (tP.get s) w (tP.get t) (fun pt' => addNC tm (tN.get s) w (tN.get t)
          fun nt' => k (tP.set t pt') (tN.set t nt')) = true := hk
      obtain ⟨pt', nt', hk2, hs1, hs2, hd⟩ :=
        sAdd_core d sw v tm hsw htm t _ _ w tP tN sPs sNs sPt sNt k hk'
      have hval' : cf.val = (w:ℚ) / scl y0 t := hval
      exact fin _ _ pt' nt' hk2 hs1 hs2 hd (fun T _ => by rw [hcs T, hval']; ring)
    | true =>
      have hk' : addNC tm (tN.get s) w (tP.get t) (fun pt' => addNC tm (tP.get s) w (tN.get t)
          fun nt' => k (tP.set t pt') (tN.set t nt')) = true := hk
      obtain ⟨pt', nt', hk2, hs1, hs2, hd⟩ :=
        sAdd_core d sw v tm hsw htm t _ _ w tP tN sNs sPs sPt sNt k hk'
      have hval' : cf.val = -(w:ℚ) / scl y0 t := hval
      exact fin _ _ pt' nt' hk2 hs1 hs2 hd (fun T _ => by rw [hcs T, hval']; ring)

end SSC
