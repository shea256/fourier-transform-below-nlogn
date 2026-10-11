import Work.GCert.Scalar.Bits
import Work.CarrierCheck.ScalRun

/-!
# (key: gx-scalar) One add of the kernel check is one add on abstract states

* `modK_eq`     the one-descent update of a trie leaf;
* `absG`, `GOk` abstract state of a trie with packed leaves (untagged positive and negative vector
  of every register) and the invariant of the check;
* `gcont`       coefficient of source `T` in the content of a register (`unit` per register);
* `GStep`       one add `t += cf * s` on abstract states;
* `gAdd_sound`  the kernel's add is a `GStep`.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace GS
open SSC GXD

theorem modK_leaf (x key : Nat) (f : Nat → (Nat → Bool) → Bool) (k : Trie → Bool) :
    modK (.leaf x) key f k = if key = 0 then f x (fun y => k (.leaf y)) else false := by
  cases key <;> rfl

theorem modK_node (l r : Trie) (key : Nat) (f : Nat → (Nat → Bool) → Bool) (k : Trie → Bool) :
    modK (.node l r) key f k = if key % 2 = 0 then modK l (key/2) f (fun l' => k (.node l' r))
      else modK r (key/2) f (fun r' => k (.node l r')) := by
  have h1 : Nat.shiftRight key 1 = key / 2 := Nat.shiftRight_one key
  have h2 : Nat.land key 1 = key % 2 := Nat.and_one_is_mod key
  show Bool.rec (motive := fun _ => Bool) (modK r (Nat.shiftRight key 1) f fun r' => k (.node l r'))
    (modK l (Nat.shiftRight key 1) f fun l' => k (.node l' r)) (Nat.beq (Nat.land key 1) 0) = _
  rw [h1, h2]
  rcases Nat.mod_two_eq_zero_or_one key with h | h <;> rw [h] <;> rfl

theorem modK_eq (d : Nat) (t : Trie) (hwf : t.wf d) (key : Nat) (f : Nat → (Nat → Bool) → Bool)
    (k : Trie → Bool) :
    modK t key f k = (decide (key < 2^d) && f (t.get key) (fun x => k (t.set key x))) := by
  induction d generalizing t key k with
  | zero =>
    cases t with
    | leaf v =>
      rw [modK_leaf]
      by_cases h : key = 0
      · subst h; simp [Trie.get, Trie.set_leaf]
      · have h' : ¬ key < 2^0 := by simpa using h
        simp [h, h']
    | node l r => exact False.elim hwf
  | succ d ih =>
    cases t with
    | leaf v => exact False.elim hwf
    | node l r =>
      obtain ⟨hl, hr⟩ := hwf
      rw [modK_node]
      have hlt : (key / 2 < 2^d) ↔ (key < 2^(d+1)) := by rw [pow_succ]; omega
      by_cases h : key % 2 = 0
      · have e : (fun x => k ((Trie.node l r).set key x)) = fun x => k (.node (l.set (key/2) x) r) := by
          funext x; rw [Trie.set_node, if_pos h]
        rw [if_pos h, ih l hl, e]; simp [Trie.get, h, hlt]
      · have e : (fun x => k ((Trie.node l r).set key x)) = fun x => k (.node l (r.set (key/2) x)) := by
          funext x; rw [Trie.set_node, if_neg h]
        rw [if_neg h, ih r hr, e]; simp [Trie.get, h, hlt]

/-- abstract state: untagged positive / negative packed vector of every register -/
def absG (d K : Nat) (tr : Trie) : SSt :=
  ⟨fun r => (absS (2^d) tr r % 2^K) >>> 64, fun r => (absS (2^d) tr r >>> K) >>> 64⟩

/-- invariant of the check: both halves of every leaf are tagged vectors with small digits -/
structure GOk (d sw n : Nat) (tr : Trie) : Prop where
  wf : tr.wf d
  ok : ∀ r, OkW sw n (absS (2^d) tr r % 2^(64 + sw * n)) ∧ OkW sw n (absS (2^d) tr r >>> (64 + sw * n))

theorem GOk.small {d sw n : Nat} {tr : Trie} (h : GOk d sw n tr) :
    SmallSt sw n (absG d (64 + sw * n) tr) := fun r => ⟨(h.ok r).1.1, (h.ok r).2.1⟩

/-- coefficient of source `T` in the content of the register `r` (digits over the unit `u r`) -/
def gcont (sw : Nat) (u : Nat → Nat) (a : SSt) (r T : Nat) : ℚ :=
  ((dg sw (a.P r) T : ℚ) - (dg sw (a.N r) T : ℚ)) / (u r : ℚ)

theorem gcont_congr (sw : Nat) (u : Nat → Nat) (a b : SSt) (r T : Nat) (hP : b.P r = a.P r)
    (hN : b.N r = a.N r) : gcont sw u b r T = gcont sw u a r T := by
  unfold gcont
  rw [hP, hN]

/-- one add `t += cf * s` on abstract states -/
def GStep (sw n : Nat) (u : Nat → Nat) (t s : Nat) (cf : Coef) (a b : SSt) : Prop :=
  t ≠ s ∧ (∀ r, r ≠ t → b.P r = a.P r ∧ b.N r = a.N r) ∧
    ∀ T, T < n → gcont sw u b t T = gcont sw u a t T + cf.val * gcont sw u a s T

theorem unitK_pos (ux us uy v v2 r : Nat) (hx : 1 ≤ ux) (hs : 1 ≤ us) (hy : 1 ≤ uy) :
    1 ≤ unitK ux us uy v v2 r := by
  unfold unitK
  cases Nat.ble (Nat.succ r) v <;> cases Nat.ble (Nat.succ r) v2 <;> assumption

/-- **one add of the kernel check is one add on abstract states** -/
theorem gAdd_sound (d sw n tm K ux us uy v v2 : Nat) (hsw : 1 ≤ sw) (htm : tm = maskW sw n)
    (hK : K = 64 + sw * n) (hu : ∀ r, 1 ≤ unitK ux us uy v v2 r)
    (t s : Nat) (co : Co) (ok : Bool) (tr : Trie) (hI : GOk d sw n tr) (k : Trie → Bool)
    (h : gAdd tm K (2^K) ux us uy v v2 t s co ok tr k = true) :
    ∃ tr', GOk d sw n tr' ∧ k tr' = true ∧ ok = true ∧
      GStep sw n (unitK ux us uy v v2) t s (toCoef co) (absG d K tr) (absG d K tr') := by
  subst hK
  obtain ⟨hwf, hok⟩ := hI
  unfold gAdd at h
  obtain ⟨hokb, h1⟩ := guard_true h
  cases hts : Nat.beq t s with
  | true =>
    rw [hts] at h1
    exact absurd h1 Bool.false_ne_true
  | false =>
    rw [hts] at h1
    replace h1 : tr.getK s (fun vs => modK tr t (fun vt kk =>
      gW ux us uy v v2 t s co fun ng a b =>
        gAcc tm (64 + sw * n) (2^(64 + sw * n)) ng a b (vs % 2^(64 + sw * n)) (vs >>> (64 + sw * n))
          (vt % 2^(64 + sw * n)) (vt >>> (64 + sw * n)) kk) k) = true := h1
    have hne : t ≠ s := fun e => by
      rw [e, Nat.beq_refl] at hts
      exact Bool.noConfusion hts
    rw [Trie.getK_eq d tr hwf] at h1
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    obtain ⟨hs2, h2⟩ := h1
    rw [modK_eq d tr hwf] at h2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
    obtain ⟨ht2, h3⟩ := h2
    obtain ⟨a, b, h4, hb, hus, hw⟩ := gW_sound _ _ _ _ _ _ _ _ _ h3
    have es : absS (2^d) tr s = tr.get s := absS_apply d tr s hs2
    have et : absS (2^d) tr t = tr.get t := absS_apply d tr t ht2
    obtain ⟨hps, hns⟩ := hok s
    obtain ⟨hpt, hnt⟩ := hok t
    rw [es] at hps hns
    rw [et] at hpt hnt
    obtain ⟨pt', nt', hpt', hnt', hlt, hk, hd⟩ := gAcc_sound sw n tm (64 + sw * n) hsw htm co.neg a b
      _ _ _ _ hps hns hpt hnt _ h4
    have hset := absS_set d tr hwf t (pt' + nt' <<< (64 + sw * n)) ht2
    refine ⟨tr.set t (pt' + nt' <<< (64 + sw * n)), ⟨Trie.wf_set d tr hwf _ _, ?_⟩, hk, hokb, hne,
      ?_, ?_⟩
    · intro r
      rw [hset]
      by_cases e : r = t
      · rw [e, Function.update_self, dec_lo _ _ _ hlt, dec_hi _ _ _ hlt]
        exact ⟨hpt', hnt'⟩
      · rw [Function.update_of_ne e]
        exact hok r
    · intro r hr
      show (absS (2^d) (tr.set t (pt' + nt' <<< (64 + sw * n))) r % 2^(64 + sw * n)) >>> 64
          = (absS (2^d) tr r % 2^(64 + sw * n)) >>> 64 ∧
        (absS (2^d) (tr.set t (pt' + nt' <<< (64 + sw * n))) r >>> (64 + sw * n)) >>> 64
          = (absS (2^d) tr r >>> (64 + sw * n)) >>> 64
      rw [hset, Function.update_of_ne hr]
      exact ⟨rfl, rfl⟩
    · intro T hT
      obtain ⟨qp, qn, e1, e2, e3⟩ := hd T hT
      have hc := coef_wgt co a b _ _ hb hus (hu t) hw (qp:ℚ) (qn:ℚ)
      show ((dg sw ((absS (2^d) (tr.set t (pt' + nt' <<< (64 + sw * n))) t % 2^(64 + sw * n)) >>> 64) T : ℚ)
            - (dg sw ((absS (2^d) (tr.set t (pt' + nt' <<< (64 + sw * n))) t >>> (64 + sw * n)) >>> 64) T : ℚ))
            / (unitK ux us uy v v2 t : ℚ)
          = ((dg sw ((absS (2^d) tr t % 2^(64 + sw * n)) >>> 64) T : ℚ)
              - (dg sw ((absS (2^d) tr t >>> (64 + sw * n)) >>> 64) T : ℚ)) / (unitK ux us uy v v2 t : ℚ)
            + (toCoef co).val * (((dg sw ((absS (2^d) tr s % 2^(64 + sw * n)) >>> 64) T : ℚ)
              - (dg sw ((absS (2^d) tr s >>> (64 + sw * n)) >>> 64) T : ℚ)) / (unitK ux us uy v v2 s : ℚ))
      rw [hset, Function.update_self, dec_lo _ _ _ hlt, dec_hi _ _ _ hlt, et, es, e1, e2, e3]
      push_cast
      rw [hc]
      ring

#print axioms modK_eq
#print axioms gAdd_sound

end GS
