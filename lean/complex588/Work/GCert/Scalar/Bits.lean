import Work.GCert.Scalar.Seg
import Work.CarrierCheck.ScalSound

/-!
# (key: gx-scalar) Tagged packed vectors: mask, repeated addition, exact division, weights

A tagged vector is `W = V * 2^64 + tag`: `V = W >>> 64` packs `n` digits of width `sw`, the low
64 bits mean nothing.  `OkW sw n W`: the digits of `V` are below `2^(sw-1)` and the tag is below
`2^63` (so two tags never carry into the digits).

* `ok_of_mask`     the mask test gives `OkW`;
* `addNCW_sound`   `addNC` on tagged vectors adds the digits;
* `gDiv_sound`     exact division: every digit of `X` is `b` times the digit of the quotient;
* `gW_sound`, `coef_wgt`   the reduced digit weight of a coefficient;
* `gAcc_sound`     the two halves of an add.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace GS
open SSC GXD

/-- the mask of the tagged vectors -/
def maskW (sw n : Nat) : Nat := ((rep sw n <<< (sw - 1)) <<< 64) ||| 2^63

def OkW (sw n W : Nat) : Prop := SmallV sw n (W >>> 64) ∧ W % 2^64 < 2^63

theorem ok_zero (sw n : Nat) : OkW sw n 0 := by
  refine ⟨?_, by norm_num⟩
  rw [Nat.zero_shiftRight]
  exact small_zero sw n

theorem ok_of_mask (sw n W : Nat) (hsw : 1 ≤ sw) (h : W &&& maskW sw n = 0) : OkW sw n W := by
  unfold maskW at h
  rw [Nat.and_or_distrib_left] at h
  obtain ⟨h1, h2⟩ := Nat.or_eq_zero_iff.mp h
  refine ⟨small_of_mask sw n _ hsw ?_, ?_⟩
  · apply Nat.eq_of_testBit_eq
    intro i
    have hb : (W &&& ((rep sw n <<< (sw - 1)) <<< 64)).testBit (i + 64) = false := by
      rw [h1]; exact Nat.zero_testBit _
    rw [Nat.testBit_and, Nat.testBit_shiftLeft] at hb
    have e : i + 64 - 64 = i := by omega
    have hge : decide (i + 64 ≥ 64) = true := by simp
    rw [e, hge, Bool.true_and] at hb
    rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.zero_testBit, Nat.add_comm 64 i]
    exact hb
  · apply Nat.lt_pow_two_of_testBit
    intro i hi
    rw [Nat.testBit_mod_two_pow]
    by_cases h64 : i < 64
    · have e : i = 63 := by omega
      subst e
      have hb : (W &&& 2^63).testBit 63 = false := by rw [h2]; exact Nat.zero_testBit _
      rw [Nat.testBit_and, Nat.testBit_two_pow_self, Bool.and_true] at hb
      rw [hb, Bool.and_false]
    · rw [decide_eq_false h64, Bool.false_and]

/-- two tags never carry -/
theorem shr_add (W1 W2 : Nat) (h1 : W1 % 2^64 < 2^63) (h2 : W2 % 2^64 < 2^63) :
    (W1 + W2) >>> 64 = (W1 >>> 64) + (W2 >>> 64) := by
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
    Nat.add_div (by norm_num : 0 < 2^64)]
  have : ¬ (2^64 ≤ W1 % 2^64 + W2 % 2^64) := by omega
  rw [if_neg this, Nat.add_zero]

theorem addNCW_sound (sw n tm a : Nat) (hsw : 1 ≤ sw) (htm : tm = maskW sw n)
    (ha : OkW sw n a) : ∀ (w acc : Nat) (k : Nat → Bool), OkW sw n acc →
      addNC tm a w acc k = true →
      ∃ r, k r = true ∧ OkW sw n r ∧
        ∀ T, T < n → dg sw (r >>> 64) T = dg sw (acc >>> 64) T + w * dg sw (a >>> 64) T := by
  intro w
  induction w with
  | zero =>
    intro acc k hacc h
    exact ⟨acc, h, hacc, fun T _ => by rw [Nat.zero_mul, Nat.add_zero]⟩
  | succ w ih =>
    intro acc k hacc h
    rw [addNC_succ] at h
    obtain ⟨hb, h2⟩ := guard_true h
    have hm : (acc + a) &&& tm = 0 := beq_true hb
    rw [htm] at hm
    have hs := ok_of_mask sw n (acc + a) hsw hm
    obtain ⟨r, hk, hr, hd⟩ := ih (acc + a) k hs h2
    refine ⟨r, hk, hr, fun T hT => ?_⟩
    rw [hd T hT, shr_add acc a hacc.2 ha.2, dg_add_small sw n _ _ hsw hacc.1 ha.1 T hT, Nat.succ_mul]
    omega

theorem gDiv_sound (sw n tm b X : Nat) (hsw : 1 ≤ sw) (htm : tm = maskW sw n) (hX : OkW sw n X)
    (k : Nat → Bool) (h : gDiv tm b X k = true) :
    ∃ q, k q = true ∧ OkW sw n q ∧ ∀ T, T < n → dg sw (X >>> 64) T = b * dg sw (q >>> 64) T := by
  unfold gDiv at h
  cases hb : Nat.beq b 1 with
  | true =>
    rw [hb] at h
    have e : b = 1 := beq_true hb
    exact ⟨X, h, hX, fun T _ => by rw [e, Nat.one_mul]⟩
  | false =>
    rw [hb] at h
    replace h : forceN (Nat.div X b) (fun q => guard (Nat.beq (Nat.land q tm) 0)
      (addNC tm q b 0 fun r => guard (Nat.beq r X) (k q))) = true := h
    rw [forceN_eq] at h
    obtain ⟨hm, h2⟩ := guard_true h
    have hm' : (X / b) &&& tm = 0 := beq_true hm
    rw [htm] at hm'
    have hq := ok_of_mask sw n (X / b) hsw hm'
    obtain ⟨r, hk, _, hd⟩ := addNCW_sound sw n tm (X / b) hsw htm hq b 0 _ (ok_zero sw n) h2
    obtain ⟨hr, hk2⟩ := guard_true hk
    have er : r = X := beq_true hr
    refine ⟨X / b, hk2, hq, fun T hT => ?_⟩
    have := hd T hT
    rw [er, Nat.zero_shiftRight, dg_zero_left, Nat.zero_add] at this
    exact this

theorem gEnc_sound (K p n : Nat) (kk : Nat → Bool) (h : gEnc K (2^K) p n kk = true) :
    p < 2^K ∧ kk (p + n <<< K) = true := by
  unfold gEnc at h
  obtain ⟨h1, h2⟩ := guard_true h
  rw [forceN_eq] at h2
  exact ⟨ble_true h1, h2⟩

theorem dec_lo (K p n : Nat) (hp : p < 2^K) : (p + n <<< K) % 2^K = p := by
  rw [Nat.shiftLeft_eq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hp]

theorem dec_hi (K p n : Nat) (hp : p < 2^K) : (p + n <<< K) >>> K = n := by
  rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.add_mul_div_right _ _ (Nat.two_pow_pos K),
    Nat.div_eq_of_lt hp, Nat.zero_add]

/-- the coefficient `(-1)^neg num / den` as an `SSC.Coef` -/
def toCoef (x : Co) : Coef := ⟨x.neg, x.num, x.den⟩

theorem gW_sound (ux us uy v v2 t s : Nat) (co : Co) (k : Bool → Nat → Nat → Bool)
    (h : gW ux us uy v v2 t s co k = true) :
    ∃ a b, k co.neg a b = true ∧ 1 ≤ b ∧ 1 ≤ co.den * unitK ux us uy v v2 s ∧
      a * (co.den * unitK ux us uy v v2 s) = co.num * unitK ux us uy v v2 t * b := by
  obtain ⟨ng, num, den⟩ := co
  have h' : forceN (Nat.mul num (unitK ux us uy v v2 t)) (fun A =>
      forceN (Nat.mul den (unitK ux us uy v v2 s)) fun B =>
        forceN (Nat.gcd A B) fun g => forceN (Nat.div A g) fun a => forceN (Nat.div B g) fun b =>
          guard (Nat.ble 1 B) (guard (Nat.ble 1 b)
            (guard (Nat.beq (Nat.mul a B) (Nat.mul A b)) (k ng a b)))) = true := h
  rw [forceN_eq, forceN_eq, forceN_eq, forceN_eq, forceN_eq] at h'
  obtain ⟨h1, h2⟩ := guard_true h'
  obtain ⟨h3, h4⟩ := guard_true h2
  obtain ⟨h5, h6⟩ := guard_true h4
  exact ⟨_, _, h6, ble_true h3, ble_true h1, beq_true h5⟩

/-- the reduced digit weight is the coefficient -/
theorem coef_wgt (co : Co) (a b us ut : Nat) (hb : 1 ≤ b) (hus : 1 ≤ co.den * us) (hut : 1 ≤ ut)
    (hw : a * (co.den * us) = co.num * ut * b) (dp dn : ℚ) :
    (toCoef co).val * (((b:ℚ) * dp - (b:ℚ) * dn) / (us:ℚ))
      = (bif co.neg then -(a:ℚ) else (a:ℚ)) * (dp - dn) / (ut:ℚ) := by
  obtain ⟨ng, num, den⟩ := co
  have hden : 1 ≤ den := by
    rcases Nat.eq_zero_or_pos den with e | e
    · rw [e, Nat.zero_mul] at hus; omega
    · exact e
  have hus' : 1 ≤ us := by
    rcases Nat.eq_zero_or_pos us with e | e
    · rw [e, Nat.mul_zero] at hus; omega
    · exact e
  have hq : (a:ℚ) * ((den:ℚ) * (us:ℚ)) = (num:ℚ) * (ut:ℚ) * (b:ℚ) := by exact_mod_cast hw
  have d0 : (den:ℚ) ≠ 0 := by positivity
  have u0 : (us:ℚ) ≠ 0 := by positivity
  have t0 : (ut:ℚ) ≠ 0 := by positivity
  unfold toCoef Coef.val
  cases ng
  · simp only [Bool.false_eq_true, ↓reduceIte, cond_false]
    field_simp
    linear_combination (dn - dp) * hq
  · simp only [↓reduceIte, cond_true]
    field_simp
    linear_combination (dp - dn) * hq

/-- the two halves of an add on tagged vectors -/
theorem gAcc_sound (sw n tm K : Nat) (hsw : 1 ≤ sw) (htm : tm = maskW sw n) (ng : Bool)
    (a b ps ns pt nt : Nat) (hps : OkW sw n ps) (hns : OkW sw n ns) (hpt : OkW sw n pt)
    (hnt : OkW sw n nt) (kk : Nat → Bool) (h : gAcc tm K (2^K) ng a b ps ns pt nt kk = true) :
    ∃ pt' nt', OkW sw n pt' ∧ OkW sw n nt' ∧ pt' < 2^K ∧ kk (pt' + nt' <<< K) = true ∧
      ∀ T, T < n → ∃ qp qn : Nat, dg sw (ps >>> 64) T = b * qp ∧ dg sw (ns >>> 64) T = b * qn ∧
        ((dg sw (pt' >>> 64) T : ℚ) - (dg sw (nt' >>> 64) T : ℚ)
          = (dg sw (pt >>> 64) T : ℚ) - (dg sw (nt >>> 64) T : ℚ)
            + (bif ng then -(a:ℚ) else (a:ℚ)) * ((qp:ℚ) - (qn:ℚ))) := by
  unfold gAcc at h
  obtain ⟨qp, h1, hqp, dqp⟩ := gDiv_sound sw n tm b ps hsw htm hps _ h
  obtain ⟨qn, h2, hqn, dqn⟩ := gDiv_sound sw n tm b ns hsw htm hns _ h1
  cases ng with
  | false =>
    replace h2 : addNC tm qp a pt (fun pt' => addNC tm qn a nt fun nt' =>
      gEnc K (2^K) pt' nt' kk) = true := h2
    obtain ⟨pt', h3, hpt', d1⟩ := addNCW_sound sw n tm qp hsw htm hqp a pt _ hpt h2
    obtain ⟨nt', h4, hnt', d2⟩ := addNCW_sound sw n tm qn hsw htm hqn a nt _ hnt h3
    obtain ⟨hlt, hk⟩ := gEnc_sound K pt' nt' kk h4
    refine ⟨pt', nt', hpt', hnt', hlt, hk, fun T hT => ⟨_, _, dqp T hT, dqn T hT, ?_⟩⟩
    rw [d1 T hT, d2 T hT]
    push_cast
    simp only [cond_false]
    ring
  | true =>
    replace h2 : addNC tm qn a pt (fun pt' => addNC tm qp a nt fun nt' =>
      gEnc K (2^K) pt' nt' kk) = true := h2
    obtain ⟨pt', h3, hpt', d1⟩ := addNCW_sound sw n tm qn hsw htm hqn a pt _ hpt h2
    obtain ⟨nt', h4, hnt', d2⟩ := addNCW_sound sw n tm qp hsw htm hqp a nt _ hnt h3
    obtain ⟨hlt, hk⟩ := gEnc_sound K pt' nt' kk h4
    refine ⟨pt', nt', hpt', hnt', hlt, hk, fun T hT => ⟨_, _, dqp T hT, dqn T hT, ?_⟩⟩
    rw [d1 T hT, d2 T hT]
    push_cast
    simp only [cond_true]
    ring

#print axioms gAcc_sound
#print axioms coef_wgt

end GS
