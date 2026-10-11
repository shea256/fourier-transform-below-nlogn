import Work.CarrierCheck.ScalDef
import Work.CarrierCheck.Valid
import Work.SharedSumChecker.Scalar

/-!
# (key: carrier-check) Soundness of the scalar check of a carrier certificate

Part 1 (this file): digits of packed vectors, the abstract state `SSt` of the check, one gate
(`sAdd_sound`), a gate list (`SRun`), and the content matrix `Cm`:

    SRun a ms b  →  Cm b = matP unemb ms * Cm a        (`SRun_Cm`)

i.e. the checker state follows the ordered product of the transvections of the micro-program.
Part 2: `Work.CarrierCheck.ScalRun` (the checker functions run `SRun`), part 3:
`Work.CarrierCheck.ScalId` (the scalar identity of an accepted certificate).

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace SSC
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM OAI.PowerSaving.SS Finset Matrix

/-! ## digits -/

/-- digit `T` of `X` in base `2^sw` -/
def dg (sw X T : Nat) : Nat := (X >>> (sw * T)) % 2^sw

theorem dg_zero' (sw X : Nat) : dg sw X 0 = X % 2^sw := by
  unfold dg
  rw [Nat.mul_zero, Nat.shiftRight_zero]

theorem dg_succ (sw X T : Nat) : dg sw X (T+1) = dg sw (X / 2^sw) T := by
  have e : 2^(sw*(T+1)) = 2^sw * 2^(sw*T) := by ring
  unfold dg
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, e, Nat.div_div_eq_div_mul]

theorem dg_zero_left (sw T : Nat) : dg sw 0 T = 0 := by
  unfold dg
  rw [Nat.zero_shiftRight, Nat.zero_mod]

/-- digits add when no carry occurs up to that digit -/
theorem dg_add (sw : Nat) : ∀ (T X Y : Nat),
    (∀ T', T' ≤ T → dg sw X T' + dg sw Y T' < 2^sw) →
    dg sw (X + Y) T = dg sw X T + dg sw Y T := by
  intro T
  induction T with
  | zero =>
    intro X Y h
    have h0 := h 0 (Nat.le_refl _)
    rw [dg_zero', dg_zero'] at h0
    rw [dg_zero', dg_zero', dg_zero', Nat.add_mod, Nat.mod_eq_of_lt h0]
  | succ T ih =>
    intro X Y h
    have h0 := h 0 (Nat.zero_le _)
    rw [dg_zero', dg_zero'] at h0
    have hnl : ¬ (2^sw ≤ X % 2^sw + Y % 2^sw) := Nat.not_le.mpr h0
    have hdiv : (X + Y) / 2^sw = X / 2^sw + Y / 2^sw := by
      rw [Nat.add_div (Nat.two_pow_pos sw), if_neg hnl, Nat.add_zero]
    rw [dg_succ, dg_succ, dg_succ, hdiv]
    apply ih
    intro T' hT'
    have h1 := h (T'+1) (by omega)
    rw [dg_succ, dg_succ] at h1
    exact h1

/-- digits of `a * 2^(sw * S)` -/
theorem dg_mul_pow (sw a : Nat) (ha : a < 2^sw) : ∀ (S T : Nat),
    dg sw (a * 2^(sw*S)) T = if T = S then a else 0 := by
  intro S
  induction S with
  | zero =>
    intro T
    rw [Nat.mul_zero, Nat.pow_zero, Nat.mul_one]
    cases T with
    | zero => rw [dg_zero', Nat.mod_eq_of_lt ha, if_pos rfl]
    | succ T => rw [dg_succ, Nat.div_eq_of_lt ha, dg_zero_left, if_neg (Nat.succ_ne_zero T)]
  | succ S ih =>
    intro T
    have e : a * 2^(sw*(S+1)) = a * 2^(sw*S) * 2^sw := by ring
    rw [e]
    cases T with
    | zero =>
      rw [dg_zero', if_neg (Nat.succ_ne_zero S).symm]
      exact Nat.mul_mod_left _ _
    | succ T =>
      rw [dg_succ, Nat.mul_div_cancel _ (Nat.two_pow_pos sw), ih T]
      by_cases h : T = S
      · subst h
        rw [if_pos rfl, if_pos rfl]
      · rw [if_neg h, if_neg (fun h' => h (Nat.succ.inj h'))]

/-- all digits below `v` are below `2^(sw-1)` -/
def SmallV (sw v X : Nat) : Prop := ∀ T, T < v → dg sw X T < 2^(sw - 1)

theorem small_zero (sw v : Nat) : SmallV sw v 0 := by
  intro T _
  rw [dg_zero_left]
  exact Nat.two_pow_pos _

theorem two_half (sw : Nat) (hsw : 1 ≤ sw) : 2^(sw-1) + 2^(sw-1) = 2^sw := by
  have e : sw = (sw - 1) + 1 := by omega
  have h : 2^((sw - 1) + 1) = 2^(sw - 1) * 2 := Nat.pow_succ 2 (sw - 1)
  rw [← e] at h
  omega

/-- the mask test: the top bit of every digit below `v` is clear -/
theorem small_of_mask (sw v X : Nat) (hsw : 1 ≤ sw) (h : X &&& (rep sw v <<< (sw - 1)) = 0) :
    SmallV sw v X := by
  intro T hT
  have hrep := rep_bit sw (by omega) v T 0 (by omega)
  rw [Nat.add_zero] at hrep
  have hm : (rep sw v <<< (sw - 1)).testBit (sw * T + (sw - 1)) = true := by
    rw [Nat.testBit_shiftLeft, Nat.add_sub_cancel, hrep]
    simp [hT]
  have hx : X.testBit (sw * T + (sw - 1)) = false := by
    have hb : (X &&& (rep sw v <<< (sw - 1))).testBit (sw * T + (sw - 1)) = false := by
      rw [h]; exact Nat.zero_testBit _
    rw [Nat.testBit_and, hm, Bool.and_true] at hb
    exact hb
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  unfold dg
  rw [Nat.testBit_mod_two_pow]
  by_cases h1 : i < sw
  · have e : i = sw - 1 := by omega
    subst e
    rw [Nat.testBit_shiftRight, hx, Bool.and_false]
  · rw [decide_eq_false h1, Bool.false_and]

theorem dg_add_small (sw v X Y : Nat) (hsw : 1 ≤ sw) (hX : SmallV sw v X) (hY : SmallV sw v Y)
    (T : Nat) (hT : T < v) : dg sw (X + Y) T = dg sw X T + dg sw Y T := by
  apply dg_add
  intro T' hT'
  have a := hX T' (by omega)
  have b := hY T' (by omega)
  have e := two_half sw hsw
  omega

/-! ## repeated addition -/

theorem addNC_zero (tm a acc : Nat) (k : Nat → Bool) : addNC tm a 0 acc k = k acc := rfl

theorem addNC_succ (tm a n acc : Nat) (k : Nat → Bool) :
    addNC tm a (n+1) acc k
      = guard (Nat.beq (Nat.land (Nat.add acc a) tm) 0) (addNC tm a n (Nat.add acc a) k) := by
  show forceN (Nat.add acc a) (fun acc' =>
    guard (Nat.beq (Nat.land acc' tm) 0) (addNC tm a n acc' k)) = _
  rw [forceN_eq]

theorem addNC_sound (sw v tm a : Nat) (hsw : 1 ≤ sw) (htm : tm = rep sw v <<< (sw - 1))
    (ha : SmallV sw v a) : ∀ (w acc : Nat) (k : Nat → Bool), SmallV sw v acc →
      addNC tm a w acc k = true →
      ∃ r, k r = true ∧ SmallV sw v r ∧ ∀ T, T < v → dg sw r T = dg sw acc T + w * dg sw a T := by
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
    have hs := small_of_mask sw v (acc + a) hsw hm
    obtain ⟨r, hk, hr, hd⟩ := ih (acc + a) k hs h2
    refine ⟨r, hk, hr, fun T hT => ?_⟩
    rw [hd T hT, dg_add_small sw v acc a hsw hacc ha T hT, Nat.succ_mul]
    omega

/-! ## the weight of a coefficient -/

theorem wgtK_sound (isY : Bool) (cf : Coef) (k : Bool → Nat → Bool) (h : wgtK isY cf k = true) :
    ∃ ng w, k ng w = true ∧
      cf.val = (bif ng then -(w:ℚ) else (w:ℚ)) / (bif isY then (2:ℚ) else 1) := by
  obtain ⟨ng, num, den⟩ := cf
  cases isY with
  | false =>
    have h' : guard (Nat.beq den 1) (k ng num) = true := h
    obtain ⟨hb, hk⟩ := guard_true h'
    have e : den = 1 := beq_true hb
    subst e
    refine ⟨ng, num, hk, ?_⟩
    cases ng <;> simp [Coef.val]
  | true =>
    have h' : Bool.rec (motive := fun _ => Bool) (guard (Nat.beq den 1) (k ng (Nat.mul 2 num)))
        (k ng num) (Nat.beq den 2) = true := h
    cases h2 : Nat.beq den 2 with
    | true =>
      rw [h2] at h'
      have e : den = 2 := beq_true h2
      subst e
      refine ⟨ng, num, h', ?_⟩
      cases ng <;> simp [Coef.val]
    | false =>
      rw [h2] at h'
      obtain ⟨hb, hk⟩ := guard_true h'
      have e : den = 1 := beq_true hb
      subst e
      refine ⟨ng, 2 * num, hk, ?_⟩
      cases ng <;> simp [Coef.val] <;> ring

end SSC
