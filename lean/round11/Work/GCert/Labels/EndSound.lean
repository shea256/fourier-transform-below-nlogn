import Work.GCert.Labels.Ends

/-!
# (key: gx-labels) Soundness of the end check: `endK … = true → Ends …`

`PortOK p v S0 SA SF t u`: everything the chain asks about port `t` with mask `u`
(`x_t`, `y_t` at the start, at the scatter, at the end).  `Ends`: shape, all ports, all slots,
all retained registers.  **`endK_sound`** (needs the checked frame table).

No `sorry`.
-/

set_option linter.unusedVariables false
set_option linter.deprecated false

namespace GLab
open SSC GXD OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.GF Finset

/-- what the end check proves about port `t` with mask `u` -/
structure PortOK (p : Par) (v : Nat) (S0 SA SF : Trie) (t u : Nat) : Prop where
  unit : dot (tvec p.h u) (tvec p.h u) = 1
  gap : ∃ q : Fin p.h, tvec p.h u q = 0
  x0d : cdim (p.tab.get (S0.get t)) = 1
  x0m : (lab p.h (p.tab.get (S0.get t))).Mem (tvec p.h u)
  y0 : S0.get (v + t) = 0
  yA : SA.get (v + t) = 0
  xF : cdim (p.tab.get (SF.get t)) = p.h
  yFd : cdim (p.tab.get (SF.get (v + t))) + 1 = p.h
  yFm : ∀ x, (lab p.h (p.tab.get (SF.get (v + t)))).Mem x → dot (tvec p.h u) x = 0

theorem portsK_sound (p : Par) (hT : tabK p.h p.tab = true) (hh : 0 < p.h) (v : Nat)
    (S0 SA SF : Trie) : ∀ (l : List Nat) (t0 : Nat),
    portsK p (2 ^ p.h - 1) (rep p.h p.h) (Nat.add 8 p.h) v S0 SA SF l t0 = true →
    t0 + l.length = v ∧ ∀ i, i < l.length → PortOK p v S0 SA SF (t0 + i) (l.getD i 0) := by
  intro l
  induction l with
  | nil =>
    intro t0 H
    exact ⟨beq_true H, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | cons u l ih =>
    intro t0 H
    obtain ⟨g1, H⟩ := guard_true H
    obtain ⟨g2, H⟩ := guard_true H
    have H := getK_true _ _ _ H
    have H := getK_true _ _ _ H
    obtain ⟨g3, H⟩ := guard_true H
    obtain ⟨g4, H⟩ := guard_true H
    have H := getK_true _ _ _ H
    obtain ⟨g5, H⟩ := guard_true H
    have H := getK_true _ _ _ H
    obtain ⟨g6, H⟩ := guard_true H
    have H := getK_true _ _ _ H
    have H := getK_true _ _ _ H
    obtain ⟨g7, H⟩ := guard_true H
    have H := getK_true _ _ _ H
    have H := getK_true _ _ _ H
    obtain ⟨g8, H⟩ := guard_true H
    obtain ⟨g9, H⟩ := guard_true H
    rw [forceN_eq] at H
    obtain ⟨a, b⟩ := ih _ H
    have hu : u < 2 ^ p.h - 1 := ble_true g1
    have hu' : u < 2 ^ p.h := by omega
    have P0 : PortOK p v S0 SA SF t0 u :=
      { unit := unit_of_pars p.h u (beq_true g2)
        gap := gap_of_lt p.h u hu
        x0d := beq_true g3
        x0m := mem_of_elim p.h hh _ u (tabK_good p.h p.tab hT _) g4
        y0 := beq_true g5
        yA := beq_true g6
        xF := beq_true g7
        yFd := beq_true g8
        yFm := perp_of_dots p.h _ (tabK_good p.h p.tab hT _) _
          (dots_zero p.h hh _ u hu' (beq_true g9)) }
    refine ⟨by simp only [List.length_cons]; omega, fun i hi => ?_⟩
    cases i with
    | zero => exact P0
    | succ i =>
      have e : t0 + (i + 1) = t0.succ + i := by omega
      rw [e]
      exact b i (by simpa using hi)

theorem slotsK_sound (p : Par) (v2 : Nat) (S0 SF : Trie) : ∀ n, slotsK p v2 S0 SF n = true →
    ∀ q, q < n → S0.get (v2 + q) = 0 ∧ cdim (p.tab.get (SF.get (v2 + q))) = p.h := by
  intro n
  induction n with
  | zero => intro _ q hq; exact absurd hq (Nat.not_lt_zero q)
  | succ n ih =>
    intro H q hq
    have H := getK_true _ _ _ H
    obtain ⟨g1, H⟩ := guard_true H
    have H := getK_true _ _ _ H
    have H := getK_true _ _ _ H
    obtain ⟨g2, H⟩ := guard_true H
    rcases Nat.lt_succ_iff_lt_or_eq.mp hq with h1 | h1
    · exact ih H q h1
    · rw [h1]; exact ⟨beq_true g1, beq_true g2⟩

theorem retsK_sound (p : Par) (SA : Trie) : ∀ l, retsK p SA l = true →
    ∀ r ∈ l, 0 < cdim (p.tab.get (SA.get r)) := by
  intro l
  induction l with
  | nil => intro _ r hr; exact absurd hr List.not_mem_nil
  | cons a l ih =>
    intro H r hr
    have H := getK_true _ _ _ H
    have H := getK_true _ _ _ H
    obtain ⟨g1, H⟩ := guard_true H
    rcases List.mem_cons.mp hr with h1 | h1
    · rw [h1]; exact ble_true g1
    · exact ih H r h1

/-- everything the end check proves -/
structure Ends (p : Par) (v : Nat) (ports rets : List Nat) (S0 SA SF : Trie) : Prop where
  hh : 0 < p.h
  w0 : S0.wf p.d
  hn : p.n ≤ 2 ^ p.d
  hv : 2 * v ≤ p.n
  z0 : cdim (p.tab.get 0) = 0
  len : ports.length = v
  port : ∀ t, t < v → PortOK p v S0 SA SF t (ports.getD t 0)
  slot : ∀ q, q < p.n - 2 * v →
    S0.get (2 * v + q) = 0 ∧ cdim (p.tab.get (SF.get (2 * v + q))) = p.h
  ret : ∀ r ∈ rets, 0 < cdim (p.tab.get (SA.get r))

/-- **soundness of the end check** -/
theorem endK_sound {p : Par} {v : Nat} {ports rets : List Nat} {S0 SA SF : Trie}
    (hT : tabK p.h p.tab = true) (H : endK p v ports rets S0 SA SF = true) :
    Ends p v ports rets S0 SA SF := by
  unfold endK at H
  obtain ⟨g0, H⟩ := guard_true H
  obtain ⟨g1, H⟩ := guard_true H
  obtain ⟨g2, H⟩ := guard_true H
  obtain ⟨g3, H⟩ := guard_true H
  have H := getK_true _ _ _ H
  obtain ⟨g4, H⟩ := guard_true H
  rw [forceN_eq] at H
  rw [forceN_eq] at H
  obtain ⟨g5, H⟩ := guard_true H
  have hh : 0 < p.h := ble_true g0
  have eO : Nat.div (Nat.sub (Nat.pow 2 (Nat.mul p.h p.h)) 1) (Nat.sub (Nat.pow 2 p.h) 1)
      = rep p.h p.h := rep_of_mul p.h p.h _ hh (beq_true g5)
  rw [eO] at H
  obtain ⟨g6, H⟩ := guard_true H
  obtain ⟨g7, g8⟩ := guard_true H
  obtain ⟨a, b⟩ := portsK_sound p hT hh v S0 SA SF ports 0 g6
  have len : ports.length = v := by omega
  exact
    { hh := hh
      w0 := wfK_sound _ _ g1
      hn := ble_true g2
      hv := ble_true g3
      z0 := beq_true g4
      len := len
      port := fun t ht => by
        have := b t (by omega)
        rw [Nat.zero_add] at this
        exact this
      slot := slotsK_sound p _ S0 SF _ g7
      ret := retsK_sound p SA rets g8 }

end GLab

#print axioms GLab.endK_sound
