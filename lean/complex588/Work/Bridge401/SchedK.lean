import Work.Bridge401.Sched

/-!
# (key: bridge-401) A bank schedule as data, checked by the kernel (`schedK`)

Data (per certificate, from `bank401.json`): `rows` = 72 lists, row `k = 9 ρ + l` (time order, replica-outer), entry `q` =
the bank id of slot `q` in stage `l` of run `ρ`; `pad` = the pad rank of every bank; `res` = the residual `9 - e_q` of
every slot.  `schedK` checks 72 rows of length `R`, entries `< nb` and distinct per row (a `Nat` bitset), `nb` pads `< 73`,
`R` residuals with `72 * Σ res < 2^20`, and the packed sum `Σ_k Σ_q res q * 2^(20 * bank) = Σ_b (73 - pad b) * 2^(20 b)`
(digit-wise: every load is `73 - pad b`).  `BankSched.ofTab`, `ofTab_fits`, `ofTab_nb`, `ofTab_padPrice`.
Bank schedules: Lydakis (#275), DFT Structure.  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace GX
open Finset CB GF

/-- one row: every entry `< nb`, no entry twice (`seen` = the bitset of the entries so far). -/
def skInj (nb : ℕ) : ℕ → List ℕ → Bool
  | _, [] => true
  | seen, x :: xs => (decide (x < nb) && !(seen.testBit x)) && skInj nb (seen ||| (1 <<< x)) xs

/-- the packed residuals of one row. -/
def skRow : List ℕ → List ℕ → ℕ
  | x :: xs, r :: rs => (r <<< (20 * x)) + skRow xs rs
  | _, _ => 0

/-- the packed target loads `73 - pad`. -/
def skTgt : ℕ → List ℕ → ℕ
  | _, [] => 0
  | i, p :: ps => ((73 - p) <<< (20 * i)) + skTgt (i + 1) ps

/-- **The schedule check.** -/
def schedK (nb R : ℕ) (rows : List (List ℕ)) (pad res : List ℕ) : Bool :=
  (rows.length == 72) && rows.all (fun row => (row.length == R) && skInj nb 0 row) &&
  (pad.length == nb) && pad.all (fun p => decide (p < 73)) && (res.length == R) &&
  decide (72 * res.sum < 2 ^ 20) && ((rows.map (fun row => skRow row res)).sum == skTgt 0 pad)

/-- the bank of slot `q` in row `k`. -/
def tabF (rows : List (List ℕ)) (k q : ℕ) : ℕ := (rows.getD k []).getD q 0

section Lemmas

lemma skInj_sound (nb : ℕ) : ∀ (seen : ℕ) (xs : List ℕ), skInj nb seen xs = true →
    (∀ x ∈ xs, x < nb ∧ seen.testBit x = false) ∧ xs.Nodup := by
  intro seen xs
  induction xs generalizing seen with
  | nil => intro _; simp
  | cons x xs ih =>
    intro h
    simp only [skInj, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
    obtain ⟨⟨hx, hs⟩, hr⟩ := h
    obtain ⟨h1, h2⟩ := ih _ hr
    have hb : ∀ y, (seen ||| (1 <<< x)).testBit y = (seen.testBit y || decide (x = y)) := by
      intro y
      rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
    refine ⟨fun y hy => ?_, List.nodup_cons.mpr ⟨fun hm => ?_, h2⟩⟩
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨hx, hs⟩
      · obtain ⟨hy1, hy2⟩ := h1 y hy
        rw [hb, Bool.or_eq_false_iff] at hy2
        exact ⟨hy1, hy2.1⟩
    · have := (h1 x hm).2
      rw [hb] at this
      simp at this

lemma skRow_eq : ∀ (row res : List ℕ), row.length = res.length →
    skRow row res = ∑ q ∈ range row.length, res.getD q 0 * 2 ^ (20 * row.getD q 0) := by
  intro row
  induction row with
  | nil => intro res _; simp [skRow]
  | cons x xs ih =>
    intro res h
    cases res with
    | nil => simp at h
    | cons r rs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      rw [skRow, ih rs h, List.length_cons, Finset.sum_range_succ', Nat.shiftLeft_eq]
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      ring

lemma map_sum_eq {α M : Type} [AddCommMonoid M] (f : α → M) (d : α) : ∀ l : List α,
    (l.map f).sum = ∑ k ∈ range l.length, f (l.getD k d) := by
  intro l
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.map_cons, List.sum_cons, ih, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    exact add_comm _ _

lemma skTgt_eq : ∀ (i : ℕ) (ps : List ℕ),
    skTgt i ps = ∑ b ∈ range ps.length, (73 - ps.getD b 0) * 2 ^ (20 * (i + b)) := by
  intro i ps
  induction ps generalizing i with
  | nil => simp [skTgt]
  | cons p ps ih =>
    rw [skTgt, ih, List.length_cons, Finset.sum_range_succ', Nat.shiftLeft_eq]
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero]
    have e : ∀ b, i + 1 + b = i + (b + 1) := fun b => by ring
    simp only [e]
    ring

lemma regroup (n m : ℕ) (f g : ℕ → ℕ) (B : ℕ) (hg : ∀ q ∈ range n, g q < m) :
    ∑ q ∈ range n, f q * B ^ g q = ∑ b ∈ range m, (∑ q ∈ range n, if g q = b then f q else 0) * B ^ b := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  simp_rw [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq (range m) (g q) (fun b => f q * B ^ b), if_pos (Finset.mem_range.mpr (hg q hq))]

lemma digits_bound (B : ℕ) : ∀ (n : ℕ) (a : ℕ → ℕ), (∀ b < n, a b < B) →
    ∑ b ∈ range n, a b * B ^ b < B ^ n := by
  intro n
  induction n with
  | zero => intro a _; simp
  | succ n ih =>
    intro a ha
    rw [Finset.sum_range_succ, pow_succ]
    have h1 := ih a (fun b hb => ha b (by omega))
    have h2 : a n + 1 ≤ B := ha n (by omega)
    have h3 : (a n + 1) * B ^ n ≤ B * B ^ n := Nat.mul_le_mul_right _ h2
    nlinarith

lemma digits_unique (B : ℕ) (hB : 0 < B) : ∀ (n : ℕ) (a c : ℕ → ℕ), (∀ b < n, a b < B) → (∀ b < n, c b < B) →
    ∑ b ∈ range n, a b * B ^ b = ∑ b ∈ range n, c b * B ^ b → ∀ b < n, a b = c b := by
  intro n
  induction n with
  | zero => intro a c _ _ _ b hb; omega
  | succ n ih =>
    intro a c ha hc h b hb
    rw [Finset.sum_range_succ, Finset.sum_range_succ] at h
    have hp : 0 < B ^ n := pow_pos hB n
    have ha' := digits_bound B n a (fun b hb => ha b (by omega))
    have hc' := digits_bound B n c (fun b hb => hc b (by omega))
    have hd : a n = c n := by
      have e1 : (∑ b ∈ range n, a b * B ^ b + a n * B ^ n) / B ^ n
          = (∑ b ∈ range n, c b * B ^ b + c n * B ^ n) / B ^ n := by rw [h]
      rw [Nat.add_mul_div_right _ _ hp, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt ha',
        Nat.div_eq_of_lt hc'] at e1
      omega
    have hs : ∑ b ∈ range n, a b * B ^ b = ∑ b ∈ range n, c b * B ^ b := by
      rw [hd] at h
      omega
    rcases Nat.lt_succ_iff_lt_or_eq.mp hb with hb | rfl
    · exact ih a c (fun b hb => ha b (by omega)) (fun b hb => hc b (by omega)) hs b hb
    · exact hd

lemma nodup_getD_inj {l : List ℕ} (hl : l.Nodup) {i j : ℕ} (hi : i < l.length) (hj : j < l.length)
    (h : l.getD i 0 = l.getD j 0) : i = j := by
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at h
  exact hl.getElem_inj_iff.mp h

end Lemmas

section Sound
variable {nb R : ℕ} {rows : List (List ℕ)} {pad res : List ℕ}

lemma schedK_parts (h : schedK nb R rows pad res = true) :
    rows.length = 72 ∧ (∀ row ∈ rows, row.length = R ∧ skInj nb 0 row = true) ∧ pad.length = nb ∧
      (∀ p ∈ pad, p < 73) ∧ res.length = R ∧ 72 * res.sum < 2 ^ 20 ∧
      (rows.map (fun row => skRow row res)).sum = skTgt 0 pad := by
  simp only [schedK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

lemma row_mem (h : schedK nb R rows pad res = true) {k : ℕ} (hk : k < 72) : rows.getD k [] ∈ rows := by
  have hl := (schedK_parts h).1
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact List.getElem_mem _

lemma row_len (h : schedK nb R rows pad res = true) {k : ℕ} (hk : k < 72) : (rows.getD k []).length = R :=
  ((schedK_parts h).2.1 _ (row_mem h hk)).1

lemma row_ok (h : schedK nb R rows pad res = true) {k : ℕ} (hk : k < 72) :
    (∀ x ∈ rows.getD k [], x < nb ∧ (0 : ℕ).testBit x = false) ∧ (rows.getD k []).Nodup :=
  skInj_sound nb 0 _ ((schedK_parts h).2.1 _ (row_mem h hk)).2

lemma tabF_lt (h : schedK nb R rows pad res = true) {k q : ℕ} (hk : k < 72) (hq : q < R) :
    tabF rows k q < nb := by
  have hl := row_len h hk
  unfold tabF
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact ((row_ok h hk).1 _ (List.getElem_mem _)).1

end Sound

/-- **A checked table as a bank schedule.** -/
def BankSched.ofTab (nb R : ℕ) (rows : List (List ℕ)) (pad res : List ℕ) (h : schedK nb R rows pad res = true) :
    BankSched (Fin R) where
  nb := nb
  use ρ l q := ⟨tabF rows (9 * ρ.val + l.val) q.val, tabF_lt h (by have := ρ.isLt; have := l.isLt; omega) q.isLt⟩
  hinj ρ l := by
    intro q1 q2 he
    have hk : 9 * ρ.val + l.val < 72 := by have := ρ.isLt; have := l.isLt; omega
    have e : tabF rows (9 * ρ.val + l.val) q1.val = tabF rows (9 * ρ.val + l.val) q2.val := congrArg Fin.val he
    have hl := row_len h hk
    exact Fin.ext (nodup_getD_inj (row_ok h hk).2 (by rw [hl]; exact q1.isLt) (by rw [hl]; exact q2.isLt) e)
  pad b := pad.getD b.val 0

section Fits
variable (nb R : ℕ) (rows : List (List ℕ)) (pad res : List ℕ) (h : schedK nb R rows pad res = true)

lemma BankSched.ofTab_nb : (BankSched.ofTab nb R rows pad res h).nb = nb := rfl

lemma BankSched.ofTab_pad (b : Fin nb) : (BankSched.ofTab nb R rows pad res h).pad b = pad.getD b.val 0 := rfl

/-- the pad price of a checked table. -/
lemma BankSched.ofTab_padPrice (φ : ℕ → ℝ) :
    ∑ b : Fin (BankSched.ofTab nb R rows pad res h).nb, bcost φ ((BankSched.ofTab nb R rows pad res h).pad b)
      = rcost φ pad := by
  show ∑ b : Fin nb, bcost φ (pad.getD b.val 0) = rcost φ pad
  have hl := (schedK_parts h).2.2.1
  unfold rcost
  rw [map_sum_eq (bcost φ) 0 pad, hl]
  exact Fin.sum_univ_eq_sum_range (fun b => bcost φ (pad.getD b 0)) nb

/-- the load of a bank of a checked table, as a finite sum over rows and slots. -/
lemma BankSched.ofTab_load (b : Fin nb) :
    (BankSched.ofTab nb R rows pad res h).load (fun q => res.getD q.val 0) b
      = ∑ k ∈ range 72, ∑ q ∈ range R, if tabF rows k q = b.val then res.getD q 0 else 0 := by
  rw [← BankSched.L_eq (BankSched.ofTab nb R rows pad res h) (fun q => res.getD q.val 0) b]
  unfold B401.L B401.rr
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk' : k < 72 := Finset.mem_range.mp hk
  rw [Finset.sum_filter]
  have e : ∀ q : Fin R, ((BankSched.ofTab nb R rows pad res h).useK k q = b) ↔ tabF rows k q.val = b.val := by
    intro q
    have ek : 9 * (k / 9 % 8) + k % 9 = k := by omega
    show (⟨tabF rows (9 * (k / 9 % 8) + k % 9) q.val, _⟩ : Fin nb) = b ↔ _
    rw [Fin.ext_iff]
    simp only [ek]
  simp_rw [e]
  exact Fin.sum_univ_eq_sum_range (fun q => if tabF rows k q = b.val then res.getD q 0 else 0) R

/-- **A checked table fits the entrance labels whose residuals are `res`.** -/
theorem BankSched.ofTab_fits {H : Type} [Fintype H] (ent : Fin R → SLbl H)
    (hent : ∀ q, Fintype.card H - (ent q).dim = res.getD q.val 0) :
    (BankSched.ofTab nb R rows pad res h).fits ent := by
  obtain ⟨hlen, hrows, hpl, hpd, hrl, hsum, heq⟩ := schedK_parts h
  have hr : (fun q : Fin R => Fintype.card H - (ent q).dim) = (fun q => res.getD q.val 0) := funext hent
  have hpad : ∀ b : Fin nb, pad.getD b.val 0 < 73 := fun b =>
    hpd _ (by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)
  refine ⟨fun b => ?_, fun b => hpad b⟩
  show (BankSched.ofTab nb R rows pad res h).load (fun q => Fintype.card H - (ent q).dim) b + pad.getD b.val 0 = 73
  rw [hr, BankSched.ofTab_load nb R rows pad res h b]
  -- the packed identity, digit by digit
  let a : ℕ → ℕ := fun c => ∑ k ∈ range 72, ∑ q ∈ range R, if tabF rows k q = c then res.getD q 0 else 0
  let cc : ℕ → ℕ := fun c => 73 - pad.getD c 0
  have htot : ∀ c, a c ≤ 72 * res.sum := by
    intro c
    have e1 : ∑ q ∈ range R, res.getD q 0 = res.sum := by
      rw [← hrl]
      have := map_sum_eq (fun x : ℕ => x) 0 res
      simpa using this.symm
    calc a c ≤ ∑ k ∈ range 72, ∑ q ∈ range R, res.getD q 0 := by
          refine Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun q _ => ?_))
          split_ifs <;> omega
      _ = 72 * res.sum := by rw [e1, Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hL : (rows.map (fun row => skRow row res)).sum = ∑ c ∈ range nb, a c * (2 ^ 20) ^ c := by
    rw [map_sum_eq (fun row => skRow row res) [] rows, hlen]
    have e2 : ∀ k ∈ range 72, skRow (rows.getD k []) res
        = ∑ c ∈ range nb, (∑ q ∈ range R, if tabF rows k q = c then res.getD q 0 else 0) * (2 ^ 20) ^ c := by
      intro k hk
      have hk' : k < 72 := Finset.mem_range.mp hk
      have hl := row_len h hk'
      rw [skRow_eq _ _ (by rw [hl, hrl]), hl]
      simp_rw [pow_mul]
      exact regroup R nb (fun q => res.getD q 0) (fun q => tabF rows k q) (2 ^ 20)
        (fun q hq => tabF_lt h hk' (Finset.mem_range.mp hq))
    rw [Finset.sum_congr rfl e2, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.sum_mul]
  have hT : skTgt 0 pad = ∑ c ∈ range nb, cc c * (2 ^ 20) ^ c := by
    rw [skTgt_eq, hpl]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Nat.zero_add, pow_mul]
  have hd := digits_unique (2 ^ 20) (by norm_num) nb a cc
    (fun c _ => lt_of_le_of_lt (htot c) hsum) (fun c _ => by show 73 - pad.getD c 0 < 2 ^ 20; omega)
    (by rw [← hL, ← hT]; exact heq) b.val b.isLt
  show a b.val + pad.getD b.val 0 = 73
  rw [hd]
  show 73 - pad.getD b.val 0 + pad.getD b.val 0 = 73
  have := hpad b
  omega

end Fits
end GX
end PowerSaving
end OAI



#print axioms OAI.PowerSaving.GX.BankSched.ofTab_fits
#print axioms OAI.PowerSaving.GX.BankSched.ofTab_padPrice
