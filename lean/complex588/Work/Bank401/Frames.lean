import Work.Bank401.Adapt
import Work.GFrame.Top.Api

/-!
# (key: bank-401, L2/L3) The frames of all banks over a schedule of uses

A schedule of `K` sub-stages: in sub-stage `k` the slot `q` of the invocation `d` uses the bank `(d, use k q)`
(`use k` injective: at most ONE use of a bank per sub-stage).  The gauged step of `q` is
`Wn k d q = C * pk R * C'` with `C`, `C'` free and `|R| = r q` (the residual `9 - e_q`; `gauged_Wn`).
`L k b` is the load of bank `b` after `k` sub-stages.

`bank_frames`: there are bank frames `Zb k d b` (before sub-stage `k`) and `Zp k d b` (after the free adapter of
sub-stage `k`) with
* `Zb 0 = 1`;
* `Zb k → Zp k` is free (`bank_adapt`, an address permutation between free adapters);
* a used bank: `Wn k d q * Zp k d (use k q) = Zb (k+1) d (use k q)`; an unused bank: `Zb (k+1) = Zp k`;
* `Zb K → kernel α` is ONE block of rank `card α - L K b` (the pad; free if the bank is full).

The entrance gauges and residual banks are Dugongue's (CrocSwap/integer-mult-bounds PR #401); the engine is Jacob
Sussman's.  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace B401
open Binary Matrix Finset GF CB
noncomputable section

section Sched
variable {α Γ Sl : Type} [Fintype α] [DecidableEq α] [Fintype Sl] [DecidableEq Sl] {nb : ℕ}
variable (use : ℕ → Sl → Fin nb) (r : Sl → ℕ)

/-- the residual the bank `b` takes in sub-stage `k`. -/
def rr (k : ℕ) (b : Fin nb) : ℕ := ∑ q ∈ univ.filter (fun q => use k q = b), r q

/-- the load of the bank `b` after `k` sub-stages. -/
def L (k : ℕ) (b : Fin nb) : ℕ := ∑ j ∈ range k, rr use r j b

lemma L_zero (b : Fin nb) : L use r 0 b = 0 := by simp [L]

lemma L_succ (k : ℕ) (b : Fin nb) : L use r (k + 1) b = L use r k b + rr use r k b := by
  simp [L, Finset.sum_range_succ]

lemma L_mono {k k' : ℕ} (h : k ≤ k') (b : Fin nb) : L use r k b ≤ L use r k' b :=
  Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr h)

lemma rr_of_use {k : ℕ} (hinj : Function.Injective (use k)) {q : Sl} {b : Fin nb} (hq : use k q = b) :
    rr use r k b = r q := by
  unfold rr
  rw [Finset.sum_eq_single q]
  · intro q' hq' hne
    exact absurd (hinj ((Finset.mem_filter.mp hq').2.trans hq.symm)) hne
  · intro h
    exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ q, hq⟩) h

lemma rr_of_not {k : ℕ} {b : Fin nb} (h : ∀ q, use k q ≠ b) : rr use r k b = 0 := by
  unfold rr
  exact Finset.sum_eq_zero (fun q hq => absurd (Finset.mem_filter.mp hq).2 (h q))

variable (Wn : ℕ → Γ → Sl → CMat α)

/-- the property of one step of one bank (`t = (P, A2, U2)`). -/
def StepOk (k : ℕ) (d : Γ) (b : Fin nb) (A : CMat α) (U : Finset α) (t : CMat α × CMat α × Finset α) : Prop :=
  Free t.1 ∧ Free t.2.1 ∧ t.2.2.card = L use r (k + 1) b ∧
    (∀ q, use k q = b → Wn k d q * (t.1 * (A * pk U)) = t.2.1 * pk t.2.2) ∧
    ((∀ q, use k q ≠ b) → t.1 = 1 ∧ t.2.1 * pk t.2.2 = A * pk U)

lemma step_ex {k : ℕ} (d : Γ) (b : Fin nb) {A : CMat α} {U : Finset α} (hA : Free A)
    (hU : U.card = L use r k b) (hb : L use r (k + 1) b ≤ Fintype.card α)
    (hinj : Function.Injective (use k))
    (hWn : ∀ q, ∃ (C C' : CMat α) (R : Finset α), Free C ∧ Free C' ∧ R.card = r q ∧ Wn k d q = C * pk R * C') :
    ∃ t, StepOk use r Wn k d b A U t := by
  by_cases h : ∃ q, use k q = b
  · obtain ⟨q0, hq0⟩ := h
    obtain ⟨C, C', R, hC, hC', hR, hW⟩ := hWn q0
    have hL : L use r (k + 1) b = U.card + R.card := by
      rw [L_succ, rr_of_use use r hinj hq0, hU, hR]
    obtain ⟨P, hP, A2, U2, hA2, -, hc, he⟩ := bank_adapt (B := 1) hA hC hC' U R (by rw [← hL]; exact hb)
    refine ⟨(P, A2, U2), hP, hA2, by rw [hL]; exact hc, fun q hq => ?_, fun hn => absurd hq0 (hn q0)⟩
    have e : q = q0 := hinj (hq.trans hq0.symm)
    subst e
    rw [Matrix.mul_one, Matrix.mul_one] at he
    show Wn k d q * (P * (A * pk U)) = A2 * pk U2
    rw [hW]
    exact he
  · push_neg at h
    refine ⟨(1, A, U), Free.one, hA, ?_, fun q hq => absurd hq (h q), fun _ => ⟨rfl, rfl⟩⟩
    show U.card = L use r (k + 1) b
    rw [L_succ, rr_of_not use r h, hU, Nat.add_zero]

variable (K : ℕ)

/-- the guarded existence (outside the schedule or above the bound: anything). -/
lemma step_ex' (hinj : ∀ k < K, Function.Injective (use k))
    (hWn : ∀ k < K, ∀ d q, ∃ (C C' : CMat α) (R : Finset α), Free C ∧ Free C' ∧ R.card = r q ∧
      Wn k d q = C * pk R * C')
    (k : ℕ) (d : Γ) (b : Fin nb) (s : {p : CMat α × Finset α // Free p.1 ∧
      (k ≤ K → L use r k b ≤ Fintype.card α → p.2.card = L use r k b)}) :
    ∃ t : CMat α × CMat α × Finset α, Free t.2.1 ∧
      (k < K → L use r (k + 1) b ≤ Fintype.card α → StepOk use r Wn k d b s.1.1 s.1.2 t) := by
  by_cases hk : k < K
  · by_cases hb : L use r (k + 1) b ≤ Fintype.card α
    · have hU := s.2.2 hk.le (le_trans (L_mono use r (Nat.le_succ k) b) hb)
      obtain ⟨t, ht⟩ := step_ex use r Wn d b s.2.1 hU hb (hinj k hk) (hWn k hk d)
      exact ⟨t, ht.2.1, fun _ _ => ht⟩
    · exact ⟨(1, s.1.1, s.1.2), s.2.1, fun _ h => absurd h hb⟩
  · exact ⟨(1, s.1.1, s.1.2), s.2.1, fun h => absurd h hk⟩


/-- the state `(A, U)` of every bank after `k` sub-stages, with the step `(P, A2, U2)` of sub-stage `k`. -/
def stS (hinj : ∀ k < K, Function.Injective (use k))
    (hWn : ∀ k < K, ∀ d q, ∃ (C C' : CMat α) (R : Finset α), Free C ∧ Free C' ∧ R.card = r q ∧
      Wn k d q = C * pk R * C') (d : Γ) (b : Fin nb) : (k : ℕ) → {p : CMat α × Finset α // Free p.1 ∧
    (k ≤ K → L use r k b ≤ Fintype.card α → p.2.card = L use r k b)}
  | 0 => ⟨(1, ∅), Free.one, fun _ _ => by rw [L_zero]; rfl⟩
  | k + 1 =>
    let t := Classical.choose (step_ex' use r Wn K hinj hWn k d b (stS hinj hWn d b k))
    have ht := Classical.choose_spec (step_ex' use r Wn K hinj hWn k d b (stS hinj hWn d b k))
    ⟨(t.2.1, t.2.2), ht.1, fun hk hb => (ht.2 (Nat.lt_of_succ_le hk) hb).2.2.1⟩

/-- the step of sub-stage `k`. -/
def stT (hinj : ∀ k < K, Function.Injective (use k))
    (hWn : ∀ k < K, ∀ d q, ∃ (C C' : CMat α) (R : Finset α), Free C ∧ Free C' ∧ R.card = r q ∧
      Wn k d q = C * pk R * C') (d : Γ) (b : Fin nb) (k : ℕ) : CMat α × CMat α × Finset α :=
  Classical.choose (step_ex' use r Wn K hinj hWn k d b (stS use r Wn K hinj hWn d b k))

lemma stT_spec (hinj : ∀ k < K, Function.Injective (use k))
    (hWn : ∀ k < K, ∀ d q, ∃ (C C' : CMat α) (R : Finset α), Free C ∧ Free C' ∧ R.card = r q ∧
      Wn k d q = C * pk R * C') (d : Γ) (b : Fin nb) (k : ℕ) (hk : k < K) (hb : L use r (k + 1) b ≤ Fintype.card α) :
    StepOk use r Wn k d b (stS use r Wn K hinj hWn d b k).1.1 (stS use r Wn K hinj hWn d b k).1.2
      (stT use r Wn K hinj hWn d b k) :=
  (Classical.choose_spec (step_ex' use r Wn K hinj hWn k d b (stS use r Wn K hinj hWn d b k))).2 hk hb

lemma stS_succ (hinj : ∀ k < K, Function.Injective (use k))
    (hWn : ∀ k < K, ∀ d q, ∃ (C C' : CMat α) (R : Finset α), Free C ∧ Free C' ∧ R.card = r q ∧
      Wn k d q = C * pk R * C') (d : Γ) (b : Fin nb) (k : ℕ) :
    (stS use r Wn K hinj hWn d b (k + 1)).1 =
      ((stT use r Wn K hinj hWn d b k).2.1, (stT use r Wn K hinj hWn d b k).2.2) := rfl

/-- **The bank frames of a schedule.** -/
theorem bank_frames (hinj : ∀ k < K, Function.Injective (use k))
    (hWn : ∀ k < K, ∀ d q, ∃ (C C' : CMat α) (R : Finset α), Free C ∧ Free C' ∧ R.card = r q ∧
      Wn k d q = C * pk R * C')
    (hload : ∀ b, L use r K b ≤ Fintype.card α) (hpos : ∀ b, 1 ≤ L use r K b) :
    ∃ (Zb Zp : ℕ → Γ → Fin nb → CMat α),
      (∀ d b, Zb 0 d b = 1) ∧
      (∀ k < K, ∀ d b, GReach (Zb k d b) (Zp k d b) (fun _ => 0)) ∧
      (∀ k < K, ∀ d q, Wn k d q * Zp k d (use k q) = Zb (k + 1) d (use k q)) ∧
      (∀ k < K, ∀ d b, (∀ q, use k q ≠ b) → Zb (k + 1) d b = Zp k d b) ∧
      (∀ d b, GReach (Zb K d b) (kernel α) (fun φ => bcost φ (Fintype.card α - L use r K b))) := by
  let S := stS use r Wn K hinj hWn
  let T := stT use r Wn K hinj hWn
  have hb' : ∀ k < K, ∀ b, L use r (k + 1) b ≤ Fintype.card α := fun k hk b =>
    le_trans (L_mono use r (Nat.succ_le_of_lt hk) b) (hload b)
  refine ⟨fun k d b => (S d b k).1.1 * pk (S d b k).1.2,
    fun k d b => (T d b k).1 * ((S d b k).1.1 * pk (S d b k).1.2), ?_, ?_, ?_, ?_, ?_⟩
  · intro d b
    show 1 * pk ∅ = 1
    rw [pk_empty, Matrix.one_mul]
  · intro k hk d b
    have h := (stT_spec use r Wn K hinj hWn d b k hk (hb' k hk b)).1
    exact fun ρ _ _ l => gstep_free h l _
  · intro k hk d q
    have h := (stT_spec use r Wn K hinj hWn d (use k q) k hk (hb' k hk _)).2.2.2.1 q rfl
    show Wn k d q * ((T d (use k q) k).1 * ((S d (use k q) k).1.1 * pk (S d (use k q) k).1.2))
      = (S d (use k q) (k + 1)).1.1 * pk (S d (use k q) (k + 1)).1.2
    rw [h, stS_succ]
  · intro k hk d b hn
    have h := (stT_spec use r Wn K hinj hWn d b k hk (hb' k hk b)).2.2.2.2 hn
    show (S d b (k + 1)).1.1 * pk (S d b (k + 1)).1.2
      = (T d b k).1 * ((S d b k).1.1 * pk (S d b k).1.2)
    rw [stS_succ, h.1, h.2, Matrix.one_mul]
  · intro d b
    have hA := (S d b K).2.1
    have hU : (S d b K).1.2.card = L use r K b := (S d b K).2.2 le_rfl (hload b)
    show GReach ((S d b K).1.1 * pk (S d b K).1.2) (kernel α) _
    rcases Nat.lt_or_ge (L use r K b) (Fintype.card α) with hlt | hge
    · intro ρ _ _ l
      have h := bank_pad l hA 1 (S d b K).1.2 (by rw [hU]; exact hlt) (by rw [hU]; exact hpos b)
      rw [Matrix.mul_one, Matrix.mul_one, hU] at h
      refine h.cast (fun φ => ?_)
      rw [bcost_pos φ (by omega)]
    · have he : (S d b K).1.2 = univ := by
        apply Finset.eq_univ_of_card
        rw [hU]; exact le_antisymm (hload b) hge
      intro ρ _ _ l
      have h := bank_full l hA 1
      rw [Matrix.mul_one, Matrix.mul_one, ← he] at h
      refine h.cast (fun φ => ?_)
      rw [show Fintype.card α - L use r K b = 0 by omega, bcost_zero]

end Sched
end
end B401
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.B401.bank_frames
