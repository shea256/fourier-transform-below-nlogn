import Work.GCert.Scalar.Roles

/-!
# (key: gx-scalar) Matrix lemmas for gates INTO x roles and gates READING y roles

* `XU`            "the x rows are supported on the x columns"; `XU_mic` (every add into an x role
  reads an x role), `XU_mul`, `XU_scat`;
* `ycol_filter`   the y columns of a gate product are those of the product of the adds that READ
  a y role (when these also write a y role);
* `GRun_all`      every done add of a run passes its kind test and has `t ≠ s`;
* `okA_spec`, `okB_spec`, `U_x`, `U_y`.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace GS
open SSC GXD OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM OAI.PowerSaving.SS
  OAI.PowerSaving.CB OAI.PowerSaving.CR Finset Matrix

theorem okA_spec {v v2 nr t s : Nat} (h : okAK v v2 nr t s = true) :
    t < nr ∧ s < nr ∧ v2 ≤ t ∧ (s < v ∨ v2 ≤ s) := by
  simp only [okAK, Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq] at h
  omega

theorem okB_spec {v v2 nr t s : Nat} (h : okBK v v2 nr t s = true) :
    t < nr ∧ s < nr ∧ (v ≤ t ∨ s < v) ∧ (s < v ∨ v2 ≤ s ∨ (v ≤ t ∧ t < v2)) := by
  simp only [okBK, Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq] at h
  omega

theorem selY_spec {v v2 s : Nat} : selY v v2 s = true ↔ v ≤ s ∧ s < v2 := by
  simp only [selY, Bool.and_eq_true, Nat.ble_eq]
  omega

theorem U_x (c : Raw) (p : SPar) (r : Nat) (h : r < c.v) : U c p r = p.ux := by
  have e : Nat.ble (Nat.succ r) c.v = true := Nat.ble_eq_true_of_le h
  unfold U unitK
  rw [e]

theorem U_y (c : Raw) (p : SPar) (r : Nat) (h1 : c.v ≤ r) (h2 : r < 2 * c.v) : U c p r = p.uy := by
  have e1 : Nat.ble (Nat.succ r) c.v = false :=
    Bool.eq_false_iff.mpr (fun h => by have := ble_true h; omega)
  have e2 : Nat.ble (Nat.succ r) (2 * c.v) = true := Nat.ble_eq_true_of_le h2
  unfold U unitK
  rw [e1, e2]

/-- every done add of a run passes its kind test and joins two different registers -/
theorem GRun_all (sw n : Nat) (u : Nat → Nat) (okf : Nat → Nat → Bool) (sel : Nat → Bool)
    (l : List (Nat × Nat × Co)) : ∀ (a b : SSt), GRun sw n u okf sel a l b →
    ∀ x ∈ l, sel x.2.1 = true → okf x.1 x.2.1 = true ∧ x.1 ≠ x.2.1 := by
  induction l with
  | nil => intro a b _ x hx; exact absurd hx List.not_mem_nil
  | cons y l ih =>
    intro a b h x hx hsx
    have h' : if sel y.2.1 = true then (okf y.1 y.2.1 = true ∧ ∃ m, GStep sw n u y.1 y.2.1
        (toCoef y.2.2) a m ∧ GRun sw n u okf sel m l b) else GRun sw n u okf sel a l b := h
    by_cases hs : sel y.2.1 = true
    · rw [if_pos hs] at h'
      obtain ⟨ho, m, hst, hr⟩ := h'
      rcases List.mem_cons.mp hx with e | e
      · rw [e]; exact ⟨ho, hst.1⟩
      · exact ih m b hr x e hsx
    · rw [if_neg hs] at h'
      rcases List.mem_cons.mp hx with e | e
      · rw [e] at hsx; exact absurd hsx hs
      · exact ih a b h' x e hsx

theorem mem_mic (l : List (Nat × Nat × Co)) (t s : Nat) (cf : Coef)
    (h : Micro.add t s cf ∈ mic l) : ∃ x ∈ l, x.1 = t ∧ x.2.1 = s := by
  obtain ⟨x, hx, e⟩ := List.mem_map.mp h
  have e' : Micro.add x.1 x.2.1 (toCoef x.2.2) = Micro.add t s cf := e
  injection e' with e1 e2 e3
  exact ⟨x, hx, e1, e2⟩

section
variable {T Sl : Type} [Fintype T] [DecidableEq T] [Fintype Sl] [DecidableEq Sl]

/-- the x rows are supported on the x columns -/
def XU (M : Matrix (L3 T Sl) (L3 T Sl) ℚ) : Prop :=
  ∀ (t : T) (j : L3 T Sl), (∀ τ : T, j ≠ lX τ) → M (lX t) j = 0

theorem XU_mul (A B : Matrix (L3 T Sl) (L3 T Sl) ℚ) (hA : XU A) (hB : XU B) : XU (A * B) := by
  intro t j hj
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  rcases k with (τ | S) | q
  · rw [hB τ j hj, mul_zero]
  · rw [hA t _ (fun τ h => by cases h), zero_mul]
  · rw [hA t _ (fun τ h => by cases h), zero_mul]

theorem XU_scat (K : Matrix T Sl ℚ) : XU (scatM K) := by
  intro t j hj
  unfold scatM
  rw [Matrix.add_apply, Matrix.one_apply, embYS_rowX, add_zero, if_neg (fun h => hj t h.symm)]

/-- every add into an x role reads an x role: the gate product keeps the x rows on the x columns -/
theorem XU_mic (un : Nat → L3 T Sl) (l : List (Nat × Nat × Co))
    (h : ∀ x ∈ l, ∀ τ : T, un x.1 = lX τ → ∃ σ : T, un x.2.1 = lX σ) : XU (matP un (mic l)) := by
  induction l with
  | nil =>
    intro t j hj
    show (1 : Matrix (L3 T Sl) (L3 T Sl) ℚ) (lX t) j = 0
    rw [Matrix.one_apply, if_neg (fun e => hj t e.symm)]
  | cons x l ih =>
    have ih' := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    intro t j hj
    show (matP un (mic l) * addMat (un x.1) (un x.2.1) (toCoef x.2.2).val) (lX t) j = 0
    rw [mul_addMat_apply, ih' t j hj, zero_add]
    by_cases e : j = un x.2.1
    · rw [if_pos e]
      have ha : ∀ τ : T, un x.1 ≠ lX τ := by
        intro τ hτ
        obtain ⟨σ, hσ⟩ := h x (List.mem_cons_self ..) τ hτ
        exact hj σ (e.trans hσ)
      rw [ih' t _ ha, mul_zero]
    · rw [if_neg e]

/-- the y columns of a gate product: only the adds READING a y role count (they write y roles) -/
theorem ycol_filter (un : Nat → L3 T Sl) (sel : Nat → Bool) (l : List (Nat × Nat × Co))
    (h1 : ∀ x ∈ l, sel x.2.1 = false → ∀ τ : T, un x.2.1 ≠ lY τ)
    (h2 : ∀ x ∈ l, sel x.2.1 = true → ∃ τ : T, un x.1 = lY τ) :
    ∀ (i : L3 T Sl) (τ : T), matP un (mic l) i (lY τ) = matP un (micF sel l) i (lY τ) := by
  induction l with
  | nil => intro i τ; rfl
  | cons x l ih =>
    have ih' := ih (fun y hy => h1 y (List.mem_cons_of_mem _ hy))
      (fun y hy => h2 y (List.mem_cons_of_mem _ hy))
    intro i τ
    have em : micF sel (x :: l) = if sel x.2.1 = true then mic1 x :: micF sel l else micF sel l :=
      rfl
    show (matP un (mic l) * addMat (un x.1) (un x.2.1) (toCoef x.2.2).val) i (lY τ) = _
    rw [mul_addMat_apply, em]
    by_cases hs : sel x.2.1 = true
    · obtain ⟨τ', hτ'⟩ := h2 x (List.mem_cons_self ..) hs
      rw [if_pos hs]
      show _ = (matP un (micF sel l) * addMat (un x.1) (un x.2.1) (toCoef x.2.2).val) i (lY τ)
      rw [mul_addMat_apply, ih' i τ, hτ', ih' i τ']
    · have hs' : sel x.2.1 = false := by
        cases hh : sel x.2.1 with
        | false => rfl
        | true => exact absurd hh hs
      have hne : ¬ (lY τ : L3 T Sl) = un x.2.1 := fun e => h1 x (List.mem_cons_self ..) hs' τ e.symm
      rw [if_neg hs, if_neg hne, add_zero, ih' i τ]

end

#print axioms XU_mic
#print axioms ycol_filter
#print axioms GRun_all

end GS
