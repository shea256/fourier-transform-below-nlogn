import Work.CarrierCheck.ScalOps
import Work.CarrierCheck.Roles

/-!
# (key: carrier-check) The content matrix follows the gates; the scatter rows

* `SRun_Cm`      `SRun a ms b → Cm b = matP unemb ms * Cm a`;
* `scatRow_run`, `scatFrom_run`   what the scatter rows do to the contents: the target role
  `t0 + j` receives `∑ coef * content (slot ret k)` over its row, nothing else changes.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace SSC
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM OAI.PowerSaving.SS Finset Matrix

theorem cont_congr (sw y0 : Nat) (a b : SSt) (r T : Nat) (hP : b.P r = a.P r) (hN : b.N r = a.N r) :
    cont sw y0 b r T = cont sw y0 a r T := by
  unfold cont
  rw [hP, hN]

section
variable {ρ : Type} [Fintype ρ] [DecidableEq ρ]

/-- the content matrix: coefficient of `x_T` in the role -/
def Cm (sw v y0 : Nat) (emb : ρ → Nat) (a : SSt) : Matrix ρ (Fin v) ℚ :=
  fun i T => cont sw y0 a (emb i) T.val

/-- **the content matrix follows the ordered product of the gates** -/
theorem SRun_Cm (sw v y0 : Nat) (emb : ρ → Nat) (unemb : Nat → ρ) (hun : ∀ q, unemb (emb q) = q)
    (ms : List Micro)
    (hadd : ∀ t s cf, Micro.add t s cf ∈ ms → emb (unemb t) = t ∧ emb (unemb s) = s) :
    ∀ (a b : SSt), SRun sw v y0 a ms b →
      Cm sw v y0 emb b = matP unemb ms * Cm sw v y0 emb a := by
  induction ms with
  | nil =>
    intro a b h
    have e : b = a := h
    rw [e]
    show _ = 1 * _
    rw [Matrix.one_mul]
  | cons m ms ih =>
    intro a b h
    have ih' := ih (fun t s cf hm => hadd t s cf (List.mem_cons_of_mem _ hm))
    cases m with
    | add t s cf =>
      obtain ⟨m1, hstep, hrun⟩ := h
      obtain ⟨ht, hs⟩ := hadd t s cf (List.mem_cons_self ..)
      show Cm sw v y0 emb b
        = matP unemb ms * addMat (unemb t) (unemb s) cf.val * Cm sw v y0 emb a
      rw [ih' m1 b hrun, Matrix.mul_assoc]
      congr 1
      obtain ⟨_, _, hoth, hcont⟩ := hstep
      ext i T
      rw [addMat_mul_apply]
      by_cases e : i = unemb t
      · rw [if_pos e, e]
        show cont sw y0 m1 (emb (unemb t)) T.val
          = cont sw y0 a (emb (unemb t)) T.val + cf.val * cont sw y0 a (emb (unemb s)) T.val
        rw [ht, hs]
        exact hcont T.val T.isLt
      · rw [if_neg e, add_zero]
        have hne : emb i ≠ t := fun h' => e (by rw [← hun i, h'])
        obtain ⟨p1, p2⟩ := hoth (emb i) hne
        exact cont_congr sw y0 a m1 (emb i) T.val p1 p2
    | dir r z => exact ih' a b h
    | shift r z => exact ih' a b h
    | copy _ _ => exact False.elim h
    | erase _ => exact False.elim h
    | expect _ _ => exact ih' a b h

end

theorem SRun_split (sw v y0 : Nat) (l1 l2 : List Micro) : ∀ (a b : SSt),
    SRun sw v y0 a (l1 ++ l2) b → ∃ m, SRun sw v y0 a l1 m ∧ SRun sw v y0 m l2 b := by
  induction l1 with
  | nil =>
    intro a b h
    exact ⟨a, rfl, h⟩
  | cons x l1 ih =>
    intro a b h
    cases x with
    | add t s cf =>
      obtain ⟨m1, hs, hr⟩ := h
      obtain ⟨m, h1, h2⟩ := ih m1 b hr
      exact ⟨m, ⟨m1, hs, h1⟩, h2⟩
    | dir r z => exact ih a b h
    | shift r z => exact ih a b h
    | copy _ _ => exact False.elim h
    | erase _ => exact False.elim h
    | expect _ _ => exact ih a b h

/-! ## the scatter rows -/

/-- one scatter row: the target `t` (a y role) receives the listed contents, read in the
reference state `a0` (which agrees with the current state on the roles below `y0`). -/
theorem scatRow_run (sw v y0 vv : Nat) (ret : List Nat) (t : Nat) (ht : y0 ≤ t)
    (l : List (Nat × Coef)) : ∀ (a b a0 : SSt),
    (∀ r, r < y0 → a.P r = a0.P r ∧ a.N r = a0.N r) →
    SRun sw v y0 a (scatRowM vv ret t l) b →
    (∀ r, r ≠ t → b.P r = a.P r ∧ b.N r = a.N r) ∧
    ∀ T, T < v → cont sw y0 b t T = cont sw y0 a t T
      + (l.map fun x => x.2.val * cont sw y0 a0 (vv + ret.getD x.1 0) T).sum := by
  induction l with
  | nil =>
    intro a b a0 _ h
    have e : b = a := h
    rw [e]
    exact ⟨fun r _ => ⟨rfl, rfl⟩, fun T _ => by simp⟩
  | cons x l ih =>
    intro a b a0 h0 h
    obtain ⟨m, hstep, hrun⟩ : ∃ m, SStep sw v y0 t (vv + ret.getD x.1 0) x.2 a m ∧
        SRun sw v y0 m (scatRowM vv ret t l) b := h
    obtain ⟨hsy, _, hoth, hcont⟩ := hstep
    have hm0 : ∀ r, r < y0 → m.P r = a0.P r ∧ m.N r = a0.N r := by
      intro r hr
      obtain ⟨p1, p2⟩ := hoth r (by omega)
      obtain ⟨q1, q2⟩ := h0 r hr
      exact ⟨p1.trans q1, p2.trans q2⟩
    obtain ⟨i1, i2⟩ := ih m b a0 hm0 hrun
    refine ⟨fun r hr => ?_, fun T hT => ?_⟩
    · obtain ⟨p1, p2⟩ := hoth r hr
      obtain ⟨q1, q2⟩ := i1 r hr
      exact ⟨q1.trans p1, q2.trans p2⟩
    · obtain ⟨q1, q2⟩ := h0 _ hsy
      rw [i2 T hT, hcont T hT, cont_congr sw y0 a0 a _ T q1 q2, List.map_cons, List.sum_cons]
      ring

/-- all scatter rows: the role `t0 + j` receives its row; all other roles are unchanged. -/
theorem scatFrom_run (sw v y0 vv : Nat) (ret : List Nat) (rows : List (List (Nat × Coef))) :
    ∀ (t0 : Nat) (a b a0 : SSt), y0 ≤ t0 →
    (∀ r, r < y0 → a.P r = a0.P r ∧ a.N r = a0.N r) →
    SRun sw v y0 a (scatFromM vv ret t0 rows) b →
    (∀ r, (r < t0 ∨ t0 + rows.length ≤ r) → b.P r = a.P r ∧ b.N r = a.N r) ∧
    ∀ j, j < rows.length → ∀ T, T < v → cont sw y0 b (t0 + j) T = cont sw y0 a (t0 + j) T
      + ((rows.getD j []).map fun x => x.2.val * cont sw y0 a0 (vv + ret.getD x.1 0) T).sum := by
  induction rows with
  | nil =>
    intro t0 a b a0 _ _ h
    have e : b = a := h
    rw [e]
    exact ⟨fun r _ => ⟨rfl, rfl⟩, fun j hj => absurd hj (by simp)⟩
  | cons l rows ih =>
    intro t0 a b a0 ht0 h0 h
    obtain ⟨m, h1, h2⟩ := SRun_split sw v y0 (scatRowM vv ret t0 l) (scatFromM vv ret (t0+1) rows)
      a b h
    obtain ⟨r1, r2⟩ := scatRow_run sw v y0 vv ret t0 ht0 l a m a0 h0 h1
    have hm0 : ∀ r, r < y0 → m.P r = a0.P r ∧ m.N r = a0.N r := by
      intro r hr
      obtain ⟨p1, p2⟩ := r1 r (by omega)
      obtain ⟨q1, q2⟩ := h0 r hr
      exact ⟨p1.trans q1, p2.trans q2⟩
    obtain ⟨i1, i2⟩ := ih (t0+1) m b a0 (by omega) hm0 h2
    have hlen : (l :: rows).length = rows.length + 1 := rfl
    refine ⟨fun r hr => ?_, fun j hj T hT => ?_⟩
    · rw [hlen] at hr
      obtain ⟨p1, p2⟩ := r1 r (by omega)
      obtain ⟨q1, q2⟩ := i1 r (by omega)
      exact ⟨q1.trans p1, q2.trans p2⟩
    · cases j with
      | zero =>
        obtain ⟨q1, q2⟩ := i1 t0 (Or.inl (by omega))
        show cont sw y0 b (t0 + 0) T = cont sw y0 a (t0 + 0) T
          + (l.map fun x => x.2.val * cont sw y0 a0 (vv + ret.getD x.1 0) T).sum
        rw [Nat.add_zero, cont_congr sw y0 m b t0 T q1 q2]
        exact r2 T hT
      | succ j =>
        have hj' : j < rows.length := by rw [hlen] at hj; omega
        have e : t0 + (j + 1) = t0 + 1 + j := by omega
        obtain ⟨p1, p2⟩ := r1 (t0 + 1 + j) (by omega)
        show cont sw y0 b (t0 + (j + 1)) T = cont sw y0 a (t0 + (j + 1)) T
          + ((rows.getD j []).map fun x => x.2.val * cont sw y0 a0 (vv + ret.getD x.1 0) T).sum
        rw [e, i2 j hj' T hT, cont_congr sw y0 a m (t0 + 1 + j) T p1 p2]

end SSC
