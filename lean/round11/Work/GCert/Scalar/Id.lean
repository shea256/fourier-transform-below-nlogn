import Work.GCert.Scalar.Check
import Work.CarrierCheck.Mat

/-!
# (key: gx-scalar) The content matrix follows the gate product; what the scatter rows do

* `mic`, `micF`   a list of adds (all / the selected ones) as a micro-program of `SSC.Micro.add`;
* `Cm`, `GRun_Cm` `GRun a l b → Cm b = matP unemb (micF sel l) * Cm a`;
* `scatFrom_run`  the scatter rows: the target `t0 + j` receives `∑ coef * content (register of
  total k)` over its row, nothing else changes.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace GS
open SSC GXD OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM OAI.PowerSaving.SS Finset Matrix

/-- a single add as a micro-op -/
def mic1 (x : Nat × Nat × Co) : Micro := .add x.1 x.2.1 (toCoef x.2.2)

/-- a list of adds as a micro-program -/
def mic (l : List (Nat × Nat × Co)) : List Micro := l.map mic1

/-- the selected adds as a micro-program -/
def micF (sel : Nat → Bool) : List (Nat × Nat × Co) → List Micro
  | [] => []
  | x :: l => if sel x.2.1 = true then mic1 x :: micF sel l else micF sel l

theorem micF_true (l : List (Nat × Nat × Co)) : micF (fun _ => true) l = mic l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    show (if (fun _ => true) x.2.1 = true then mic1 x :: micF (fun _ => true) l
      else micF (fun _ => true) l) = mic1 x :: mic l
    rw [if_pos rfl, ih]

theorem mem_micF (sel : Nat → Bool) (l : List (Nat × Nat × Co)) (t s : Nat) (cf : Coef)
    (h : Micro.add t s cf ∈ micF sel l) : ∃ x ∈ l, x.1 = t ∧ x.2.1 = s ∧ sel s = true := by
  induction l with
  | nil => exact absurd h List.not_mem_nil
  | cons x l ih =>
    have h' : Micro.add t s cf ∈ (if sel x.2.1 = true then mic1 x :: micF sel l else micF sel l) := h
    by_cases hs : sel x.2.1 = true
    · rw [if_pos hs] at h'
      rcases List.mem_cons.mp h' with e | e
      · have e' : Micro.add t s cf = Micro.add x.1 x.2.1 (toCoef x.2.2) := e
        injection e' with e1 e2 e3
        exact ⟨x, List.mem_cons_self .., e1.symm, e2.symm, by rw [e2]; exact hs⟩
      · obtain ⟨y, hy, hh⟩ := ih e
        exact ⟨y, List.mem_cons_of_mem _ hy, hh⟩
    · rw [if_neg hs] at h'
      obtain ⟨y, hy, hh⟩ := ih h'
      exact ⟨y, List.mem_cons_of_mem _ hy, hh⟩

section
variable {ρ : Type} [Fintype ρ] [DecidableEq ρ]

/-- the content matrix: coefficient of source `T` in the register of `i` -/
def Cm (sw n : Nat) (u : Nat → Nat) (emb : ρ → Nat) (a : SSt) : Matrix ρ (Fin n) ℚ :=
  fun i T => gcont sw u a (emb i) T.val

/-- **the content matrix follows the ordered product of the (selected) adds** -/
theorem GRun_Cm (sw n : Nat) (u : Nat → Nat) (okf : Nat → Nat → Bool) (sel : Nat → Bool)
    (emb : ρ → Nat) (unemb : Nat → ρ) (hun : ∀ q, unemb (emb q) = q)
    (hok : ∀ t s, okf t s = true → emb (unemb t) = t ∧ emb (unemb s) = s)
    (l : List (Nat × Nat × Co)) : ∀ (a b : SSt), GRun sw n u okf sel a l b →
      Cm sw n u emb b = matP unemb (micF sel l) * Cm sw n u emb a := by
  induction l with
  | nil =>
    intro a b h
    have e : b = a := h
    rw [e]
    show _ = 1 * _
    rw [Matrix.one_mul]
  | cons x l ih =>
    intro a b h
    have h' : if sel x.2.1 = true then (okf x.1 x.2.1 = true ∧ ∃ m, GStep sw n u x.1 x.2.1
        (toCoef x.2.2) a m ∧ GRun sw n u okf sel m l b) else GRun sw n u okf sel a l b := h
    have em : micF sel (x :: l) = if sel x.2.1 = true then mic1 x :: micF sel l else micF sel l :=
      rfl
    by_cases hs : sel x.2.1 = true
    · rw [if_pos hs] at h'
      obtain ⟨ho, m1, hstep, hrun⟩ := h'
      obtain ⟨ht, hs'⟩ := hok _ _ ho
      rw [em, if_pos hs]
      show Cm sw n u emb b
        = matP unemb (micF sel l) * addMat (unemb x.1) (unemb x.2.1) (toCoef x.2.2).val
          * Cm sw n u emb a
      rw [ih m1 b hrun, Matrix.mul_assoc]
      congr 1
      obtain ⟨_, hoth, hcont⟩ := hstep
      ext i T
      rw [addMat_mul_apply]
      by_cases e : i = unemb x.1
      · rw [if_pos e, e]
        show gcont sw u m1 (emb (unemb x.1)) T.val
          = gcont sw u a (emb (unemb x.1)) T.val
            + (toCoef x.2.2).val * gcont sw u a (emb (unemb x.2.1)) T.val
        rw [ht, hs']
        exact hcont T.val T.isLt
      · rw [if_neg e, add_zero]
        have hne : emb i ≠ x.1 := fun h' => e (by rw [← hun i, h'])
        obtain ⟨p1, p2⟩ := hoth (emb i) hne
        exact gcont_congr sw u a m1 (emb i) T.val p1 p2
    · rw [if_neg hs] at h'
      rw [em, if_neg hs]
      exact ih a b h'

end

/-! ## the scatter rows -/

section
variable (sw n : Nat) (u : Nat → Nat) (okf : Nat → Nat → Bool) (v2 : Nat)
  (hok : ∀ t s, okf t s = true → v2 ≤ s ∧ t < v2) (ret : List (Nat × Nat))
include hok

/-- one scatter row: the target `t` receives the listed contents, read in the reference state
`a0` (which agrees with the current state on the registers `≥ v2`, the slots). -/
theorem scatRow_run (t : Nat) (l : List (Nat × Co)) : ∀ (a b a0 : SSt),
    (∀ r, v2 ≤ r → a.P r = a0.P r ∧ a.N r = a0.N r) →
    GRun sw n u okf (fun _ => true) a (scatRowAdds ret t l) b →
    (∀ r, r ≠ t → b.P r = a.P r ∧ b.N r = a.N r) ∧
    ∀ T, T < n → gcont sw u b t T = gcont sw u a t T
      + (l.map fun x => (toCoef x.2).val * gcont sw u a0 (ret.getD x.1 (0, 0)).1 T).sum := by
  induction l with
  | nil =>
    intro a b a0 _ h
    have e : b = a := h
    rw [e]
    exact ⟨fun r _ => ⟨rfl, rfl⟩, fun T _ => by simp⟩
  | cons x l ih =>
    intro a b a0 h0 h
    have h' : if (fun _ => true) (ret.getD x.1 (0, 0)).1 = true then
        (okf t (ret.getD x.1 (0, 0)).1 = true ∧ ∃ m, GStep sw n u t (ret.getD x.1 (0, 0)).1
          (toCoef x.2) a m ∧ GRun sw n u okf (fun _ => true) m (scatRowAdds ret t l) b)
        else GRun sw n u okf (fun _ => true) a (scatRowAdds ret t l) b := h
    rw [if_pos rfl] at h'
    obtain ⟨ho, m, hstep, hrun⟩ := h'
    obtain ⟨hs2, ht2⟩ := hok _ _ ho
    obtain ⟨_, hoth, hcont⟩ := hstep
    have hm0 : ∀ r, v2 ≤ r → m.P r = a0.P r ∧ m.N r = a0.N r := by
      intro r hr
      obtain ⟨p1, p2⟩ := hoth r (by omega)
      obtain ⟨q1, q2⟩ := h0 r hr
      exact ⟨p1.trans q1, p2.trans q2⟩
    obtain ⟨i1, i2⟩ := ih m b a0 hm0 hrun
    refine ⟨fun r hr => ?_, fun T hT => ?_⟩
    · obtain ⟨p1, p2⟩ := hoth r hr
      obtain ⟨q1, q2⟩ := i1 r hr
      exact ⟨q1.trans p1, q2.trans p2⟩
    · obtain ⟨q1, q2⟩ := h0 _ hs2
      rw [i2 T hT, hcont T hT, gcont_congr sw u a0 a _ T q1 q2, List.map_cons, List.sum_cons]
      ring

/-- all scatter rows: the register `t0 + j` receives its row; all other registers are unchanged. -/
theorem scatFrom_run (rows : List (List (Nat × Co))) :
    ∀ (t0 : Nat) (a b a0 : SSt), t0 + rows.length ≤ v2 →
    (∀ r, v2 ≤ r → a.P r = a0.P r ∧ a.N r = a0.N r) →
    GRun sw n u okf (fun _ => true) a (scatAddsFrom ret t0 rows) b →
    (∀ r, (r < t0 ∨ t0 + rows.length ≤ r) → b.P r = a.P r ∧ b.N r = a.N r) ∧
    ∀ j, j < rows.length → ∀ T, T < n → gcont sw u b (t0 + j) T = gcont sw u a (t0 + j) T
      + ((rows.getD j []).map fun x =>
          (toCoef x.2).val * gcont sw u a0 (ret.getD x.1 (0, 0)).1 T).sum := by
  induction rows with
  | nil =>
    intro t0 a b a0 _ _ h
    have e : b = a := h
    rw [e]
    exact ⟨fun r _ => ⟨rfl, rfl⟩, fun j hj => absurd hj (by simp)⟩
  | cons l rows ih =>
    intro t0 a b a0 ht0 h0 h
    have hlen : (l :: rows).length = rows.length + 1 := rfl
    rw [hlen] at ht0
    obtain ⟨m, h1, h2⟩ := GRun_split sw n u okf _ (scatRowAdds ret t0 l)
      (scatAddsFrom ret (t0+1) rows) a b h
    obtain ⟨r1, r2⟩ := scatRow_run sw n u okf v2 hok ret t0 l a m a0 h0 h1
    have hm0 : ∀ r, v2 ≤ r → m.P r = a0.P r ∧ m.N r = a0.N r := by
      intro r hr
      obtain ⟨p1, p2⟩ := r1 r (by omega)
      obtain ⟨q1, q2⟩ := h0 r hr
      exact ⟨p1.trans q1, p2.trans q2⟩
    obtain ⟨i1, i2⟩ := ih (t0+1) m b a0 (by omega) hm0 h2
    refine ⟨fun r hr => ?_, fun j hj T hT => ?_⟩
    · rw [hlen] at hr
      obtain ⟨p1, p2⟩ := r1 r (by omega)
      obtain ⟨q1, q2⟩ := i1 r (by omega)
      exact ⟨q1.trans p1, q2.trans p2⟩
    · cases j with
      | zero =>
        obtain ⟨q1, q2⟩ := i1 t0 (Or.inl (by omega))
        show gcont sw u b (t0 + 0) T = gcont sw u a (t0 + 0) T
          + (l.map fun x => (toCoef x.2).val * gcont sw u a0 (ret.getD x.1 (0, 0)).1 T).sum
        rw [Nat.add_zero, gcont_congr sw u m b t0 T q1 q2]
        exact r2 T hT
      | succ j =>
        have hj' : j < rows.length := by rw [hlen] at hj; omega
        have e : t0 + (j + 1) = t0 + 1 + j := by omega
        obtain ⟨p1, p2⟩ := r1 (t0 + 1 + j) (by omega)
        show gcont sw u b (t0 + (j + 1)) T = gcont sw u a (t0 + (j + 1)) T
          + ((rows.getD j []).map fun x =>
              (toCoef x.2).val * gcont sw u a0 (ret.getD x.1 (0, 0)).1 T).sum
        rw [e, i2 j hj' T hT, gcont_congr sw u a m (t0 + 1 + j) T p1 p2]

end

#print axioms GRun_Cm
#print axioms scatFrom_run

end GS
