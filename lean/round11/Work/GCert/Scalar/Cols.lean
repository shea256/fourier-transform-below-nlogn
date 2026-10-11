import Work.GCert.Scalar.Mat3

/-!
# (key: gx-scalar) What an accepted replay says about the adds and about the total matrix

`Mt = MB * scatM (Jrm * Ccm) * MA`.

* `XRun.addA`, `XRun.addB`   bounds and kinds of every single add;
* `XRun.xcol`    for a source `t` of the batch: `Mt (lX t') (lX t) = δ` and `Mt (lY S) (lX t) = δ`;
* `unemb_of_x`, `unemb_of_y`   which registers the x / y roles are.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace GS
open SSC GXD OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM OAI.PowerSaving.SS
  OAI.PowerSaving.CB OAI.PowerSaving.CR Finset Matrix

variable {c : Raw}

/-- the total matrix of the main phase -/
noncomputable def Mt (c : Raw) (hv : 0 < c.v) : Matrix (Rl c) (Rl c) ℚ :=
  MB c hv * scatM (Jrm c * Ccm c) * MA c hv

theorem unemb_of_x (hv : 0 < c.v) (r : Nat) (hr : r < 2 * c.v + c.R) (τ : Fin c.v)
    (h : unemb c hv r = lX τ) : r < c.v := by
  by_contra h1
  by_cases h2 : r < 2 * c.v
  · rw [unemb_y hv r (by omega) h2] at h; cases h
  · rw [unemb_s hv r (by omega) hr] at h; cases h

theorem unemb_of_y (hv : 0 < c.v) (r : Nat) (hr : r < 2 * c.v + c.R) (τ : Fin c.v)
    (h : unemb c hv r = lY τ) : c.v ≤ r ∧ r < 2 * c.v := by
  by_cases h1 : r < c.v
  · rw [unemb_x hv r h1] at h; cases h
  · by_cases h2 : r < 2 * c.v
    · omega
    · rw [unemb_s hv r (by omega) hr] at h; cases h

theorem XRun.addA {lo n : Nat} (h : XRun c lo n) : ∀ x ∈ addsA c,
    x.1 < 2 * c.v + c.R ∧ x.2.1 < 2 * c.v + c.R ∧ x.1 ≠ x.2.1 ∧ 2 * c.v ≤ x.1 ∧
      (x.2.1 < c.v ∨ 2 * c.v ≤ x.2.1) := by
  obtain ⟨p, a0, a1, a2, a3, hp, hi, rA, rS, hsh, rB, hsm, fx, fy⟩ := h
  intro x hx
  obtain ⟨ho, hne⟩ := GRun_all _ _ _ _ _ _ _ _ rA x hx rfl
  obtain ⟨h1, h2, h3, h4⟩ := okA_spec ho
  exact ⟨h1, h2, hne, h3, h4⟩

theorem XRun.addB {lo n : Nat} (h : XRun c lo n) : ∀ x ∈ addsB c,
    x.1 < 2 * c.v + c.R ∧ x.2.1 < 2 * c.v + c.R ∧ x.1 ≠ x.2.1 ∧ (x.1 < c.v → x.2.1 < c.v) ∧
      (c.v ≤ x.2.1 → x.2.1 < 2 * c.v → c.v ≤ x.1 ∧ x.1 < 2 * c.v) := by
  obtain ⟨p, a0, a1, a2, a3, hp, hi, rA, rS, hsh, rB, hsm, fx, fy⟩ := h
  intro x hx
  obtain ⟨ho, hne⟩ := GRun_all _ _ _ _ _ _ _ _ rB x hx rfl
  obtain ⟨h1, h2, h3, h4⟩ := okB_spec ho
  exact ⟨h1, h2, hne, by omega, by omega⟩

theorem XRun.ret {lo n : Nat} (h : XRun c lo n) :
    ∀ x ∈ c.ret, 2 * c.v ≤ x.1 ∧ x.1 < 2 * c.v + c.R := by
  obtain ⟨p, a0, a1, a2, a3, hp, _⟩ := h
  exact hp.hret

/-- **the columns of the sources of a batch**: x rows and y rows of the total matrix -/
theorem XRun.xcol (hv : 0 < c.v) {lo n : Nat} (h : XRun c lo n) (t : Fin c.v) (hlo : lo ≤ t.val)
    (hhi : t.val < lo + n) :
    (∀ t' : Fin c.v, Mt c hv (lX t') (lX t) = if t' = t then 1 else 0) ∧
      ∀ S : Fin c.v, Mt c hv (lY S) (lX t) = if S = t then 1 else 0 := by
  obtain ⟨p, a0, a1, a2, a3, hp, hi, rA, rS, hsh, rB, hsm, fx, fy⟩ := h
  have hokA : ∀ t s, okA c t s = true → emb c (unemb c hv t) = t ∧ emb c (unemb c hv s) = s :=
    fun t s ho => ⟨emb_unemb hv t (okA_spec ho).1, emb_unemb hv s (okA_spec ho).2.1⟩
  have hokB : ∀ t s, okB c t s = true → emb c (unemb c hv t) = t ∧ emb c (unemb c hv s) = s :=
    fun t s ho => ⟨emb_unemb hv t (okB_spec ho).1, emb_unemb hv s (okB_spec ho).2.1⟩
  have hCA : Cm p.sw n (U c p) (emb c) a1 = MA c hv * Cm p.sw n (U c p) (emb c) a0 := by
    have := GRun_Cm p.sw n (U c p) (okA c) (fun _ => true) (emb c) (unemb c hv) (unemb_emb hv) hokA
      (addsA c) a0 a1 rA
    rw [micF_true] at this
    exact this
  have hCB : Cm p.sw n (U c p) (emb c) a3 = MB c hv * Cm p.sw n (U c p) (emb c) a2 := by
    have := GRun_Cm p.sw n (U c p) (okB c) (fun _ => true) (emb c) (unemb c hv) (unemb_emb hv) hokB
      (addsB c) a2 a3 rB
    rw [micF_true] at this
    exact this
  have hCS := cm_scat p lo n hp a1 a2 rS hsh
  have hus : p.ux < 2^p.sw :=
    lt_of_lt_of_le hp.hxs (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hT : t.val - lo < n := by omega
  have hC0 : ∀ j : Rl c, Cm p.sw n (U c p) (emb c) a0 j ⟨t.val - lo, hT⟩
      = if j = lX t then 1 else 0 := by
    intro j
    have h1 := cont_start p.sw n (U c p) a0 lo p.ux hp.hx hus hi (emb c j) (t.val - lo) hT
      (fun hr => U_x c p _ (by have := hp.hn; omega))
    show gcont p.sw (U c p) a0 (emb c j) (t.val - lo) = _
    rw [h1]
    have e : lo + (t.val - lo) = t.val := by omega
    by_cases hj : j = lX t
    · rw [if_pos hj, hj, if_pos (by rw [e]; rfl)]
    · have hne : ¬ emb c j = lo + (t.val - lo) := by
        intro he
        apply hj
        rw [← unemb_emb hv j, he, e, unemb_x hv t.val t.isLt]
      rw [if_neg hj, if_neg hne]
  have key : ∀ i : Rl c, Mt c hv i (lX t) = Cm p.sw n (U c p) (emb c) a3 i ⟨t.val - lo, hT⟩ := by
    intro i
    have e1 := mul_unitCol (Mt c hv) (Cm p.sw n (U c p) (emb c) a0) (lX t) ⟨t.val - lo, hT⟩ hC0 i
    rw [← e1]
    unfold Mt
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← hCA, ← hCS, ← hCB]
  refine ⟨fun t' => ?_, fun S => ?_⟩
  · rw [key]
    have hf := fx t'.val t'.isLt
    rw [Nat.zero_add] at hf
    have h1 := cont_end p.sw n (U c p) a3 t'.val p.ux (t'.val - lo) (lo ≤ t'.val ∧ t'.val < lo + n)
      hp.hsw hp.hx hp.hxs (U_x c p _ t'.isLt) (hsm t'.val).2 hf (t.val - lo) hT
    show gcont p.sw (U c p) a3 t'.val (t.val - lo) = _
    rw [h1]
    by_cases e : t' = t
    · rw [if_pos e, if_pos ⟨by rw [e]; exact ⟨hlo, hhi⟩, by rw [e]⟩]
    · have hne : ¬ ((lo ≤ t'.val ∧ t'.val < lo + n) ∧ t.val - lo = t'.val - lo) := by
        intro hh
        exact e (Fin.ext (by omega))
      rw [if_neg e, if_neg hne]
  · rw [key]
    have hf := fy S.val S.isLt
    have h1 := cont_end p.sw n (U c p) a3 (c.v + S.val) p.uy (S.val - lo)
      (lo ≤ S.val ∧ S.val < lo + n) hp.hsw hp.hy hp.hys
      (U_y c p _ (by omega) (by have := S.isLt; omega)) (hsm (c.v + S.val)).2 hf (t.val - lo) hT
    show gcont p.sw (U c p) a3 (c.v + S.val) (t.val - lo) = _
    rw [h1]
    by_cases e : S = t
    · rw [if_pos e, if_pos ⟨by rw [e]; exact ⟨hlo, hhi⟩, by rw [e]⟩]
    · have hne : ¬ ((lo ≤ S.val ∧ S.val < lo + n) ∧ t.val - lo = S.val - lo) := by
        intro hh
        exact e (Fin.ext (by omega))
      rw [if_neg e, if_neg hne]

#print axioms XRun.addA
#print axioms XRun.addB
#print axioms XRun.xcol

end GS
