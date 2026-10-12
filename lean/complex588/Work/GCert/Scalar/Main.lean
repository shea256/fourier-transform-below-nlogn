import Work.GCert.Scalar.Cols

/-!
# (key: gx-scalar) THE SCALAR HALF: the three facts about the total matrix of the main phase

`ScalOK c`: every source lies in an accepted batch of the scalar check (`XRun`) and of the y
check (`YRun`).  Then for `Mt = MB * scatM (Jrm * Ccm) * MA`:

* `ScalOK.hx`    the x rows are unit rows   (gates INTO x roles allowed: they read x roles, and
  the replay ends with `x_t` holding exactly source `t`);
* `ScalOK.hy`    the y columns are unit columns   (gates READING y roles allowed: they write y
  roles, and their product is the identity: the y check);
* `ScalOK.hid`   the block `y ← x` is the identity;
* `ScalOK.hAi`, `ScalOK.hBi`   the inverses of the gate products.

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

/-- **the scalar half of a `gcert/1` certificate is checked** -/
structure ScalOK (c : Raw) : Prop where
  hv : 0 < c.v
  hs : ∀ t, t < c.v → ∃ lo n, lo ≤ t ∧ t < lo + n ∧ XRun c lo n
  hyc : ∀ t, t < c.v → ∃ lo n, lo ≤ t ∧ t < lo + n ∧ YRun c lo n

theorem ScalOK.of_one (hv : 0 < c.v) (h1 : XRun c 0 c.v) (h2 : YRun c 0 c.v) : ScalOK c :=
  ⟨hv, fun t ht => ⟨0, c.v, Nat.zero_le _, by omega, h1⟩,
    fun t ht => ⟨0, c.v, Nat.zero_le _, by omega, h2⟩⟩

namespace ScalOK
variable (K : ScalOK c)
include K

theorem addA : ∀ x ∈ addsA c, x.1 < 2 * c.v + c.R ∧ x.2.1 < 2 * c.v + c.R ∧ x.1 ≠ x.2.1 ∧
    2 * c.v ≤ x.1 ∧ (x.2.1 < c.v ∨ 2 * c.v ≤ x.2.1) := by
  obtain ⟨lo, n, _, _, h⟩ := K.hs 0 K.hv
  exact h.addA

theorem addB : ∀ x ∈ addsB c, x.1 < 2 * c.v + c.R ∧ x.2.1 < 2 * c.v + c.R ∧ x.1 ≠ x.2.1 ∧
    (x.1 < c.v → x.2.1 < c.v) ∧ (c.v ≤ x.2.1 → x.2.1 < 2 * c.v → c.v ≤ x.1 ∧ x.1 < 2 * c.v) := by
  obtain ⟨lo, n, _, _, h⟩ := K.hs 0 K.hv
  exact h.addB

theorem ret_slot : ∀ x ∈ c.ret, 2 * c.v ≤ x.1 ∧ x.1 < 2 * c.v + c.R := by
  obtain ⟨lo, n, _, _, h⟩ := K.hs 0 K.hv
  exact h.ret

theorem un_ne (t s : Nat) (ht : t < 2 * c.v + c.R) (hs : s < 2 * c.v + c.R) (hne : t ≠ s) :
    unemb c K.hv t ≠ unemb c K.hv s := fun e => hne (by
  rw [← emb_unemb K.hv t ht, e, emb_unemb K.hv s hs])

theorem hAi : MAi c K.hv * MA c K.hv = 1 := by
  apply mul_eq_one_comm.mp
  exact matP_inv _ _ (gatesDistinct_of _ _ (fun t s cf hm => by
    obtain ⟨x, hx, rfl, rfl⟩ := mem_mic _ _ _ _ hm
    obtain ⟨h1, h2, h3, _⟩ := K.addA x hx
    exact K.un_ne _ _ h1 h2 h3))

theorem hBi : MBi c K.hv * MB c K.hv = 1 := by
  apply mul_eq_one_comm.mp
  exact matP_inv _ _ (gatesDistinct_of _ _ (fun t s cf hm => by
    obtain ⟨x, hx, rfl, rfl⟩ := mem_mic _ _ _ _ hm
    obtain ⟨h1, h2, h3, _⟩ := K.addB x hx
    exact K.un_ne _ _ h1 h2 h3))

/-- **the block `y ← x` is the identity** -/
theorem hid (S t : Fin c.v) :
    (MB c K.hv * scatM (Jrm c * Ccm c) * MA c K.hv) (lY S) (lX t) = if S = t then 1 else 0 := by
  obtain ⟨lo, n, hlo, hhi, h⟩ := K.hs t.val t.isLt
  exact (h.xcol K.hv t hlo hhi).2 S

theorem xu : XU (Mt c K.hv) := by
  unfold Mt
  refine XU_mul _ _ (XU_mul _ _ (XU_mic _ _ ?_) (XU_scat _)) (XU_mic _ _ ?_)
  · intro x hx τ hτ
    obtain ⟨h1, h2, _, h4, _⟩ := K.addB x hx
    have := h4 (unemb_of_x K.hv x.1 h1 τ hτ)
    exact ⟨⟨x.2.1, this⟩, unemb_x K.hv x.2.1 this⟩
  · intro x hx τ hτ
    obtain ⟨h1, _, _, h4, _⟩ := K.addA x hx
    have := unemb_of_x K.hv x.1 h1 τ hτ
    omega

/-- **the x rows are unit rows** -/
theorem hx (t : Fin c.v) (j : Rl c) :
    (MB c K.hv * scatM (Jrm c * Ccm c) * MA c K.hv) (lX t) j = if lX t = j then 1 else 0 := by
  rcases j with (τ | S) | q
  · obtain ⟨lo, n, hlo, hhi, h⟩ := K.hs τ.val τ.isLt
    have h1 := (h.xcol K.hv τ hlo hhi).1 t
    show Mt c K.hv (lX t) (lX τ) = _
    rw [h1]
    by_cases e : t = τ
    · rw [if_pos e, e, if_pos rfl]
    · rw [if_neg e, if_neg (fun hh => e (Sum.inl.inj (Sum.inl.inj hh)))]
  · have h1 := K.xu t (lY S) (fun τ hh => by cases hh)
    show Mt c K.hv (lX t) (lY S) = _
    rw [h1, if_neg (fun hh => by cases hh)]
  · have h1 := K.xu t (lS q) (fun τ hh => by cases hh)
    show Mt c K.hv (lX t) (lS q) = _
    rw [h1, if_neg (fun hh => by cases hh)]

/-- the y columns of the product of phase B -/
theorem mb_ycol (i : Rl c) (t : Fin c.v) : MB c K.hv i (lY t) = if i = lY t then 1 else 0 := by
  have hf := ycol_filter (unemb c K.hv) (selY c.v (2 * c.v)) (addsB c)
    (fun x hx hsel τ hτ => by
      obtain ⟨_, h2, _⟩ := K.addB x hx
      have := selY_spec.mpr (unemb_of_y K.hv x.2.1 h2 τ hτ)
      rw [hsel] at this
      exact Bool.false_ne_true this)
    (fun x hx hsel => by
      obtain ⟨_, _, _, _, h5⟩ := K.addB x hx
      obtain ⟨g1, g2⟩ := selY_spec.mp hsel
      obtain ⟨g3, g4⟩ := h5 g1 g2
      exact ⟨_, unemb_y K.hv x.1 g3 g4⟩) i t
  show matP (unemb c K.hv) (mic (addsB c)) i (lY t) = _
  rw [hf]
  -- targets of the selected adds are y roles
  have htg : ∀ t' s cf, Micro.add t' s cf ∈ micF (selY c.v (2 * c.v)) (addsB c) →
      ∃ τ : Fin c.v, unemb c K.hv t' = lY τ := by
    intro t' s cf hm
    obtain ⟨x, hx, rfl, rfl, hsel⟩ := mem_micF _ _ _ _ _ hm
    obtain ⟨_, _, _, _, h5⟩ := K.addB x hx
    obtain ⟨g1, g2⟩ := selY_spec.mp hsel
    obtain ⟨g3, g4⟩ := h5 g1 g2
    exact ⟨_, unemb_y K.hv x.1 g3 g4⟩
  rcases i with (τ | S) | q
  · exact matP_row _ _ _ (fun t' s cf hm hh => by
      obtain ⟨τ', hτ'⟩ := htg t' s cf hm
      rw [hτ'] at hh; cases hh) _
  · obtain ⟨lo, n, hlo, hhi, p, a0, a3, hp, hi, hr, hsm, fy⟩ := K.hyc t.val t.isLt
    have hokB : ∀ t s, okB c t s = true →
        emb c (unemb c K.hv t) = t ∧ emb c (unemb c K.hv s) = s :=
      fun t s ho => ⟨emb_unemb K.hv t (okB_spec ho).1, emb_unemb K.hv s (okB_spec ho).2.1⟩
    have hC := GRun_Cm p.sw n (U c p) (okB c) (selY c.v (2 * c.v)) (emb c) (unemb c K.hv)
      (unemb_emb K.hv) hokB (addsB c) a0 a3 hr
    have hus : p.uy < 2^p.sw :=
      lt_of_lt_of_le hp.hys (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hT : t.val - lo < n := by omega
    have hC0 : ∀ j : Rl c, Cm p.sw n (U c p) (emb c) a0 j ⟨t.val - lo, hT⟩
        = if j = lY t then 1 else 0 := by
      intro j
      have h1 := cont_start p.sw n (U c p) a0 (c.v + lo) p.uy hp.hy hus hi (emb c j) (t.val - lo) hT
        (fun hr => U_y c p _ (by omega) (by have := hp.hn; omega))
      show gcont p.sw (U c p) a0 (emb c j) (t.val - lo) = _
      rw [h1]
      have e : c.v + lo + (t.val - lo) = c.v + t.val := by omega
      by_cases hj : j = lY t
      · rw [if_pos hj, hj, if_pos (by rw [e]; rfl)]
      · have hne : ¬ emb c j = c.v + lo + (t.val - lo) := by
          intro he
          apply hj
          rw [← unemb_emb K.hv j, he, e, unemb_y K.hv (c.v + t.val) (by omega)
            (by have := t.isLt; omega)]
          exact congrArg (fun x => (Sum.inl (Sum.inr x) : Rl c)) (Fin.ext (by simp))
        rw [if_neg hj, if_neg hne]
    have e1 := mul_unitCol (matP (unemb c K.hv) (micF (selY c.v (2 * c.v)) (addsB c)))
      (Cm p.sw n (U c p) (emb c) a0) (lY t) ⟨t.val - lo, hT⟩ hC0 (lY S)
    rw [← e1, ← hC]
    have h1 := cont_end p.sw n (U c p) a3 (c.v + S.val) p.uy (S.val - lo)
      (lo ≤ S.val ∧ S.val < lo + n) hp.hsw hp.hy hp.hys
      (U_y c p _ (by omega) (by have := S.isLt; omega)) (hsm (c.v + S.val)).2 (fy S.val S.isLt)
      (t.val - lo) hT
    show gcont p.sw (U c p) a3 (c.v + S.val) (t.val - lo) = _
    rw [h1]
    by_cases e : S = t
    · rw [e, if_pos ⟨⟨hlo, hhi⟩, rfl⟩, if_pos rfl]
    · have hne : ¬ ((lo ≤ S.val ∧ S.val < lo + n) ∧ t.val - lo = S.val - lo) := by
        intro hh
        exact e (Fin.ext (by omega))
      rw [if_neg hne, if_neg (fun hh => e (Sum.inr.inj (Sum.inl.inj hh)))]
  · exact matP_row _ _ _ (fun t' s cf hm hh => by
      obtain ⟨τ', hτ'⟩ := htg t' s cf hm
      rw [hτ'] at hh; cases hh) _

/-- **the y columns are unit columns** -/
theorem hy (i : Rl c) (t : Fin c.v) :
    (MB c K.hv * scatM (Jrm c * Ccm c) * MA c K.hv) i (lY t) = if i = lY t then 1 else 0 := by
  have hA : ∀ i : Rl c, MA c K.hv i (lY t) = if i = lY t then 1 else 0 :=
    matP_col (unemb c K.hv) (lY t) (mic (addsA c)) (fun t' s cf hm hh => by
    obtain ⟨x, hx, rfl, rfl⟩ := mem_mic _ _ _ _ hm
    obtain ⟨_, h2, _, _, h5⟩ := K.addA x hx
    have := unemb_of_y K.hv x.2.1 h2 t hh
    omega)
  have hS : ∀ i : Rl c, scatM (Jrm c * Ccm c) i (lY t) = if i = lY t then 1 else 0 := by
    intro i
    unfold scatM
    rw [Matrix.add_apply, Matrix.one_apply, embYS_colY, add_zero]
  have hcol := unitCol_mul _ _ (lY t) hS hA
  rw [Matrix.mul_assoc, mul_unitCol (MB c K.hv) _ (lY t) (lY t) hcol i]
  exact K.mb_ycol i t

end ScalOK

#print axioms ScalOK.hx
#print axioms ScalOK.hy
#print axioms ScalOK.hid
#print axioms ScalOK.hAi
#print axioms ScalOK.hBi

end GS
