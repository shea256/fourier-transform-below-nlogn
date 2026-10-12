import Work.CarrierCheck.Routes
import Work.CarrierCheck.ScalFin
import Work.Carrier.Phases

/-!
# (key: carrier-check) The scalar identity of a checked carrier certificate, in the form of
`CR.Phased` (`Work.Carrier.Phases`)

With `MA = matP un mA`, `MB = matP un mB` (ordered gate products of the two phases),
`Jr S k = ∑` of the scatter coefficients of target `S` at the retained total `k`,
`Cc k q = 1` iff slot `q` holds the retained total `k`:

    Valid.hid :  (MB * CR.scatM (Jr * Cc) * MA) (y S) (x t) = if S = t then 1 else 0

from `c.scalarCheck = true` (the content matrix follows the gates, `SRun_Cm`; the scatter rows
are the matrix `CR.scatM (Jr * Cc)`, `Valid.cm_scat`).

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace SSC
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM OAI.PowerSaving.SS
  OAI.PowerSaving.CB OAI.PowerSaving.CR Finset Matrix

/-- product with the block `y ← slots` -/
theorem embYS_mul_apply {T Sl m : Type} [Fintype T] [DecidableEq T] [Fintype Sl] [DecidableEq Sl]
    (K : Matrix T Sl ℚ) (X : Matrix (L3 T Sl) m ℚ) (i : L3 T Sl) (j : m) :
    (embYS K * X) i j
      = Sum.elim (Sum.elim (fun _ => 0) (fun S => ∑ q, K S q * X (Sum.inr q) j)) (fun _ => 0) i := by
  rw [Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_sum_type]
  rcases i with (a | S) | q
  · simp [embYS]
  · simp [embYS]
  · simp [embYS]

theorem embYS_rowX {T Sl : Type} [Fintype T] [DecidableEq T] [Fintype Sl] [DecidableEq Sl]
    (K : Matrix T Sl ℚ) (t : T) (j : L3 T Sl) : embYS K (Sum.inl (Sum.inl t)) j = 0 := rfl

theorem embYS_colY {T Sl : Type} [Fintype T] [DecidableEq T] [Fintype Sl] [DecidableEq Sl]
    (K : Matrix T Sl ℚ) (i : L3 T Sl) (t : T) : embYS K i (Sum.inl (Sum.inr t)) = 0 := by
  rcases i with (a | S) | q <;> rfl

namespace CCert
variable {c : CCert}

/-- the slot of the retained total `k` -/
def retq (c : CCert) (hR : 0 < c.R) (k : Fin c.ret.length) : Fin c.R :=
  ⟨c.ret.getD k.val 0 % c.R, Nat.mod_lt _ hR⟩

/-- copies += slots: copy `k` reads the slot `ret k` -/
def Ccm (c : CCert) (hR : 0 < c.R) : Matrix (Fin c.ret.length) (Fin c.R) ℚ :=
  fun k q => if q = c.retq hR k then 1 else 0

/-- y += copies: the scatter rows -/
noncomputable def Jrm (c : CCert) : Matrix (Fin c.v) (Fin c.ret.length) ℚ :=
  fun S k => rowOf (c.scat.getD S.val []) k

theorem Valid.all_ret (V : c.Valid) (k : Fin c.ret.length) : c.ret.getD k.val 0 < c.R := by
  have h := List.all_eq_true.mp V.hret _ (getD_mem_lt c.ret 0 k.val k.isLt)
  simpa using h

theorem Valid.emb_retq (V : c.Valid) (k : Fin c.ret.length) :
    c.emb3 (Sum.inr (c.retq V.hR k)) = c.v + c.ret.getD k.val 0 := by
  show c.v + c.ret.getD k.val 0 % c.R = _
  rw [Nat.mod_eq_of_lt (V.all_ret k)]

/-- **the scatter rows act on the content matrix as `CR.scatM (Jr * Cc)`** -/
theorem Valid.cm_scat (V : c.Valid) (a1 a2 : SSt)
    (h : SRun c.sw c.v (c.v + c.R) a1 c.scatL a2) :
    Cm c.sw c.v (c.v + c.R) c.emb3 a2
      = scatM (c.Jrm * c.Ccm V.hR) * Cm c.sw c.v (c.v + c.R) c.emb3 a1 := by
  obtain ⟨u1, u2⟩ := scatFrom_run c.sw c.v (c.v + c.R) c.v c.ret c.scat (c.v + c.R) a1 a2 a1
    (Nat.le_refl _) (fun r _ => ⟨rfl, rfl⟩) h
  ext i T
  unfold scatM
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, embYS_mul_apply]
  rcases i with (t' | S') | q
  · have hlt : t'.val < c.v + c.R := by have := t'.isLt; omega
    obtain ⟨p1, p2⟩ := u1 t'.val (Or.inl hlt)
    show cont c.sw (c.v + c.R) a2 t'.val T.val = cont c.sw (c.v + c.R) a1 t'.val T.val + 0
    rw [cont_congr c.sw (c.v + c.R) a1 a2 _ _ p1 p2, add_zero]
  · have hS : S'.val < c.scat.length := by rw [V.hsl]; exact S'.isLt
    have hl : ∀ x ∈ c.scat.getD S'.val [], x.1 < c.ret.length := by
      intro x hx
      have h1 := List.all_eq_true.mp V.hsc _ (getD_mem_lt c.scat [] S'.val hS)
      have h2 := List.all_eq_true.mp h1 x hx
      simpa using h2
    have hg : ∀ k : Fin c.ret.length,
        Cm c.sw c.v (c.v + c.R) c.emb3 a1 (Sum.inr (c.retq V.hR k)) T
          = cont c.sw (c.v + c.R) a1 (c.v + c.ret.getD k.val 0) T.val := by
      intro k
      show cont c.sw (c.v + c.R) a1 (c.emb3 (Sum.inr (c.retq V.hR k))) T.val = _
      rw [V.emb_retq k]
    have step : ∑ q, (c.Jrm * c.Ccm V.hR) S' q * Cm c.sw c.v (c.v + c.R) c.emb3 a1 (Sum.inr q) T
        = ∑ k, c.Jrm S' k * Cm c.sw c.v (c.v + c.R) c.emb3 a1 (Sum.inr (c.retq V.hR k)) T := by
      calc ∑ q, (c.Jrm * c.Ccm V.hR) S' q * Cm c.sw c.v (c.v + c.R) c.emb3 a1 (Sum.inr q) T
          = ∑ q, ∑ k, c.Jrm S' k * c.Ccm V.hR k q
              * Cm c.sw c.v (c.v + c.R) c.emb3 a1 (Sum.inr q) T := by
            refine Finset.sum_congr rfl (fun q _ => ?_)
            rw [Matrix.mul_apply, Finset.sum_mul]
        _ = ∑ k, ∑ q, c.Jrm S' k * c.Ccm V.hR k q
              * Cm c.sw c.v (c.v + c.R) c.emb3 a1 (Sum.inr q) T := Finset.sum_comm
        _ = ∑ k, c.Jrm S' k * Cm c.sw c.v (c.v + c.R) c.emb3 a1 (Sum.inr (c.retq V.hR k)) T := by
            refine Finset.sum_congr rfl (fun k _ => ?_)
            rw [Finset.sum_eq_single (c.retq V.hR k)]
            · show c.Jrm S' k * (if c.retq V.hR k = c.retq V.hR k then (1:ℚ) else 0) * _ = _
              rw [if_pos rfl, mul_one]
            · intro q _ hq
              show c.Jrm S' k * (if q = c.retq V.hR k then (1:ℚ) else 0) * _ = 0
              rw [if_neg hq, mul_zero, zero_mul]
            · intro hb
              exact absurd (Finset.mem_univ _) hb
    show cont c.sw (c.v + c.R) a2 (c.v + c.R + S'.val) T.val
      = cont c.sw (c.v + c.R) a1 (c.v + c.R + S'.val) T.val
        + ∑ q, (c.Jrm * c.Ccm V.hR) S' q * Cm c.sw c.v (c.v + c.R) c.emb3 a1 (Sum.inr q) T
    rw [u2 S'.val hS T.val T.isLt, step]
    congr 1
    exact (rowOf_sum (c.scat.getD S'.val []) hl
      (fun k => Cm c.sw c.v (c.v + c.R) c.emb3 a1 (Sum.inr (c.retq V.hR k)) T)
      (fun k' => cont c.sw (c.v + c.R) a1 (c.v + c.ret.getD k' 0) T.val) hg).symm
  · have hlt : c.v + q.val < c.v + c.R := by have := q.isLt; omega
    obtain ⟨p1, p2⟩ := u1 (c.v + q.val) (Or.inl hlt)
    show cont c.sw (c.v + c.R) a2 (c.v + q.val) T.val
      = cont c.sw (c.v + c.R) a1 (c.v + q.val) T.val + 0
    rw [cont_congr c.sw (c.v + c.R) a1 a2 _ _ p1 p2, add_zero]

end CCert

end SSC
