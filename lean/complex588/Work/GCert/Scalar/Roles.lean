import Work.GCert.Scalar.Id
import Work.CarrierCheck.Scat

/-!
# (key: gx-scalar) Live roles, gate products, scatter matrices of a `gcert/1` certificate

* `Rl c = L3 (Fin v) (Fin R)`, `emb`, `unemb`: `lX t` = register `t`, `lY t` = `v + t`,
  `lS q` = `2 v + q`;
* `MA`, `MAi`, `MB`, `MBi`: products of the single adds of phase A / B (and inverses);
* `Ccm` (copies += slots), `Jrm` (y += copies);
* `cm_scat`: the scatter adds act on the content matrix as `CR.scatM (Jrm * Ccm)`.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace GS
open SSC GXD OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM OAI.PowerSaving.SS
  OAI.PowerSaving.CB OAI.PowerSaving.CR Finset Matrix

/-- the live roles: x, y, slots -/
abbrev Rl (c : Raw) : Type := L3 (Fin c.v) (Fin c.R)

def emb (c : Raw) : Rl c → Nat
  | .inl (.inl t) => t.val
  | .inl (.inr S) => c.v + S.val
  | .inr q => 2 * c.v + q.val

def unemb (c : Raw) (hv : 0 < c.v) (r : Nat) : Rl c :=
  if r < c.v then .inl (.inl ⟨r % c.v, Nat.mod_lt _ hv⟩)
  else if r < 2 * c.v then .inl (.inr ⟨(r - c.v) % c.v, Nat.mod_lt _ hv⟩)
  else if h : r - 2 * c.v < c.R then .inr ⟨r - 2 * c.v, h⟩
  else .inl (.inl ⟨0, hv⟩)

variable {c : Raw}

theorem unemb_x (hv : 0 < c.v) (r : Nat) (h : r < c.v) : unemb c hv r = lX ⟨r, h⟩ := by
  unfold unemb
  rw [if_pos h]
  exact congrArg (fun x => (Sum.inl (Sum.inl x) : Rl c)) (Fin.ext (Nat.mod_eq_of_lt h))

theorem unemb_y (hv : 0 < c.v) (r : Nat) (h1 : c.v ≤ r) (h2 : r < 2 * c.v) :
    unemb c hv r = lY ⟨r - c.v, by omega⟩ := by
  unfold unemb
  rw [if_neg (by omega), if_pos h2]
  exact congrArg (fun x => (Sum.inl (Sum.inr x) : Rl c)) (Fin.ext (Nat.mod_eq_of_lt (by omega)))

theorem unemb_s (hv : 0 < c.v) (r : Nat) (h1 : 2 * c.v ≤ r) (h2 : r < 2 * c.v + c.R) :
    unemb c hv r = lS ⟨r - 2 * c.v, by omega⟩ := by
  unfold unemb
  rw [if_neg (by omega), if_neg (by omega), dif_pos (by omega)]

theorem unemb_emb (hv : 0 < c.v) (q : Rl c) : unemb c hv (emb c q) = q := by
  rcases q with (t | S) | q
  · exact unemb_x hv t.val t.isLt
  · have h := unemb_y hv (c.v + S.val) (by omega) (by have := S.isLt; omega)
    rw [show emb c (Sum.inl (Sum.inr S)) = c.v + S.val from rfl, h]
    exact congrArg (fun x => (Sum.inl (Sum.inr x) : Rl c)) (Fin.ext (by simp))
  · have h := unemb_s hv (2 * c.v + q.val) (by omega) (by have := q.isLt; omega)
    rw [show emb c (Sum.inr q) = 2 * c.v + q.val from rfl, h]
    exact congrArg (fun x => (Sum.inr x : Rl c)) (Fin.ext (by simp))

theorem emb_unemb (hv : 0 < c.v) (r : Nat) (hr : r < 2 * c.v + c.R) : emb c (unemb c hv r) = r := by
  by_cases h1 : r < c.v
  · rw [unemb_x hv r h1]; rfl
  · by_cases h2 : r < 2 * c.v
    · rw [unemb_y hv r (by omega) h2]
      show c.v + (r - c.v) = r
      omega
    · rw [unemb_s hv r (by omega) hr]
      show 2 * c.v + (r - 2 * c.v) = r
      omega

/-- gate products of phase A / phase B on the live roles, and their inverses -/
noncomputable def MA (c : Raw) (hv : 0 < c.v) : Matrix (Rl c) (Rl c) ℚ :=
  matP (unemb c hv) (mic (addsA c))
noncomputable def MAi (c : Raw) (hv : 0 < c.v) : Matrix (Rl c) (Rl c) ℚ :=
  matPinv (unemb c hv) (mic (addsA c))
noncomputable def MB (c : Raw) (hv : 0 < c.v) : Matrix (Rl c) (Rl c) ℚ :=
  matP (unemb c hv) (mic (addsB c))
noncomputable def MBi (c : Raw) (hv : 0 < c.v) : Matrix (Rl c) (Rl c) ℚ :=
  matPinv (unemb c hv) (mic (addsB c))

/-- copies += slots: copy `k` reads the slot register of the retained total `k` -/
def Ccm (c : Raw) : Matrix (Fin c.ret.length) (Fin c.R) ℚ :=
  fun k q => if 2 * c.v + q.val = (c.ret.getD k.val (0, 0)).1 then 1 else 0

/-- y += copies: the scatter rows -/
noncomputable def Jrm (c : Raw) : Matrix (Fin c.v) (Fin c.ret.length) ℚ :=
  fun S k => rowOf (((scatRows c).getD S.val []).map fun x => (x.1, toCoef x.2)) k

theorem okS_spec {v v2 nr t s : Nat} (h : okSK v v2 nr t s = true) :
    v ≤ t ∧ t < v2 ∧ v2 ≤ s ∧ s < nr := by
  simp only [okSK, Bool.and_eq_true, Nat.ble_eq] at h
  omega

/-- **the scatter adds act on the content matrix as `CR.scatM (Jr * Cc)`** -/
theorem cm_scat (p : SPar) (lo n : Nat) (hp : PGood c p lo n) (a1 a2 : SSt)
    (h : GRun p.sw n (U c p) (okS c) (fun _ => true) a1 (scatAdds c) a2) (hsh : ScatShape c) :
    Cm p.sw n (U c p) (emb c) a2 = scatM (Jrm c * Ccm c) * Cm p.sw n (U c p) (emb c) a1 := by
  obtain ⟨hlen, hent⟩ := hsh
  have hl : (scatRows c).length = c.v := by omega
  obtain ⟨u1, u2⟩ := scatFrom_run p.sw n (U c p) (okS c) (2 * c.v)
    (fun t s ho => ⟨(okS_spec ho).2.2.1, (okS_spec ho).2.1⟩) c.ret (scatRows c) c.v a1 a2 a1
    (by omega) (fun r _ => ⟨rfl, rfl⟩) h
  ext i T
  unfold scatM
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, embYS_mul_apply]
  rcases i with (t' | S') | q
  · obtain ⟨p1, p2⟩ := u1 t'.val (Or.inl t'.isLt)
    show gcont p.sw (U c p) a2 t'.val T.val = gcont p.sw (U c p) a1 t'.val T.val + 0
    rw [gcont_congr p.sw (U c p) a1 a2 _ _ p1 p2, add_zero]
  · have hS : S'.val < (scatRows c).length := by rw [hl]; exact S'.isLt
    have hrow : ∀ x ∈ (scatRows c).getD S'.val [], x.1 < c.ret.length :=
      hent _ (getD_mem_lt (scatRows c) [] S'.val hS)
    -- the slot register of a retained total
    have hg : ∀ k : Fin c.ret.length,
        ∑ q, Ccm c k q * Cm p.sw n (U c p) (emb c) a1 (Sum.inr q) T
          = gcont p.sw (U c p) a1 (c.ret.getD k.val (0, 0)).1 T.val := by
      intro k
      obtain ⟨r1, r2⟩ := hp.hret _ (getD_mem_lt c.ret (0, 0) k.val k.isLt)
      rw [Finset.sum_eq_single (⟨(c.ret.getD k.val (0, 0)).1 - 2 * c.v, by omega⟩ : Fin c.R)]
      · have e : 2 * c.v + ((c.ret.getD k.val (0, 0)).1 - 2 * c.v) = (c.ret.getD k.val (0, 0)).1 := by
          omega
        show (if 2 * c.v + ((c.ret.getD k.val (0, 0)).1 - 2 * c.v) = (c.ret.getD k.val (0, 0)).1
          then (1:ℚ) else 0) * gcont p.sw (U c p) a1
            (2 * c.v + ((c.ret.getD k.val (0, 0)).1 - 2 * c.v)) T.val = _
        rw [if_pos e, one_mul, e]
      · intro q _ hq
        have hne : ¬ 2 * c.v + q.val = (c.ret.getD k.val (0, 0)).1 := fun e =>
          hq (Fin.ext (by show q.val = (c.ret.getD k.val (0, 0)).1 - 2 * c.v; omega))
        show (if 2 * c.v + q.val = (c.ret.getD k.val (0, 0)).1 then (1:ℚ) else 0) * _ = 0
        rw [if_neg hne, zero_mul]
      · intro hb
        exact absurd (Finset.mem_univ _) hb
    have step : ∑ q, (Jrm c * Ccm c) S' q * Cm p.sw n (U c p) (emb c) a1 (Sum.inr q) T
        = ∑ k, Jrm c S' k * gcont p.sw (U c p) a1 (c.ret.getD k.val (0, 0)).1 T.val := by
      calc ∑ q, (Jrm c * Ccm c) S' q * Cm p.sw n (U c p) (emb c) a1 (Sum.inr q) T
          = ∑ q, ∑ k, Jrm c S' k * (Ccm c k q * Cm p.sw n (U c p) (emb c) a1 (Sum.inr q) T) := by
            refine Finset.sum_congr rfl (fun q _ => ?_)
            rw [Matrix.mul_apply, Finset.sum_mul]
            exact Finset.sum_congr rfl (fun k _ => mul_assoc _ _ _)
        _ = ∑ k, ∑ q, Jrm c S' k * (Ccm c k q * Cm p.sw n (U c p) (emb c) a1 (Sum.inr q) T) :=
            Finset.sum_comm
        _ = ∑ k, Jrm c S' k * gcont p.sw (U c p) a1 (c.ret.getD k.val (0, 0)).1 T.val := by
            refine Finset.sum_congr rfl (fun k _ => ?_)
            rw [← Finset.mul_sum, hg k]
    show gcont p.sw (U c p) a2 (c.v + S'.val) T.val = gcont p.sw (U c p) a1 (c.v + S'.val) T.val
      + ∑ q, (Jrm c * Ccm c) S' q * Cm p.sw n (U c p) (emb c) a1 (Sum.inr q) T
    rw [u2 S'.val hS T.val T.isLt, step]
    congr 1
    have hl' : ∀ x ∈ ((scatRows c).getD S'.val []).map (fun x => (x.1, toCoef x.2)),
        x.1 < c.ret.length := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact hrow y hy
    have := rowOf_sum (((scatRows c).getD S'.val []).map fun x => (x.1, toCoef x.2)) hl'
      (fun k => gcont p.sw (U c p) a1 (c.ret.getD k.val (0, 0)).1 T.val)
      (fun k' => gcont p.sw (U c p) a1 (c.ret.getD k' (0, 0)).1 T.val) (fun _ => rfl)
    rw [List.map_map] at this
    exact this.symm
  · obtain ⟨p1, p2⟩ := u1 (2 * c.v + q.val) (Or.inr (by omega))
    show gcont p.sw (U c p) a2 (2 * c.v + q.val) T.val
      = gcont p.sw (U c p) a1 (2 * c.v + q.val) T.val + 0
    rw [gcont_congr p.sw (U c p) a1 a2 _ _ p1 p2, add_zero]

#print axioms unemb_emb
#print axioms emb_unemb
#print axioms cm_scat

end GS
