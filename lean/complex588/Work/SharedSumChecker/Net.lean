import Work.SharedSumChecker.Scalar
import Work.SharedSumStructured.Certificate

/-!
# Shared-sum checker: from a kernel-checked certificate to the two-stage network and the engine

`PCert.Valid.certificate` / `PCert.Valid.engine`: a certificate accepted by the three kernel
checks (labels, shape, scalar identity) is a helper circuit of the generic two-stage network
of `Work.SharedSumStructured.Certificate` (`network_certificate`, `engine_of_network`).  The
network has `2 v^2 + 2 v R + pad` live roles (inputs `X`, targets `Y`, the dirty helper slots
of the `2v` invocations, idle padding), uses scratch copies of the retained totals, and its
tally is `(live roles) * h^2 - v^2 + 2 v cst`, `cst` = sum of the dimensions of the retained
labels.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace SSC
open OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.RAM OAI.PowerSaving.RAM.Ty
  OAI.PowerSaving.SS Finset Matrix

namespace PCert
variable {c : PCert}

theorem Valid.base_ex (V : c.Valid) (t : Fin c.v) :
    ∃ A : OBase (Fin c.p.h), c.tv t = A.v ⟨0, V.hh⟩ := by
  have C := V.complete (fun t : Fin c.v => t.val) (fun t => by have := t.isLt; omega)
  obtain ⟨A, hA⟩ := C.base t
  obtain ⟨l, hl⟩ := hist_prefix c.H0 c.tot t.val
  refine ⟨A, ?_⟩
  rw [hA, hl]
  show _ = vecF c.p (((if t.val < c.v then [c.trips.getD t.val 0] else []) ++ l).getD 0 0)
  rw [if_pos t.isLt]
  rfl

/-- the network data of the structured development -/
noncomputable def Valid.netdata (V : c.Valid) (hid : c.ScalarId V.hR) (pad : ℕ) :
    NetData (Fin c.p.h) (Fin c.v) (Fin c.R) (Fin c.p.h) where
  K := V.circuit hid
  base := fun t => Classical.choose (V.base_ex t)
  piv := fun _ => ⟨0, V.hh⟩
  hbase := fun t => Classical.choose_spec (V.base_ex t)
  pad := pad

/-- copy cost of one invocation: the dimensions of the labels of the retained totals -/
def cstN (c : PCert) : ℕ := (c.retLab.map fun L => cntOf c.p (dec L)).sum

theorem Valid.cst_eq (V : c.Valid) (hid : c.ScalarId V.hR) (pad : ℕ) :
    (V.netdata hid pad).cst = c.cstN := by
  show ∑ k : Fin c.p.h, (c.phi5 (c.retq V.hR k)).d = _
  have hterm : ∀ k : Fin c.p.h,
      (c.phi5 (c.retq V.hR k)).d = cntOf c.p (dec (c.retLab.getD k.val 0)) := by
    intro k
    obtain ⟨_, p5, _, _⟩ := V.points
    have hmem : (c.v + c.ret.getD k.val 0, c.retLab.getD k.val 0) ∈ c.e5 :=
      List.mem_map.mpr ⟨(c.ret.getD k.val 0, c.retLab.getD k.val 0),
        zip_getD_mem _ _ _ _ _ (by rw [V.hrl]; exact k.isLt) (by rw [V.hrl']; exact k.isLt), rfl⟩
    have h := p5 _ hmem
    show cntOf c.p (runLab c.p c.lab0 c.a5 (c.embS (c.retq V.hR k))) = _
    have e : c.embS (c.retq V.hR k) = c.v + c.ret.getD k.val 0 := by
      show c.v + c.ret.getD k.val 0 % c.R = _
      rw [Nat.mod_eq_of_lt (V.all_ret k)]
    rw [e, h]
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  unfold cstN
  rw [list_sum_range (fun L => cntOf c.p (dec L)) c.retLab, V.hrl']
  exact Fin.sum_univ_eq_sum_range (fun k => cntOf c.p (dec (c.retLab.getD k 0))) c.p.h

/-- **The scratch certificate of the two-stage network with the checked helper circuit.** -/
theorem Valid.certificate (V : c.Valid) (hid : c.ScalarId V.hR) (pad : ℕ) (hv : 0 < c.v) :
    ∃ p : PWord (Fin c.p.h × Fin c.p.h) (Role (Fin c.v) (Fin c.R) (Fin c.p.h) pad),
      tally p + c.v * c.v
        = (2 * (c.v * c.v) + 2 * (c.v * c.R) + pad) * (c.p.h * c.p.h) + 2 * (c.v * c.cstN) ∧
      LiveKernel (Sum.inl : Live (Fin c.v) (Fin c.R) pad →
        Role (Fin c.v) (Fin c.R) (Fin c.p.h) pad) p := by
  obtain ⟨p, hp, hw⟩ := network_certificate (V.netdata hid pad) ⟨0, hv⟩
  refine ⟨p, ?_, hw⟩
  rw [V.cst_eq hid pad] at hp
  simp only [Fintype.card_fin] at hp
  exact hp

universe U

/-- **The engine from a checked certificate**: statement of upstream `hills_program` with the
envelope `(k+1)^z`, as soon as the live roles number `2^a` and the tally satisfies the rate
inequality. -/
theorem Valid.engine (V : c.Valid) (hid : c.ScalarId V.hR) (a pad : ℕ) (hv : 0 < c.v)
    (hlive : 2 * (c.v * c.v) + 2 * (c.v * c.R) + pad = 2^a) (hm : 3 ≤ c.p.h * c.p.h)
    (z : ℝ) (hz : 0 ≤ z)
    (hrate : ∀ n : ℕ, n + c.v * c.v = 2^a * (c.p.h * c.p.h) + 2 * (c.v * c.cstN) →
      (n:ℝ)/(2:ℝ)^a < ((c.p.h * c.p.h : ℕ) : ℝ)^z)
    (cl : Paint) (m : Bool) {ι : Type U} (k : ι → ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*envelope z (k i)) := by
  refine engine_of_network (V.netdata hid pad) ⟨0, hv⟩ a ?_ ?_ z hz ?_ cl m k v
  · rw [card_live (V.netdata hid pad)]
    simp only [Fintype.card_fin]
    exact hlive
  · simpa [Fintype.card_fin] using hm
  · intro n hn
    rw [V.cst_eq hid pad] at hn
    simp only [Fintype.card_fin] at hn ⊢
    exact hrate n hn

end PCert

end SSC
