import Work.Bridge401.Roles
import Work.Bridge377.Sweep

/-!
# (key: bridge-401) The scalar chain of one run of the compressed nine-stage word, and the exchange

Credits: the entrance gauges and the residual banks are Dugongue's (CrocSwap/integer-mult-bounds PR #401); the bank
patterns are Lydakis's (#275); the compressed nine-stage layout is jacklightChen's (#377); the bridged word B_K is
DaysSky's (#363); B_2, the engine, the stage geometry and the E8 unit are Jacob Sussman's (wht-power-saving-lean,
Apache-2.0).  Written by w-newsums/gen401/gen401.py (from gen377.py).

The gate layers of B_4 (DaysSky) between twins at equal frames, on the data of the run (`q = 2 .. 4`):
    after stage 2q-3   X(q-1) += X(q),  Y(q) -= Y(q-1)
    after stage 2q-2   Y(q) += Y(q-1),  X(q-1) -= X(q)
    at the end, q = 4 .. 2:   Y(q-1) -= Y(q),  X(q) += X(q-1)
Result of a run on its replica: `X_p = -y_p`, `Y_p = x_p` (`chainQ_eq`), banks unchanged.  The run maps
`liftRun4 ρ chainQ` keep the other replicas and the banks (`liftRun4_fix`, `liftRun4_fixB`) and read only replica `ρ`
and the banks (`liftRun4_loc`).  The signed exchange `brec401` on all replicas.  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace OAI
namespace PowerSaving
namespace GX
open Binary Matrix Finset RAM SS CB RF BR GF
noncomputable section

section Gates
variable {Γ T Sl C : Type} {nb : ℕ}

def pABQ_2 : BRun4 Γ T nb C → BRun4 Γ T nb C :=
  mkR4 (fun g t => rqX2 (g,t)) (fun g t => rqY1 (g,t)) (fun g t => rqX2 (g,t)) (fun g t => rqY1 (g,t)) (fun g t => rqX3 (g,t)) (fun g t => rqY3 (g,t)) (fun g t => rqX4 (g,t)) (fun g t => rqY4 (g,t)) (fun g b => rqS (g,b)) (fun g c => rqC (g,c))
def kAQ_2 : BRun4 Γ T nb C → ℚ :=
  mkR4 (fun _ _ => 1) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => -1) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)
def kBQ_2 : BRun4 Γ T nb C → ℚ :=
  mkR4 (fun _ _ => -1) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 1) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)
def pCQ_2 : BRun4 Γ T nb C → BRun4 Γ T nb C :=
  mkR4 (fun g t => rqX1 (g,t)) (fun g t => rqY2 (g,t)) (fun g t => rqX1 (g,t)) (fun g t => rqY2 (g,t)) (fun g t => rqX3 (g,t)) (fun g t => rqY3 (g,t)) (fun g t => rqX4 (g,t)) (fun g t => rqY4 (g,t)) (fun g b => rqS (g,b)) (fun g c => rqC (g,c))
def kCQ_2 : BRun4 Γ T nb C → ℚ :=
  mkR4 (fun _ _ => 0) (fun _ _ => -1) (fun _ _ => 1) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)

def pABQ_3 : BRun4 Γ T nb C → BRun4 Γ T nb C :=
  mkR4 (fun g t => rqX1 (g,t)) (fun g t => rqY1 (g,t)) (fun g t => rqX3 (g,t)) (fun g t => rqY2 (g,t)) (fun g t => rqX3 (g,t)) (fun g t => rqY2 (g,t)) (fun g t => rqX4 (g,t)) (fun g t => rqY4 (g,t)) (fun g b => rqS (g,b)) (fun g c => rqC (g,c))
def kAQ_3 : BRun4 Γ T nb C → ℚ :=
  mkR4 (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 1) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => -1) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)
def kBQ_3 : BRun4 Γ T nb C → ℚ :=
  mkR4 (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => -1) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 1) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)
def pCQ_3 : BRun4 Γ T nb C → BRun4 Γ T nb C :=
  mkR4 (fun g t => rqX1 (g,t)) (fun g t => rqY1 (g,t)) (fun g t => rqX2 (g,t)) (fun g t => rqY3 (g,t)) (fun g t => rqX2 (g,t)) (fun g t => rqY3 (g,t)) (fun g t => rqX4 (g,t)) (fun g t => rqY4 (g,t)) (fun g b => rqS (g,b)) (fun g c => rqC (g,c))
def kCQ_3 : BRun4 Γ T nb C → ℚ :=
  mkR4 (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => -1) (fun _ _ => 1) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)

def pABQ_4 : BRun4 Γ T nb C → BRun4 Γ T nb C :=
  mkR4 (fun g t => rqX1 (g,t)) (fun g t => rqY1 (g,t)) (fun g t => rqX2 (g,t)) (fun g t => rqY2 (g,t)) (fun g t => rqX4 (g,t)) (fun g t => rqY3 (g,t)) (fun g t => rqX4 (g,t)) (fun g t => rqY3 (g,t)) (fun g b => rqS (g,b)) (fun g c => rqC (g,c))
def kAQ_4 : BRun4 Γ T nb C → ℚ :=
  mkR4 (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 1) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => -1) (fun _ _ => 0) (fun _ _ => 0)
def kBQ_4 : BRun4 Γ T nb C → ℚ :=
  mkR4 (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => -1) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 1) (fun _ _ => 0) (fun _ _ => 0)
def pCQ_4 : BRun4 Γ T nb C → BRun4 Γ T nb C :=
  mkR4 (fun g t => rqX1 (g,t)) (fun g t => rqY1 (g,t)) (fun g t => rqX2 (g,t)) (fun g t => rqY2 (g,t)) (fun g t => rqX3 (g,t)) (fun g t => rqY4 (g,t)) (fun g t => rqX3 (g,t)) (fun g t => rqY4 (g,t)) (fun g b => rqS (g,b)) (fun g c => rqC (g,c))
def kCQ_4 : BRun4 Γ T nb C → ℚ :=
  mkR4 (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => -1) (fun _ _ => 1) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)

/-- scalar map of a gate layer. -/
def gscQ (p : BRun4 Γ T nb C → BRun4 Γ T nb C) (k : BRun4 Γ T nb C → ℚ)
    (x : BRun4 Γ T nb C → ℂ) : BRun4 Γ T nb C → ℂ := fun i => x i + (k i : ℂ) * x (p i)

/-- the scalar map of one run before the exchange. -/
def chainQ (us : Fin 9 → Sl → Fin nb) : (BRun4 Γ T nb C → ℂ) → (BRun4 Γ T nb C → ℂ) :=
  gscQ pCQ_2 kCQ_2 ∘ (gscQ pCQ_3 kCQ_3 ∘ (gscQ pCQ_4 kCQ_4 ∘ (id ∘ (liftQ8 (us 8) GF ∘ (id ∘ (liftQ7 (us 7) GB ∘ (id ∘ (gscQ pABQ_4 kBQ_4 ∘ (id ∘ (liftQ6 (us 6) GF ∘ (id ∘ (gscQ pABQ_4 kAQ_4 ∘ (id ∘ (liftQ5 (us 5) GB ∘ (id ∘ (gscQ pABQ_3 kBQ_3 ∘ (id ∘ (liftQ4 (us 4) GF ∘ (id ∘ (gscQ pABQ_3 kAQ_3 ∘ (id ∘ (liftQ3 (us 3) GB ∘ (id ∘ (gscQ pABQ_2 kBQ_2 ∘ (id ∘ (liftQ2 (us 2) GF ∘ (id ∘ (gscQ pABQ_2 kAQ_2 ∘ (id ∘ (liftQ1 (us 1) GB ∘ (id ∘ (liftQ0 (us 0) GF ∘ (id)))))))))))))))))))))))))))))))))

/-- **The scalar identity of a run**: `X_p = -y_p`, `Y_p = x_p` on every pair of its replica, banks unchanged. -/
lemma chainQ_eq (us : Fin 9 → Sl → Fin nb) (x : BRun4 Γ T nb C → ℂ) (l : BRunL4 Γ T nb) :
    chainQ us x (Sum.inl l) = mkR4 (fun g t => -x (rqY1 (g,t))) (fun g t => x (rqX1 (g,t))) (fun g t => -x (rqY2 (g,t))) (fun g t => x (rqX2 (g,t))) (fun g t => -x (rqY3 (g,t))) (fun g t => x (rqX3 (g,t))) (fun g t => -x (rqY4 (g,t))) (fun g t => x (rqX4 (g,t))) (fun g b => x (rqS (g,b))) (fun g c => x (rqC (g,c))) (Sum.inl l) := by
  rcases l with (((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|⟨g,b⟩)
  all_goals
    simp only [chainQ, Function.comp_apply, id_eq, gscQ, liftQ0, liftQ1, liftQ2, liftQ3, liftQ4, liftQ5, liftQ6, liftQ7, liftQ8, GF, GB, mkR4, mkD4, mkS, pABQ_2, kAQ_2, kBQ_2, pCQ_2, kCQ_2, pABQ_3, kAQ_3, kBQ_3, pCQ_3, kCQ_3, pABQ_4, kAQ_4, kBQ_4, pCQ_4, kCQ_4, posQ0, posQ1, posQ2, posQ3, posQ4, posQ5, posQ6, posQ7, posQ8, rqX1, rqY1, rqX2, rqY2, rqX3, rqY3, rqX4, rqY4, dqX1, dqY1, dqX2, dqY2, dqX3, dqY3, dqX4, dqY4, rqS, rqC, jX, jY, jS, jC]
    first
      | (push_cast; ring)
      | (push_cast; done)
      | ring

/-- run `ρ` keeps every other replica and the banks. -/
lemma liftRun4_fix (use : Fin 8 → Fin 9 → Sl → Fin nb) (i ρ : Fin 8) (hi : i ≠ ρ) (x : BRole401 Γ T nb C → ℂ)
    (s : BRole401 Γ T nb C) (hs : inA4 ρ s) : liftRun4 i (chainQ (use i)) x s = x s := by
  rcases s with ((⟨ρ',d⟩|⟨g,b⟩)|⟨g,c⟩)
  · have hs' : ρ' = ρ := hs
    exact if_neg (fun e => hi (e.symm.trans hs'))
  · show chainQ (use i) (x ∘ runPos4 i) (Sum.inl (Sum.inr (g, b))) = _
    rw [chainQ_eq]
    rfl
  · exact hs.elim

/-- every run keeps the banks. -/
lemma liftRun4_fixB (use : Fin 8 → Fin 9 → Sl → Fin nb) (i : Fin 8) (x : BRole401 Γ T nb C → ℂ)
    (s : BRole401 Γ T nb C) (hs : isBk4 s) : liftRun4 i (chainQ (use i)) x s = x s := by
  rcases s with ((⟨ρ',d⟩|⟨g,b⟩)|⟨g,c⟩)
  · exact hs.elim
  · show chainQ (use i) (x ∘ runPos4 i) (Sum.inl (Sum.inr (g, b))) = _
    rw [chainQ_eq]
    rfl
  · exact hs.elim

/-- run `ρ` on its replica reads only its replica and the banks. -/
lemma liftRun4_loc (use : Fin 8 → Fin 9 → Sl → Fin nb) (ρ : Fin 8) (d : BDat4 Γ T) (x x' : BRole401 Γ T nb C → ℂ)
    (hxx : ∀ s, inA4 ρ s → x s = x' s) :
    liftRun4 ρ (chainQ (use ρ)) x (Sum.inl (Sum.inl (ρ, d)))
      = liftRun4 ρ (chainQ (use ρ)) x' (Sum.inl (Sum.inl (ρ, d))) := by
  rw [liftRun4_self, liftRun4_self, chainQ_eq, chainQ_eq]
  rcases d with ((((⟨g,t⟩|⟨g,t⟩)|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))|(⟨g,t⟩|⟨g,t⟩))
  · show -x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inl (Sum.inl (Sum.inr ((g,t)))))))) = -x' (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inl (Sum.inl (Sum.inr ((g,t))))))))
    rw [hxx (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inl (Sum.inl (Sum.inr ((g,t)))))))) rfl]
  · show x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inl (Sum.inl (Sum.inl ((g,t)))))))) = x' (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inl (Sum.inl (Sum.inl ((g,t))))))))
    exact hxx (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inl (Sum.inl (Sum.inl ((g,t)))))))) rfl
  · show -x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inl (Sum.inr (Sum.inr ((g,t)))))))) = -x' (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inl (Sum.inr (Sum.inr ((g,t))))))))
    rw [hxx (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inl (Sum.inr (Sum.inr ((g,t)))))))) rfl]
  · show x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inl (Sum.inr (Sum.inl ((g,t)))))))) = x' (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inl (Sum.inr (Sum.inl ((g,t))))))))
    exact hxx (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inl (Sum.inr (Sum.inl ((g,t)))))))) rfl
  · show -x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inr (Sum.inr ((g,t))))))) = -x' (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inr (Sum.inr ((g,t)))))))
    rw [hxx (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inr (Sum.inr ((g,t))))))) rfl]
  · show x (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inr (Sum.inl ((g,t))))))) = x' (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inr (Sum.inl ((g,t)))))))
    exact hxx (Sum.inl (Sum.inl (ρ, Sum.inl (Sum.inr (Sum.inl ((g,t))))))) rfl
  · show -x (Sum.inl (Sum.inl (ρ, Sum.inr (Sum.inr ((g,t)))))) = -x' (Sum.inl (Sum.inl (ρ, Sum.inr (Sum.inr ((g,t))))))
    rw [hxx (Sum.inl (Sum.inl (ρ, Sum.inr (Sum.inr ((g,t)))))) rfl]
  · show x (Sum.inl (Sum.inl (ρ, Sum.inr (Sum.inl ((g,t)))))) = x' (Sum.inl (Sum.inl (ρ, Sum.inr (Sum.inl ((g,t))))))
    exact hxx (Sum.inl (Sum.inl (ρ, Sum.inr (Sum.inl ((g,t)))))) rfl

/-- **The sweep of the 8 runs on replica `ρ`** is run `ρ` on it. -/
lemma sweep_data4 (use : Fin 8 → Fin 9 → Sl → Fin nb) (ρ : Fin 8) (d : BDat4 Γ T) (x : BRole401 Γ T nb C → ℂ) :
    sweepMap (fun i : Fin 8 => liftRun4 i (chainQ (Γ := Γ) (T := T) (C := C) (use i))) x
        (Sum.inl (Sum.inl (ρ, d)))
      = chainQ (use ρ) (x ∘ runPos4 ρ) (Sum.inl (Sum.inl d)) :=
  (sweepMap_local (inA4 ρ) (Sum.inl (Sum.inl (ρ, d))) rfl (fun i : Fin 8 => liftRun4 i (chainQ (use i))) ρ
    (fun i hi x s hs => liftRun4_fix use i ρ hi x s hs) (fun x x' hxx => liftRun4_loc use ρ d x x' hxx) x).trans
    (liftRun4_self ρ (chainQ (use ρ)) x d)

/-- the sweep keeps the banks. -/
lemma sweep_bank4 (use : Fin 8 → Fin 9 → Sl → Fin nb) (g : Γ) (b : Fin nb) (x : BRole401 Γ T nb C → ℂ) :
    sweepMap (fun i : Fin 8 => liftRun4 i (chainQ (Γ := Γ) (T := T) (C := C) (use i))) x
        (Sum.inl (Sum.inr (g, b))) = x (Sum.inl (Sum.inr (g, b))) :=
  sweepMap_fix isBk4 (fun i : Fin 8 => liftRun4 i (chainQ (use i))) (fun i x s hs => liftRun4_fixB use i x s hs) x
    (Sum.inl (Sum.inr (g, b))) trivial

/-- the signed exchange `X_p := Y_p`, `Y_p := -X_p` on every pair of every replica. -/
def bpull401 : BRole401 Γ T nb C → BRole401 Γ T nb C :=
  mk401 (fun ρ => mkD4 (fun g t => Sum.inl (Sum.inl (ρ, dqY1 (g,t)))) (fun g t => Sum.inl (Sum.inl (ρ, dqX1 (g,t)))) (fun g t => Sum.inl (Sum.inl (ρ, dqY2 (g,t)))) (fun g t => Sum.inl (Sum.inl (ρ, dqX2 (g,t)))) (fun g t => Sum.inl (Sum.inl (ρ, dqY3 (g,t)))) (fun g t => Sum.inl (Sum.inl (ρ, dqX3 (g,t)))) (fun g t => Sum.inl (Sum.inl (ρ, dqY4 (g,t)))) (fun g t => Sum.inl (Sum.inl (ρ, dqX4 (g,t))))) (fun g b => Sum.inl (Sum.inr (g, b))) (fun g c => Sum.inr (g, c))

def bsgn401 : BRole401 Γ T nb C → ℚ :=
  mk401 (fun _ => mkD4 (fun _ _ => 1) (fun _ _ => -1) (fun _ _ => 1) (fun _ _ => -1) (fun _ _ => 1) (fun _ _ => -1) (fun _ _ => 1) (fun _ _ => -1)) (fun _ _ => 1) (fun _ _ => 1)

variable [Fintype Γ] [DecidableEq Γ] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]

def brec401 : Matrix (BRole401 Γ T nb C) (BRole401 Γ T nb C) ℚ :=
  fun i j => if j = bpull401 i then bsgn401 i else 0

lemma actPoint_brec401 (x : BRole401 Γ T nb C → ℂ) (i : BRole401 Γ T nb C) :
    actPoint brec401 x i = (bsgn401 i : ℂ) * x (bpull401 i) := by
  unfold actPoint
  rw [sum_eq_single (bpull401 i)]
  · simp [brec401]
  · intro j _ hj; simp [brec401, hj]
  · simp

end Gates
end
end GX
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.GX.chainQ_eq
#print axioms OAI.PowerSaving.GX.sweep_data4
#print axioms OAI.PowerSaving.GX.sweep_bank4
