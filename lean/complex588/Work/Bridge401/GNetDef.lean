import Work.Bridge401.GStage
import Work.Bridge401.StageE
import Work.Bridge377.Bank

/-!
# (key: bridge-401) The nine-stage word with entrance gauges and residual banks (PR #401): data and frames

Credits: the entrance gauges and the residual banks are Dugongue's (CrocSwap/integer-mult-bounds PR #401); the bank
patterns are Lydakis's (#275); the compressed nine-stage layout is jacklightChen's (#377); the bridged word B_K is
DaysSky's (#363); B_2, the engine, the stage geometry and the E8 unit are Jacob Sussman's (wht-power-saving-lean,
Apache-2.0).  Written by w-newsums/gen401/gen401.py (from gen377.py).
One RUN is the B_4 word of genk (stages 0, 1, 2 on pair 1; stages 2p-1, 2p on pair p >= 2; idle climbs and gate
layers between) for the data of ONE replica.  In stage `l` of run `ρ` the slot `q` of the invocation `g` uses the bank
`(g, use ρ l q)`; before the stage every bank takes its free adapter (`Zb` to `Zp`, `bank_adapt`), and the gauged
step `Wn` moves the used banks to `Zb` of the next sub-stage.  The unit is the 8 runs one after the other
(replica-outer), then ONE padding block of rank `pad b` on every bank.  No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace OAI
namespace PowerSaving
namespace GX
open Binary Matrix Finset RAM SS CB RF BR GF
noncomputable section

/-- See the file header.  Stages are numbered 0 to 8, runs (replicas) 0 to 7. -/
structure G401 (H T Sl C α Γ : Type) (nb : ℕ) [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
    [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] [Fintype α] [DecidableEq α] where
  /-- the gauged invocation (`GInvE`, L1 of DFT Bridge3). -/
  I : GInvE H T Sl C
  /-- frame maps of the invocations of the 9 stages. -/
  G0 : Γ → GWin H α
  G1 : Γ → GWin H α
  G2 : Γ → GWin H α
  G3 : Γ → GWin H α
  G4 : Γ → GWin H α
  G5 : Γ → GWin H α
  G6 : Γ → GWin H α
  G7 : Γ → GWin H α
  G8 : Γ → GWin H α
  /-- the class `(g,t)` is served by the invocation `g` in stage 0 and `r_l t g` in stage `l` (every run). -/
  r1 : T → Γ ≃ Γ
  r2 : T → Γ ≃ Γ
  r3 : T → Γ ≃ Γ
  r4 : T → Γ ≃ Γ
  r5 : T → Γ ≃ Γ
  r6 : T → Γ ≃ Γ
  r7 : T → Γ ≃ Γ
  r8 : T → Γ ≃ Γ
  /-- entrance step of the slot `q` of the invocation `d` in stage `l`: right inverse `N<l> d q`, step `Wn<l> d q`. -/
  N0 : Γ → Sl → CMat α
  Wn0 : Γ → Sl → CMat α
  N1 : Γ → Sl → CMat α
  Wn1 : Γ → Sl → CMat α
  N2 : Γ → Sl → CMat α
  Wn2 : Γ → Sl → CMat α
  N3 : Γ → Sl → CMat α
  Wn3 : Γ → Sl → CMat α
  N4 : Γ → Sl → CMat α
  Wn4 : Γ → Sl → CMat α
  N5 : Γ → Sl → CMat α
  Wn5 : Γ → Sl → CMat α
  N6 : Γ → Sl → CMat α
  Wn6 : Γ → Sl → CMat α
  N7 : Γ → Sl → CMat α
  Wn7 : Γ → Sl → CMat α
  N8 : Γ → Sl → CMat α
  Wn8 : Γ → Sl → CMat α
  /-- the bank of the slot `q` in stage `l` of run `ρ` (at most one use of a bank per sub-stage). -/
  use : Fin 8 → Fin 9 → Sl → Fin nb
  hinj : ∀ ρ l, Function.Injective (use ρ l)
  /-- bank frames before sub-stage `9 ρ + l` (`Zb`) and after its free adapter (`Zp`); the pad ranks. -/
  Zb : ℕ → Γ → Fin nb → CMat α
  Zp : ℕ → Γ → Fin nb → CMat α
  pad : Fin nb → ℕ
  u : Γ → T → Space α
  YF : Γ → T → CMat α
  hm : 2 ≤ Fintype.card α
  /-- prices of the idle climbs, for every price list. -/
  caX2 : (ℕ → ℝ) → ℝ
  caY2 : (ℕ → ℝ) → ℝ
  caX3 : (ℕ → ℝ) → ℝ
  caY3 : (ℕ → ℝ) → ℝ
  caX4 : (ℕ → ℝ) → ℝ
  caY4 : (ℕ → ℝ) → ℝ
  cX1 : (ℕ → ℝ) → ℝ
  cY1 : (ℕ → ℝ) → ℝ
  cX2 : (ℕ → ℝ) → ℝ
  cY2 : (ℕ → ℝ) → ℝ
  cX3 : (ℕ → ℝ) → ℝ
  cY3 : (ℕ → ℝ) → ℝ
  cX4 : (ℕ → ℝ) → ℝ
  cY4 : (ℕ → ℝ) → ℝ
  inv0 : ∀ g t, ∃ N : CMat α, (G0 g).Xm.Φ (tt (I.tv t)) * N = 1
  z0 : ∀ g, (G0 g).Xm.Φ 0 = 1
  hN0 : ∀ d q, (G0 d).X.Φ (I.ent q) * N0 d q = 1
  hW0 : ∀ d q, (G0 d).X.Φ (I.ent q).top = Wn0 d q * (G0 d).X.Φ (I.ent q)
  hN1 : ∀ d q, (G1 d).X.Φ (I.ent q) * N1 d q = 1
  hW1 : ∀ d q, (G1 d).X.Φ (I.ent q).top = Wn1 d q * (G1 d).X.Φ (I.ent q)
  hN2 : ∀ d q, (G2 d).X.Φ (I.ent q) * N2 d q = 1
  hW2 : ∀ d q, (G2 d).X.Φ (I.ent q).top = Wn2 d q * (G2 d).X.Φ (I.ent q)
  hN3 : ∀ d q, (G3 d).X.Φ (I.ent q) * N3 d q = 1
  hW3 : ∀ d q, (G3 d).X.Φ (I.ent q).top = Wn3 d q * (G3 d).X.Φ (I.ent q)
  hN4 : ∀ d q, (G4 d).X.Φ (I.ent q) * N4 d q = 1
  hW4 : ∀ d q, (G4 d).X.Φ (I.ent q).top = Wn4 d q * (G4 d).X.Φ (I.ent q)
  hN5 : ∀ d q, (G5 d).X.Φ (I.ent q) * N5 d q = 1
  hW5 : ∀ d q, (G5 d).X.Φ (I.ent q).top = Wn5 d q * (G5 d).X.Φ (I.ent q)
  hN6 : ∀ d q, (G6 d).X.Φ (I.ent q) * N6 d q = 1
  hW6 : ∀ d q, (G6 d).X.Φ (I.ent q).top = Wn6 d q * (G6 d).X.Φ (I.ent q)
  hN7 : ∀ d q, (G7 d).X.Φ (I.ent q) * N7 d q = 1
  hW7 : ∀ d q, (G7 d).X.Φ (I.ent q).top = Wn7 d q * (G7 d).X.Φ (I.ent q)
  hN8 : ∀ d q, (G8 d).X.Φ (I.ent q) * N8 d q = 1
  hW8 : ∀ d q, (G8 d).X.Φ (I.ent q).top = Wn8 d q * (G8 d).X.Φ (I.ent q)
  /-- the data frames a stage leaves are the data frames the next stage starts from. -/
  x01 : ∀ g t, (G0 g).Xm.Φ 1 = (G1 (r1 t g)).Xm.Φ (tt (I.tv t))
  y01 : ∀ g t, (G0 g).Xm.Φ (1 + tt (I.tv t)) = (G1 (r1 t g)).Xm.Φ 0
  x12 : ∀ g t, (G1 (r1 t g)).Xm.Φ 1 = (G2 (r2 t g)).Xm.Φ (tt (I.tv t))
  y12 : ∀ g t, (G1 (r1 t g)).Xm.Φ (1 + tt (I.tv t)) = (G2 (r2 t g)).Xm.Φ 0
  x23 : ∀ g t, (G2 (r2 t g)).Xm.Φ 1 = (G3 (r3 t g)).Xm.Φ (tt (I.tv t))
  y23 : ∀ g t, (G2 (r2 t g)).Xm.Φ (1 + tt (I.tv t)) = (G3 (r3 t g)).Xm.Φ 0
  x34 : ∀ g t, (G3 (r3 t g)).Xm.Φ 1 = (G4 (r4 t g)).Xm.Φ (tt (I.tv t))
  y34 : ∀ g t, (G3 (r3 t g)).Xm.Φ (1 + tt (I.tv t)) = (G4 (r4 t g)).Xm.Φ 0
  x45 : ∀ g t, (G4 (r4 t g)).Xm.Φ 1 = (G5 (r5 t g)).Xm.Φ (tt (I.tv t))
  y45 : ∀ g t, (G4 (r4 t g)).Xm.Φ (1 + tt (I.tv t)) = (G5 (r5 t g)).Xm.Φ 0
  x56 : ∀ g t, (G5 (r5 t g)).Xm.Φ 1 = (G6 (r6 t g)).Xm.Φ (tt (I.tv t))
  y56 : ∀ g t, (G5 (r5 t g)).Xm.Φ (1 + tt (I.tv t)) = (G6 (r6 t g)).Xm.Φ 0
  x67 : ∀ g t, (G6 (r6 t g)).Xm.Φ 1 = (G7 (r7 t g)).Xm.Φ (tt (I.tv t))
  y67 : ∀ g t, (G6 (r6 t g)).Xm.Φ (1 + tt (I.tv t)) = (G7 (r7 t g)).Xm.Φ 0
  x78 : ∀ g t, (G7 (r7 t g)).Xm.Φ 1 = (G8 (r8 t g)).Xm.Φ (tt (I.tv t))
  y78 : ∀ g t, (G7 (r7 t g)).Xm.Φ (1 + tt (I.tv t)) = (G8 (r8 t g)).Xm.Φ 0
  /-- the banks: start at `1`; before every stage a free adapter; the gauged step; the pad to the kernel. -/
  z0b : ∀ g b, Zb 0 g b = 1
  hP0 : ∀ (ρ : Fin 8) g b, GReach (Zb (9 * ρ.val + 0) g b) (Zp (9 * ρ.val + 0) g b) (fun _ => 0)
  hZ0 : ∀ (ρ : Fin 8) g q, Wn0 g q * Zp (9 * ρ.val + 0) g (use ρ 0 q) = Zb (9 * ρ.val + 1) g (use ρ 0 q)
  hZn0 : ∀ (ρ : Fin 8) g b, (∀ q, use ρ 0 q ≠ b) → Zb (9 * ρ.val + 1) g b = Zp (9 * ρ.val + 0) g b
  hP1 : ∀ (ρ : Fin 8) g b, GReach (Zb (9 * ρ.val + 1) g b) (Zp (9 * ρ.val + 1) g b) (fun _ => 0)
  hZ1 : ∀ (ρ : Fin 8) g q, Wn1 g q * Zp (9 * ρ.val + 1) g (use ρ 1 q) = Zb (9 * ρ.val + 2) g (use ρ 1 q)
  hZn1 : ∀ (ρ : Fin 8) g b, (∀ q, use ρ 1 q ≠ b) → Zb (9 * ρ.val + 2) g b = Zp (9 * ρ.val + 1) g b
  hP2 : ∀ (ρ : Fin 8) g b, GReach (Zb (9 * ρ.val + 2) g b) (Zp (9 * ρ.val + 2) g b) (fun _ => 0)
  hZ2 : ∀ (ρ : Fin 8) g q, Wn2 g q * Zp (9 * ρ.val + 2) g (use ρ 2 q) = Zb (9 * ρ.val + 3) g (use ρ 2 q)
  hZn2 : ∀ (ρ : Fin 8) g b, (∀ q, use ρ 2 q ≠ b) → Zb (9 * ρ.val + 3) g b = Zp (9 * ρ.val + 2) g b
  hP3 : ∀ (ρ : Fin 8) g b, GReach (Zb (9 * ρ.val + 3) g b) (Zp (9 * ρ.val + 3) g b) (fun _ => 0)
  hZ3 : ∀ (ρ : Fin 8) g q, Wn3 g q * Zp (9 * ρ.val + 3) g (use ρ 3 q) = Zb (9 * ρ.val + 4) g (use ρ 3 q)
  hZn3 : ∀ (ρ : Fin 8) g b, (∀ q, use ρ 3 q ≠ b) → Zb (9 * ρ.val + 4) g b = Zp (9 * ρ.val + 3) g b
  hP4 : ∀ (ρ : Fin 8) g b, GReach (Zb (9 * ρ.val + 4) g b) (Zp (9 * ρ.val + 4) g b) (fun _ => 0)
  hZ4 : ∀ (ρ : Fin 8) g q, Wn4 g q * Zp (9 * ρ.val + 4) g (use ρ 4 q) = Zb (9 * ρ.val + 5) g (use ρ 4 q)
  hZn4 : ∀ (ρ : Fin 8) g b, (∀ q, use ρ 4 q ≠ b) → Zb (9 * ρ.val + 5) g b = Zp (9 * ρ.val + 4) g b
  hP5 : ∀ (ρ : Fin 8) g b, GReach (Zb (9 * ρ.val + 5) g b) (Zp (9 * ρ.val + 5) g b) (fun _ => 0)
  hZ5 : ∀ (ρ : Fin 8) g q, Wn5 g q * Zp (9 * ρ.val + 5) g (use ρ 5 q) = Zb (9 * ρ.val + 6) g (use ρ 5 q)
  hZn5 : ∀ (ρ : Fin 8) g b, (∀ q, use ρ 5 q ≠ b) → Zb (9 * ρ.val + 6) g b = Zp (9 * ρ.val + 5) g b
  hP6 : ∀ (ρ : Fin 8) g b, GReach (Zb (9 * ρ.val + 6) g b) (Zp (9 * ρ.val + 6) g b) (fun _ => 0)
  hZ6 : ∀ (ρ : Fin 8) g q, Wn6 g q * Zp (9 * ρ.val + 6) g (use ρ 6 q) = Zb (9 * ρ.val + 7) g (use ρ 6 q)
  hZn6 : ∀ (ρ : Fin 8) g b, (∀ q, use ρ 6 q ≠ b) → Zb (9 * ρ.val + 7) g b = Zp (9 * ρ.val + 6) g b
  hP7 : ∀ (ρ : Fin 8) g b, GReach (Zb (9 * ρ.val + 7) g b) (Zp (9 * ρ.val + 7) g b) (fun _ => 0)
  hZ7 : ∀ (ρ : Fin 8) g q, Wn7 g q * Zp (9 * ρ.val + 7) g (use ρ 7 q) = Zb (9 * ρ.val + 8) g (use ρ 7 q)
  hZn7 : ∀ (ρ : Fin 8) g b, (∀ q, use ρ 7 q ≠ b) → Zb (9 * ρ.val + 8) g b = Zp (9 * ρ.val + 7) g b
  hP8 : ∀ (ρ : Fin 8) g b, GReach (Zb (9 * ρ.val + 8) g b) (Zp (9 * ρ.val + 8) g b) (fun _ => 0)
  hZ8 : ∀ (ρ : Fin 8) g q, Wn8 g q * Zp (9 * ρ.val + 8) g (use ρ 8 q) = Zb (9 * ρ.val + 9) g (use ρ 8 q)
  hZn8 : ∀ (ρ : Fin 8) g b, (∀ q, use ρ 8 q ≠ b) → Zb (9 * ρ.val + 9) g b = Zp (9 * ρ.val + 8) g b
  bpad : ∀ g b, GReach (Zb 72 g b) (kernel α) (fun φ => bcost φ (pad b))
  /-- pair 2, idle until stage 1: ONE block from its start frame to the frame of its twin. -/
  aX2 : ∀ g t, XReach ((G0 g).Xm.Φ (tt (I.tv t))) ((G1 (r1 t g)).Xm.Φ 1) caX2
  aY2 : ∀ g t, XReach ((G0 g).Xm.Φ 0) ((G1 (r1 t g)).Xm.Φ (1 + tt (I.tv t))) caY2
  /-- pair 3, idle until stage 3: ONE block from its start frame to the frame of its twin. -/
  aX3 : ∀ g t, XReach ((G0 g).Xm.Φ (tt (I.tv t))) ((G3 (r3 t g)).Xm.Φ 1) caX3
  aY3 : ∀ g t, XReach ((G0 g).Xm.Φ 0) ((G3 (r3 t g)).Xm.Φ (1 + tt (I.tv t))) caY3
  /-- pair 4, idle until stage 5: ONE block from its start frame to the frame of its twin. -/
  aX4 : ∀ g t, XReach ((G0 g).Xm.Φ (tt (I.tv t))) ((G5 (r5 t g)).Xm.Φ 1) caX4
  aY4 : ∀ g t, XReach ((G0 g).Xm.Φ 0) ((G5 (r5 t g)).Xm.Φ (1 + tt (I.tv t))) caY4
  /-- pair 1 after stage 2: ONE final block. -/
  fX1 : ∀ g t, XReach ((G2 (r2 t g)).Xm.Φ 1) (kernel α) cX1
  fY1 : ∀ g t, XReach ((G2 (r2 t g)).Xm.Φ (1 + tt (I.tv t))) (YF g t) cY1
  /-- pair 2 after stage 4: ONE final block. -/
  fX2 : ∀ g t, XReach ((G4 (r4 t g)).Xm.Φ 1) (kernel α) cX2
  fY2 : ∀ g t, XReach ((G4 (r4 t g)).Xm.Φ (1 + tt (I.tv t))) (YF g t) cY2
  /-- pair 3 after stage 6: ONE final block. -/
  fX3 : ∀ g t, XReach ((G6 (r6 t g)).Xm.Φ 1) (kernel α) cX3
  fY3 : ∀ g t, XReach ((G6 (r6 t g)).Xm.Φ (1 + tt (I.tv t))) (YF g t) cY3
  /-- pair 4 after stage 8: ONE final block. -/
  fX4 : ∀ g t, XReach ((G8 (r8 t g)).Xm.Φ 1) (kernel α) cX4
  fY4 : ∀ g t, XReach ((G8 (r8 t g)).Xm.Φ (1 + tt (I.tv t))) (YF g t) cY4
  term : ∀ g t, kernel α * (G0 g).Xm.Φ (tt (I.tv t)) = shift (u g t) * YF g t

section Net
variable {H T Sl C α Γ : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C] [Fintype α] [DecidableEq α]
  [Fintype Γ] [DecidableEq Γ]
variable {nb : ℕ} (N : G401 H T Sl C α Γ nb)

/-- price of the blocks of ONE run per element of `Γ`: 9 invocations and the idle climbs of the data of
every class of its replica. -/
def G401.runUnit (φ : ℕ → ℝ) : ℝ :=
  9 * N.I.cost φ + (Fintype.card T : ℝ) * ((N.caX2 φ + N.caY2 φ) + 2 * bcost φ (Fintype.card H - 1)
      + ((N.caX3 φ + N.caY3 φ) + 2 * bcost φ (Fintype.card H - 1))
      + ((N.caX4 φ + N.caY4 φ) + 2 * bcost φ (Fintype.card H - 1))
      + (N.cX1 φ + N.cY1 φ)
      + (N.cX2 φ + N.cY2 φ)
      + (N.cX3 φ + N.cY3 φ)
      + (N.cX4 φ + N.cY4 φ))

/-- price of the blocks of one unit (one element of `Γ`): 8 runs and the padding blocks of the banks. -/
def G401.unit (φ : ℕ → ℝ) : ℝ :=
  8 * N.runUnit φ + ∑ b, bcost φ (N.pad b)

/-! data frames of the class `(g,t)`: `xi l`, `yi l` at the START of stage `l`; `xo l`, `yo l` at the
END of stage `l` (only where no next stage follows on that pair). -/
def G401.xi0 (g : Γ) (t : T) : CMat α := (N.G0 g).Xm.Φ (tt (N.I.tv t))
def G401.yi0 (g : Γ) (t : T) : CMat α := (N.G0 g).Xm.Φ 0
def G401.xi1 (g : Γ) (t : T) : CMat α := (N.G1 (N.r1 t g)).Xm.Φ (tt (N.I.tv t))
def G401.yi1 (g : Γ) (t : T) : CMat α := (N.G1 (N.r1 t g)).Xm.Φ 0
def G401.xi2 (g : Γ) (t : T) : CMat α := (N.G2 (N.r2 t g)).Xm.Φ (tt (N.I.tv t))
def G401.yi2 (g : Γ) (t : T) : CMat α := (N.G2 (N.r2 t g)).Xm.Φ 0
def G401.xi3 (g : Γ) (t : T) : CMat α := (N.G3 (N.r3 t g)).Xm.Φ (tt (N.I.tv t))
def G401.yi3 (g : Γ) (t : T) : CMat α := (N.G3 (N.r3 t g)).Xm.Φ 0
def G401.xi4 (g : Γ) (t : T) : CMat α := (N.G4 (N.r4 t g)).Xm.Φ (tt (N.I.tv t))
def G401.yi4 (g : Γ) (t : T) : CMat α := (N.G4 (N.r4 t g)).Xm.Φ 0
def G401.xi5 (g : Γ) (t : T) : CMat α := (N.G5 (N.r5 t g)).Xm.Φ (tt (N.I.tv t))
def G401.yi5 (g : Γ) (t : T) : CMat α := (N.G5 (N.r5 t g)).Xm.Φ 0
def G401.xi6 (g : Γ) (t : T) : CMat α := (N.G6 (N.r6 t g)).Xm.Φ (tt (N.I.tv t))
def G401.yi6 (g : Γ) (t : T) : CMat α := (N.G6 (N.r6 t g)).Xm.Φ 0
def G401.xi7 (g : Γ) (t : T) : CMat α := (N.G7 (N.r7 t g)).Xm.Φ (tt (N.I.tv t))
def G401.yi7 (g : Γ) (t : T) : CMat α := (N.G7 (N.r7 t g)).Xm.Φ 0
def G401.xi8 (g : Γ) (t : T) : CMat α := (N.G8 (N.r8 t g)).Xm.Φ (tt (N.I.tv t))
def G401.yi8 (g : Γ) (t : T) : CMat α := (N.G8 (N.r8 t g)).Xm.Φ 0
def G401.xo2 (g : Γ) (t : T) : CMat α := (N.G2 (N.r2 t g)).Xm.Φ 1
def G401.yo2 (g : Γ) (t : T) : CMat α := (N.G2 (N.r2 t g)).Xm.Φ (1 + tt (N.I.tv t))
def G401.xo4 (g : Γ) (t : T) : CMat α := (N.G4 (N.r4 t g)).Xm.Φ 1
def G401.yo4 (g : Γ) (t : T) : CMat α := (N.G4 (N.r4 t g)).Xm.Φ (1 + tt (N.I.tv t))
def G401.xo6 (g : Γ) (t : T) : CMat α := (N.G6 (N.r6 t g)).Xm.Φ 1
def G401.yo6 (g : Γ) (t : T) : CMat α := (N.G6 (N.r6 t g)).Xm.Φ (1 + tt (N.I.tv t))
def G401.xo8 (g : Γ) (t : T) : CMat α := (N.G8 (N.r8 t g)).Xm.Φ 1
def G401.yo8 (g : Γ) (t : T) : CMat α := (N.G8 (N.r8 t g)).Xm.Φ (1 + tt (N.I.tv t))

/-- the data of a replica before its run and after it. -/
def G401.InitD : BDat4 Γ T → CMat α := mkD4 N.xi0 N.yi0 N.xi0 N.yi0 N.xi0 N.yi0 N.xi0 N.yi0
def G401.FinD : BDat4 Γ T → CMat α := mkD4 (fun _ _ => kernel α) N.YF (fun _ _ => kernel α) N.YF (fun _ _ => kernel α) N.YF (fun _ _ => kernel α) N.YF

/-- frames of a run (on the roles of the run) after each step. -/
def G401.S0 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xi0 N.yi0 N.xi0 N.yi0 N.xi0 N.yi0 N.xi0 N.yi0 (fun g b => N.Zb (9 * ρ.val + 0) g b) (cOne Γ C α)
def G401.S1 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xi0 N.yi0 N.xi0 N.yi0 N.xi0 N.yi0 N.xi0 N.yi0 (fun g b => N.Zp (9 * ρ.val + 0) g b) (cOne Γ C α)
def G401.S2 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xi1 N.yi1 N.xi0 N.yi0 N.xi0 N.yi0 N.xi0 N.yi0 (fun g b => N.Zb (9 * ρ.val + 1) g b) (cOne Γ C α)
def G401.S3 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xi1 N.yi1 N.xi0 N.yi0 N.xi0 N.yi0 N.xi0 N.yi0 (fun g b => N.Zp (9 * ρ.val + 1) g b) (cOne Γ C α)
def G401.S4 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xi2 N.yi2 N.xi0 N.yi0 N.xi0 N.yi0 N.xi0 N.yi0 (fun g b => N.Zb (9 * ρ.val + 2) g b) (cOne Γ C α)
def G401.S5 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xi2 N.yi2 N.xi2 N.yi2 N.xi0 N.yi0 N.xi0 N.yi0 (fun g b => N.Zb (9 * ρ.val + 2) g b) (cOne Γ C α)
def G401.S6 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xi2 N.yi2 N.xi2 N.yi2 N.xi0 N.yi0 N.xi0 N.yi0 (fun g b => N.Zp (9 * ρ.val + 2) g b) (cOne Γ C α)
def G401.S7 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xo2 N.yo2 N.xi2 N.yi2 N.xi0 N.yi0 N.xi0 N.yi0 (fun g b => N.Zb (9 * ρ.val + 3) g b) (cOne Γ C α)
def G401.S8 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xo2 N.yo2 N.xi3 N.yi3 N.xi0 N.yi0 N.xi0 N.yi0 (fun g b => N.Zb (9 * ρ.val + 3) g b) (cOne Γ C α)
def G401.S9 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xo2 N.yo2 N.xi3 N.yi3 N.xi0 N.yi0 N.xi0 N.yi0 (fun g b => N.Zp (9 * ρ.val + 3) g b) (cOne Γ C α)
def G401.S10 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xo2 N.yo2 N.xi4 N.yi4 N.xi0 N.yi0 N.xi0 N.yi0 (fun g b => N.Zb (9 * ρ.val + 4) g b) (cOne Γ C α)
def G401.S11 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xo2 N.yo2 N.xi4 N.yi4 N.xi4 N.yi4 N.xi0 N.yi0 (fun g b => N.Zb (9 * ρ.val + 4) g b) (cOne Γ C α)
def G401.S12 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xo2 N.yo2 N.xi4 N.yi4 N.xi4 N.yi4 N.xi0 N.yi0 (fun g b => N.Zp (9 * ρ.val + 4) g b) (cOne Γ C α)
def G401.S13 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xo2 N.yo2 N.xo4 N.yo4 N.xi4 N.yi4 N.xi0 N.yi0 (fun g b => N.Zb (9 * ρ.val + 5) g b) (cOne Γ C α)
def G401.S14 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xo2 N.yo2 N.xo4 N.yo4 N.xi5 N.yi5 N.xi0 N.yi0 (fun g b => N.Zb (9 * ρ.val + 5) g b) (cOne Γ C α)
def G401.S15 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xo2 N.yo2 N.xo4 N.yo4 N.xi5 N.yi5 N.xi0 N.yi0 (fun g b => N.Zp (9 * ρ.val + 5) g b) (cOne Γ C α)
def G401.S16 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xo2 N.yo2 N.xo4 N.yo4 N.xi6 N.yi6 N.xi0 N.yi0 (fun g b => N.Zb (9 * ρ.val + 6) g b) (cOne Γ C α)
def G401.S17 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xo2 N.yo2 N.xo4 N.yo4 N.xi6 N.yi6 N.xi6 N.yi6 (fun g b => N.Zb (9 * ρ.val + 6) g b) (cOne Γ C α)
def G401.S18 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xo2 N.yo2 N.xo4 N.yo4 N.xi6 N.yi6 N.xi6 N.yi6 (fun g b => N.Zp (9 * ρ.val + 6) g b) (cOne Γ C α)
def G401.S19 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xo2 N.yo2 N.xo4 N.yo4 N.xo6 N.yo6 N.xi6 N.yi6 (fun g b => N.Zb (9 * ρ.val + 7) g b) (cOne Γ C α)
def G401.S20 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xo2 N.yo2 N.xo4 N.yo4 N.xo6 N.yo6 N.xi7 N.yi7 (fun g b => N.Zb (9 * ρ.val + 7) g b) (cOne Γ C α)
def G401.S21 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xo2 N.yo2 N.xo4 N.yo4 N.xo6 N.yo6 N.xi7 N.yi7 (fun g b => N.Zp (9 * ρ.val + 7) g b) (cOne Γ C α)
def G401.S22 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xo2 N.yo2 N.xo4 N.yo4 N.xo6 N.yo6 N.xi8 N.yi8 (fun g b => N.Zb (9 * ρ.val + 8) g b) (cOne Γ C α)
def G401.S23 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xo2 N.yo2 N.xo4 N.yo4 N.xo6 N.yo6 N.xi8 N.yi8 (fun g b => N.Zp (9 * ρ.val + 8) g b) (cOne Γ C α)
def G401.S24 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 N.xo2 N.yo2 N.xo4 N.yo4 N.xo6 N.yo6 N.xo8 N.yo8 (fun g b => N.Zb (9 * ρ.val + 9) g b) (cOne Γ C α)
def G401.S25 (ρ : Fin 8) : BRun4 Γ T nb C → CMat α := mkR4 (fun _ _ => kernel α) N.YF (fun _ _ => kernel α) N.YF (fun _ _ => kernel α) N.YF (fun _ _ => kernel α) N.YF (fun g b => N.Zb (9 * ρ.val + 9) g b) (cOne Γ C α)

/-- frames of all roles at the start of run `k` (`k = 8`: after the last run). -/
def G401.Sfull (k : Fin 9) : BRole401 Γ T nb C → CMat α :=
  mk401 (fun ρ' d => if ρ'.val < k.val then N.FinD d else N.InitD d) (fun g b => N.Zb (9 * k.val) g b) (cOne Γ C α)

/-- frames of all roles after the padding climbs. -/
def G401.Sfin : BRole401 Γ T nb C → CMat α :=
  mk401 (fun _ d => N.FinD d) (fun _ _ => kernel α) (cOne Γ C α)

end Net
end
end GX
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.GX.G401.unit
