import Work.Reframe.Erase
import Work.Reframe.FrameAlg

/-!
# (key: reframe) An invocation on SHARED (dirty, arbitrarily framed) helper slots

`xin Xm K Z c` / `xout Xm K Z c` : frame matrices of the roles of one invocation at its start /
end: the banks are given by the block frame map `Xm` (`X_t : Φ <t> ↦ Φ 1`,
`Y_t : Φ 0 ↦ Φ t^⊥`), the slots carry the matrices `Z q`, the copies the matrices `c k`.

* `xinvocation_fwd_erased`, `_bwd_erased`     erase ; invocation ; erase.  Slots `Φ 0 ↦ Φ 1`,
      copies ANY ↦ ANY, scalar map `shearF` / `shearB`, price `X.cost`.
* `xinvocation_fwd_reframed`, `_bwd_reframed` the same after `XRoute.reframe` with one matrix
      `Db t` per bank pair and one matrix `Ds q` per slot.
* `xinvocation_fwd_dirty`, `_bwd_dirty`       THE WORKHORSE.  Slots start at ARBITRARY matrices
      `Z q` and end at `Wn * Z q`, where `Wn` is the frame of the window
      (`Xm.Φ 1 = Wn * Xm.Φ 0`) and `Xm.Φ 0` (the frame of the base) is invertible.
* `xinvocation_fwd_shared`, `_bwd_shared`     projector form: base `Q`, window `W`, slots at
      `frameM (A q)` with `A q ⟂ W` end at `frameM (W + A q)`.
* `xinvocation_fwd_shared_basis`, `_bwd_shared_basis`  index-set form in ONE orthonormal basis
      `B`: base `frame B q`, window `frame B w`, slots `frame B a ↦ frame B (w ∪ a)`.

In all of them the word and the price are those of the plain invocation, and the scalar map is
exactly `(x, y, s, c) ↦ (x, y + x, s, 0)` resp. `(x - y, y, s, 0)` for EVERY input.

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace CB
open Binary Matrix Finset RAM SS
noncomputable section

section Shared
variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]
variable {α : Type} [Fintype α] [DecidableEq α]

/-- frame matrices at the START of an invocation: banks from the frame map, slots `Z`,
copies `c`. -/
def xin (Xm : XMap H α) (K : Circuit H T Sl C) (Z : Sl → CMat α) (c : C → CMat α) :
    Box T Sl C → CMat α :=
  stamp (fun t => Xm.Φ (tt (K.tv t))) (fun _ => Xm.Φ 0) Z c

/-- frame matrices at the END of an invocation. -/
def xout (Xm : XMap H α) (K : Circuit H T Sl C) (Z : Sl → CMat α) (c : C → CMat α) :
    Box T Sl C → CMat α :=
  stamp (fun _ => Xm.Φ 1) (fun t => Xm.Φ (1 + tt (K.tv t))) Z c

variable (X : XCircuit H T Sl C)

/-- **Erase-wrapped forward invocation.**  Price of the plain invocation; the copies enter and
leave with arbitrary frame matrices. -/
theorem xinvocation_fwd_erased (Xm : XMap H α) (c0 c1 : C → CMat α) :
    XRoute (xin Xm X.K (fun _ => Xm.Φ 0) c0) (xout Xm X.K (fun _ => Xm.Φ 1) c1)
      shearF X.cost := by
  have e0 : XRoute (xin Xm X.K (fun _ => Xm.Φ 0) c0)
      (xst Xm (fun t => lineL (X.K.tv t)) (fun _ => zeroL) (fun _ => zeroL) X.K.cen)
      eraseC (fun _ => 0) :=
    xerase (fun t => rfl) (fun t => rfl) (fun q => rfl)
  have e1 : XRoute
      (xst Xm (fun _ => fullL) (fun t => perpL (X.K.tv t)) (fun _ => fullL) (fun _ => zeroL))
      (xout Xm X.K (fun _ => Xm.Φ 1) c1) eraseC (fun _ => 0) :=
    xerase (fun t => rfl) (fun t => rfl) (fun q => rfl)
  have tot := (e0.trans (xinvocation_fwd X Xm)).trans e1
  refine (tot.castg (g' := shearF) (erase_fwd_erase X.K)).cast (fun φ => ?_)
  simp

/-- **Erase-wrapped backward invocation.** -/
theorem xinvocation_bwd_erased (Xm : XMap H α) (c0 c1 : C → CMat α) :
    XRoute (xin Xm X.K (fun _ => Xm.Φ 0) c0) (xout Xm X.K (fun _ => Xm.Φ 1) c1)
      shearB X.cost := by
  have e0 : XRoute (xin Xm X.K (fun _ => Xm.Φ 0) c0)
      (xst Xm (fun t => lineL (X.K.tv t)) (fun _ => zeroL) (fun _ => zeroL) (fun _ => zeroL))
      eraseC (fun _ => 0) :=
    xerase (fun t => rfl) (fun t => rfl) (fun q => rfl)
  have e1 : XRoute
      (xst Xm (fun _ => fullL) (fun t => perpL (X.K.tv t)) (fun _ => fullL) X.K.cen)
      (xout Xm X.K (fun _ => Xm.Φ 1) c1) eraseC (fun _ => 0) :=
    xerase (fun t => rfl) (fun t => rfl) (fun q => rfl)
  have tot := (e0.trans (xinvocation_bwd X Xm)).trans e1
  refine (tot.castg (g' := shearB) (erase_bwd_erase X.K)).cast (fun φ => ?_)
  simp

/-- re-framing matrices of the roles of an invocation: `Db t` on the bank pair `t`, `Ds q` on
the slot `q`, nothing on the copies. -/
def boxD (Db : T → CMat α) (Ds : Sl → CMat α) : Box T Sl C → CMat α :=
  stamp Db Db Ds (fun _ => 1)

lemma xin_boxD (Xm : XMap H α) (K : Circuit H T Sl C) (Z : Sl → CMat α) (c : C → CMat α)
    (Db : T → CMat α) (Ds : Sl → CMat α) :
    (fun r => xin Xm K Z c r * boxD Db Ds r)
      = stamp (fun t => Xm.Φ (tt (K.tv t)) * Db t) (fun t => Xm.Φ 0 * Db t)
          (fun q => Z q * Ds q) c := by
  funext r
  rcases r with ((t|t)|(q|k))
  · rfl
  · rfl
  · rfl
  · show c k * 1 = c k
    rw [Matrix.mul_one]

lemma xout_boxD (Xm : XMap H α) (K : Circuit H T Sl C) (Z : Sl → CMat α) (c : C → CMat α)
    (Db : T → CMat α) (Ds : Sl → CMat α) :
    (fun r => xout Xm K Z c r * boxD Db Ds r)
      = stamp (fun t => Xm.Φ 1 * Db t) (fun t => Xm.Φ (1 + tt (K.tv t)) * Db t)
          (fun q => Z q * Ds q) c := by
  funext r
  rcases r with ((t|t)|(q|k))
  · rfl
  · rfl
  · rfl
  · show c k * 1 = c k
    rw [Matrix.mul_one]

/-- **Erase-wrapped forward invocation, re-framed**: one arbitrary matrix per bank pair, one
arbitrary matrix per slot. -/
theorem xinvocation_fwd_reframed (Xm : XMap H α) (Db : T → CMat α) (Ds : Sl → CMat α)
    (c0 c1 : C → CMat α) :
    XRoute
      (stamp (fun t => Xm.Φ (tt (X.K.tv t)) * Db t) (fun t => Xm.Φ 0 * Db t)
        (fun q => Xm.Φ 0 * Ds q) c0)
      (stamp (fun t => Xm.Φ 1 * Db t) (fun t => Xm.Φ (1 + tt (X.K.tv t)) * Db t)
        (fun q => Xm.Φ 1 * Ds q) c1)
      shearF X.cost := by
  have h := XRoute.reframe (boxD Db Ds) (xinvocation_fwd_erased X Xm c0 c1)
    (shearF_comm Db Ds (fun _ => 1))
  rw [xin_boxD, xout_boxD] at h
  exact h

/-- **Erase-wrapped backward invocation, re-framed.** -/
theorem xinvocation_bwd_reframed (Xm : XMap H α) (Db : T → CMat α) (Ds : Sl → CMat α)
    (c0 c1 : C → CMat α) :
    XRoute
      (stamp (fun t => Xm.Φ (tt (X.K.tv t)) * Db t) (fun t => Xm.Φ 0 * Db t)
        (fun q => Xm.Φ 0 * Ds q) c0)
      (stamp (fun t => Xm.Φ 1 * Db t) (fun t => Xm.Φ (1 + tt (X.K.tv t)) * Db t)
        (fun q => Xm.Φ 1 * Ds q) c1)
      shearB X.cost := by
  have h := XRoute.reframe (boxD Db Ds) (xinvocation_bwd_erased X Xm c0 c1)
    (shearB_comm Db Ds (fun _ => 1))
  rw [xin_boxD, xout_boxD] at h
  exact h

/-- **Forward invocation on DIRTY helper slots.**  `N0` is an inverse of the frame of the base,
`Wn` the frame of the window.  The slots start at ARBITRARY matrices `Z q` and end at
`Wn * Z q`; banks as in the plain invocation; copies arbitrary; scalar map `shearF`; price of
the plain invocation. -/
theorem xinvocation_fwd_dirty (Xm : XMap H α) (N0 Wn : CMat α) (hN : Xm.Φ 0 * N0 = 1)
    (hW : Xm.Φ 1 = Wn * Xm.Φ 0) (Z : Sl → CMat α) (c0 c1 : C → CMat α) :
    XRoute (xin Xm X.K Z c0) (xout Xm X.K (fun q => Wn * Z q) c1) shearF X.cost := by
  have h := xinvocation_fwd_reframed X Xm (fun _ => 1) (fun q => N0 * Z q) c0 c1
  have e0 : xin Xm X.K Z c0 = stamp (fun t => Xm.Φ (tt (X.K.tv t)) * (1 : CMat α))
      (fun _ => Xm.Φ 0 * (1 : CMat α)) (fun q => Xm.Φ 0 * (N0 * Z q)) c0 := by
    funext r
    rcases r with ((t|t)|(q|k))
    · show Xm.Φ (tt (X.K.tv t)) = Xm.Φ (tt (X.K.tv t)) * 1
      rw [Matrix.mul_one]
    · show Xm.Φ 0 = Xm.Φ 0 * 1
      rw [Matrix.mul_one]
    · show Z q = Xm.Φ 0 * (N0 * Z q)
      rw [← Matrix.mul_assoc, hN, Matrix.one_mul]
    · rfl
  have e1 : xout Xm X.K (fun q => Wn * Z q) c1 = stamp (fun _ => Xm.Φ 1 * (1 : CMat α))
      (fun t => Xm.Φ (1 + tt (X.K.tv t)) * (1 : CMat α)) (fun q => Xm.Φ 1 * (N0 * Z q)) c1 := by
    funext r
    rcases r with ((t|t)|(q|k))
    · show Xm.Φ 1 = Xm.Φ 1 * 1
      rw [Matrix.mul_one]
    · show Xm.Φ (1 + tt (X.K.tv t)) = Xm.Φ (1 + tt (X.K.tv t)) * 1
      rw [Matrix.mul_one]
    · show Wn * Z q = Xm.Φ 1 * (N0 * Z q)
      rw [hW, Matrix.mul_assoc, ← Matrix.mul_assoc (Xm.Φ 0), hN, Matrix.one_mul]
    · rfl
  rw [e0, e1]
  exact h

/-- **Backward invocation on DIRTY helper slots.** -/
theorem xinvocation_bwd_dirty (Xm : XMap H α) (N0 Wn : CMat α) (hN : Xm.Φ 0 * N0 = 1)
    (hW : Xm.Φ 1 = Wn * Xm.Φ 0) (Z : Sl → CMat α) (c0 c1 : C → CMat α) :
    XRoute (xin Xm X.K Z c0) (xout Xm X.K (fun q => Wn * Z q) c1) shearB X.cost := by
  have h := xinvocation_bwd_reframed X Xm (fun _ => 1) (fun q => N0 * Z q) c0 c1
  have e0 : xin Xm X.K Z c0 = stamp (fun t => Xm.Φ (tt (X.K.tv t)) * (1 : CMat α))
      (fun _ => Xm.Φ 0 * (1 : CMat α)) (fun q => Xm.Φ 0 * (N0 * Z q)) c0 := by
    funext r
    rcases r with ((t|t)|(q|k))
    · show Xm.Φ (tt (X.K.tv t)) = Xm.Φ (tt (X.K.tv t)) * 1
      rw [Matrix.mul_one]
    · show Xm.Φ 0 = Xm.Φ 0 * 1
      rw [Matrix.mul_one]
    · show Z q = Xm.Φ 0 * (N0 * Z q)
      rw [← Matrix.mul_assoc, hN, Matrix.one_mul]
    · rfl
  have e1 : xout Xm X.K (fun q => Wn * Z q) c1 = stamp (fun _ => Xm.Φ 1 * (1 : CMat α))
      (fun t => Xm.Φ (1 + tt (X.K.tv t)) * (1 : CMat α)) (fun q => Xm.Φ 1 * (N0 * Z q)) c1 := by
    funext r
    rcases r with ((t|t)|(q|k))
    · show Xm.Φ 1 = Xm.Φ 1 * 1
      rw [Matrix.mul_one]
    · show Xm.Φ (1 + tt (X.K.tv t)) = Xm.Φ (1 + tt (X.K.tv t)) * 1
      rw [Matrix.mul_one]
    · show Wn * Z q = Xm.Φ 1 * (N0 * Z q)
      rw [hW, Matrix.mul_assoc, ← Matrix.mul_assoc (Xm.Φ 0), hN, Matrix.one_mul]
    · rfl
  rw [e0, e1]
  exact h

/-- **Shared helper slots, projector form** (forward).  The invocation has base `Q` and window
`W` (orthogonal projectors, `Q ⟂ W`); the slot `q` enters with the frame of ANY projector `A q`
orthogonal to the window and leaves with the frame of `W + A q`. -/
theorem xinvocation_fwd_shared (Xm : XMap H α) {Q W : Matrix α α F} (h0 : Xm.Φ 0 = frameM Q)
    (h1 : Xm.Φ 1 = frameM (Q + W)) (hQW : Qᵀ * W = 0) (A : Sl → Matrix α α F)
    (hA : ∀ q, Wᵀ * A q = 0) (c0 c1 : C → CMat α) :
    XRoute (xin Xm X.K (fun q => frameM (A q)) c0)
      (xout Xm X.K (fun q => frameM (W + A q)) c1) shearF X.cost := by
  have hN : Xm.Φ 0 * unframeM Q = 1 := by rw [h0, frameM_unframeM]
  have hW : Xm.Φ 1 = frameM W * Xm.Φ 0 := by rw [h1, h0, frameM_add Q W hQW, frameM_comm]
  have h := xinvocation_fwd_dirty X Xm (unframeM Q) (frameM W) hN hW (fun q => frameM (A q)) c0 c1
  have e : (fun q => frameM (W + A q)) = fun q => frameM W * frameM (A q) := by
    funext q; rw [frameM_add W (A q) (hA q)]
  rw [e]
  exact h

/-- **Shared helper slots, projector form** (backward). -/
theorem xinvocation_bwd_shared (Xm : XMap H α) {Q W : Matrix α α F} (h0 : Xm.Φ 0 = frameM Q)
    (h1 : Xm.Φ 1 = frameM (Q + W)) (hQW : Qᵀ * W = 0) (A : Sl → Matrix α α F)
    (hA : ∀ q, Wᵀ * A q = 0) (c0 c1 : C → CMat α) :
    XRoute (xin Xm X.K (fun q => frameM (A q)) c0)
      (xout Xm X.K (fun q => frameM (W + A q)) c1) shearB X.cost := by
  have hN : Xm.Φ 0 * unframeM Q = 1 := by rw [h0, frameM_unframeM]
  have hW : Xm.Φ 1 = frameM W * Xm.Φ 0 := by rw [h1, h0, frameM_add Q W hQW, frameM_comm]
  have h := xinvocation_bwd_dirty X Xm (unframeM Q) (frameM W) hN hW (fun q => frameM (A q)) c0 c1
  have e : (fun q => frameM (W + A q)) = fun q => frameM W * frameM (A q) := by
    funext q; rw [frameM_add W (A q) (hA q)]
  rw [e]
  exact h

/-- **Shared helper slots, index-set form** (forward): in ONE orthonormal basis `B` the base is
the index set `q`, the window the index set `w` (disjoint from `q`), and the slots have
absorbed the index set `a` (disjoint from `w`; it need not contain `q`).  They leave with
`w ∪ a`. -/
theorem xinvocation_fwd_shared_basis (Xm : XMap H α) (B : OBase α) (q w a : Finset α)
    (hqw : Disjoint q w) (hwa : Disjoint w a) (h0 : Xm.Φ 0 = frame B q)
    (h1 : Xm.Φ 1 = frame B (q ∪ w)) (c0 c1 : C → CMat α) :
    XRoute (xin Xm X.K (fun _ => frame B a) c0) (xout Xm X.K (fun _ => frame B (w ∪ a)) c1)
      shearF X.cost := by
  have hN : Xm.Φ 0 * unframe B q = 1 := by rw [h0, unframe_right]
  have hW : Xm.Φ 1 = frame B w * Xm.Φ 0 := by
    rw [h1, h0, frame_union B q w hqw]
    exact wrap_comm _ _
  have h := xinvocation_fwd_dirty X Xm (unframe B q) (frame B w) hN hW (fun _ => frame B a) c0 c1
  have e : (fun _ : Sl => frame B (w ∪ a)) = fun _ => frame B w * frame B a := by
    funext _; rw [frame_union B w a hwa]
  rw [e]
  exact h

/-- **Shared helper slots, index-set form** (backward). -/
theorem xinvocation_bwd_shared_basis (Xm : XMap H α) (B : OBase α) (q w a : Finset α)
    (hqw : Disjoint q w) (hwa : Disjoint w a) (h0 : Xm.Φ 0 = frame B q)
    (h1 : Xm.Φ 1 = frame B (q ∪ w)) (c0 c1 : C → CMat α) :
    XRoute (xin Xm X.K (fun _ => frame B a) c0) (xout Xm X.K (fun _ => frame B (w ∪ a)) c1)
      shearB X.cost := by
  have hN : Xm.Φ 0 * unframe B q = 1 := by rw [h0, unframe_right]
  have hW : Xm.Φ 1 = frame B w * Xm.Φ 0 := by
    rw [h1, h0, frame_union B q w hqw]
    exact wrap_comm _ _
  have h := xinvocation_bwd_dirty X Xm (unframe B q) (frame B w) hN hW (fun _ => frame B a) c0 c1
  have e : (fun _ : Sl => frame B (w ∪ a)) = fun _ => frame B w * frame B a := by
    funext _; rw [frame_union B w a hwa]
  rw [e]
  exact h

end Shared
end
end CB
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.CB.xinvocation_fwd_erased
#print axioms OAI.PowerSaving.CB.xinvocation_bwd_erased
#print axioms OAI.PowerSaving.CB.xinvocation_fwd_reframed
#print axioms OAI.PowerSaving.CB.xinvocation_bwd_reframed
#print axioms OAI.PowerSaving.CB.xinvocation_fwd_dirty
#print axioms OAI.PowerSaving.CB.xinvocation_bwd_dirty
#print axioms OAI.PowerSaving.CB.xinvocation_fwd_shared
#print axioms OAI.PowerSaving.CB.xinvocation_bwd_shared
#print axioms OAI.PowerSaving.CB.xinvocation_fwd_shared_basis
#print axioms OAI.PowerSaving.CB.xinvocation_bwd_shared_basis
