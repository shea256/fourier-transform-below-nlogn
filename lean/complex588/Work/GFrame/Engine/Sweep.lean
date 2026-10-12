import Work.GFrame.Engine.Adapt

/-!
# GFrame engine, part 3: running a generalised word in the RAM (agent key: eng-ram)

Copy of section 2 of `Work/Block/Batches.lean` (`ferryB`, `open_moveB`, `sweepB`) and of
`amplifiesS` (`Work/Scratch/Engine.lean`) with `walk f w.flat` replaced by `gwalk f w`:

* `gferry`, `gcoast`      the action of one letter / of a word on a grid with leftover bits;
* `GRig.open_gmove`       one letter: an old letter as before (`Rig.open_moveB`: a block of rank
                          `rk` = ONE family of recursive calls of order `rk*f`); a free adapter =
                          one linear pass, no call;
* `GRig.gsweep`           a whole word, cost = sum over its blocks;
* `gamplifies`            semantic step of one recursion level from `GLiveKernel`.
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving.RAM
open Binary Matrix Ty Finset GF
noncomputable section

section
universe U
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
variable {ι : Type U}
variable {m : Bool} {f : ι → ℕ} {s : Ty} {x : ι → T s}
    {cl : Paint} {X : Layout α} {R : Layout ρ} {r : ℕ} {v : ∀ i, Grain α ρ r (f i)}
    {b : Bank (hatch cl) ι}

/-- The action of one letter of a generalised word on a grid with leftover bits. -/
def gferry (r f : ℕ) (mv : GMove α ρ) (v : Grain α ρ r f) : Grain α ρ r f :=
  fun x => mv.act f (fun i j => v (i,x.2.1,j)) x.1 x.2.2

/-- Total action of a generalised word on a grid with leftover bits. -/
def gcoast (r f : ℕ) (w : GWord α ρ) (v : Grain α ρ r f) : Grain α ρ r f :=
  fun x => gwalk f w (fun i j => v (i,x.2.1,j)) x.1 x.2.2

theorem gcoast_cons (r f : ℕ) (mv : GMove α ρ) (w : GWord α ρ) (v : Grain α ρ r f) :
    gcoast r f (mv :: w) v = gcoast r f w (gferry r f mv v) := rfl

namespace GRig
variable (h : GRig m b.B f s x cl X R r v)
include h

/-- **One letter of a generalised word.**  `n rk i` = number of batches of a rank-`rk` block,
`τ rk i` = cost of one call of order `rk * f i`.  Free adapters: no call. -/
lemma open_gmove (n τ : ℕ → ι → ℕ) (Q : Layout σ) (hQ : 0<Q.n)
    (hk : ∀ rk, 1 ≤ rk → rk < X.n → Contract cl b (fun i => rk * f i) (τ rk) Q)
    (hg : ∀ rk, 1 ≤ rk → rk < X.n → ∀ i,
      n rk i*(sim Q (rk * f i)).n=(book X r (f i)).n)
    (mv : GMove α ρ) (hp : mv.Proper X.n) :
    Able m b s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape (gferry r (f i) mv (v i)))
      (fun i => (fleet X R r (f i)).n)
      (fun i => mv.shadow.cost (fun rk => n rk i * τ rk i)) := by
  cases mv with
  | old mv => exact h.rig.open_moveB n τ Q hQ hk hg mv hp
  | perm l G =>
    exact (show Able _ b _ _ _ _ _ _ from Able.of_can (b:=b) (h.rig.perm_cost l G))
  | phase l z c =>
    exact (show Able _ b _ _ _ _ _ _ from Able.of_can (b:=b) (h.phase_cost l z c))

/-- **A whole generalised word**: cost = sum over its blocks. -/
lemma gsweep (n τ : ℕ → ι → ℕ) (Q : Layout σ) (hQ : 0<Q.n)
    (hk : ∀ rk, 1 ≤ rk → rk < X.n → Contract cl b (fun i => rk * f i) (τ rk) Q)
    (hg : ∀ rk, 1 ≤ rk → rk < X.n → ∀ i,
      n rk i*(sim Q (rk * f i)).n=(book X r (f i)).n)
    (P : GWord α ρ) (hP : P.Proper X.n) :
    Able m b s (bundle cl) x
      (fun i => (fleet X R r (f i)).tape (gcoast r (f i) P (v i)))
      (fun i => (fleet X R r (f i)).n)
      (fun i => P.cost (fun rk => n rk i * τ rk i)) := by
  induction P generalizing s v with
  | nil =>
    have ht := h.rig.items.mono (W':=fun i => (fleet X R r (f i)).n) (fun _ => Nat.zero_le _)
    have hz := Able.of_can (b:=b) ht
    simp only [GWord.cost_nil]
    exact hz
  | cons g pth ih =>
    let v' i := gferry r (f i) g (v i)
    let env i : T (Ty.p s (bundle cl)) := (x i,(fleet X R r (f i)).tape (v' i))
    have hk' := h.gather id env (t:=Ty.p s (bundle cl)) Can.first
    have hl : GRig m b.B f (Ty.p s (bundle cl)) env cl X R r v' :=
      ⟨⟨hk'.rig.gear,hk'.rig.imag,Can.second⟩,hk'.lumT⟩
    have hh := ih hl hP.tail
    have H := (h.open_gmove (b:=b) n τ Q hQ hk hg g hP.head).save_keep hh
    simpa only [gcoast_cons, GWord.cost_cons] using H

end GRig
end

section
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]

/-- Semantic step of one recursion level (replaces `amplifiesS`): embed the slots, run the
generalised word on the table of roles, extract the slots. -/
lemma gamplifies (X : Layout α) (r f k : ℕ) (h : X.n*f+r=k) (e : σ → ρ)
    (he : Function.Injective e) (p : GWord α ρ) (hp : GLiveKernel e p)
    (v : Sim σ k → ℂ) :
    let eQ := ebb X r f k h v
    let zQ : Grain α σ r f := fun i => chords r f (fun j => eQ (i.1,j)) i.2
    crossAct r f (extM e) (gcoast r f p (crossAct r f (embM e) zQ)) =
      ebb X r f k h (whole k v) := by
  intro eQ zQ
  funext i
  obtain ⟨l,a⟩ := i
  rw [crossAct_ext]
  unfold gcoast
  rw [hp f _ (fun s hs => funext fun j => crossAct_emb_off e r f zQ s hs (a.1,j)) l]
  have hz : (fun j => crossAct r f (embM e) zQ (e l,a.1,j)) = fun j => zQ (l,a.1,j) :=
    funext fun j => crossAct_emb e he r f zQ l (a.1,j)
  rw [hz]
  exact (ripple_grid X r f h (fun j => v (l,j)) a).symm

end
end
end PowerSaving.RAM
end OAI

#print axioms OAI.PowerSaving.RAM.GRig.open_gmove
#print axioms OAI.PowerSaving.RAM.GRig.gsweep
#print axioms OAI.PowerSaving.RAM.gamplifies
