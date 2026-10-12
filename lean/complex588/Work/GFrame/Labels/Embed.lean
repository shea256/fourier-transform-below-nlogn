import Work.GFrame.Labels.GXMap
import Work.Carrier.Sched

/-!
# GFrame labels, part 6 (key: eng-labels): the OLD label calculus embeds

Everything of `Work/SharedSumStructured/Labels.lean` (`Lbl`, `Climb`), `Work/Carrier/Sched.lean`
(`Mv`, `Step`, `SchedOk`, `sched_route`) and `Work/Combine/XG.lean` (`XMap`) is a special case:

* `gram_mat`, `mat_fam`, `mat_union`   a projector `A.mat s` is its own Gram matrix, and a climb
                    `s ⊆ t` in one orthonormal basis adds `∑ z zᵀ` over the lines of `t \ s`;
* `Climb.gclimbO`   every old `Climb U V` is a `GClimbO U V (V.d - U.d)`;
* `Mv.gmv`          every old `Mv U V` is a `GMv ar U V [mvRank U V]`;
* `emb`, `emb_ok`, `emb_out`, `emb_act`, `emb_ranks`
                    every old legal schedule is a legal generalised schedule, in EVERY engine and
                    for EVERY `GXMap`, with the same labels, scalar map and block ranks;
* `sched_route_any` the old `sched_route`, for every engine `K` and every `GXMap`;
* `GXMap.toXMap`    every `GXMap` is an old `XMap` (so every old theorem that takes an `XMap`
                    accepts it).

No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving.GF
open Binary Matrix Finset RAM CB SS
noncomputable section

section
variable {H α : Type} [Fintype H] [DecidableEq H] [Fintype α] [DecidableEq α]

/-- a projector of an orthonormal basis is its own Gram matrix. -/
lemma gram_mat (A : OBase H) (s : Finset H) : gram (A.mat s) = A.mat s := by
  ext i j
  simp only [gram, Matrix.mul_apply, Matrix.transpose_apply, OBase.mat]
  simp_rw [Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]
  have key : ∀ k' ∈ s, ∑ l, A.v k l * A.v k i * (A.v k' l * A.v k' j)
      = if k = k' then A.v k i * A.v k' j else 0 := by
    intro k' _
    have h := A.rows k k'
    simp only [dot] at h
    calc ∑ l, A.v k l * A.v k i * (A.v k' l * A.v k' j)
        = (∑ l, A.v k l * A.v k' l) * (A.v k i * A.v k' j) := by
          rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro l _; ring
      _ = _ := by rw [h]; split <;> simp
  rw [Finset.sum_congr rfl key, Finset.sum_ite_eq]
  simp [hk]

/-- the projector of the lines `d` is `∑ z zᵀ` over the block family of `d`. -/
lemma mat_fam (A : OBase H) (d : Finset H) : A.mat d = ∑ x, tt (A.fam d x) := by
  ext i j
  rw [Matrix.sum_apply]
  simp only [OBase.mat, tt, OBase.fam]
  rw [← Finset.sum_coe_sort d (fun k => A.v k i * A.v k j)]
  exact (Equiv.sum_comp d.equivFin.symm (fun k : {y // y ∈ d} => A.v k.1 i * A.v k.1 j)).symm

lemma mat_union (A : OBase H) {s t : Finset H} (hst : s ⊆ t) :
    A.mat t = A.mat s + A.mat (t \ s) := by
  ext i j
  simp only [OBase.mat, Matrix.add_apply]
  rw [add_comm]
  exact (Finset.sum_sdiff hst).symm

lemma gram_climb (A : OBase H) {s t : Finset H} (hst : s ⊆ t) :
    gram (A.mat t) = gram (A.mat s) + ∑ x, tt (A.fam (t \ s) x) := by
  rw [gram_mat, gram_mat, ← mat_fam, ← mat_union A hst]

/-- **Every old climb is a generalised climb.** -/
theorem Climb.gclimbO {U V : Lbl H} (h : Climb U V) : GClimbO U V (V.d - U.d) := by
  obtain ⟨A, s, t, hst, hU, hV, hd⟩ := h
  have e : V.d - U.d = (t \ s).card := by omega
  rw [e]
  exact ⟨A.fam (t \ s), A.fam_indep _, by rw [hU, hV]; exact gram_climb A hst, by omega⟩

/-- **Every old move is a generalised move**, with the same block rank. -/
theorem Mv.gmv (ar : ℕ → List ℕ) {U V : Lbl H} (h : CR.Mv U V) :
    GMv ar U V [CR.mvRank U V] := by
  rcases h with h | h | h
  · subst h
    rw [CR.mvRank_self]; exact GMv.stay U
  · rw [CR.mvRank_climb h]; exact GMv.up (Climb.gclimbO h)
  · rw [CR.mvRank_descend h]; exact GMv.down (Climb.gclimbO h)

/-- an old move is a one-role move of EVERY engine (no alternating residual involved). -/
theorem GXMap.mv_old (X : GXMap H α) (K : Calc α) {U V : Lbl H} (h : CR.Mv U V) :
    FMv K (X.Φ U.P) (X.Φ V.P) [CR.mvRank U V] := by
  rcases h with h | h | h
  · subst h
    rw [CR.mvRank_self]; exact FMv.zero (FMv.refl K _)
  · rw [CR.mvRank_climb h]
    obtain ⟨z, ind, hg, _⟩ := Climb.gclimbO h
    exact X.orth K _ _ z ind hg
  · rw [CR.mvRank_descend h]
    obtain ⟨z, ind, hg, _⟩ := Climb.gclimbO h
    exact X.orth K _ _ z ind (rel_symm hg)

/-- **Every `GXMap` is an old `XMap`.** -/
def GXMap.toXMap (X : GXMap H α) : XMap H α where
  Φ := X.Φ
  up := fun A s t hst ρ _ _ l =>
    XStep.cast (FMv.step (X.orth (xcalc α) _ _ (A.fam (t \ s)) (A.fam_indep _)
      (gram_climb A hst)) l) (fun φ => rcost_single φ _)
  down := fun A s t hst ρ _ _ l =>
    XStep.cast (FMv.step (X.orth (xcalc α) _ _ (A.fam (t \ s)) (A.fam_indep _)
      (rel_symm (gram_climb A hst))) l) (fun φ => rcost_single φ _)

end

section Emb
variable {H α ρ : Type} [Fintype H] [DecidableEq H] [Fintype α] [DecidableEq α]
  [Fintype ρ] [DecidableEq ρ]

/-- an old step as a generalised step (a move records its block rank). -/
def embSt (lab : ρ → Lbl H) : CR.Step H ρ → GSt (Lbl H) ρ
  | .gate G => .gate G
  | .relab G new => .relab G new
  | .move r V => .move r V [CR.mvRank (lab r) V]

/-- an old schedule as a generalised schedule. -/
def emb : (ρ → Lbl H) → List (CR.Step H ρ) → List (GSt (Lbl H) ρ)
  | _, [] => []
  | lab, s :: l => embSt lab s :: emb (s.out lab) l

lemma embSt_out (lab : ρ → Lbl H) (s : CR.Step H ρ) : (embSt lab s).out lab = s.out lab := by
  cases s <;> rfl
lemma embSt_act (lab : ρ → Lbl H) (s : CR.Step H ρ) : (embSt lab s).act = s.act := by
  cases s <;> rfl
lemma embSt_ranks (lab : ρ → Lbl H) (s : CR.Step H ρ) : (embSt lab s).ranks = s.ranks lab := by
  cases s <;> rfl

theorem emb_out (lab : ρ → Lbl H) (l : List (CR.Step H ρ)) :
    gschedOut lab (emb lab l) = CR.schedOut lab l := by
  induction l generalizing lab with
  | nil => rfl
  | cons s l ih =>
    show gschedOut ((embSt lab s).out lab) (emb (s.out lab) l) = CR.schedOut (s.out lab) l
    rw [embSt_out, ih]

theorem emb_act (lab : ρ → Lbl H) (l : List (CR.Step H ρ)) :
    gschedAct (emb lab l) = CR.schedAct l := by
  induction l generalizing lab with
  | nil => rfl
  | cons s l ih =>
    show gschedAct (emb (s.out lab) l) ∘ (embSt lab s).act = CR.schedAct l ∘ s.act
    rw [embSt_act, ih]

theorem emb_ranks (lab : ρ → Lbl H) (l : List (CR.Step H ρ)) :
    gschedRanks (emb lab l) = CR.schedRanks lab l := by
  induction l generalizing lab with
  | nil => rfl
  | cons s l ih =>
    show (embSt lab s).ranks ++ gschedRanks (emb (s.out lab) l)
      = s.ranks lab ++ CR.schedRanks (s.out lab) l
    rw [embSt_ranks, ih]

/-- **Every old legal schedule is a legal generalised schedule**, in every engine and for
every `GXMap`. -/
theorem emb_ok (X : GXMap H α) (K : Calc α) (lab : ρ → Lbl H) (l : List (CR.Step H ρ))
    (h : CR.SchedOk lab l) : GSchedOk K (fun U => X.Φ U.P) lab (emb lab l) := by
  induction l generalizing lab with
  | nil => trivial
  | cons s l ih =>
    refine ⟨?_, ?_⟩
    · have h1 := h.1
      cases s with
      | gate G => exact fun i j hij => congrArg X.Φ (h1 i j hij)
      | relab G new => exact fun i j hij => congrArg X.Φ (h1 i j hij)
      | move r V => exact X.mv_old K h1
    · rw [embSt_out]; exact ih _ h.2

/-- **The old `sched_route`, for every engine and every `GXMap`.** -/
theorem sched_route_any (X : GXMap H α) (K : Calc α) (l : List (CR.Step H ρ))
    (lab : ρ → Lbl H) (h : CR.SchedOk lab l) :
    K.Route (fun r => X.Φ (lab r).P) (fun r => X.Φ (CR.schedOut lab l r).P) (CR.schedAct l)
      (fun φ => rcost φ (CR.schedRanks lab l)) := by
  have g := gsched_route K (fun U : Lbl H => X.Φ U.P) (emb lab l) lab (emb_ok X K lab l h)
  rw [emb_out, emb_act, emb_ranks] at g
  exact g

end Emb
end
end PowerSaving.GF
end OAI

#print axioms OAI.PowerSaving.GF.Climb.gclimbO
#print axioms OAI.PowerSaving.GF.GXMap.toXMap
#print axioms OAI.PowerSaving.GF.emb_ok
#print axioms OAI.PowerSaving.GF.sched_route_any
