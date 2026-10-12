import Work.Block.Frames

/-!
# Block moves, part 10: the path calculus with blocks

(agent key: block-engine).  Block analogues of upstream `Path` (DirectionalWords.lean:86,
FrameLifting.lean) and of `Route` (Work/Scratch/Engine.lean, section 7).  Instead of a number
of unit moves, a route carries an upper bound `c : ℝ` for the additive cost
`w.costR φ = ∑ over blocks of φ (rank)`; with `φ r = (r/u)^z` this is the MOMENT that the
engine needs to be `< 2^a`.

* `BRoute φ S T g c`   a proper block word of cost `≤ c` taking role matrices `S` to `T` while
                       the scalar network does `g`  (`refl`, `mono`, `trans`, `gate`, `on_role`,
                       `of_route`, `lift`, `parallel`);
* `BPath φ A s t g c`  the special case of frames of fixed orthonormal bases (`gate`, `reframe`,
                       `inc`); same statement shape as upstream `Path`;
* `BRoute.liveKernel`  a route from invertible matrices to `kernel * (start)` on the live roles
                       is a scratch certificate in block form;
* `engine_program_broute`  the engine theorem fed directly with such a route of cost `< 2^a`.
-/

set_option linter.unusedSectionVars false

namespace OAI
namespace PowerSaving.Binary
open Matrix Finset
noncomputable section
section
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]

/-- Re-index the roles of a letter through an embedding (as upstream `Move.over`). -/
def BMove.over (e : ρ ↪ σ) : BMove α ρ → BMove α σ
  | .localM M => .localM (wide e M)
  | .shift r z => .shift (e r) z
  | .block r rk z ind => .block (e r) rk z ind

lemma BMove.flat_over (e : ρ ↪ σ) (mv : BMove α ρ) :
    (mv.over e).flat = mv.flat.map (Move.over e) := by
  cases mv with
  | localM M => rfl
  | shift r z => rfl
  | block r rk z ind =>
    simp only [BMove.over, BMove.flat, List.map_ofFn]
    rfl

lemma BWord.flat_over (e : ρ ↪ σ) (w : BWord α ρ) :
    BWord.flat (w.map (BMove.over e)) = w.flat.map (Move.over e) := by
  induction w with
  | nil => rfl
  | cons mv w ih =>
    rw [List.map_cons, BWord.flat_cons, BWord.flat_cons, List.map_append, ih, BMove.flat_over]

lemma BWord.costR_over (φ : ℕ → ℝ) (e : ρ ↪ σ) (w : BWord α ρ) :
    BWord.costR φ (w.map (BMove.over e)) = BWord.costR φ w := by
  induction w with
  | nil => rfl
  | cons mv w ih =>
    rw [List.map_cons, BWord.costR_cons, BWord.costR_cons, ih]
    congr 1
    cases mv <;> rfl

lemma BWord.proper_over (u : ℕ) (e : ρ ↪ σ) (w : BWord α ρ) (h : w.Proper u) :
    BWord.Proper u (w.map (BMove.over e)) := by
  intro mv hmv
  obtain ⟨m0, hm0, rfl⟩ := List.mem_map.mp hmv
  have h0 := h m0 hm0
  cases m0 <;> exact h0

lemma BWord.costR_ofPWord (φ : ℕ → ℝ) (p : PWord α ρ) :
    (BWord.ofPWord p).costR φ = (tally p : ℝ) * φ 1 := by
  induction p with
  | nil => simp [BWord.ofPWord, tally]
  | cons mv p ih =>
    change BWord.costR φ (BMove.ofMove mv :: BWord.ofPWord p) = _
    rw [BWord.costR_cons, ih]
    have ht : tally (mv :: p) = toll mv + tally p := by simp [tally]
    rw [ht]
    push_cast
    cases mv with
    | localM g => simp [BMove.ofMove, BMove.costR, BMove.rk?, toll]
    | shift l z => simp [BMove.ofMove, BMove.costR, BMove.rk?, toll]
    | dir l z nz =>
      simp only [BMove.ofMove, BMove.costR, BMove.rk?, toll]
      ring

end
end
end PowerSaving.Binary

namespace PowerSaving.RAM
open Binary Matrix Finset
noncomputable section
section
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α] [Fintype ρ] [DecidableEq ρ]
  [Fintype σ] [DecidableEq σ]

/-- **Block route.**  A proper block word of cost at most `c` (a block of rank `rk` costs
`φ rk`) that carries role `r` from the matrix `S r` to the matrix `T r` while the scalar
network does `g`.  Block analogue of `Route` (Work/Scratch/Engine.lean). -/
def BRoute (φ : ℕ → ℝ) (S T : ρ → CMat α) (g : (ρ→ℂ) → (ρ→ℂ)) (c : ℝ) : Prop :=
  ∃ w : BWord α ρ, w.Proper (Fintype.card α) ∧ w.costR φ ≤ c ∧
    ∀ (f : ℕ) (x : Data α ρ f), walk f w.flat (multiAct f S x) = multiAct f T (point f g x)

/-- **Block path**: a block route between frames of fixed orthonormal bases.  Same statement
shape as upstream `Path` (DirectionalWords.lean:86), with the cost bound `c` in place of the
mass identity. -/
abbrev BPath (φ : ℕ → ℝ) (A : ρ → OBase α) (s t : ρ → Finset α)
    (g : (ρ→ℂ) → (ρ→ℂ)) (c : ℝ) : Prop :=
  BRoute φ (fun r => frame (A r) (s r)) (fun r => frame (A r) (t r)) g c

namespace BRoute
variable {φ : ℕ → ℝ} {S T U : ρ → CMat α}

theorem refl : BRoute φ S S id 0 :=
  ⟨[], fun mv h => by simp at h, le_rfl, fun f x => rfl⟩

theorem mono {g : (ρ→ℂ) → (ρ→ℂ)} {c c' : ℝ} (h : BRoute φ S T g c) (hc : c ≤ c') :
    BRoute φ S T g c' := by
  obtain ⟨w, hw, hcost, hwalk⟩ := h
  exact ⟨w, hw, hcost.trans hc, hwalk⟩

theorem trans {g h : (ρ→ℂ) → (ρ→ℂ)} {c c' : ℝ} (a : BRoute φ S T g c)
    (b : BRoute φ T U h c') : BRoute φ S U (h ∘ g) (c + c') := by
  obtain ⟨p,hp,cp,ap⟩ := a
  obtain ⟨q,hq,cq,aq⟩ := b
  refine ⟨p++q, hp.append hq, by rw [BWord.costR_append]; linarith, ?_⟩
  intro f x
  rw [BWord.flat_append, walk_append, ap, aq]; rfl

/-- **Copy / overwrite / erase gate** (cost 0): a point gate may give role `i` a new matrix
`T i` provided every role `j` it reads for `i` currently has that matrix. -/
theorem gate (g : Matrix ρ ρ ℚ) (S T : ρ → CMat α)
    (cond : ∀ i j, g i j ≠ 0 → T i = S j) :
    BRoute φ S T (actPoint g) 0 := by
  refine ⟨[.localM g], ?_, ?_, ?_⟩
  · intro mv hmv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmv
    subst hmv; trivial
  · simp [BWord.costR, BMove.costR, BMove.rk?]
  intro f x
  rw [show BWord.flat [BMove.localM g] = [Move.localM g] from rfl]
  let M (r : ρ) := digitProd (fun _ : Fin f => S r)
  let N (r : ρ) := digitProd (fun _ : Fin f => T r)
  funext r i
  change ∑ j, (g r j:ℂ)* (∑ a, M j i a * x j a)
    = ∑ a, N r i a * (∑ j, (g r j:ℂ)*x j a)
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro j hj
  by_cases gh : g r j = 0
  · simp [gh]
  · dsimp only [M, N]
    rw [cond r j gh]
    ac_rfl

/-- A block word on one role moves the matrix of that role only. -/
theorem on_role (S : ρ → CMat α) (l : ρ) (N : CMat α) {c : ℝ}
    (h : RoleStep φ l (S l) N c) :
    BRoute φ S (Function.update S l N) id c := by
  obtain ⟨w, V, hw, hc, hV, hwalk⟩ := h
  refine ⟨w, hw, hc.le, fun f x => ?_⟩
  rw [hwalk, show point f id x = x from rfl]
  funext j
  by_cases hj : j = l
  · subst hj
    simp [roleAct, multiAct, hV]
  · simp [roleAct, multiAct, hj]

/-- Every unit-move `Route` is a block route: each directional move a block of rank one. -/
theorem of_route (hm : 2 ≤ Fintype.card α) {g : (ρ→ℂ) → (ρ→ℂ)} {c : ℕ}
    (h : Route S T g c) : BRoute φ S T g ((c:ℝ) * φ 1) := by
  obtain ⟨p, hp, hw⟩ := h
  refine ⟨BWord.ofPWord p, BWord.proper_ofPWord _ hm p, ?_, ?_⟩
  · rw [BWord.costR_ofPWord, hp]
  · intro f x
    rw [BWord.flat_ofPWord]
    exact hw f x

/-- Re-index a route on a sub-network of roles (as upstream `Path.lift`). -/
theorem lift (e : ρ ↪ σ) {S T : σ → CMat α}
    {g : (σ→ℂ) → (σ→ℂ)} {h : (ρ→ℂ) → (ρ→ℂ)} {c : ℝ}
    (q : BRoute φ (S ∘ e) (T ∘ e) h c)
    (hin : ∀ x, (g x) ∘ e = h (x ∘ e)) (hout : ∀ x i, i∉covered e → g x i=x i)
    (he : ∀ i, i∉covered e → S i = T i) :
    BRoute φ S T g c := by
  obtain ⟨w,hw,hc,ha⟩ := q
  refine ⟨w.map (BMove.over e), BWord.proper_over _ e w hw,
    by rw [BWord.costR_over]; exact hc, ?_⟩
  intro f x
  rw [BWord.flat_over]
  have frame_cont (S : σ → CMat α) (x : Data α σ f) :
      multiAct f S x ∘ e = multiAct f (S∘e) (x∘e) := rfl
  have point_cont :
      point f g x ∘ e = point f h (x ∘ e) := by
    funext i j
    exact congr_fun (hin _) i
  funext i
  by_cases hm : i∈covered e
  · obtain ⟨j,rfl⟩ := (cover_iff ..).mp hm
    exact congr_fun (show walk f _ _ ∘ e = multiAct f T _ ∘ e by
      rw [walk_over,frame_cont, ha,frame_cont,point_cont]) j
  · rw [walk_out e w.flat _ _ hm]
    unfold multiAct
    simp only [he i hm]
    apply congrArg
    funext j
    exact (hout (fun r => x r j) i hm).symm

section Parallel
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Compose routes on disjoint sets of roles (as upstream `Path.parallel`); costs add. -/
theorem parallel (e : J → ρ ↪ σ)
    (dis : ∀ i j, i ≠ j → ∀ r ∈ covered (e i), r ∉ covered (e j))
    {S T : σ → CMat α} {d : J → ℝ}
    {g : (σ→ℂ)→(σ→ℂ)} {h : J → (ρ→ℂ) → (ρ→ℂ)}
    (q : ∀ i, BRoute φ (S ∘ e i) (T ∘ e i) (h i) (d i))
    (hin : ∀ i x, (g x) ∘ e i = h i (x ∘ e i))
    (hout : ∀ x r, (∀ i, r∉covered (e i)) → g x r=x r)
    (he : ∀ r, (∀ i, r∉covered (e i)) → S r=T r) :
    BRoute φ S T g (∑ i, d i) := by
  let u (j : Finset J) := j.biUnion fun i => covered (e i)
  let l (j : Finset J) (r : σ) := if r∈u j then T r else S r
  let k (j : Finset J) (x : σ→ℂ) (r : σ) := if r∈u j then g x r else x r
  have hh (j : Finset J) : BRoute φ S (l j) (k j) (∑ i ∈ j, d i) := by
    induction j using Finset.induction with
    | empty =>
      simp only [k,l,u,biUnion_empty,notMem_empty,ite_false,sum_empty]
      exact BRoute.refl
    | insert i j hi ih =>
      have hiu (r) (hr : r∈covered (e i)) : r ∉ u j := by
        intro hg
        obtain ⟨w,hw,he'⟩ := mem_biUnion.mp hg
        have hw' : i ≠ w := fun hh => hi (hh ▸ hw)
        exact dis _ _ hw' r hr he'
      have hui (r) : r∈u (insert i j) ↔ r∈covered (e i) ∨ r∈u j := by
        simp [u]
      let fn (x : σ→ℂ) (r : σ) := if r∈covered (e i) then g x r else x r
      have compi (x) : fn x ∘ e i = h i (x∘e i) := by
        rw [← hin]
        funext j; simp [fn,covered]
      have gg : BRoute φ (l j) (l (insert i j)) fn (d i) := by
        apply BRoute.lift (e i) (h:=h i) _ compi
        · intro x l hl; simp [fn,hl]
        · intro r hr; simp [l,hui,hr]
        · have eq1 : l j ∘ e i = S ∘ e i := by
            funext r
            have h : e i r ∈ covered (e i) := by simp [covered]
            simp [l, hiu _ h]
          have eq2 : l (insert i j) ∘ e i = T ∘ e i := by
            funext r
            have h : e i r ∈ covered (e i) := by simp [covered]
            simp [l,hui,h]
          rw [eq1,eq2]; apply q
      have cmp : fn ∘ k j = k (insert i j) := by
        funext x r
        by_cases hqr : r ∈ covered (e i)
        · obtain ⟨r,rfl⟩ := (cover_iff ..).mp hqr
          change fn (k j x) _ = _
          have eq : k j x ∘ e i = x ∘ e i := by
            funext r
            have h : e i r ∈ covered (e i) := by simp [covered]
            simp [k,hiu _ h]
          have H := congr_fun (show fn (k j x) ∘ e i = g x ∘ e i by rw [compi,eq,hin]) r
          exact H.trans (by simp [k,hui,hqr])
        · simp [Function.comp,k,fn,hui,hqr]
      rw [sum_insert hi,add_comm]
      rw [← cmp]
      exact ih.trans gg
  have ha (r) : r∉u univ ↔ ∀ i, r∉covered (e i) := by simp [u]
  have eq1 : l univ = T := by
    funext r; by_cases h : r∈u univ
    · simp [l,h]
    · simp [l,h,he r ((ha r).1 h)]
  have eq2 : k univ = g := by
    funext x r; by_cases h : r∈u univ
    · simp [k,h]
    · simp [k,h,hout x r ((ha r).1 h)]
  have H := hh univ
  rwa [eq1,eq2] at H

end Parallel

/-- **Assembling a scratch certificate in block form from a block route** (block analogue of
`LiveKernel.of_route`).  If the route starts from invertible matrices, ends at
`kernel * (start)` on every live role, and its scalar network returns the live inputs whenever
the scratch inputs are zero, its word is a scratch certificate. -/
theorem liveKernel (e : σ → ρ) (S S' T : ρ → CMat α) (hS : ∀ r, S r * S' r = 1)
    (g : (ρ→ℂ) → (ρ→ℂ)) (c : ℝ) (h : BRoute φ S T g c)
    (hg : ∀ x : ρ → ℂ, (∀ s, (∀ l, e l ≠ s) → x s = 0) → ∀ l, g x (e l) = x (e l))
    (hT : ∀ l, T (e l) = kernel α * S (e l)) :
    ∃ w : BWord α ρ, w.Proper (Fintype.card α) ∧ w.costR φ ≤ c ∧ LiveKernel e w.flat := by
  obtain ⟨w,hp,hc,hw⟩ := h
  refine ⟨w, hp, hc, ?_⟩
  intro f v hv l
  let y : Data α ρ f := multiAct f S' v
  have hy : multiAct f S y = v := by
    funext r; simp [y, multiAct, hS]
  have hy0 (s : ρ) (hs : ∀ l, e l ≠ s) : y s = 0 := by
    change matAct f (S' s) (v s) = 0
    rw [hv s hs]; exact matAct_zero f _
  have hpt : point f g y (e l) = y (e l) := by
    funext i
    exact hg (fun r => y r i) (fun s hs => by rw [hy0 s hs]; rfl) l
  have h1 := congrFun (hw f y) (e l)
  rw [hy] at h1
  rw [h1]
  change matAct f (T (e l)) (point f g y (e l)) = _
  rw [hpt, hT, ← matAct_mul]
  exact congrArg _ (congrFun hy (e l))

end BRoute

namespace BPath
variable {φ : ℕ → ℝ} {A : ρ → OBase α} {s t : ρ → Finset α}

/-- Move through a gate whose nonzero entries stay within a common frame (as upstream
`Path.gate`); cost 0. -/
theorem gate (g : Matrix ρ ρ ℚ)
    (cond : ∀ i j, g i j ≠ 0 → frame (A i) (s i) = frame (A j) (s j)) :
    BPath φ A s s (actPoint g) 0 :=
  BRoute.gate g _ _ cond

/-- **Reframe with blocks** (block analogue of upstream `Path.reframe`): every role pays one
down-block of rank `|s r \ t r|` and one up-block of rank `|t r \ s r|` (a residual of full rank
`m` is split `(m-1)+1`, a residual of rank `0` is free). -/
theorem reframe (hm : 2 ≤ Fintype.card α) (A : ρ → OBase α) (s t : ρ → Finset α) :
    BPath φ A s t id (∑ r, (splitCost φ (Fintype.card α) (s r \ t r).card +
      splitCost φ (Fintype.card α) (t r \ s r).card)) := by
  have hh (J : Finset ρ) :
      BPath φ A s (fun r => if r ∈ J then t r else s r) id
        (∑ r ∈ J, (splitCost φ (Fintype.card α) (s r \ t r).card +
          splitCost φ (Fintype.card α) (t r \ s r).card)) := by
    induction J using Finset.induction_on with
    | empty =>
      have e0 : (fun r => if r ∈ (∅ : Finset ρ) then t r else s r) = s := by
        funext r; simp
      rw [e0, Finset.sum_empty]
      exact BRoute.refl
    | insert l J hl ih =>
      have hsl : (if l ∈ J then t l else s l) = s l := if_neg hl
      have step : RoleStep φ l (frame (A l) (if l ∈ J then t l else s l)) (frame (A l) (t l))
          (splitCost φ (Fintype.card α) (s l \ t l).card +
            splitCost φ (Fintype.card α) (t l \ s l).card) := by
        rw [hsl]; exact (A l).reframe_step φ hm l (s l) (t l)
      have b := BRoute.on_role (φ:=φ)
        (fun r => frame (A r) (if r ∈ J then t r else s r)) l (frame (A l) (t l)) step
      have hupd : Function.update (fun r => frame (A r) (if r ∈ J then t r else s r)) l
          (frame (A l) (t l)) =
          fun r => frame (A r) (if r ∈ insert l J then t r else s r) := by
        funext r
        by_cases hr : r = l
        · subst hr; simp
        · simp [Function.update_of_ne hr, Finset.mem_insert, hr]
      rw [hupd] at b
      have tr := ih.trans b
      rw [Finset.sum_insert hl, add_comm]
      exact tr
  have H := hh Finset.univ
  have e1 : (fun r => if r ∈ (Finset.univ : Finset ρ) then t r else s r) = t := by
    funext r; simp
  rw [e1] at H
  exact H

/-- Growing frames (block analogue of upstream `Path.inc`): one up-block per role. -/
theorem inc (hm : 2 ≤ Fintype.card α) (A : ρ → OBase α) {s t : ρ → Finset α}
    (h : ∀ r, s r ⊆ t r) :
    BPath φ A s t id (∑ r, splitCost φ (Fintype.card α) (t r \ s r).card) := by
  have H := reframe (φ:=φ) hm A s t
  have e : (∑ r, (splitCost φ (Fintype.card α) (s r \ t r).card +
      splitCost φ (Fintype.card α) (t r \ s r).card)) =
      ∑ r, splitCost φ (Fintype.card α) (t r \ s r).card := by
    apply Finset.sum_congr rfl
    intro r _
    have h0 : s r \ t r = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr (h r)
    rw [h0]
    simp [splitCost]
  rw [e] at H
  exact H

end BPath
end

universe U

/-- **The block engine fed with a block route.**  A route with weights
`φ r = (r/u)^z` and cost `c < 2^a`, from invertible matrices `S` to `kernel * S` on the live
roles, gives the engine conclusion with exponent `z`. -/
theorem engine_program_broute {α ρ σ : Type} [Fintype α] [DecidableEq α] [Fintype ρ]
    [DecidableEq ρ] [Fintype σ] [DecidableEq σ]
    (u a : ℕ) (hα : Fintype.card α = u) (hσ : Fintype.card σ = 2^a) (hu : 3 ≤ u)
    (e : σ → ρ) (he : Function.Injective e)
    (z : ℝ) (hz : 0 ≤ z)
    (S S' T : ρ → CMat α) (hS : ∀ r, S r * S' r = 1)
    (g : (ρ→ℂ) → (ρ→ℂ)) (c : ℝ)
    (h : BRoute (fun r => ((r:ℝ)/(u:ℝ))^z) S T g c) (hc : c < (2:ℝ)^a)
    (hg : ∀ x : ρ → ℂ, (∀ s, (∀ l, e l ≠ s) → x s = 0) → ∀ l, g x (e l) = x (e l))
    (hT : ∀ l, T (e l) = kernel α * S (e l))
    (cl : Paint) (m : Bool) {ι : Type U} (k : ι→ℕ) (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*envelope z (k i)) := by
  obtain ⟨w, hP, hcost, hw⟩ := BRoute.liveKernel e S S' T hS g c h hg hT
  rw [hα] at hP
  exact engine_program_block_costR u a hα hσ hu e he w hw hP z hz (lt_of_le_of_lt hcost hc)
    cl m k v

end
end PowerSaving.RAM
end OAI

#print axioms OAI.PowerSaving.RAM.BRoute.parallel
#print axioms OAI.PowerSaving.RAM.BRoute.liveKernel
#print axioms OAI.PowerSaving.RAM.BPath.reframe
#print axioms OAI.PowerSaving.RAM.engine_program_broute
