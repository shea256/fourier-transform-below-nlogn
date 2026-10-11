import Work.Scratch.Engine

/-!
# (key: shared-sum-structured) Paths on arbitrary frame matrices

Upstream's `Path` (DirectionalWords.lean) fixes ONE orthonormal basis per role and describes the
frame of the role by a set of basis indices.  A shared-sum helper circuit needs labels whose
natural bases change along the life of a role.  Here a role carries an arbitrary matrix (its
frame) and a NOMINAL dimension; a legal climb is `Reach`: a product of unit `delta` factors.
The nominal dimensions only serve the bookkeeping identity
`tally + mass(start) = mass(end) + 2 * losses` (as upstream's `Path`).

* `Reach A B n`       : `B = delta z_n * ... * delta z_1 * A` with unit `z_i`;
* `Reach.of_subset`   : inside one orthonormal basis, a bigger index set is reached with one
                        directional move per new index;
* `GPath s t g L`     : a word from frames `s` to frames `t` with scalar map `g`, `L` losses;
* `GPath.gate`, `GPath.move_all`, `GPath.climb_all`, `GPath.lift`, `GPath.parallel`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OAI
namespace PowerSaving
namespace SS
open Binary Matrix Finset RAM
noncomputable section

section
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- `B` is `A` after `n` directional steps along unit vectors. -/
def Reach (A B : CMat α) (n : ℕ) : Prop :=
  ∃ zs : List (Space α), zs.length = n ∧ (∀ z ∈ zs, dot z z = 1) ∧
    B = (zs.map delta).prod * A

namespace Reach

lemma refl (A : CMat α) : Reach A A 0 := ⟨[], rfl, by simp, by simp⟩

lemma trans {A B C : CMat α} {n k : ℕ} (h : Reach A B n) (g : Reach B C k) :
    Reach A C (n+k) := by
  obtain ⟨zs, hl, hu, rfl⟩ := h
  obtain ⟨ws, hl', hu', rfl⟩ := g
  refine ⟨ws ++ zs, by simp [hl, hl', add_comm], ?_, ?_⟩
  · intro z hz
    rcases List.mem_append.mp hz with h|h
    · exact hu' z h
    · exact hu z h
  · simp [List.map_append, List.prod_append, Matrix.mul_assoc]

lemma mul_right {A B : CMat α} {n : ℕ} (h : Reach A B n) (K : CMat α) :
    Reach (A*K) (B*K) n := by
  obtain ⟨zs, hl, hu, rfl⟩ := h
  exact ⟨zs, hl, hu, by rw [Matrix.mul_assoc]⟩

lemma one_step (A : CMat α) (z : Space α) (hz : dot z z = 1) : Reach A (delta z * A) 1 :=
  ⟨[z], rfl, by simp [hz], by simp⟩

lemma cast {A B : CMat α} {n k : ℕ} (h : Reach A B n) (e : n = k) : Reach A B k := e ▸ h

/-- Inside one orthonormal basis: one step per new index. -/
lemma of_subset (A : OBase α) {s t : Finset α} (h : s ⊆ t) :
    Reach (frame A s) (frame A t) (t \ s).card := by
  have key : ∀ u : Finset α, Disjoint u s → Reach (frame A s) (frame A (s ∪ u)) u.card := by
    intro u
    induction u using Finset.induction with
    | empty => intro _; simpa using Reach.refl (frame A s)
    | insert i u hi ih =>
      intro hd
      have hd' : Disjoint u s := disjoint_of_subset_left (subset_insert i u) hd
      have his : i ∉ s := fun h => (disjoint_left.mp hd) (mem_insert_self i u) h
      have hnot : i ∉ s ∪ u := by simp [his, hi]
      have e : s ∪ insert i u = insert i (s ∪ u) := by
        ext x; simp only [mem_union, mem_insert]; tauto
      rw [e, frame_ins A _ i hnot, card_insert_of_notMem hi]
      exact (ih hd').trans (one_step _ _ (A.self i))
  have h2 := key (t \ s) sdiff_disjoint
  rwa [union_sdiff_of_subset h] at h2

end Reach

/-- frames of disjoint index sets multiply. -/
lemma frame_union (A : OBase α) (s t : Finset α) (h : Disjoint s t) :
    frame A (s ∪ t) = frame A s * frame A t := by
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
    have hd : Disjoint s t := disjoint_of_subset_left (subset_insert i s) h
    have hit : i ∉ t := fun g => (disjoint_left.mp h) (mem_insert_self i s) g
    have hnot : i ∉ s ∪ t := by simp [hi, hit]
    rw [insert_union, frame_ins A _ i hnot, ih hd, frame_ins A _ i hi, Matrix.mul_assoc]

variable {ρ σ : Type*} [Fintype ρ] [DecidableEq ρ]

lemma roleAct_one (f : ℕ) (r : ρ) (x : Data α ρ f) : roleAct f r (1 : CMat α) x = x := by
  funext j
  by_cases h : j = r <;> simp [roleAct, h]

/-- a word for a product of unit `delta`s on one role. -/
lemma units_word (r : ρ) (zs : List (Space α)) (hu : ∀ z ∈ zs, dot z z = 1) :
    ∃ q : PWord α ρ, tally q = zs.length ∧
      ∀ f (x : Data α ρ f), walk f q x = roleAct f r ((zs.map delta).prod) x := by
  induction zs with
  | nil =>
    refine ⟨[], rfl, fun f x => ?_⟩
    simp only [List.map_nil, List.prod_nil, roleAct_one]
    rfl
  | cons z zs ih =>
    obtain ⟨q, hq, hw⟩ := ih (fun w hw => hu w (List.mem_cons_of_mem _ hw))
    obtain ⟨u, hu1, hu2⟩ := up_word (ρ:=ρ) r z (hu z List.mem_cons_self)
    refine ⟨q ++ u, by rw [tally_append, hq, hu1]; simp, fun f x => ?_⟩
    rw [walk_append, hw, hu2, roleAct_mul]
    simp only [List.map_cons, List.prod_cons]

/-- a word for the inverse of a product of unit `delta`s on one role. -/
lemma units_word_inv (r : ρ) (zs : List (Space α)) (hu : ∀ z ∈ zs, dot z z = 1) :
    ∃ (N : CMat α) (q : PWord α ρ), N * (zs.map delta).prod = 1 ∧ tally q = zs.length ∧
      ∀ f (x : Data α ρ f), walk f q x = roleAct f r N x := by
  induction zs with
  | nil =>
    refine ⟨1, [], by simp, rfl, fun f x => ?_⟩
    rw [roleAct_one]; rfl
  | cons z zs ih =>
    obtain ⟨N, q, hN, hq, hw⟩ := ih (fun w hw => hu w (List.mem_cons_of_mem _ hw))
    have hz := hu z List.mem_cons_self
    obtain ⟨u, hu1, hu2⟩ := down_word (ρ:=ρ) r z hz
    refine ⟨N * (shift z * delta z), u ++ q, ?_, ?_, ?_⟩
    · simp only [List.map_cons, List.prod_cons]
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (shift z * delta z), Matrix.mul_assoc (shift z),
        delta_sq z hz, shift_sq, Matrix.one_mul, hN]
    · rw [tally_append, hq, hu1]; simp [add_comm]
    · intro f x
      rw [walk_append, hu2, hw, roleAct_mul]

/-- frame matrix of a role together with its nominal dimension. -/
structure Fr (α : Type*) where
  M : CMat α
  d : ℕ

def fmass (s : ρ → Fr α) : ℕ := ∑ r, (s r).d

lemma fmass_update (s : ρ → Fr α) (r : ρ) (B : Fr α) :
    fmass (Function.update s r B) + (s r).d = fmass s + B.d := by
  unfold fmass
  rw [← Finset.add_sum_erase univ (fun x => (Function.update s r B x).d) (mem_univ r),
    ← Finset.add_sum_erase univ (fun x => (s x).d) (mem_univ r)]
  have h : ∑ x ∈ univ.erase r, (Function.update s r B x).d = ∑ x ∈ univ.erase r, (s x).d :=
    sum_congr rfl (fun x hx => by rw [Function.update_of_ne (ne_of_mem_erase hx)])
  simp only [Function.update_self]
  omega

/-- A word from frames `s` to frames `t` with scalar map `g`; `L` counts decreases. -/
def GPath (s t : ρ → Fr α) (g : (ρ→ℂ) → (ρ→ℂ)) (L : ℕ) : Prop :=
  ∃ p : PWord α ρ, tally p + fmass s = fmass t + 2*L ∧
    ∀ (f : ℕ) (x : Data α ρ f),
      walk f p (multiAct f (fun r => (s r).M) x) = multiAct f (fun r => (t r).M) (point f g x)

namespace GPath
variable {s t u : ρ → Fr α}

theorem refl : GPath s s id 0 := ⟨[], by simp [tally], fun f x => rfl⟩

theorem trans {g h : (ρ→ℂ) → (ρ→ℂ)} {i j : ℕ} (a : GPath s t g i) (b : GPath t u h j) :
    GPath s u (h ∘ g) (i+j) := by
  obtain ⟨p,hp,ap⟩ := a
  obtain ⟨q,hq,aq⟩ := b
  refine ⟨p++q, by rw [tally_append]; omega, ?_⟩
  intro f x
  rw [walk_append, ap, aq]; rfl

theorem cast {g g' : (ρ→ℂ) → (ρ→ℂ)} {i j : ℕ} (a : GPath s t g i) (hg : g = g') (hi : i = j) :
    GPath s t g' j := by subst hg; subst hi; exact a

/-- A gate whose nonzero entries stay within a common frame matrix. -/
theorem gate (g : Matrix ρ ρ ℚ) (cond : ∀ i j, g i j ≠ 0 → (s i).M = (s j).M) :
    GPath s s (actPoint g) 0 := by
  obtain ⟨p, hp, hw⟩ := Route.gate (α:=α) g (fun r => (s r).M) (fun r => (s r).M) cond
  exact ⟨p, by rw [hp]; simp, hw⟩

/-- one role climbs. -/
theorem up (s : ρ → Fr α) (r : ρ) (B : Fr α) (n : ℕ) (h : Reach (s r).M B.M n)
    (hd : B.d = (s r).d + n) : GPath s (Function.update s r B) id 0 := by
  obtain ⟨zs, hl, hu, hB⟩ := h
  obtain ⟨q, hq, hw⟩ := units_word r zs hu
  refine ⟨q, ?_, ?_⟩
  · have := fmass_update s r B
    omega
  · intro f x
    rw [hw]
    have hpt : point f id x = x := rfl
    rw [hpt]
    funext j
    by_cases h : j = r
    · subst h
      simp only [roleAct, multiAct, if_true, Function.update_self, matAct_mul, hB]
    · simp only [roleAct, multiAct, h, if_false, Function.update_of_ne h]

/-- one role descends: `n` losses. -/
theorem down (s : ρ → Fr α) (r : ρ) (B : Fr α) (n : ℕ) (h : Reach B.M (s r).M n)
    (hd : (s r).d = B.d + n) : GPath s (Function.update s r B) id n := by
  obtain ⟨zs, hl, hu, hB⟩ := h
  obtain ⟨N, q, hN, hq, hw⟩ := units_word_inv r zs hu
  refine ⟨q, ?_, ?_⟩
  · have := fmass_update s r B
    omega
  · intro f x
    rw [hw]
    have hpt : point f id x = x := rfl
    rw [hpt]
    funext j
    by_cases h : j = r
    · subst h
      simp only [roleAct, multiAct, if_true, Function.update_self, matAct_mul, hB]
      rw [← Matrix.mul_assoc, hN, Matrix.one_mul]
    · simp only [roleAct, multiAct, h, if_false, Function.update_of_ne h]

/-- every role climbs or descends by a legal sequence of unit steps. -/
theorem move_all (s t : ρ → Fr α) (ℓ : ρ → ℕ)
    (h : ∀ r, (∃ n, Reach (s r).M (t r).M n ∧ (t r).d = (s r).d + n ∧ ℓ r = 0) ∨
              (∃ n, Reach (t r).M (s r).M n ∧ (s r).d = (t r).d + n ∧ ℓ r = n)) :
    GPath s t id (∑ r, ℓ r) := by
  have key : ∀ u : Finset ρ,
      GPath s (fun r => if r ∈ u then t r else s r) id (∑ r ∈ u, ℓ r) := by
    intro u
    induction u using Finset.induction with
    | empty =>
      have e : (fun r => if r ∈ (∅ : Finset ρ) then t r else s r) = s := by funext r; simp
      rw [e, sum_empty]; exact refl
    | insert i u hi ih =>
      let w : ρ → Fr α := fun r => if r ∈ u then t r else s r
      have hwi : w i = s i := by simp [w, hi]
      have e : Function.update w i (t i) = fun r => if r ∈ insert i u then t r else s r := by
        funext r
        by_cases hri : r = i
        · subst hri; simp
        · simp [w, hri, Function.update_of_ne hri]
      rw [sum_insert hi, add_comm]
      rcases h i with ⟨n, hr, hd, hl⟩ | ⟨n, hr, hd, hl⟩
      · have st := up w i (t i) n (by rw [hwi]; exact hr) (by rw [hwi]; exact hd)
        rw [e] at st
        rw [hl]
        exact (ih.trans st).cast (by rfl) (by omega)
      · have st := down w i (t i) n (by rw [hwi]; exact hr) (by rw [hwi]; exact hd)
        rw [e] at st
        rw [hl]
        exact (ih.trans st).cast (by rfl) rfl
  have H := key univ
  have e : (fun r => if r ∈ (univ : Finset ρ) then t r else s r) = t := by funext r; simp
  rwa [e] at H

/-- every role climbs (or stays). -/
theorem climb_all (s t : ρ → Fr α)
    (h : ∀ r, ∃ n, Reach (s r).M (t r).M n ∧ (t r).d = (s r).d + n) : GPath s t id 0 := by
  have H := move_all s t (fun _ => 0) (fun r => by
    obtain ⟨n, h1, h2⟩ := h r
    exact Or.inl ⟨n, h1, h2, rfl⟩)
  simpa using H

variable [Fintype σ] [DecidableEq σ]

/-- transport along an embedding of roles (upstream `Path.lift`). -/
theorem lift (e : ρ ↪ σ) {s t : σ → Fr α}
    {g : (σ→ℂ) → (σ→ℂ)} {h : (ρ→ℂ) → (ρ→ℂ)} {d : ℕ}
    (q : GPath (s ∘ e) (t ∘ e) h d)
    (hin : ∀ x, (g x) ∘ e = h (x ∘ e)) (hout : ∀ x i, i∉covered e → g x i=x i)
    (he : ∀ i, i∉covered e → s i = t i) :
    GPath s t g d := by
  obtain ⟨p,hp,ha⟩ := q
  refine ⟨p.map (Move.over e),?_,?_⟩
  · have hm (s : σ → Fr α) :
        fmass s = fmass (s ∘ e) + ∑ i ∈ (covered e)ᶜ, (s i).d := by
      unfold fmass
      nth_rw 1 [← Finset.sum_add_sum_compl (covered e)]
      rw [covered, sum_map]
      rfl
    have hh : ∑ i ∈ (covered e)ᶜ, (s i).d = ∑ i ∈ (covered e)ᶜ, (t i).d := by
      apply sum_congr rfl; intro i hi; rw [he i (mem_compl.mp hi)]
    rw [hm s, hm t, hh]
    have ht : toll ∘ (Move.over (α:=α) e) = toll := funext (fun i => by cases i <;> rfl)
    have hz : tally (p.map (Move.over e)) = tally p := by simp [tally,ht]
    rw [hz]; omega
  · intro f x
    have point_cont : point f g x ∘ e = point f h (x ∘ e) := by
      funext i j
      exact congr_fun (hin _) i
    funext i
    by_cases hm : i∈covered e
    · obtain ⟨j,rfl⟩ := (cover_iff ..).mp hm
      have h1 := congr_fun (walk_over e p f (multiAct f (fun r => (s r).M) x)) j
      have h2 : (multiAct f (fun r => (s r).M) x) ∘ e
          = multiAct f (fun r => ((s ∘ e) r).M) (x ∘ e) := rfl
      rw [h2, ha] at h1
      refine h1.trans ?_
      change matAct f (t (e j)).M (point f h (x ∘ e) j) = matAct f (t (e j)).M (point f g x (e j))
      rw [← point_cont]; rfl
    · rw [walk_out e p _ _ hm]
      unfold multiAct
      simp only [he i hm]
      apply congrArg
      funext j
      exact (hout (fun r => x r j) i hm).symm

section Parallel
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Compose paths on disjoint sets of roles (upstream `Path.parallel`). -/
theorem parallel (e : J → ρ ↪ σ)
    (dis : ∀ i j, i ≠ j → ∀ r ∈ covered (e i), r ∉ covered (e j))
    {s t : σ → Fr α} {d : J → ℕ}
    {g : (σ→ℂ)→(σ→ℂ)} {h : J → (ρ→ℂ) → (ρ→ℂ)}
    (q : ∀ i, GPath (s ∘ e i) (t ∘ e i) (h i) (d i))
    (hin : ∀ i x, (g x) ∘ e i = h i (x ∘ e i))
    (hout : ∀ x r, (∀ i, r∉covered (e i)) → g x r=x r)
    (he : ∀ r, (∀ i, r∉covered (e i)) → s r=t r) :
    GPath s t g (∑ i, d i) := by
  let u (j : Finset J) := j.biUnion fun i => covered (e i)
  let l (j : Finset J) (r : σ) := if r∈u j then t r else s r
  let k (j : Finset J) (x : σ→ℂ) (r : σ) := if r∈u j then g x r else x r
  have hh (j : Finset J) : GPath s (l j) (k j) (∑ i ∈ j, d i) := by
    induction j using Finset.induction with
    | empty =>
      simp only [k,l,u,biUnion_empty,notMem_empty,ite_false,sum_empty]
      exact GPath.refl
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
      have gg : GPath (l j) (l (insert i j)) fn (d i) := by
        apply GPath.lift (e i) (h:=h i) _ compi
        · intro x l hl; simp [fn,hl]
        · intro r hr; simp [l,hui,hr]
        · have eq1 : l j ∘ e i = s ∘ e i := by
            funext r
            have h : e i r ∈ covered (e i) := by simp [covered]
            simp [l, hiu _ h]
          have eq2 : l (insert i j) ∘ e i = t ∘ e i := by
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
  have eq1 : l univ = t := by
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

/-- every `GPath` is a `Route` of the scratch engine, with its tally given by the masses. -/
theorem route {g : (ρ→ℂ) → (ρ→ℂ)} {L : ℕ} (h : GPath s t g L) :
    ∃ c, c + fmass s = fmass t + 2*L ∧ Route (fun r => (s r).M) (fun r => (t r).M) g c := by
  obtain ⟨p,hp,hw⟩ := h
  exact ⟨tally p, hp, p, rfl, hw⟩

end GPath
end
end
end SS
end PowerSaving
end OAI
