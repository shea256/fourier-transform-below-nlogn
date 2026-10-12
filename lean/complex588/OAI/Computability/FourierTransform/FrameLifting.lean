import OAI.Computability.FourierTransform.DirectionalWords

namespace OAI
namespace PowerSaving.Binary
open Matrix Finset
noncomputable section
variable {α ρ σ : Type*} [Fintype α] [DecidableEq α]
  [Fintype ρ] [DecidableEq ρ] [Fintype σ] [DecidableEq σ]

/-- Portion of sigma occupied by the smaller network. -/
def covered (e : ρ ↪ σ) := univ.map e

omit [DecidableEq ρ] [Fintype σ] [DecidableEq σ] in
theorem cover_iff (e : ρ ↪ σ) (i : σ) : i ∈ covered e ↔ ∃ j, e j=i := by simp [covered]

private def src (e : ρ ↪ σ) {i : σ} (h : i∈covered e) : ρ :=
  Classical.choose ((cover_iff ..).mp h)

omit [DecidableEq ρ] [Fintype σ] [DecidableEq σ] in
private theorem src_spec (e : ρ ↪ σ) {i : σ} (h : i∈covered e) :
    e (src e h) = i := Classical.choose_spec ((cover_iff e i).mp h)

omit [DecidableEq ρ] [Fintype σ] [DecidableEq σ] in
private theorem src_self (e : ρ ↪ σ) (i : ρ) (h : e i ∈ covered e) :
    src e h = i := e.injective (src_spec e h)

def wide (e : ρ ↪ σ) (M : Matrix ρ ρ ℚ) : Matrix σ σ ℚ :=
  fun i j => if h : i∈covered e then if h' : j∈covered e then M (src e h) (src e h') else 0
    else if i=j then 1 else 0

omit [DecidableEq ρ] [Fintype σ] in
theorem wide_both (e : ρ ↪ σ) (M : Matrix ρ ρ ℚ) (i j : ρ) :
    wide e M (e i) (e j)=M i j := by simp [wide,src_self,covered]

omit [DecidableEq ρ] in
theorem wide_in (e : ρ ↪ σ) (M : Matrix ρ ρ ℚ) (i : ρ) (x : σ→ℂ) :
    actPoint (wide e M) x (e i) = actPoint M (x ∘ e) i := by
  unfold actPoint
  rw [← Finset.sum_add_sum_compl (covered e)]
  have hz : ∑ j ∈ (covered e)ᶜ, (wide e M (e i) j : ℂ) * x j = 0 := by
    apply sum_eq_zero
    intro j hj
    replace hj := mem_compl.mp hj
    have h : e i ∈ covered e := by simp [covered]
    simp [wide,h,hj]
  rw [hz, add_zero, covered, sum_map]
  simp [wide_both]

omit [DecidableEq ρ] in
theorem wide_out (e : ρ ↪ σ) (M : Matrix ρ ρ ℚ) (x : σ→ℂ) {i : σ} (h : i ∉ covered e) :
    actPoint (wide e M) x i = x i := by
  unfold actPoint
  rw [Finset.sum_eq_single i]
  · simp [wide,h]
  · intro j _ g; simp [wide,h, Ne.symm g]
  · simp

def Move.over (e : ρ ↪ σ) : Move α ρ → Move α σ
  | .localM M => .localM (wide e M)
  | .dir r z nz => .dir (e r) z nz
  | .shift r z => .shift (e r) z

theorem go_over (e : ρ ↪ σ) (m : Move α ρ) (f : ℕ) (x : Data α σ f) :
    (m.over e |>.go f x) ∘ e = m.go f (x ∘ e) := by
  funext i
  cases m with
  | localM M =>
    funext j; exact wide_in e M i _
  | dir => simp [Move.over,Move.go, Function.comp, roleAct]
  | shift => simp [Move.over,Move.go, Function.comp, roleAct]

omit [DecidableEq ρ] in
theorem go_out (e : ρ ↪ σ) (m : Move α ρ) (f : ℕ)
    (x : Data α σ f) {i : σ} (h : i ∉ covered e) :
    ((m.over e).go f x) i = x i := by
  have hh (j : ρ) : i ≠ e j := fun g => h ((cover_iff ..).2 ⟨j,g.symm⟩)
  cases m with
  | localM M => funext j; exact wide_out e M _ h
  | dir => simp [Move.over,Move.go,roleAct, hh]
  | shift => simp [Move.over,Move.go,roleAct, hh]

theorem walk_over (e : ρ ↪ σ) (p : PWord α ρ) (f : ℕ) (x : Data α σ f) :
    walk f (p.map (Move.over e)) x ∘ e = walk f p (x ∘ e) := by
  induction p generalizing x with
  | nil => rfl
  | cons m p ih =>
    change walk _ _ _ ∘ e = walk f p (m.go f (x∘e))
    rw [← go_over]
    exact ih _

omit [DecidableEq ρ] in
theorem walk_out (e : ρ ↪ σ) (p : PWord α ρ) (f : ℕ) (x : Data α σ f)
    {i : σ} (h : i ∉ covered e) :
    walk f (p.map (Move.over e)) x i = x i := by
  induction p generalizing x with
  | nil => rfl
  | cons m p ih =>
    exact (ih _).trans (go_out e m f _ h)

namespace Path

theorem lift (e : ρ ↪ σ) (A : σ → OBase α) {s t : σ → Finset α}
    {g : (σ→ℂ) → (σ→ℂ)} {h : (ρ→ℂ) → (ρ→ℂ)} {d : ℕ}
    (q : Path (A ∘ e) (s ∘ e) (t ∘ e) h d)
    (hin : ∀ x, (g x) ∘ e = h (x ∘ e)) (hout : ∀ x i, i∉covered e → g x i=x i)
    (he : ∀ i, i∉covered e → s i = t i) :
    Path A s t g d := by
  obtain ⟨p,hp,ha⟩ := q
  refine ⟨p.map (Move.over e),?_,?_⟩
  · have hm (s : σ → Finset α) :
        mass s = mass (s ∘ e) + ∑ i ∈ (covered e)ᶜ, (s i).card := by
      unfold mass
      nth_rw 1 [← Finset.sum_add_sum_compl (covered e)]
      rw [covered, sum_map]
      rfl
    have hh : ∑ i ∈ (covered e)ᶜ, (s i).card = ∑ i ∈ (covered e)ᶜ, (t i).card := by
      apply sum_congr rfl; intro i hi; rw [he i (mem_compl.mp hi)]
    rw [hm,hm,hh]
    have ht : toll ∘ (Move.over (α:=α) e) = toll := funext (fun i => by cases i <;> rfl)
    have hz : tally (p.map (Move.over e)) = tally p := by simp [tally,ht]
    rw [hz]; omega
  · intro f x
    have frame_cont (s : σ → Finset α) (x : Data α σ f) :
        withFrame A s f x ∘ e = withFrame (A∘e) (s∘e) f (x∘e) := rfl
    have point_cont :
        point f g x ∘ e = point f h (x ∘ e) := by
      funext i j
      exact congr_fun (hin _) i
    funext i
    by_cases hm : i∈covered e
    · obtain ⟨j,rfl⟩ := (cover_iff ..).mp hm
      exact congr_fun (show walk f _ _ ∘ e = withFrame A t f _ ∘ e by
        rw [walk_over,frame_cont, ha,frame_cont,point_cont]) j
    · rw [walk_out e p _ _ hm]
      unfold withFrame multiAct
      simp only [he i hm]
      apply congrArg
      funext j
      exact (hout (fun r => x r j) i hm).symm

section Parallel

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Compose paths on disjoint sets of roles. -/
theorem parallel (e : J → ρ ↪ σ)
    (dis : ∀ i j, i ≠ j → ∀ r ∈ covered (e i), r ∉ covered (e j))
    (A : σ → OBase α) {s t : σ → Finset α} {d : J → ℕ}
    {g : (σ→ℂ)→(σ→ℂ)} {h : J → (ρ→ℂ) → (ρ→ℂ)}
    (q : ∀ i, Path (A ∘ e i) (s ∘ e i) (t ∘ e i) (h i) (d i))
    (hin : ∀ i x, (g x) ∘ e i = h i (x ∘ e i))
    (hout : ∀ x r, (∀ i, r∉covered (e i)) → g x r=x r)
    (he : ∀ r, (∀ i, r∉covered (e i)) → s r=t r) :
    Path A s t g (∑ i, d i) := by
  let u (j : Finset J) := j.biUnion fun i => covered (e i)
  let l (j : Finset J) (r : σ) := if r∈u j then t r else s r
  let k (j : Finset J) (x : σ→ℂ) (r : σ) := if r∈u j then g x r else x r
  have hh (j : Finset J) : Path A s (l j) (k j) (∑ i ∈ j, d i) := by
    induction j using Finset.induction with
    | empty =>
      simp only [k,l,u,biUnion_empty,notMem_empty,ite_false,sum_empty]
      exact Path.refl
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
      have gg : Path A (l j) (l (insert i j)) fn (d i) := by
        apply Path.lift (e i) A (h:=h i) _ compi
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
end Path
end
end PowerSaving.Binary

end OAI
