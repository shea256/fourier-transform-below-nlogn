import OAI.Computability.FourierTransform.Layout
import OAI.Computability.FourierTransform.ProgramConstruction

namespace OAI

/-! Programming over a logical layout. Case splits over *fixed* finite sets are fine.
No computation of Layout etc occurs in code; all needed address calculations use RAM
combinators. -/
namespace PowerSaving.RAM
open Ty Finset
noncomputable section

universe U V
variable {ι : Type U} {α : ι → Type V}

private lemma as_tab {μ η : Type*} (L : Layout μ) (x : μ → η) (z : η) :
    Tape.tab L.n (fun j => if h : j < L.n then x (L.atFin ⟨j,h⟩) else z)
    = L.tape x := by
  unfold Tape.tab Layout.tape; congr 1
  funext i; simp [i.isLt]

namespace Able
variable {m : Bool} {r : Port} {b : Bank r ι} {s t : Ty}
  {x : ι → T s} {W Z P H : ι → ℕ}

theorem layout {L : ∀ i, Layout (α i)} {v : ∀ i, α i → T t}
    (h : Able m b s w x (fun i => (L i).n) W Z)
    (hs : Able m (b.comap (Sigma.fst (β:=α))) (p s w) t
      (fun d => (x d.1,(L d.1).loc d.2)) (fun d => v d.1 d.2)
      (fun d => P d.1) (fun d => H d.1))
    (hc : Small b.B fun i => (L i).n) :
    Able m b s (a t) x (fun i => (L i).tape (v i))
      (fun i => W i+(L i).n+(L i).n*P i) (fun i => Z i+(L i).n*H i) := by
  let n i := (L i).n
  let vals (i : ι) (j : ℕ) : T t :=
    if hg : j < n i then v i ((L i).atFin ⟨j,hg⟩) else t.blank
  let k (q : During n) : Σ i, α i :=
    ⟨q.i, (L q.i).atFin ⟨q.j,q.hj⟩⟩
  have hx := hs.reindex k
  have hh : Able m (b.comap (During.i (n:=n))) (p s w) t
      (fun d => (x d.i,d.j)) (fun d => vals d.i d.j)
      (fun d => P d.i) (fun d => H d.i) := by
    refine hx.cong ?_ ?_
    · rintro ⟨i,j,hj⟩; simp [k]
    · rintro ⟨i,j,hj⟩; simp [vals,k,hj]
  have ht := Able.tab (n:=n) (v:=vals) (Wb:=fun i _ => P i) (Zb:=fun i _ => H i) h hh hc
  have he (i) : Tape.tab (n i) (vals i) = (L i).tape (v i) :=
    as_tab _ _ _
  simpa only [he,sum_const,card_range,nsmul_eq_mul,Nat.cast_id] using ht

end Able

namespace Small

lemma loc {B : ι → ℕ} {x : ∀ i, α i} {L : ∀ i, Layout (α i)}
    (h : Small B fun i => (L i).n) :
    Small B fun i => (L i).loc (x i) :=
  h.mono fun i => ((L i).bd _).le

end Small

namespace Can
variable {m : Bool} {s t : Ty} {x : ι → T s}
  {B W P : ι → ℕ} {L : ∀ i, Layout (α i)} {v : ∀ i, α i → T t}

theorem layout (h : Can m B s w x (fun i => (L i).n) W)
    (g : Can m (fun d : Σ i, α i => B d.1) (p s w) t
      (fun d => (x d.1,(L d.1).loc d.2)) (fun d => v d.1 d.2) (fun d => P d.1))
    (hn : Small B fun i => (L i).n) :
    Can m B s (a t) x (fun i => (L i).tape (v i))
      (fun i => W i+(L i).n+(L i).n*P i) := by
  have ht := Able.layout (b:=Bank.closed B) (L:=L) (v:=v)
    (P:=P) (H:=fun _ => 0) h g hn
  simpa [Can] using ht

theorem fetch {i : ∀ d, α d}
    (h : Can m B s (a t) x (fun i => (L i).tape (v i)) W)
    (g : Can m B s w x (fun d => (L d).loc (i d)) W) :
    Can m B s t x (fun d => v d (i d)) W :=
  (h.look g).cong (fun _ => rfl) (fun _ => Layout.read ..)

variable {μ : Type V}

/-- Equality test via comparison operations. -/
theorem eqbit {n q : ι → ℕ} (h : Can m B s w x n W) (k : Can m B s w x q W) :
    Can m B s w x (fun i => if n i = q i then 0 else 1) W := by
  let f i := if n i < q i then 1 else 0
  let g i := if q i < n i then 1 else 0
  have a : Small B f := by
    apply (Small.const B 1).mono; intro; unfold f; split <;> omega
  have b : Small B g := by
    apply (Small.const B 1).mono; intro; unfold g; split <;> omega
  refine ((h.wlt k).wadd (k.wlt h) (a.add b)).cong (fun _ => rfl) ?_
  intro i
  rcases lt_trichotomy (n i) (q i) with h|h|h
  · simp [h, not_lt.mpr h.le, ne_of_lt h]
  · simp [h]
  · simp [h, not_lt.mpr h.le, ne_of_gt h]

private def blankProg (m : Bool) (s : Ty) : (t : Ty) → Prog m s t
  | .w => .atom (.lit 0)
  | .c e => .atom (.cz e)
  | .p q u => .fork (blankProg m s q) (blankProg m s u)
  | .a q => .tab (.atom (.lit 0)) (.comp (.atom .fst) (blankProg m s q))

/-- split according to a fixed finite value on which code is allowed to depend. -/
theorem cases_code [DecidableEq μ] [Fintype μ] {y : ι → T t} {q : ι→μ}
    (D : Layout μ) (h : Can m B s w x (fun i => D.loc (q i)) W)
    (g : ∀ f : μ, Can m (fun i : {i // q i=f} => B i.1) s t
      (fun i => x i.1) (fun i => y i.1) (fun i => W i.1)) :
    Can m B s t x y W := by
  have hg (l : Finset μ) : Can m (fun i : {i // q i∈l} => B i.1) s t
      (fun i => x i.1) (fun i => y i.1) (fun i => W i.1) := by
    induction l using Finset.induction with
    | empty =>
      refine ⟨blankProg m s t,0,0,?_⟩
      rintro ⟨i,hi⟩; simp at hi
    | insert i l hi ih =>
      let K := {j // q j∈insert i l}
      let n (a : K) := if D.loc (q a.1)=D.loc i then 0 else 1
      apply Can.testz (n:=n) ((h.reindex (fun j : K => j.1)).eqbit (Can.wc _))
      · let p (f : {j : K // n j=0}) : {j // q j=i} := ⟨f.1.1, by
          have hh := f.2
          apply D.inj
          unfold n at hh
          split at hh
          next h => exact h
          next h => simp at hh⟩
        exact (g i).reindex p
      · let p (f : {j : K // n j ≠ 0}) : {j // q j∈l} :=
          ⟨f.1.1,by
            have hh := f.2
            have hg := f.1.2
            rw [mem_insert] at hg
            rcases hg with g|g
            · simp [n,g] at hh
            · exact g⟩
        exact ih.reindex p
  exact (hg univ).reindex (fun i => ⟨i, mem_univ _⟩)

/-- An arbitrary RAM word sum over a fixed finite set. -/
theorem sum_wconst [Fintype μ] {v : μ → ι → ℕ}
    (h : ∀ i : μ, Can m B s w x (v i) W)
    (g : ∀ i : μ, Small B (v i)) :
    Can m B s w x (fun j => ∑ i, v i j) W := by
  classical
  have hh (l : Finset μ) :
      Can m B s w x (fun j => ∑ i ∈ l, v i j) W ∧ Small B (fun j => ∑ i ∈ l, v i j) := by
    induction l using Finset.induction with
    | empty =>
      simpa using And.intro (Can.wc (B:=B) (m:=m) (x:=x) (W:=W) 0)
        (Small.const B 0)
    | insert i l hi ih =>
      have ht := (g i).add ih.2
      simpa [hi] using And.intro ((h i).wadd ih.1 ht) ht
  exact (hh _).1

theorem sum_cconst [Fintype μ] {cl} {v : μ → ι → ℂ}
    (h : ∀ i : μ, Can m B s (c cl) x (v i) W) :
    Can m B s (c cl) x (fun j => ∑ i, v i j) W := by
  classical
  have hh (l : Finset μ) :
      Can m B s (c cl) x (fun j => ∑ i ∈ l, v i j) W := by
    induction l using Finset.induction with
    | empty => simpa using (Can.zero (cl:=cl) (m:=m) (B:=B) (x:=x) (W:=W))
    | insert i l hi ih =>
      simpa [hi] using (h i).add ih
  exact hh _

end Can
end
end PowerSaving.RAM

end OAI
