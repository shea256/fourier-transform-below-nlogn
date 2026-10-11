import OAI.Computability.FourierTransform.TensorRecursion

namespace OAI
namespace PowerSaving.RAM
open Ty Binary Matrix Finset
noncomputable section
universe U

variable {ι : Type U} {m : Bool}

namespace Able
variable {r : Port} {b : Bank r ι} {s t : Ty} {x : ι → T s} {y : ι → T t}
  {W Z n : ι → ℕ}

/-- With a closed-code test. -/
lemma branch (h : Can m b.B s w x n W) (P : ι → Prop) (hp : ∀ i, n i=0 ↔ P i)
    (g : Able m (b.comap (fun i : {i // P i} => i.1)) s t
      (fun i => x i.1) (fun i => y i.1) (fun i => W i.1) (fun i => Z i.1))
    (k : Able m (b.comap (fun i : {i // ¬P i} => i.1)) s t
      (fun i => x i.1) (fun i => y i.1) (fun i => W i.1) (fun i => Z i.1)) :
    Able m b s t x y W Z := by
  let f (i : {i // n i=0}) : {i // P i} := ⟨i.1,(hp i.1).1 i.2⟩
  let j (i : {i // n i≠0}) : {i // ¬P i} :=
    ⟨i.1,(fun h => i.property ((hp i.1).2 h))⟩
  have H := Able.ifz (b:=b) (x:=x) (y:=y) (W:=W) (Z:=Z) (of_can h)
    (show Able m (b.comap (fun i : {i // n i=0} => i.1)) s t
      (fun i => x i.1) (fun i => y i.1) (fun i => W i.1) (fun i => Z i.1)
      from g.reindex f)
    (show Able m (b.comap (fun i : {i // n i≠0} => i.1)) s t
      (fun i => x i.1) (fun i => y i.1) (fun i => W i.1) (fun i => Z i.1)
      from k.reindex j)
  exact H.weaken ((Dom.self W).add (Dom.self W)) (fun i => by simp)

private def defaultProg (m : Bool) (s : Ty) : (t : Ty) → Prog m s t
  | .w => .atom (.lit 0)
  | .c f => .atom (.cz f)
  | .p v u => .fork (defaultProg m s v) (defaultProg m s u)
  | .a v => .tab (.atom (.lit 0)) (.comp (.atom .fst) (defaultProg m s v))

/-- Dispatch according to a bounded integer. -/
lemma dispatch (d : ℕ) (h : Can m b.B s w x n W)
    (hd : ∀ i, n i<d)
    (g : ∀ k<d, Able m (b.comap (fun i : {i // n i=k} => i.1)) s t
      (fun i => x i.1) (fun i => y i.1) (fun i => W i.1) (fun i => Z i.1)) :
    Able m b s t x y W Z := by
  have H (e : ℕ) (he : e≤d) :
      Able m (b.comap (fun i : {i // n i<e} => i.1)) s t
        (fun i => x i.1) (fun i => y i.1) (fun i => W i.1) (fun i => Z i.1) := by
    induction e with
    | zero =>
      refine ⟨.importClosed (defaultProg _ _ _),0,0,?_⟩
      rintro ⟨i,hi⟩
      exact (Nat.not_lt_zero _ hi).elim
    | succ e ih =>
      let G := {i // n i<e+1}
      let P (i : G) : Prop := n i.1=e
      refine Able.branch (n:=fun i : G => if n i.1=e then 0 else 1)
        ((h.reindex (fun i : G => i.1)).eqbit (Can.wc e)) P
        (by intro i; unfold P; split <;> simp_all) ?_ ?_
      · let f (i : {i:G // P i}) : {i // n i=e} := ⟨i.1.1,i.2⟩
        exact (g e (by omega)).reindex f
      · let f (i : {i:G // ¬P i}) : {i // n i<e} :=
          ⟨i.1.1,by have h : n i.1.1≠e := i.2; have := i.1.2; omega⟩
        exact (ih (by omega)).reindex f
  exact (H d le_rfl).reindex (fun i => ⟨i,hd i⟩)

end Able

section Base
variable {ρ : Type*} [Fintype ρ] [DecidableEq ρ]
variable {B W : ι → ℕ}

-- Handles small tensor orders. all logical coordinates are fixed-size in this lemma.
lemma fixed_order (m : Bool) (B W : ι → ℕ) (cl : Paint) (k : ℕ) (R : Layout ρ)
    (v : ι→ Sim ρ k→ℂ) :
    Can m B (simIn cl) (bundle cl) (fun i => loaded cl R k (v i))
      (fun i => (sim R k).tape (whole k (v i))) W := by
  let L := sim R k
  let S (i : ι) := Sim ρ k
  let E1 i := loaded cl R k (v i)
  let E (d : Σ i, S i) : T (p (simIn cl) w) := (E1 d.1,L.loc d.2)
  let B1 (d : Σ i,S i) := B d.1
  let G (i) := whole k (v i)
  have h : Has m B1 (p (simIn cl) w) (c cl) E (fun d => G d.1 d.2) := by
    refine Can.cases_code (q:=Sigma.snd (β:=S)) L Can.second ?_
    intro l
    let K := {d : Σ i,S i // d.2=l}
    let B2 (d : K) := B d.1.1
    let E2 (d : K) := E d.1
    have Ha : Has m B2 (p (simIn cl) w) sc E2 (fun _ => Complex.I) :=
      Can.fst (Can.snd Can.first)
    have Hi (i j : F) :
        Has m B2 (p (simIn cl) w) sc E2 (fun _ => littleC i j) := by
      have h2 : Has m B2 (p (simIn cl) w) sc E2 (fun _ => (2:ℂ)) := by
        simpa using Can.cNat (m:=m) (s:=p (simIn cl) w) (B:=B2) (W:=fun _ => 0) (x:=E2) 2
      have hh := h2.inv (by simp)
      unfold littleC ca cb
      split
      · simp only [div_eq_mul_inv]; exact (Can.one.add Ha).mul hh
      · simp only [div_eq_mul_inv]; exact (Can.one.sub Ha).mul hh
    have hh (z : Bits k) :
        Has m B2 (p (simIn cl) w) (c cl) E2 (fun d => kernel (Fin k) l.2 z * v d.1.1 (l.1,z)) := by
      have hk := Can.fetch (α:=fun (_:K) => Sim ρ k) (i:=fun _ => (l.1,z))
        (t:=c cl) (m:=m) (x:=E2) (W:=fun _ => 0) (v:=fun d => v d.1.1)
        (B:=B2) (L:=fun _ => L) (s:=p (simIn cl) w)
        (Can.snd (Can.snd Can.first)) (Can.wc _)
      exact (Can.prod_cconst (v:=fun i _ => littleC (l.2 i) (z i))
        (fun i => Hi _ _)).mul hk
    refine (Can.sum_cconst hh).cong (fun _ => rfl) (fun i => ?_)
    exact congr_arg (G i.1.1) i.2.symm
  have H := Can.layout (L:=fun (_:ι) => L) (v:=G) (x:=E1) (P:=fun _ => 0)
    (W:=fun _ => 0) (α:=S) (t:=c cl) (m:=m) (B:=B) (s:=simIn cl)
    (Can.wc L.n) h (Small.const ..)
  exact H.weaken (Dom.const W (0+L.n+L.n*0))

lemma almost_fixed (m : Bool) (B W : ι → ℕ) (cl : Paint)
    (k : ι → ℕ) (K : ℕ) (hk : ∀ i,k i=K)
    (R : Layout ρ) (v : ∀ i, Sim ρ (k i)→ℂ) :
    Can m B (simIn cl) (bundle cl) (fun i => loaded cl R (k i) (v i))
      (fun i => (sim R (k i)).tape (whole (k i) (v i))) W := by
  have hg := funext hk
  subst k
  exact fixed_order m B W cl K R v

end Base
end
end PowerSaving.RAM

end OAI
