import OAI.Computability.FourierTransform.TensorSaving

namespace OAI

/-! Kernel power algorithm in exact RAM model. -/
namespace PowerSaving.RAM
open Binary Matrix Ty Finset Cluster
noncomputable section
universe U

theorem hills_all (cl : Paint) (m : Bool) {ι : Type U} (k : ι→ℕ)
    (v : ∀ i, Sim Role (k i)→ℂ) :
    let R := Layout.someLayout Role
    Can m (fun i => 2^k i) (simIn cl) (bundle cl) (fun i => loaded cl R (k i) (v i))
      (fun i => (sim R (k i)).tape (whole (k i) (v i)))
      (fun i => 2^k i*hills (k i)) := by
  intro R
  let X := Layout.someLayout Blocks
  have hr : R.n=2^50 := R.card.symm.trans card_role
  have hx : X.n=mcol := X.card.symm.trans card_block
  obtain ⟨p,hp,hw⟩ := certificate
  have h := recurse_run cl m X R mcol 50 hx (by norm_num [mcol]) hr p hw k v
  rw [hp] at h
  obtain ⟨c,hc⟩ := total_hills
  exact h.weaken ⟨c,fun i => hc (k i)⟩

def givenBits (cl : Paint) (k : ℕ) (v : Bits k→ℂ) : T (simIn cl) :=
  (k,Complex.I,(bits k).tape v)

private theorem hills_project {ρ : Type*} (cl : Paint) (m : Bool) {ι : Type U}
    (k : ι → ℕ) (v : ∀ i, Bits (k i) → ℂ) (R : Layout ρ) (l : ρ)
    (h : Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => loaded cl R (k i) (fun j => v i j.2))
      (fun i => (sim R (k i)).tape (whole (k i) (fun j => v i j.2)))
      (fun i => 2^k i*hills (k i))) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*hills (k i)) := by
  let B i := 2^k i
  let W i := 2^k i*hills (k i)
  let x i := givenBits cl (k i) (v i)
  let L i := bits (k i)
  let M i := sim R (k i)
  let E (i) (j : Sim ρ (k i)) := v i j.2
  have hd : Dom W B := Dom.of_le (fun i => Nat.le_mul_of_pos_right _ (hills_pos _))
  have he : Dom W (fun i => (M i).n) := by
    refine hd.trans ?_
    refine ⟨R.n+1,fun i => ?_⟩
    change R.n*B i+1 ≤ _
    simp only [mul_add,add_mul,mul_one,one_mul]
    gcongr <;> simp
  have HX : Has m B (simIn cl) (bundle cl) x fun i => (L i).tape (v i) :=
    Can.second.snd
  have hl : Knows m B (simIn cl) x fun i => (L i).n := HX.len (Small.self B)
  have hh : Can m B (simIn cl) (bundle cl) x (fun i => (M i).tape (E i)) W := by
    let Q := Σ i, Sim ρ (k i)
    have hb : Small B fun i => (M i).n :=
      (Small.const B R.n).mul (Small.self B)
    have ht : Has m (fun d : Q => B d.1) (p (simIn cl) w) (c cl)
        (fun d => (x d.1,(M d.1).loc d.2)) (fun d => E d.1 d.2) := by
      let σ := Sigma.fst (β:=fun i => Sim ρ (k i))
      exact Can.fetch (t:=c cl) (L:=fun i => L i.1) (v:=fun i => v i.1)
        (i:=fun i : Q => i.2.2)
        (Can.first.then_do (HX.reindex σ)) (Can.addr_low
          (L:=fun _ => R) (R:=fun i : Q => L i.1) (u:=fun d : Q => d.2)
          Can.second (Can.then_do (Can.first (s:=simIn cl) (t:=w) (v:=fun d : Q => (x d.1,(M d.1).loc d.2))) (hl.reindex σ)) (hb.reindex σ))
    have H := Can.layout (L:=M) (t:=c cl) (P:=fun _ => 0) (v:=E)
      ((Can.wc R.n).times hl (Small.const B R.n) (Small.self B)) ht hb
    simp only [Nat.mul_zero,Nat.zero_add,Nat.add_zero] at H
    exact H.weaken he
  have hk : Can m B (simIn cl) (bundle cl) x
      (fun i => (M i).tape (whole (k i) (E i))) W := by
    refine Can.then_do ?_ h
    exact Can.pair Can.first ((Can.second.fst).pair hh)
  -- locally keep x as well to supply size
  let Y i := whole (k i) (E i)
  let s := p (simIn cl) (bundle cl)
  let env (i : ι) : T s := (x i,(M i).tape (Y i))
  refine Can.bind hk (g:=?_)
  change Can m B s (bundle cl) env _ W
  have hl' := Can.then_do (show Has m B s (simIn cl) env x from Can.first) hl
  let σ := Sigma.fst (β:=fun i => Bits (k i))
  have ht : Has m (fun d : Σ i, Bits (k i) => B d.1) (p s w) (c cl)
      (fun d => (env d.1,(L d.1).loc d.2)) (fun d => ripple _ (v d.1) d.2) := by
    exact Can.fetch (i:=fun d : Σ i,Bits (k i) => (l,d.2)) (L:=fun i => M i.1)
      (v:=fun i => Y i.1) (t:=c cl)
      (Can.first.snd) (Can.addr_join (u:=fun d : Σ i,Bits (k i) => (l,d.2)) (L:=fun _=> R)
        (R:=fun d : Σ i,Bits (k i) => L d.1) (Can.wc (R.loc l)) Can.second (Can.then_do (Can.first (s:=s) (t:=w) (v:=fun d : Σ i,Bits (k i) => (env d.1,(L d.1).loc d.2))) (hl'.reindex σ))
        (Small.const (fun d : Σ i,Bits (k i) => B d.1) R.n) ((Small.self B).reindex σ))
  have H := Can.layout (L:=L) (t:=c cl) (P:=fun _ => 0)
    (v:=fun i => ripple (k i) (v i)) hl' ht (Small.self B)
  simp only [Nat.mul_zero,Nat.zero_add,Nat.add_zero] at H
  exact H.weaken hd

theorem hills_program (cl : Paint) (m : Bool) {ι : Type U} (k : ι→ℕ)
    (v : ∀ i, Bits (k i) → ℂ) :
    Can m (fun i => 2^k i) (simIn cl) (bundle cl)
      (fun i => givenBits cl (k i) (v i)) (fun i => (bits (k i)).tape (ripple (k i) (v i)))
      (fun i => 2^k i*hills (k i)) := by
  have ht := hills_all cl m k (fun i (j : Sim Role (k i)) => v i j.2)
  have H : Nonempty Role :=
    Fintype.card_pos_iff.mp (by rw [card_role]; unfold tower; positivity)
  obtain ⟨l⟩ := H
  exact hills_project cl m k v (Layout.someLayout Role) l ht

end
end PowerSaving.RAM

end OAI
