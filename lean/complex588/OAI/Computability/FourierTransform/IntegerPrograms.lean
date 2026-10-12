import OAI.Computability.FourierTransform.LayoutPrograms

namespace OAI

namespace PowerSaving.RAM
open Ty Finset
noncomputable section

universe U
variable {ι : Type U} {m : Bool}

namespace Small
variable {B P Q : ι → ℕ}

theorem sub (h : Small B P) : Small B (fun i => P i-Q i) :=
  h.mono fun _ => Nat.sub_le _ _

theorem div (h : Small B P) : Small B (fun i => P i/Q i) :=
  h.mono fun _ => Nat.div_le_self _ _

theorem mod (h : Small B P) : Small B (fun i => P i%Q i) :=
  h.mono fun _ => Nat.mod_le _ _
end Small

namespace Can
variable {s t : Ty} {x : ι → T s} {B W A Q : ι → ℕ}

lemma minus (h : Can m B s w x A W) (k : Can m B s w x Q W)
    (hh : Small B A) : Can m B s w x (fun i => A i - Q i) W :=
  h.wsub k hh.sub

lemma times (h : Can m B s w x A W) (k : Can m B s w x Q W)
    (hh : Small B A) (gg : Small B Q) : Can m B s w x (fun i => A i * Q i) W :=
  h.wmul k (hh.mul gg)

lemma plus (h : Can m B s w x A W) (k : Can m B s w x Q W)
    (hh : Small B A) (gg : Small B Q) : Can m B s w x (fun i => A i + Q i) W :=
  h.wadd k (hh.add gg)

lemma dvdW (h : Can m B s w x A W) (k : Can m B s w x Q W) (hh : Small B A) :
    Can m B s w x (fun i => A i / Q i) W :=
  h.wdiv k hh.div

lemma modW (h : Can m B s w x A W) (k : Can m B s w x Q W) (hh : Small B A) :
    Can m B s w x (fun i => A i % Q i) W :=
  h.wmod k hh.mod

lemma wpow_fixed (n : ℕ) (h : Can m B s w x A W) (hh : Small B A) :
    Can m B s w x (fun i => (A i)^n) W := by
  induction n with
  | zero => simpa using wc (s:=s) (m:=m) (B:=B) (x:=x) (W:=W) 1
  | succ n ih => simpa [pow_succ] using ih.times h (hh.pow n) hh

/-- Cost-sensitive powering of two to a variable exponent by doubling. -/
lemma wTwo (h : Can m B s w x A W) (hh : Small B A)
    (hq : Small B fun i => 2^A i) (ha : Dom W A) :
    Can m B s w x (fun i => 2^A i) W := by
  let v (_ : ι) (n : ℕ) := 2^n
  have hs : Can m (fun d : During A => B d.i) (p s (p w w)) w
      (fun d => (x d.i, d.j, v d.i d.j)) (fun d => v d.i (d.j+1)) (fun _ => 0) := by
    have hp : Small (fun d : During A => B d.i) fun d => v d.i d.j :=
      (hq.reindex During.i).mono (fun d => Nat.pow_le_pow_right (by omega) d.hj.le)
    unfold v at *
    simp only [pow_succ]
    exact (Can.snd Can.second).times (Can.wc _) hp (Small.const ..)
  have ht := Can.loop (t:=w) (v:=v) (W':=fun _ => 0) (uB:=fun _ _ => 0) h
    (by simpa only [v,pow_zero] using (Can.wc (m:=m) (W:=fun _ => 0)
      (B:=B) (s:=s) (x:=x) 1)) hs hh
  simp only [Finset.sum_const_zero,Nat.add_zero] at ht
  exact ht.weaken ((Dom.self W).add ha)

end Can

namespace Can
variable {s t : Ty} {x : ι → T s} {B W A Q : ι → ℕ}

lemma neg {cl} {z : ι→ℂ} (h : Can m B s (c cl) x z W) :
    Can m B s (c cl) x (fun i => -(z i)) W := by
  simpa using (Can.sub Can.zero h)

lemma cNat (n : ℕ) : Can m B s sc x (fun _ => (n:ℂ)) W := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero]
    exact Can.zero
  | succ n ih => simpa using ih.add Can.one

lemma cInt (n : ℤ) : Can m B s sc x (fun _ => (n:ℂ)) W := by
  cases n with
  | ofNat n =>
    simpa using (cNat (s:=s) (m:=m) (B:=B) (W:=W) (x:=x) n)
  | negSucc n =>
    simpa using (cNat (s:=s) (m:=m) (B:=B) (W:=W) (x:=x) (n+1)).neg

lemma rat (z : ℚ) : Can m B s sc x (fun _ => (z:ℂ)) W := by
  rw [Rat.cast_def]
  simp only [div_eq_mul_inv]
  exact (Can.cInt _).mul ((Can.cNat _).inv (by intro i; exact_mod_cast z.den_nz))

lemma cpow_fixed (n : ℕ) {v : ι→ℂ} (h : Can m B s sc x v W) :
    Can m B s sc x (fun i => v i ^ n) W := by
  induction n with
  | zero =>
    simp only [pow_zero]
    exact Can.one
  | succ n ih => simpa [pow_succ] using ih.mul h

lemma prod_cconst {μ : Type*} [Fintype μ] {v : μ→ι→ℂ}
    (h : ∀ i : μ, Can m B s sc x (v i) W) :
    Can m B s sc x (fun j => ∏ i, v i j) W := by
  classical
  have hh (l : Finset μ) : Can m B s sc x (fun j => ∏ i∈l,v i j) W := by
    induction l using Finset.induction with
    | empty =>
      simp only [prod_empty]
      exact Can.one
    | insert i l hi ih =>
      simp only [prod_insert hi]
      exact (h i).mul ih
  exact hh _

end Can

namespace Can
-- product addressing at arbitrary parameter types
variable {s t : Ty} {x : ι → T s} {B W : ι → ℕ}
variable {α β : ι → Type*} {L : ∀ i, Layout (α i)} {R : ∀ i, Layout (β i)}
  {u : ∀ i, α i × β i}

lemma addr_join (h : Can m B s w x (fun i => (L i).loc (u i).1) W)
    (k : Can m B s w x (fun i => (R i).loc (u i).2) W)
    (d : Can m B s w x (fun i => (R i).n) W)
    (hl : Small B fun i => (L i).n) (hr : Small B fun i => (R i).n) :
    Can m B s w x (fun i => ((L i).pair (R i)).loc (u i)) W :=
  (h.times d (Small.loc (x:=fun i => (u i).1) (L:=L) hl) hr).plus k
    ((Small.loc (x:=fun i => (u i).1) (L:=L) hl).mul hr)
    (Small.loc (x:=fun i => (u i).2) (L:=R) hr)

lemma addr_high (h : Can m B s w x (fun i => ((L i).pair (R i)).loc (u i)) W)
    (k : Can m B s w x (fun i => (R i).n) W)
    (hs : Small B fun i => (L i).n*(R i).n) :
    Can m B s w x (fun i => (L i).loc (u i).1) W :=
  (h.dvdW k (Small.loc (L:=fun i => (L i).pair (R i)) (x:=u) hs)).cong
    (fun _ => rfl) (fun _ => Layout.pair_div ..)

lemma addr_low (h : Can m B s w x (fun i => ((L i).pair (R i)).loc (u i)) W)
    (k : Can m B s w x (fun i => (R i).n) W)
    (hs : Small B fun i => (L i).n*(R i).n) :
    Can m B s w x (fun i => (R i).loc (u i).2) W :=
  (h.modW k (Small.loc (L:=fun i => (L i).pair (R i)) (x:=u) hs)).cong
    (fun _ => rfl) (fun _ => Layout.pair_mod ..)

end Can
end
end PowerSaving.RAM

end OAI
