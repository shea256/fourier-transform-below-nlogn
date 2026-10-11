import OAI.Computability.FourierTransform.IntegerPrograms
import OAI.Computability.FourierTransform.TensorFibers

namespace OAI

/-! Transposed column address trick: a table of the addition of two f-bit digit
 vectors. We will be able to charge construction of the *whole* table. -/

namespace PowerSaving.RAM
open Binary Ty Finset
noncomputable section

def xorOrd (k : ℕ) : Layout (Bits k × Bits k) := (bits k).pair (bits k)

def xorTab (k : ℕ) : Tape ℕ := (xorOrd k).tape (fun i => (bits k).loc (i.1+i.2))

private lemma digit_prefix (z p : ℕ) (hp : p>0) :
    z % (p*2) = z%p + (z/p%2)*p := by
  have h : (z/p/2)*(p*2) + ((z/p%2)*p+z%p) = z := by
    calc
      _ = ((2*(z/p/2)+z/p%2)*p) + z%p := by ring
      _ = z := by rw [Nat.div_add_mod, mul_comm, Nat.div_add_mod]
  have hd : (z/p%2)*p+z%p < p*2 := by
    rw [mul_comm p]
    exact Layout.lt_join (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ hp)
  exact (congr_arg (· % (p*2)) h).symm.trans ((Layout.mod_join hd).trans (add_comm ..))

private lemma digit_plus (k : ℕ) (x y : Bits k) (j : ℕ) (hj : j<k) :
    let b := (bits k).loc
    b (x+y) / 2^j % 2 =
      ((b x / 2^j) + (b y / 2^j))%2 := by
  intro b
  let i : Fin k := ⟨j,hj⟩
  have h (v : Bits k) : b v / 2^j % 2 = (v i).val := bits_div k v i
  rw [Nat.add_mod,h,h,h]
  exact ZMod.val_add _ _

namespace Can
universe U
variable {ι : Type U} {m : Bool} {s : Ty} {x : ι→T s} {B f : ι→ℕ}

/-- Assume the input environment supplies arguments to this subcalculation at O(1) cost. -/
private theorem xor_value (v : ∀ i, Bits (f i) × Bits (f i))
    (hf : Can m B s w x f (fun _ => 0))
    (ha : Can m B s w x (fun i => (bits (f i)).loc (v i).1) (fun _ => 0))
    (hb : Can m B s w x (fun i => (bits (f i)).loc (v i).2) (fun _ => 0))
    (hB : Small B f) (hd : Small B fun i => 2^f i) :
    Can m B s w x (fun i => (bits (f i)).loc ((v i).1+(v i).2)) f := by
  let X := fun i => (bits (f i)).loc ((v i).1+(v i).2)
  let a1 i := (bits (f i)).loc (v i).1
  let a2 i := (bits (f i)).loc (v i).2
  let g := fun (i : ι) (j : ℕ) => (2^j,X i % 2^j)
  let Y := p w w
  let T₀ := p s (p w Y)
  let env (d : During f) : T T₀ := (x d.i,d.j,g d.i d.j)
  let B' (d : During f) := B d.i
  let E (d : During f) := 2^d.j
  have hv (w : ∀ i, Bits (f i)) :
      Small B fun i => (bits (f i)).loc (w i) :=
    Small.loc (x:=w) (L:=fun i => bits (f i)) hd
  have sE : Small B' E :=
    (hd.reindex (During.i (n:=f))).mono (fun d => Nat.pow_le_pow_right (by omega) d.hj.le)
  have sr : Small B' (fun d : During f => (g d.i d.j).2) :=
    ((hv (fun i => (v i).1+(v i).2)).reindex (During.i (n:=f))).mod
  have step : Can m B' T₀ Y env (fun d => g d.i (d.j+1)) (fun _ => 0) := by
    have cg : Can m B' T₀ Y env (fun d => g d.i d.j) (fun _ => 0) := Can.snd Can.second
    have ce : Can m B' T₀ w env E (fun _ => 0) := cg.fst
    have cs2 : Can m B' T₀ w env (fun d => 2) (fun _ => 0) := Can.wc _
    have sa : Small B' fun d : During f => a1 d.i := (hv (fun i => (v i).1)).reindex During.i
    have sb : Small B' fun d : During f => a2 d.i := (hv (fun i => (v i).2)).reindex During.i
    have ca : Can m B' T₀ w env (fun d => a1 d.i) (fun _ => 0) :=
      Can.first.then_do (ha.reindex During.i)
    have cb : Can m B' T₀ w env (fun d => a2 d.i) (fun _ => 0) :=
      Can.first.then_do (hb.reindex During.i)
    have cp := (ca.dvdW ce sa).plus (cb.dvdW ce sb) sa.div sb.div
    have sx := (sa.div (Q:=E)).add (sb.div (Q:=E))
    have cy := (cp.modW cs2 sx).times ce sx.mod sE
    have cq := (cg.snd).plus cy sr ((sx.mod (Q:=fun _ => 2)).mul sE)
    refine ((ce.times cs2 sE (Small.const ..)).pair cq).cong (fun _ => rfl) ?_
    intro d
    apply Prod.ext
    · exact (pow_succ ..).symm
    · change X d.i % 2^d.j + _ = X d.i % 2^(d.j+1)
      rw [pow_succ,digit_prefix (X d.i) (2^d.j) (by positivity)]
      have h := digit_plus _ (v d.i).1 (v d.i).2 d.j d.hj
      congr 1
      exact congr_arg (· * 2^d.j) h.symm
  have c0 : Can m B s Y x (fun i => g i 0) (fun _ => 0) := by
    simp only [g,pow_zero,Nat.mod_one]
    exact (Can.wc _).pair (Can.wc _)
  have hh := Can.loop (t:=Y) (v:=g) (uB:=fun _ _ => 0) hf c0 step hB
  have he (i) : (g i (f i)).2=X i := Nat.mod_eq_of_lt ((bits (f i)).bd _)
  simpa [he,X] using hh.snd

theorem xor_prepare (hf : Can m B s w x f (fun _ => 0))
    (hg : Can m B s w x (fun i => 2^f i) (fun _ => 0))
    (hB : Small B f) (hd : Small B fun i => 2^f i) :
    Can m B s (a w) x (fun i => xorTab (f i)) (fun i => (2^f i)^3) := by
  let V i := (bits (f i)).n
  let D i := xorOrd (f i)
  have sn : Small B fun i => (D i).n := hd.mul hd
  have hn : Can m B s w x (fun i => (D i).n) (fun _ => 0) := hg.times hg hd hd
  let I i := Bits (f i) × Bits (f i)
  let BB (d : Σ i, I i) := B d.1
  let VV (d : Σ i, I i) : T (p s w) := (x d.1,(D d.1).loc d.2)
  have hh : Can m BB (p s w) w VV (fun d : Σ i, I i =>
      (bits (f d.1)).loc (d.2.1+d.2.2)) (fun d => f d.1) := by
    have hv : Can m BB (p s w) w VV
      (fun d => V d.1) (fun _ => 0) :=
      Can.first.then_do (hg.reindex (Sigma.fst (β:=I)))
    have hBB := sn.reindex (Sigma.fst (β:=I))
    let X (d : Σ i, I i) := bits (f d.1)
    apply xor_value (f:=fun d : Σ i, I i => f d.1) _
        (Can.first.then_do (hf.reindex (Sigma.fst (β:=I)))) _ _
        (hB.reindex Sigma.fst) (hd.reindex Sigma.fst)
    · exact Can.addr_high (u:=fun d : Σ i, I i => d.2) (L:=X) (R:=X)
        Can.second hv hBB
    · exact Can.addr_low (u:=fun d : Σ i, I i => d.2) (L:=X) (R:=X)
        Can.second hv hBB
  have ht := Can.layout (t:=w) (P:=f) (L:=D) (α:=I)
    (v:=fun (i : ι) j => (bits (f i)).loc (j.1+j.2)) hn hh sn
  refine ht.mono (fun i => ?_)
  change 0+2^f i * 2^f i + _* f i ≤ _
  have he : f i < 2^f i := Nat.lt_two_pow_self
  change 0+2^f i * 2^f i + 2^f i * 2^f i * f i ≤ _
  have h := Nat.mul_le_mul_left (2^f i * 2^f i) he
  simpa [pow_succ,Nat.mul_add,add_comm] using h

theorem xor_lookup {W : ι → ℕ}
    (v : ∀ i, Bits (f i) × Bits (f i))
    (ht : Can m B s (a w) x (fun i => xorTab (f i)) W)
    (ha : Can m B s w x (fun i => (bits (f i)).loc (v i).1) W)
    (hb : Can m B s w x (fun i => (bits (f i)).loc (v i).2) W)
    (hn : Can m B s w x (fun i => 2^f i) W)
    (hd : Small B fun i => 2^f i) :
    Can m B s w x (fun i => (bits (f i)).loc ((v i).1+(v i).2)) W :=
  Can.fetch (t:=w) (L:=fun i => xorOrd (f i)) (i:=v)
    (v:=fun i j => (bits (f i)).loc (j.1+j.2)) ht
    (Can.addr_join (u:=v) (L:=fun i => bits (f i)) (R:=fun i => bits (f i))
    ha hb hn hd hd)

end Can
end
end PowerSaving.RAM

end OAI
