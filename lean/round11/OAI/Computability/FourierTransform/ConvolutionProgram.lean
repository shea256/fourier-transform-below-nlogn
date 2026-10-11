import OAI.Computability.FourierTransform.TransformProgram

namespace OAI

/- All-length bilinear convolution. -/
namespace PowerSaving
open RAM Ty Selection Spectral Finset
noncomputable section

-- correspondence lemma for polynomials in dense coefficient representation
def polyOf (n : ℕ) (x : Vec n) : Polynomial ℂ :=
  ∑ i : Fin n, Polynomial.monomial i.val (x i)

lemma polyOf_mul (n : ℕ) (x y : Vec n) :
    polyOf (2*n-1) (conv n x y)=polyOf n x * polyOf n y := by
  open Polynomial in
    simp only [polyOf,conv,map_sum,sum_mul,mul_sum,monomial_mul_monomial]
  let q (k : Fin (2*n-1)) (r s : Fin n) :=
    Polynomial.monomial k.val (if r.val+s.val=k.val then x r*y s else 0)
  change ∑ k,∑ r,∑ s,q k r s=_
  rw [sum_comm]
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl ?_
  intro i _
  rw [sum_comm]
  refine sum_congr rfl ?_
  intro j _
  let k : Fin (2*n-1) := ⟨i.val+j.val,by have := i.isLt; have := j.isLt; omega⟩
  rw [sum_eq_single k]
  · simp [q,k]
  · intro b _ hb
    have H : i.val+j.val≠b.val := fun hg => hb (Fin.ext hg.symm)
    simp [q,H]
  · simp

lemma polyOf_coeff_exact (n : ℕ) (x : Polynomial ℂ) (hx : x.natDegree<n) :
    polyOf n (fun i => x.coeff i.val)=x := by
  rw [polyOf,Fin.sum_univ_eq_sum_range (fun j => Polynomial.monomial j (x.coeff j)) n]
  exact (Polynomial.as_sum_range' x n hx).symm

namespace RAM.Bench
universe U V
variable {ι : Type U} {κ : Type V} {b : Bench true ι} {n N : ι→ℕ}

lemma crossT (h : b.Nick N) {x y : ι→Line}
    (hx : b.Moves (fun _ => 0) (a (c Paint.left)) fun i => Tape.tab (N i) (x i))
    (hy : b.Moves (fun _ => 0) (a (c Paint.right)) fun i => Tape.tab (N i) (y i)) :
    b.Moves N convOutKind fun i => Tape.tab (N i) fun j => x i j*y i j := by
  have F := Instant.scan b N
  refine arrayNow h _ (Can.cross
    (Moves.pick (t:=c Paint.left) (n:=fun i : During N => N i.i)
      (k:=During.j) (fun i j => x i.i j) (hx.transfer F) (chop h).close During.hj)
    (Moves.pick (t:=c Paint.right) (n:=fun i : During N => N i.i) (k:=During.j) (fun i j => y i.i j)
      (hy.transfer F) (chop h).close During.hj))

def stretch (n : ℕ) := 2*n-1

lemma stretch_pos {n : ℕ} (h : 0<n) : 0<stretch n := by unfold stretch; omega

lemma fusing (h : b.Nick n) (g : ∀ i, 0<n i) {x y : ι→Line}
    (hx : b.Moves (fun _ => 0) (a (c Paint.left)) fun i => Tape.tab (n i) (x i))
    (hy : b.Moves (fun _ => 0) (a (c Paint.right)) fun i => Tape.tab (n i) (y i))
    (hz : b.Moves (fun _ => 0) sc fun i => root (receipt (stretch (n i)))) :
    b.Breezy (fun i => stretch (n i)) convOutKind fun i => Tape.tab (stretch (n i))
      (cyclic (stretch (n i)) (padline (n i) (y i)) (padline (n i) (x i))) := by
  let N i := stretch (n i)
  let U i := padline (n i) (x i)
  let V i := padline (n i) (y i)
  let X i := freq (N i) (pr false (N i)) (U i)
  let Y i := freq (N i) (pr false (N i)) (V i)
  have H : b.Nick N := ((Nick.wc 2).mul h).sub (Nick.wc 1)
  have he : ∀ i,0<N i := fun i => stretch_pos (g i)
  have Hp := H.land' he hz false (Breezy.of_moves (padM h H hx) (Dom.self N))
  have Hq := H.land' he hz false (Breezy.of_moves (padM h H hy) (Dom.self N))
  let f (i : ι) : T (p (a (c Paint.left)) (a (c Paint.right))) :=
    (Tape.tab (N i) (X i),Tape.tab (N i) (Y i))
  have F := Instant.extend b f
  have Hb := cherry b f (W:=fun _ => 0)
  let A i := pointC (N i) (pr false (N i)) (U i) (V i)
  let B i := freq (N i) (pr true (N i)) (A i)
  have ha := H.land' he hz true (x:=A)
    ((Hp.pair Hq).bind (Breezy.of_moves (crossT (H.transfer F) (x:=X) (y:=Y) Hb.fst Hb.snd)
      (Dom.self N)))
  have hb := ha.pair (Breezy.of_moves H.numeralM (Dom.self N))
  let gg (i : ι) : T (p convOutKind sc) := (Tape.tab (N i) (B i),(N i:ℂ))
  have G := Instant.extend b gg
  have HH := H.transfer G
  have J := Instant.scan (b.extend _ gg) N
  have hj := Moves.transfer (cherry b gg (W:=fun _ => 0)) J
  have h1 := Moves.pick (t:=c Paint.both) (n:=fun i : During N => N i.i)
    (k:=During.j) (fun i => B i.i) hj.fst (chop HH).close During.hj
  have h2 := hj.snd.inv fun i => Nat.cast_ne_zero.mpr (Nat.ne_of_gt (he i.i))
  exact hb.bind (Breezy.of_moves (arrayNow HH _ ((h2.mul h1).congr (fun i =>
    freq_pad_row (n i.i) _ _ _ i.hj))) (Dom.self N))
end RAM.Bench

end
end PowerSaving

end OAI
