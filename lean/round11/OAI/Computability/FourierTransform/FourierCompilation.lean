import OAI.Computability.FourierTransform.LayerCompilation

namespace OAI

namespace PowerSaving.RAM
open Ty Finset
noncomputable section

universe U V

namespace Bench
variable {m : Bool} {ι : Type U} {κ : Type V} {b : Bench m ι}
  {n : ι→ℕ} {t : Ty}

lemma inspect (b : Bench m ι) (n : ι→ℕ) (x : ι→ℕ→T t) :
    (b.climbs n t x).Feeds (b.scan n) id :=
  Feeds.select (Feeds.climbs b n x)
    ((toppings (b.along During.i) (t:=p w t) (fun d : During n => (d.j,x d.i d.j))).fst)

lemma Digit.two (h : b.Digit n) (hz : Small b.size (fun i => 2^n i)) :
    b.Digit (fun i => 2^n i) := by
  let x := fun (_ : ι) j => (2:ℕ)^j
  let P := b.climbs n w x
  have hh : P.Digit (fun i => x i.i i.j) := by
    refine ⟨stepsum (t:=w) b n x,(hz.reindex During.i).mono ?_⟩
    intro j
    exact Nat.pow_le_pow_right (by omega) j.hj.le
  have hk : P.Digit (fun i => x i.i (i.j+1)) :=
    (hh.mul (Digit.wc 2)).congr (fun i => by simp [x,pow_succ])
  exact ⟨loop (t:=w) h x ((Makes.wc 1).congr fun _ => by simp [x]) hk.run,hz⟩

namespace Makes

lemma casting (h : b.Digit n) : b.Makes sc (fun i => (n i:ℂ)) := by
  let x := fun (_ : ι) (j : ℕ) => (j:ℂ)
  exact loop (t:=sc) h x
    (zero.congr (fun _ => by simp [x]))
    (((stepsum (t:=sc) b n x).add one).congr (fun _ => by simp only [x,Nat.cast_add,Nat.cast_one]))

lemma expZ (h : b.Digit n) {u : ι→ℂ} (g : b.Makes sc u) :
    b.Makes sc fun i => (u i)^n i := by
  let x := fun i (j : ℕ) => (u i)^j
  let P := b.climbs n sc x
  have hu : P.Makes sc fun j => u j.i := pull (Feeds.climbs (t:=sc) b n x) g
  exact loop (t:=sc) h x (one.congr (fun _ => by simp [x]))
    (((stepsum (t:=sc) b n x).mul hu).congr (fun _ => by simp [x,pow_succ]))

lemma gridSum (h : b.Digit n) (x : ι→ℕ→ℂ)
    (g : (b.scan n).Makes sc fun i => x i.i i.j) :
    b.Makes sc (fun i => ∑ j ∈ range (n i), x i j) := by
  let y := fun i k => ∑ j ∈ range k, x i j
  have hx : (b.climbs n sc y).Makes sc fun i => x i.i i.j :=
    pull (inspect (t:=sc) b n y) g
  exact loop (t:=sc) h y (zero.congr fun _ => by simp [y])
    (((stepsum (t:=sc) b n y).add hx).congr (fun _ => by simp [y,sum_range_succ]))

lemma gridProd (h : b.Digit n) (x : ι→ℕ→ℂ)
    (g : (b.scan n).Makes sc fun i => x i.i i.j) :
    b.Makes sc (fun i => ∏ j ∈ range (n i), x i j) := by
  let y := fun i k => ∏ j ∈ range k, x i j
  have hx : (b.climbs n sc y).Makes sc fun i => x i.i i.j :=
    pull (inspect (t:=sc) b n y) g
  exact loop (t:=sc) h y (one.congr fun _ => by simp [y])
    (((stepsum (t:=sc) b n y).mul hx).congr (fun _ => by simp [y,prod_range_succ]))

lemma pick (x : ι→ℕ→T t)
    (h : b.Makes (a t) (fun i => Tape.tab (n i) (x i)))
    {k} (g : b.Makes w k) (hk : ∀ i, k i<n i) :
    b.Makes t (fun i => x i (k i)) :=
  (h.look g).congr (fun i => by rw [Tape.look_tab,ite_eq_left (hk i)])

end Makes
end Bench

end
end PowerSaving.RAM

end OAI
