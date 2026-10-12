import OAI.Computability.FourierTransform.ProgramBounds

namespace OAI

namespace PowerSaving.RAM
open Ty Finset

universe U V

/-- Parameters on which a loop body must be uniform. -/
structure During {ι : Type U} (n : ι → ℕ) where
  i : ι
  j : ℕ
  hj : j < n i

namespace Able
variable {ι : Type U}
  {m : Bool} {r : Port} {b : Bank r ι} {s t : Ty}
  {x : ι → T s} {y : ι → T t}
  {W Z W' Z' Wl Zl n : ι → ℕ} {Wb Zb : ι → ℕ → ℕ}

private theorem sum_time (C n d : ℕ) (P Q : ℕ → ℕ) :
    ∑ j ∈ range n, (C*(P j+1)+Q j+d)
      = C*(∑ j ∈ range n, P j) + (∑ j ∈ range n, Q j) + C*n + d*n := by
  induction n with
  | zero => simp
  | succ n ih => simp only [sum_range_succ, ih]; ring

theorem loop {v : ι → ℕ → T t}
    (h : Able m b s w x n W Z)
    (hi : Able m b s t x (fun i => v i 0) W' Z')
    (hs : Able m (b.comap (During.i (n:=n))) (p s (p w t)) t
      (fun d => (x d.i,(d.j,v d.i d.j))) (fun d => v d.i (d.j+1))
      (fun d => Wb d.i d.j) (fun d => Zb d.i d.j))
    (hc : Small b.B n) :
    Able m b s t x (fun i => v i (n i))
      (fun i => W i + W' i + n i + ∑ j ∈ range (n i), Wb i j)
      (fun i => Z i + Z' i + ∑ j ∈ range (n i), Zb i j) := by
  obtain ⟨l,A,da,ha⟩ := h
  obtain ⟨q,L,dl,hl⟩ := hi
  obtain ⟨f,F,df,hf⟩ := hs
  obtain ⟨e,he⟩ := hc
  let d := da+dl+df+e
  refine ⟨.loop l q f,A+L+F+10,d,fun i => ?_⟩
  have ga := (ha i).mono le_rfl (b.cm (show da≤d by dsimp [d]; omega) i)
  have gl := (hl i).mono le_rfl (b.cm (show dl≤d by dsimp [d]; omega) i)
  let g := fun j z => f.run (b.use i) (x i,(j,z))
  let Y := fun j => F*(Wb i j+1)+Zb i j
  have hh (j) (hj : j<n i) : (g j (v i j)).OK (v i (j+1)) (Y j) (b.cap d i) :=
    (hf ⟨i,j,hj⟩).mono le_rfl (b.cm (show df≤d by dsimp [d]; omega) i)
  have hlen : n i ≤ b.cap d i :=
    (he i).trans ((le_max_left _ _).trans
      (b.cm (show e≤d by dsimp [d]; omega) i))
  rw [Code.run]
  have H := ga.pass (f:=fun k : ℕ => (q.run (b.use i) (x i)).pass
    (fun v0 => Bill.steps v0 g k)) (gl.pass (f:=fun v0 => Bill.steps v0 g (n i)) (Bill.steps_ok (f:=g) (v:=v i)
    Y (n i) _ hlen hh))
  refine (H.pay (Nat.zero_le _)).mono ?_ le_rfl
  change _ + ((L*(_+1)+_) + (1+∑ j ∈ range (n i), (F*(Wb i j+1)+Zb i j+1))) + 1 ≤ _
  rw [sum_time]
  simp only [mul_add, add_mul, mul_one]
  omega

theorem tab {v : ι → ℕ → T t}
    (h : Able m b s w x n W Z)
    (hs : Able m (b.comap (During.i (n:=n))) (p s w) t
      (fun d => (x d.i,d.j)) (fun d => v d.i d.j)
      (fun d => Wb d.i d.j) (fun d => Zb d.i d.j))
    (hc : Small b.B n) :
    Able m b s (a t) x (fun i => Tape.tab (n i) (v i))
      (fun i => W i + n i + ∑ j ∈ range (n i), Wb i j)
      (fun i => Z i + ∑ j ∈ range (n i), Zb i j) := by
  obtain ⟨l,A,da,ha⟩ := h
  obtain ⟨f,F,df,hf⟩ := hs
  obtain ⟨e,he⟩ := hc
  let d := da+df+e
  refine ⟨.tab l f,A+F+10,d,fun i => ?_⟩
  have ga := (ha i).mono le_rfl (b.cm (show da≤d by dsimp [d]; omega) i)
  let g := fun j => f.run (b.use i) (x i,j)
  let Y := fun j => F*(Wb i j+1)+Zb i j
  have hh (j) (hj : j<n i) : (g j).OK (v i j) (Y j) (b.cap d i) :=
    (hf ⟨i,j,hj⟩).mono le_rfl (b.cm (show df≤d by dsimp [d]; omega) i)
  have hlen : n i ≤ b.cap d i :=
    (he i).trans ((le_max_left _ _).trans
      (b.cm (show e≤d by dsimp [d]; omega) i))
  rw [Code.run]
  have H := ga.pass (f:=fun k : ℕ => Bill.tab k t.blank g) (Bill.tab_ok (f:=g) (v:=v i) Y (n i) _ t.blank hlen hh)
  refine (H.pay (Nat.zero_le _)).mono ?_ le_rfl
  change _ + ((1 + ∑ j ∈ range (n i), (F*(Wb i j+1)+Zb i j+3))+(1+n i)) + 1 ≤ _
  rw [sum_time]
  simp only [mul_add, add_mul, mul_one]
  omega

theorem sow {v : ι → ℕ → ℕ × T t} {len : ι → ℕ}
    (hx : Able m b s w x len Wl Zl)
    (h : Able m b s w x n W Z)
    (hs : Able m (b.comap (During.i (n:=n))) (p s w) (p w t)
      (fun d => (x d.i,d.j)) (fun d => v d.i d.j)
      (fun d => Wb d.i d.j) (fun d => Zb d.i d.j))
    (hg : Small b.B len) (hc : Small b.B n) :
    Able m b s (a t) x (fun i => Tape.sow (len i) (n i) t.blank (v i))
      (fun i => Wl i + W i + len i + n i + ∑ j ∈ range (n i), Wb i j)
      (fun i => Zl i + Z i + ∑ j ∈ range (n i), Zb i j) := by
  obtain ⟨l,A,da,ha⟩ := hx
  obtain ⟨q,L,dl,hl⟩ := h
  obtain ⟨f,F,df,hf⟩ := hs
  obtain ⟨e1,h1⟩ := hg
  obtain ⟨e,he⟩ := hc
  let d := da+dl+df+e+e1
  refine ⟨.sow l q f,A+L+F+10,d,fun i => ?_⟩
  have ga := (ha i).mono le_rfl (b.cm (show da≤d by dsimp [d]; omega) i)
  have gl := (hl i).mono le_rfl (b.cm (show dl≤d by dsimp [d]; omega) i)
  let g := fun j => f.run (b.use i) (x i,j)
  let Y := fun j => F*(Wb i j+1)+Zb i j
  have hh (j) (hj : j<n i) : (g j).OK (v i j) (Y j) (b.cap d i) :=
    (hf ⟨i,j,hj⟩).mono le_rfl (b.cm (show df≤d by dsimp [d]; omega) i)
  have hlen : len i ≤ b.cap d i :=
    (h1 i).trans ((le_max_left _ _).trans
      (b.cm (show e1≤d by dsimp [d]; omega) i))
  have hcount : n i ≤ b.cap d i :=
    (he i).trans ((le_max_left _ _).trans
      (b.cm (show e≤d by dsimp [d]; omega) i))
  rw [Code.run]
  have H := ga.pass (f:=fun l : ℕ => (q.run (b.use i) (x i)).pass
    (fun k => Bill.sow l k t.blank g)) (gl.pass
    (f:=fun k => Bill.sow (len i) k t.blank g) (Bill.sow_ok (f:=g) (v:=v i)
    Y (len i) (n i) _ t.blank hlen hcount hh))
  refine (H.pay (Nat.zero_le _)).mono ?_ le_rfl
  change _ + ((L*(_+1)+_) + ((1+∑ j ∈ range (n i), (F*(Wb i j+1)+Zb i j+2))+(1+len i)))+1 ≤ _
  rw [sum_time]
  simp only [mul_add, add_mul, mul_one]
  omega

/-- Only require the guarantee on the active branch. Budget/charge functions of i can
  also depend on the branch. -/
theorem ifz
    (hx : Able m b s w x n W' Z')
    (hz : Able m (b.comap (fun i : {i // n i = 0} => i.val)) s t
      (fun i => x i.val) (fun i => y i.val) (fun i => W i.val) (fun i => Z i.val))
    (hn : Able m (b.comap (fun i : {i // n i ≠ 0} => i.val)) s t
      (fun i => x i.val) (fun i => y i.val) (fun i => W i.val) (fun i => Z i.val)) :
    Able m b s t x y (fun i => W' i+W i) (fun i => Z' i+Z i) := by
  obtain ⟨q,A,da,ha⟩ := hx
  obtain ⟨f,C,dc,hc⟩ := hz
  obtain ⟨g,D,dd,hd⟩ := hn
  let d := da+dc+dd
  refine ⟨.ifz q f g, A+C+D+1, d, fun i => ?_⟩
  have hh :
      (if n i = 0 then f.run (b.use i) (x i) else g.run (b.use i) (x i)).OK
        (y i) ((C+D)*(W i+1)+Z i) (b.cap d i) := by
    split
    next h =>
      refine (hc ⟨i,h⟩).mono ?_ (b.cm (show dc≤d by dsimp [d]; omega) i)
      simp only [add_mul]
      omega
    next h =>
      refine (hd ⟨i,h⟩).mono ?_ (b.cm (show dd≤d by dsimp [d]; omega) i)
      simp only [add_mul]
      omega
  have hq := (ha i).mono le_rfl (b.cm (show da≤d by dsimp [d]; omega) i)
  rw [Code.run]
  have H := hq.pass (f:=fun j : ℕ => if j=0 then _ else _) hh
  refine (H.pay (Nat.zero_le _)).mono ?_ le_rfl
  simp only [add_mul, mul_add, mul_one, one_mul]
  omega

end Able
end PowerSaving.RAM

end OAI
