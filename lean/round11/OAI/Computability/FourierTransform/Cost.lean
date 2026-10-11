import OAI.Computability.FourierTransform.RAM

namespace OAI

namespace PowerSaving
open Finset

variable {α β : Type*}

namespace Tape

theorem ext_look {a b : Tape α} (hlen : a.len = b.len)
    (z : α) (h : ∀ i, i<a.len → a.look i z = b.look i z) : a=b := by
  rcases a with ⟨n,f⟩
  rcases b with ⟨m,g⟩
  change n = m at hlen
  subst m
  congr 1
  funext i
  simpa [Tape.look, i.isLt] using (h i i.isLt)

@[simp] theorem len_tab (n : ℕ) (f : ℕ → α) : (Tape.tab n f).len = n := rfl

theorem look_tab (n : ℕ) (f : ℕ → α) (i z) :
    (tab n f).look i z = if i<n then f i else z := by
  by_cases i<n <;> simp [Tape.look, Tape.tab, *]

@[simp] theorem len_set (v : Tape α) (i x) : (v.set i x).len = v.len := rfl

theorem look_set_ne (v : Tape α) (i j z y) (h : j ≠ i) :
    (v.set i y).look j z = v.look j z := by
  by_cases j<v.len <;> simp [look, set, *]

theorem look_set_eq (v : Tape α) (i z y) (h : i < v.len) :
    (v.set i y).look i z = y := by simp [look, set, h]

@[simp] theorem sow_zero (n : ℕ) (z : α) (f) :
    sow n 0 z f = tab n (fun _ => z) := rfl

@[simp] theorem sow_succ (n k : ℕ) (z : α) f :
    sow n (k+1) z f = (sow n k z f).set (f k).1 (f k).2 := by rfl

@[simp] theorem len_sow (n k : ℕ) (z : α) f : (sow n k z f).len = n := by
  induction k <;> simp_all

theorem sow_look_written {n k i j : ℕ} {z out : α} {f : ℕ → ℕ × α}
    (hin : i<n) (hj : j<k) (hf : (f j).1 = i)
    (hlast : ∀ s, j<s → s<k → (f s).1 ≠ i) :
    (sow n k z f).look i out = (f j).2 := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [sow_succ]
    rcases eq_or_ne k j with rfl|hh
    · rw [hf]
      apply look_set_eq
      simpa using hin
    · rw [look_set_ne _ _ _ _ _ (Ne.symm (hlast k (by omega) (by omega)))]
      exact ih (by omega) (fun s h1 h2 => hlast s h1 (by omega))

theorem sow_consecutive (n : ℕ) (z : α) (f : ℕ → α) :
    (sow n n z fun i => (i,f i)) = tab n f := by
  apply ext_look (by simp) z
  intro i hi
  rw [look_tab, ite_eq_left (by simpa using hi)]
  have hil : i < n := by simpa using hi
  exact sow_look_written hil hil rfl (fun s h _ => Nat.ne_of_gt h)

end Tape

namespace RAM

/-- Evaluation guarantee. -/
structure Bill.OK (b : Bill α) (x : α) (w p : ℕ) : Prop where
  result : b.val = x
  time : b.work ≤ w
  bound : b.peak ≤ p
  valid : b.valid

namespace Bill

variable {x : α} {y : β} {w w' p p' z t : ℕ}

theorem OK.mono {b : Bill α} (h : b.OK (x:α) w p) (u : w ≤ w') (v : p ≤ p') :
    b.OK x w' p' := ⟨h.result,h.time.trans u,h.bound.trans v,h.valid⟩

theorem OK.pass {b : Bill α} (h : b.OK (x:α) w p) {f : α → Bill β}
    (g : (f x).OK y w' p) : (b.pass f).OK y (w+w') p := by
  rw [← h.result] at g
  exact ⟨g.result, Nat.add_le_add h.time g.time,
         max_le h.bound g.bound, h.valid,g.valid⟩

theorem OK.pay {b : Bill α} (h : b.OK (x:α) w p) (h' : z ≤ p) :
    (b.pay t z).OK x (w+t) p :=
  ⟨h.result,Nat.add_le_add_right h.time _,max_le h.bound h', h.valid⟩

theorem one_ok (x : α) (p : ℕ) : (one x).OK x 1 p :=
  ⟨rfl,le_rfl,Nat.zero_le _,trivial⟩

theorem word_ok {x p : ℕ} (h : x≤p) : (word x).OK x 1 p :=
  ⟨rfl,le_rfl,h,trivial⟩

theorem steps_ok {v : ℕ → α} {f : ℕ → α → Bill α}
    (W : ℕ → ℕ) (n p : ℕ) (hn : n ≤ p)
    (h : ∀ i, i<n → (f i (v i)).OK (v (i+1)) (W i) p) :
    (steps (v 0) f n).OK (v n) (1+∑ i ∈ range n, (W i+1)) p := by
  induction n with
  | zero => simpa [steps] using one_ok (v 0) p
  | succ n ih =>
    rw [Finset.sum_range_succ, steps]
    have hg := ih (by omega) (fun i hi => h i (by omega))
    have hh := (hg.pass (h n (by omega))).pay (t:=1) hn
    simpa [add_assoc] using hh

theorem sow_ok {v : ℕ → ℕ × α} {f : ℕ → Bill (ℕ × α)}
    (W : ℕ → ℕ) (len n p : ℕ) (z : α) (hl : len ≤ p) (hn : n ≤ p)
    (h : ∀ i, i<n → (f i).OK (v i) (W i) p) :
    (sow len n z f).OK (Tape.sow len n z v)
      ((1+∑ i ∈ range n, (W i+2))+(1+len)) p := by
  unfold sow
  have hs (i) (hi : i<n) :
      ((f i).pass (fun s => one ((Tape.sow len i z v).set s.1 s.2))).OK
          (Tape.sow len (i+1) z v) (W i+1) p := by
    rw [Tape.sow_succ]
    exact (h i hi).pass (one_ok _ _)
  have hh := steps_ok (v:=fun i => Tape.sow len i z v)
    (f:=fun i x => (f i).pass (fun s => one (x.set s.1 s.2)))
    (fun i => W i+1) n p hn hs
  simpa [add_assoc] using hh.pay (t:=1+len) hl

theorem tab_ok {v : ℕ → α} {f : ℕ → Bill α}
    (W : ℕ → ℕ) (len p : ℕ) (z : α) (hl : len ≤ p)
    (h : ∀ i, i<len → (f i).OK (v i) (W i) p) :
    (tab len z f).OK (Tape.tab len v)
      ((1+∑ i ∈ range len, (W i+3))+(1+len)) p := by
  rw [← Tape.sow_consecutive len z]
  unfold tab
  have hs (i) (hi : i<len) :
      ((f i).pass (fun y => one (i,y))).OK (i,v i) (W i+1) p :=
    (h i hi).pass (one_ok _ _)
  simpa [add_assoc] using (sow_ok
    (v:=fun i => (i,v i)) (fun i => W i + 1)
    len len p z hl hl hs)

end Bill
end RAM
end PowerSaving

end OAI
