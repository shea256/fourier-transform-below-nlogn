import OAI.Computability.FourierTransform.LoopBounds

namespace OAI

namespace PowerSaving.RAM
open Ty Finset

universe U V

namespace Can
variable {ι : Type U} {κ : Type V}
  {m : Bool} {s t u : Ty}
  {B B' W W' W'' : ι → ℕ}
  {x : ι → T s} {y : ι → T t} {z : ι → T u}

theorem unfold_bound (h : Can m B s t x y W) :
    ∃ (f : Prog m s t) (C d : ℕ), ∀ i,
      (run f (x i)).OK (y i) (C*(W i+1)) ((B i+2)^d) := by
  obtain ⟨f,C,d,h⟩ := h
  refine ⟨f,C,d,fun i => ?_⟩
  simpa [Bank.cap,Bank.closed] using h i

theorem reindex (h : Can m B s t x y W) (f : κ → ι) :
    Can m (fun j => B (f j)) s t (fun j => x (f j)) (fun j => y (f j))
      (fun j => W (f j)) :=
  Able.reindex h f

theorem cong (h : Can m B s t x y W) {x' y'} (hx : ∀ i, x i = x' i)
    (hy : ∀ i, y i = y' i) : Can m B s t x' y' W :=
  Able.cong h hx hy

theorem weaken (h : Can m B s t x y W) (h' : Dom W' W) :
    Can m B s t x y W' :=
  Able.weaken h h' (fun _ => le_rfl)

theorem mono (h : Can m B s t x y W) (h' : ∀ i, W i ≤ W' i) :
    Can m B s t x y W' :=
  h.weaken (Dom.of_le h')

theorem ambient (h : Can m B s t x y W) (h' : Small B' B) :
    Can m B' s t x y W :=
  Able.rebank h h' (fun _ => le_rfl) rfl

theorem pipe (h : Can m B s t x y W) (g : Can m B t u y z W') :
    Can m B s u x z (fun i => W i+ W' i) :=
  Able.comp h g

theorem then_do (h : Can m B s t x y W) (g : Can m B t u y z W) :
    Can m B s u x z W :=
  Able.comp_keep h g

theorem fork (h : Can m B s t x y W) (g : Can m B s u x z W') :
    Can m B s (p t u) x (fun i => (y i,z i)) (fun i => W i+W' i) :=
  Able.fork h g

theorem pair (h : Can m B s t x y W) (g : Can m B s u x z W) :
    Can m B s (p t u) x (fun i => (y i,z i)) W :=
  Able.fork_keep h g

theorem save (h : Can m B s t x y W) (g : Can m B (p s t) u (fun i => (x i,y i)) z W') :
    Can m B s u x z (fun i => W i+ W' i) :=
  Able.save h g

theorem bind (h : Can m B s t x y W) (g : Can m B (p s t) u (fun i => (x i,y i)) z W) :
    Can m B s u x z W :=
  Able.save_keep h g

theorem id : Can m B s s x x W := Able.id

theorem first {v : ι → T (p s t)} : Can m B (p s t) s v (fun i => (v i).1) W :=
  Able.first

theorem second {v : ι → T (p s t)} : Can m B (p s t) t v (fun i => (v i).2) W :=
  Able.second

theorem fst {v : ι → T (p t u)} (h : Can m B s (p t u) x v W) :
    Can m B s t x (fun i => (v i).1) W := Able.fst h

theorem snd {v : ι → T (p t u)} (h : Can m B s (p t u) x v W) :
    Can m B s u x (fun i => (v i).2) W := Able.snd h

theorem wc (n : ℕ) : Can m B s w x (fun _ => n) W := by
  apply Able.atom_small (.lit n) (Small.const _ n)
  intro i; rw [Atom.run]; apply Bill.word_ok le_rfl

theorem zero {cl} : Can m B s (c cl) x (fun _ => 0) W :=
  Able.atom_one (.cz _) (fun _ => rfl)

theorem one : Can m B s sc x (fun _ => 1) W :=
  Able.atom_one .cone (fun _ => rfl)

variable {cl : Paint} {f g : ι → ℂ}

theorem add (h : Can m B s (c cl) x f W) (k : Can m B s (c cl) x g W) :
    Can m B s (c cl) x (fun i => f i + g i) W :=
  (h.pair k).then_do (Able.atom_one (.add _) (fun _ => rfl))

theorem sub (h : Can m B s (c cl) x f W) (k : Can m B s (c cl) x g W) :
    Can m B s (c cl) x (fun i => f i - g i) W :=
  (h.pair k).then_do (Able.atom_one (.sub _) (fun _ => rfl))

theorem mul (h : Can m B s sc x f W) (k : Can m B s (c cl) x g W) :
    Can m B s (c cl) x (fun i => f i * g i) W :=
  (h.pair k).then_do (Able.atom_one (.scale _) (fun _ => rfl))

theorem cross (h : Can true B s (c .left) x f W)
    (k : Can true B s (c .right) x g W) :
    Can true B s (c .both) x (fun i => f i * g i) W :=
  (h.pair k).then_do (Able.atom_one (.cross rfl) (fun _ => rfl))

theorem inv (h : Can m B s sc x f W) (k : ∀ i, f i ≠ 0) :
    Can m B s sc x (fun i => (f i)⁻¹) W :=
  h.then_do (Able.atom_small .inv (Small.const _ 0)
    (fun i => ⟨rfl,le_rfl,le_rfl,k i⟩))

variable {n q : ι → ℕ} {v : ι → Tape (T t)}

theorem look (h : Can m B s (a t) x v W) (k : Can m B s w x n W) :
    Can m B s t x (fun i => (v i).look (n i) t.blank) W :=
  (h.pair k).then_do (Able.atom_one .look (fun _ => rfl))

theorem len (h : Can m B s (a t) x v W) (k : Small B fun i => (v i).len) :
    Can m B s w x (fun i => (v i).len) W := by
  apply h.then_do (Able.atom_small .len k _)
  intro; exact Bill.word_ok le_rfl

theorem nop (h : Can m B s w x n W) (k : Can m B s w x q W)
    (op : NOp) {r : ι → ℕ}
    (hr : ∀ i, op.run (n i,q i) = Bill.word (r i)) (hb : Small B r) :
    Can m B s w x r W := by
  apply (h.pair k).then_do (Able.atom_small (.int op) hb _)
  intro i
  rw [Atom.run]
  change (op.run (n i,q i)).OK _ 1 _
  rw [hr]
  exact Bill.word_ok le_rfl


theorem wadd (h : Can m B s w x n W) (k : Can m B s w x q W)
    (hb : Small B (fun i => n i + q i)) :
    Can m B s w x (fun i => n i + q i) W :=
  h.nop k .add (fun _ => rfl) hb

theorem wsub (h : Can m B s w x n W) (k : Can m B s w x q W)
    (hb : Small B (fun i => n i - q i)) :
    Can m B s w x (fun i => n i - q i) W :=
  h.nop k .sub (fun _ => rfl) hb

theorem wmul (h : Can m B s w x n W) (k : Can m B s w x q W)
    (hb : Small B (fun i => n i * q i)) :
    Can m B s w x (fun i => n i * q i) W :=
  h.nop k .mul (fun _ => rfl) hb

theorem wdiv (h : Can m B s w x n W) (k : Can m B s w x q W)
    (hb : Small B (fun i => n i / q i)) :
    Can m B s w x (fun i => n i / q i) W :=
  h.nop k .div (fun _ => rfl) hb

theorem wmod (h : Can m B s w x n W) (k : Can m B s w x q W)
    (hb : Small B (fun i => n i % q i)) :
    Can m B s w x (fun i => n i % q i) W :=
  h.nop k .mod (fun _ => rfl) hb

theorem wlt (h : Can m B s w x n W) (k : Can m B s w x q W) :
    Can m B s w x (fun i => if n i < q i then 1 else 0) W :=
  h.nop k .lt (fun _ => rfl) ((Small.const B 1).mono (fun i => by split <;> omega))

theorem testz (h : Can m B s w x n W)
    (g : Can m (fun i : {i // n i = 0} => B i.val) s t
      (fun i => x i.val) (fun i => y i.val) (fun i => W i.val))
    (j : Can m (fun i : {i // n i ≠ 0} => B i.val) s t
      (fun i => x i.val) (fun i => y i.val) (fun i => W i.val)) :
    Can m B s t x y W := by
  have H : Can m B s t x y (fun i => W i+W i) :=
    Able.ifz (b:=Bank.closed B) (Z:=fun _ => 0) h g j
  exact H.weaken ((Dom.self W).add (Dom.self W))

variable {uB : ι → ℕ → ℕ}

theorem loop {v : ι → ℕ → T t}
    (h : Can m B s w x n W)
    (hi : Can m B s t x (fun i => v i 0) W')
    (hs : Can m (fun d : During n => B d.i) (p s (p w t)) t
      (fun d => (x d.i,d.j,v d.i d.j)) (fun d => v d.i (d.j+1)) (fun d => uB d.i d.j))
    (hc : Small B n) :
    Can m B s t x (fun i => v i (n i))
      (fun i => W i + W' i + n i + ∑ j ∈ range (n i), uB i j) := by
  have H := Able.loop (b:=Bank.closed B) (v:=v) (Wb:=uB) (Zb:=fun _ _ => 0) h hi hs hc
  simpa [Can] using H

theorem tab {v : ι → ℕ → T t}
    (h : Can m B s w x n W)
    (hs : Can m (fun d : During n => B d.i) (p s w) t
      (fun d => (x d.i,d.j)) (fun d => v d.i d.j) (fun d => uB d.i d.j))
    (hc : Small B n) :
    Can m B s (a t) x (fun i => Tape.tab (n i) (v i))
      (fun i => W i + n i + ∑ j ∈ range (n i), uB i j) := by
  have H := Able.tab (b:=Bank.closed B) (v:=v) (Wb:=uB) (Zb:=fun _ _ => 0) h hs hc
  simpa [Can] using H

theorem sow {v : ι → ℕ → ℕ × T t}
    (hl : Can m B s w x q W')
    (h : Can m B s w x n W)
    (hs : Can m (fun d : During n => B d.i) (p s w) (p w t)
      (fun d => (x d.i,d.j)) (fun d => v d.i d.j) (fun d => uB d.i d.j))
    (hg : Small B q) (hc : Small B n) :
    Can m B s (a t) x (fun i => Tape.sow (q i) (n i) t.blank (v i))
      (fun i => W' i + W i + q i + n i + ∑ j ∈ range (n i), uB i j) := by
  have H := Able.sow (b:=Bank.closed B) (v:=v) (Wb:=uB) (Zb:=fun _ _ => 0) hl h hs hg hc
  simpa [Can] using H

end Can
end PowerSaving.RAM

end OAI
