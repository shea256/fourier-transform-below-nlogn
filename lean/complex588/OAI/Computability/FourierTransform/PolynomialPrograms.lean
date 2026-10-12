import OAI.Computability.FourierTransform.ProgramConstruction

namespace OAI

namespace PowerSaving.RAM
open Ty Finset

universe U V

/-- One algorithm; time is polynomial in (S+2), integer bounds polynomial in (B+2). Often
  S polylogarithmic in B. -/
def PolyCan {ι : Type U} (m : Bool) (B S : ι → ℕ) (s t) (x : ι → T s) (y : ι → T t) : Prop :=
  ∃ d : ℕ, Can m B s t x y (fun i => (S i+2)^d)

namespace PolyCan
variable {ι : Type U} {κ : Type V}
  {m : Bool} {s t u : Ty}
  {B S B' S' W : ι → ℕ}
  {x : ι → T s} {y : ι → T t} {z : ι → T u}

theorem of_can (h : Can m B s t x y W) (g : Small S W) :
    PolyCan m B S s t x y :=
  let ⟨d,hd⟩ := g
  ⟨d,h.mono hd⟩

theorem cong (h : PolyCan m B S s t x y) {x' y'} (hx : ∀ i, x i = x' i)
    (hy : ∀ i, y i = y' i) : PolyCan m B S s t x' y' :=
  let ⟨d, hd⟩ := h
  ⟨d,hd.cong hx hy⟩

theorem reindex (h : PolyCan m B S s t x y) (f : κ → ι) :
    PolyCan m (fun j => B (f j)) (fun j => S (f j)) s t (fun j => x (f j)) (fun j => y (f j)) :=
  let ⟨d,hd⟩ := h
  ⟨d,hd.reindex f⟩

theorem poly_power (S : ι → ℕ) (d : ℕ) : Small S (fun i => (S i+2)^d) :=
  ⟨d,fun _ => le_rfl⟩

theorem weaken (h : PolyCan m B S s t x y) (a : Small B' B) (b : Small S' S) :
    PolyCan m B' S' s t x y :=
  let ⟨d,hd⟩ := h
  of_can (hd.ambient a) ((poly_power S d).trans b)

theorem pipe (h : PolyCan m B S s t x y) (g : PolyCan m B S t u y z) :
    PolyCan m B S s u x z :=
  let ⟨d,hd⟩ := h
  let ⟨e,he⟩ := g
  of_can (hd.pipe he) ((poly_power S d).add (poly_power S e))

theorem pair (h : PolyCan m B S s t x y) (g : PolyCan m B S s u x z) :
    PolyCan m B S s (p t u) x (fun i => (y i,z i)) :=
  let ⟨d,hd⟩ := h
  let ⟨e,he⟩ := g
  of_can (hd.fork he) ((poly_power S d).add (poly_power S e))

theorem bind (h : PolyCan m B S s t x y)
    (g : PolyCan m B S (p s t) u (fun i => (x i,y i)) z) :
    PolyCan m B S s u x z :=
  let ⟨d,hd⟩ := h
  let ⟨e,he⟩ := g
  of_can (hd.save he) ((poly_power S d).add (poly_power S e))

theorem id : PolyCan m B S s s x x :=
  ⟨1,Can.id⟩

theorem fst {v : ι → T (p t u)} (h : PolyCan m B S s (p t u) x v) :
    PolyCan m B S s t x (fun i => (v i).1) :=
  let ⟨d,hd⟩ := h
  ⟨d,hd.fst⟩

theorem snd {v : ι → T (p t u)} (h : PolyCan m B S s (p t u) x v) :
    PolyCan m B S s u x (fun i => (v i).2) :=
  let ⟨d,hd⟩ := h
  ⟨d,hd.snd⟩

theorem first {x : ι → T (p t u)} : PolyCan m B S (p t u) t x (fun i => (x i).1) :=
  id.fst

theorem second {x : ι → T (p t u)} : PolyCan m B S (p t u) u x (fun i => (x i).2) :=
  id.snd

theorem wc (n : ℕ) : PolyCan m B S s w x (fun _ => n) := ⟨1,Can.wc _⟩

theorem zero {cl} : PolyCan m B S s (c cl) x (fun _ => 0) := ⟨1,Can.zero⟩

theorem one : PolyCan m B S s sc x (fun _ => 1) := ⟨1,Can.one⟩

variable {cl : Paint} {f g : ι → ℂ}

theorem add (h : PolyCan m B S s (c cl) x f)
    (k : PolyCan m B S s (c cl) x g) :
    PolyCan m B S s (c cl) x (fun i => f i + g i) :=
  (h.pair k).pipe ⟨1,Can.add Can.first Can.second⟩

theorem sub (h : PolyCan m B S s (c cl) x f)
    (k : PolyCan m B S s (c cl) x g) :
    PolyCan m B S s (c cl) x (fun i => f i - g i) :=
  (h.pair k).pipe ⟨1,Can.sub Can.first Can.second⟩

theorem mul (h : PolyCan m B S s sc x f)
    (k : PolyCan m B S s (c cl) x g) :
    PolyCan m B S s (c cl) x (fun i => f i * g i) :=
  (h.pair k).pipe ⟨1,Can.mul Can.first Can.second⟩

theorem inv (h : PolyCan m B S s sc x f) (hk : ∀ i, f i ≠ 0) :
    PolyCan m B S s sc x (fun i => (f i)⁻¹) :=
  h.pipe ⟨1,Can.inv Can.id hk⟩

variable {n q : ι → ℕ} {v : ι → Tape (T t)}

theorem look (h : PolyCan m B S s (a t) x v) (k : PolyCan m B S s w x n) :
    PolyCan m B S s t x (fun i => (v i).look (n i) t.blank) :=
  (h.pair k).pipe ⟨1,Can.look Can.first Can.second⟩

theorem len (h : PolyCan m B S s (a t) x v) (k : Small B fun i => (v i).len) :
    PolyCan m B S s w x (fun i => (v i).len) :=
  h.pipe ⟨1,Can.len Can.id k⟩


theorem wadd (h : PolyCan m B S s w x n) (k : PolyCan m B S s w x q)
    (hb : Small B (fun i => n i + q i)) :
    PolyCan m B S s w x (fun i => n i + q i) :=
  (h.pair k).pipe ⟨1,Can.wadd Can.first Can.second hb⟩

theorem wsub (h : PolyCan m B S s w x n) (k : PolyCan m B S s w x q)
    (hb : Small B (fun i => n i - q i)) :
    PolyCan m B S s w x (fun i => n i - q i) :=
  (h.pair k).pipe ⟨1,Can.wsub Can.first Can.second hb⟩

theorem wmul (h : PolyCan m B S s w x n) (k : PolyCan m B S s w x q)
    (hb : Small B (fun i => n i * q i)) :
    PolyCan m B S s w x (fun i => n i * q i) :=
  (h.pair k).pipe ⟨1,Can.wmul Can.first Can.second hb⟩

theorem wdiv (h : PolyCan m B S s w x n) (k : PolyCan m B S s w x q)
    (hb : Small B (fun i => n i / q i)) :
    PolyCan m B S s w x (fun i => n i / q i) :=
  (h.pair k).pipe ⟨1,Can.wdiv Can.first Can.second hb⟩

theorem wmod (h : PolyCan m B S s w x n) (k : PolyCan m B S s w x q)
    (hb : Small B (fun i => n i % q i)) :
    PolyCan m B S s w x (fun i => n i % q i) :=
  (h.pair k).pipe ⟨1,Can.wmod Can.first Can.second hb⟩

theorem wlt (h : PolyCan m B S s w x n) (k : PolyCan m B S s w x q) :
    PolyCan m B S s w x (fun i => if n i < q i then 1 else 0) :=
  (h.pair k).pipe ⟨1,Can.wlt Can.first Can.second⟩

theorem loop {v : ι → ℕ → T t}
    (h : PolyCan m B S s w x n)
    (hi : PolyCan m B S s t x (fun i => v i 0))
    (hs : PolyCan m (fun d : During n => B d.i) (fun d => S d.i)
      (p s (p w t)) t
      (fun d => (x d.i,d.j,v d.i d.j)) (fun d => v d.i (d.j+1)))
    (hc : Small B n) (hd : Small S n) :
    PolyCan m B S s t x (fun i => v i (n i)) := by
  obtain ⟨u,hu⟩ := h
  obtain ⟨l,hl⟩ := hi
  obtain ⟨f,hf⟩ := hs
  refine of_can (Can.loop (v:=v) (uB:=fun i _ => (S i+2)^f) hu hl hf hc) ?_
  simpa using (((poly_power S u).add (poly_power S l)).add hd).add (hd.mul (poly_power S f))

theorem tab {v : ι → ℕ → T t}
    (h : PolyCan m B S s w x n)
    (hs : PolyCan m (fun d : During n => B d.i) (fun d => S d.i)
      (p s w) t (fun d => (x d.i,d.j)) (fun d => v d.i d.j))
    (hc : Small B n) (hd : Small S n) :
    PolyCan m B S s (a t) x (fun i => Tape.tab (n i) (v i)) := by
  obtain ⟨u,hu⟩ := h
  obtain ⟨f,hf⟩ := hs
  refine of_can (Can.tab (v:=v) (uB:=fun i _ => (S i+2)^f) hu hf hc) ?_
  simpa using ((poly_power S u).add hd).add (hd.mul (poly_power S f))

theorem sow {v : ι → ℕ → ℕ × T t}
    (hl : PolyCan m B S s w x q)
    (h : PolyCan m B S s w x n)
    (hs : PolyCan m (fun d : During n => B d.i) (fun d => S d.i)
      (p s w) (p w t) (fun d => (x d.i,d.j)) (fun d => v d.i d.j))
    (hg : Small B q) (hc : Small B n) (hf : Small S q) (hd : Small S n) :
    PolyCan m B S s (a t) x (fun i => Tape.sow (q i) (n i) t.blank (v i)) := by
  obtain ⟨l,hl⟩ := hl
  obtain ⟨u,hu⟩ := h
  obtain ⟨k,hk⟩ := hs
  refine of_can (Can.sow (v:=v) (uB:=fun i _ => (S i+2)^k) hl hu hk hg hc) ?_
  simpa using ((((poly_power S l).add (poly_power S u)).add hf).add hd).add
    (hd.mul (poly_power S k))

theorem testz (h : PolyCan m B S s w x n)
    (g : PolyCan m (fun i : {i // n i = 0} => B i.val) (fun i => S i.val) s t
      (fun i => x i.val) (fun i => y i.val))
    (j : PolyCan m (fun i : {i // n i ≠ 0} => B i.val) (fun i => S i.val) s t
      (fun i => x i.val) (fun i => y i.val)) :
    PolyCan m B S s t x y := by
  obtain ⟨l,hl⟩ := h
  obtain ⟨u,hu⟩ := g
  obtain ⟨k,hk⟩ := j
  refine ⟨l+u+k,Can.testz (n:=n) (hl.mono ?_) (hu.mono ?_) (hk.mono ?_)⟩ <;>
    intro i <;> apply Small.pow_mono_degree <;> omega

end PolyCan
end PowerSaving.RAM

end OAI
