import OAI.Computability.FourierTransform.ParameterPrograms

namespace OAI

/- Poly-log preparation combinators. Cost polynomial in S, integer sizes in Bench.size. -/
namespace PowerSaving.RAM
open Ty
noncomputable section

universe U V

namespace Bench
variable {m : Bool} {ι : Type U} {κ : Type V} {b : Bench m ι} {q : Bench m κ} {s t : Ty}

def Dry (b : Bench m ι) (S : ι→ℕ) (t : Ty) (f : ι→T t) : Prop :=
  PolyCan m b.size S b.tray t b.env f

structure Grain (b : Bench m ι) (S f : ι→ℕ) : Prop where
  dry : b.Dry S w f
  small : Small b.size f

variable {S : ι→ℕ}

lemma Moves.dry {W x} (h : b.Moves W t x) (g : Small S W) :
    b.Dry S t x := PolyCan.of_can h g
lemma Moves.dunes {x} (h : b.Moves (fun _ => 0) t x) (S : ι→ℕ) :
    b.Dry S t x := h.dry (Small.const _ 0)
lemma Nick.grain {x} (h : b.Nick x) (S : ι→ℕ) :
    b.Grain S x := ⟨h.close.dunes S,h.small⟩

namespace Dry
variable {x y : ι→T t}

lemma congr (h : b.Dry S t x) (g : ∀ i, x i=y i) :
    b.Dry S t y := by rwa [← funext g]
lemma pair {v : ι→T s} (h : b.Dry S t x) (g : b.Dry S s v) :
    b.Dry S (p t s) fun i => (x i,v i) := PolyCan.pair h g
lemma fst {v : ι→T (p s t)} (h : b.Dry S (p s t) v) :
    b.Dry S s fun i => (v i).1 := PolyCan.fst h
lemma snd {v : ι→T (p s t)} (h : b.Dry S (p s t) v) :
    b.Dry S t fun i => (v i).2 := PolyCan.snd h
lemma wc (n : ℕ) : b.Dry S w fun _ => n := PolyCan.wc n
lemma one : b.Dry S sc fun _ => 1 := PolyCan.one
lemma mul {cl} {x y : ι→ℂ} (h : b.Dry S sc x) (g : b.Dry S (c cl) y) :
    b.Dry S (c cl) fun i => x i*y i := PolyCan.mul h g
lemma inv {x : ι→ℂ} (h : b.Dry S sc x) (g : ∀ i, x i≠0) :
    b.Dry S sc fun i => (x i)⁻¹ := PolyCan.inv h g
lemma transfer {f : ι→κ} {S : κ→ℕ} {x : κ→T t} (h : q.Dry S t x) (g : b.Instant q f) :
    b.Dry (fun i => S (f i)) t fun i => x (f i) :=
  PolyCan.pipe (g.prep.dunes _) (PolyCan.weaken (PolyCan.reindex h f) g.covers (Small.self _))
lemma together {v : ι→T s} (h : b.Dry S t x) (g : (b.extend t x).Dry S s v) :
    b.Dry S s v := PolyCan.bind h g
lemma look {x : ι→Tape (T t)} {n} (h : b.Dry S (a t) x) (g : b.Dry S w n) :
    b.Dry S t fun i => (x i).look (n i) t.blank := PolyCan.look h g
lemma pick {x : ι→ℕ→T t} {n k : ι→ℕ} (h : b.Dry S (a t) fun i => Tape.tab (n i) (x i))
    (g : b.Dry S w k) (hk : ∀ i,k i<n i) :
    b.Dry S t fun i => x i (k i) :=
  (h.look g).congr fun i => by rw [Tape.look_tab, ite_eq_left (hk i)]
lemma testz {f} (h : b.Dry S w f)
    (g : (b.along (Subtype.val (p:=fun i => f i = 0))).Dry (fun i => S i.val) t fun i => x i.val)
    (j : (b.along (Subtype.val (p:=fun i => f i ≠ 0))).Dry (fun i => S i.val) t fun i => x i.val) :
    b.Dry S t x := PolyCan.testz h g j
lemma branch {f} (h : b.Dry S w f) (g : b.Dry S t x) (j : b.Dry S t y) :
    b.Dry S t fun i => if f i = 0 then x i else y i := by
  refine testz h ?_ ?_
  · exact (g.transfer (Instant.along b (Subtype.val (p:=fun i => f i = 0)))).congr
      fun i => (ite_eq_left i.property).symm
  · exact (j.transfer (Instant.along b (Subtype.val (p:=fun i => f i ≠ 0)))).congr
      fun i => (ite_eq_right i.property).symm
end Dry
namespace Grain
variable {x y : ι→ℕ}

lemma wc (n : ℕ) : b.Grain S fun _ => n := (Nick.wc n).grain _
lemma add (h : b.Grain S x) (g : b.Grain S y) :
    b.Grain S fun i => x i+y i :=
  ⟨PolyCan.wadd h.dry g.dry (h.small.add g.small),h.small.add g.small⟩
lemma sub (h : b.Grain S x) (g : b.Grain S y) :
    b.Grain S fun i => x i-y i :=
  ⟨PolyCan.wsub h.dry g.dry h.small.sub,h.small.sub⟩
lemma mul (h : b.Grain S x) (g : b.Grain S y) :
    b.Grain S fun i => x i*y i :=
  ⟨PolyCan.wmul h.dry g.dry (h.small.mul g.small),h.small.mul g.small⟩
lemma div (h : b.Grain S x) (g : b.Grain S y) :
    b.Grain S fun i => x i/y i :=
  ⟨PolyCan.wdiv h.dry g.dry h.small.div,h.small.div⟩
lemma residue (h : b.Grain S x) (g : b.Grain S y) :
    b.Grain S fun i => x i%y i :=
  ⟨PolyCan.wmod h.dry g.dry h.small.mod,h.small.mod⟩
lemma cmp (h : b.Grain S x) (g : b.Grain S y) :
    b.Grain S fun i => if x i<y i then 1 else 0 :=
  ⟨PolyCan.wlt h.dry g.dry,(Small.const _ 1).mono fun i => by split <;> omega⟩
lemma congr (h : b.Grain S x) (g : ∀ i,x i=y i) :
    b.Grain S y := by rwa [← funext g]
lemma transfer {f : ι→κ} {S x : κ→ℕ} (h : q.Grain S x) (g : b.Instant q f) :
    b.Grain (fun i => S (f i)) fun i => x (f i) :=
  ⟨h.dry.transfer g,(h.small.reindex _).trans g.covers⟩
lemma logtwo (h : b.Grain S x) (g : Small S x) :
    b.Grain S fun i => Nat.log 2 (x i) := by
  have hh : (b.extend w x).Nick x := ⟨cherry (t:=w) b x,h.small⟩
  exact ⟨h.dry.together (hh.logM.dry g),h.small.mono fun i => Nat.log_le_self 2 _⟩
end Grain

variable {n : ι→ℕ}
lemma strideG (h : b.Grain S n) (x : ι → ℕ → T t) :
    (b.climbs n t x).Grain (fun i => S i.i) During.j :=
  ⟨PolyCan.fst PolyCan.second,
    (h.small.reindex During.i).mono (fun i : During n => i.hj.le)⟩
lemma chopG (h : b.Grain S n) :
    (b.scan n).Grain (fun i => S i.i) During.j :=
  ⟨PolyCan.second,(h.small.reindex During.i).mono (fun i : During n => i.hj.le)⟩

lemma Dry.token (b : Bench m ι) (n S : ι→ℕ) (x : ι → ℕ → T t) :
    (b.climbs n t x).Dry (fun i => S i.i) t fun i => x i.i i.j :=
  (tokenNow b n x).dunes _

lemma cycleG (h : b.Grain S n) (k : Small S n) (x : ι → ℕ → T t)
    (g : b.Dry S t fun i => x i 0)
    (j : (b.climbs n t x).Dry (fun i => S i.i) t fun i => x i.i (i.j+1)) :
    b.Dry S t fun i => x i (n i) :=
  PolyCan.loop h.dry g j h.small k

lemma arrayG (h : b.Grain S n) (k : Small S n) (x : ι→ℕ→T t)
    (g : (b.scan n).Dry (fun i => S i.i) t fun i => x i.i i.j) :
    b.Dry S (a t) fun i => Tape.tab (n i) (x i) := PolyCan.tab h.dry g h.small k

lemma Grain.twoPow (h : b.Grain S n) (k : Small S n)
    (j : Small b.size fun i => 2^n i) :
    b.Grain S fun i => 2^n i := by
  let v (i : ι) (a : ℕ) : T w := 2^a
  let D := b.climbs n w v
  have hh : D.Grain (fun i => S i.i) fun i => v i.i i.j :=
    ⟨Dry.token b n S v,
      (j.reindex During.i).mono fun i => Nat.pow_le_pow_right (by omega) i.hj.le⟩
  refine ⟨cycleG h k v ?_ ((hh.mul (wc 2)).dry.congr fun i => (pow_succ _ _).symm),j⟩
  simpa only [v,pow_zero] using Dry.wc (b:=b) (S:=S) 1

end Bench
end
end PowerSaving.RAM

end OAI
