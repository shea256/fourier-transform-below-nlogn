import OAI.Computability.FourierTransform.ArbitraryLength

namespace OAI

/- All-length including direct initial. -/
namespace PowerSaving.RAM
open Ty Selection Spectral Finset
noncomputable section
namespace Bench
universe U V
variable {ι : Type U} {κ : Type V} {m : Bool} {b : Bench m ι} {q : Bench m κ}
  {s t : Ty} {n N k : ι→ℕ} {ret : Bool}

lemma Dry.linearPow (h : b.Grain N k) (g : Small N k) {z : ι→ℂ} (hz : b.Dry N sc z) :
    b.Dry N sc fun i => z i^k i := by
  let V (i : ι) (j : ℕ) : T sc := z i^j
  have F := Instant.climbs b k V (t:=sc)
  refine cycleG h g V (one.congr fun i => (pow_zero _).symm)
    (((Dry.token b k N V (t:=sc)).mul (hz.transfer F)).congr fun i => (pow_succ _ _).symm)

-- polynomial direct branch, N^d
lemma Dry.dire (h : b.Nick N)
    {x : ι→Line} {cl} (hx : b.Dry N (a (c cl)) fun i => Tape.tab (N i) (x i))
    {z : ι→ℂ} (hz : b.Dry N sc z) :
    b.Dry N (a (c cl)) fun i => Tape.tab (N i) (freq (N i) (z i) (x i)) := by
  let D := b.scan N
  have H := Small.self N
  have F := Instant.scan b N
  let K (i : During N) := N i.i
  let V (i : During N) (j : ℕ) : T (c cl) :=
    ∑ k ∈ range j, z i.i^(i.j*k)*x i.i k
  have hk : D.Grain K K := (h.transfer F).grain _
  have G := Instant.climbs D K V (t:=c cl)
  have hj := ((chop h).grain K).transfer G
  have hp := strideG hk V
  have hA : Small (fun i : During K => K i.i) fun i => i.i.j*i.j :=
    (((Small.self K).pow 2).reindex _).mono fun i => by
      rw [pow_two]
      exact Nat.mul_le_mul i.i.hj.le i.hj.le
  have ht := (linearPow (hj.mul hp) hA (hz.transfer (G.next F))).mul
    (Dry.pick (t:=c cl) (x:=fun (i : During K) j => x i.i.i j)
      (n:=fun i : During K => N i.i.i) (k:=During.j)
      (hx.transfer (G.next F)) hp.dry During.hj)
  exact arrayG (h.grain N) H _ (cycleG hk (Small.self K) V (by
    simp only [V,range_zero,sum_empty]; exact PolyCan.zero)
    (Dry.congr (b:=D.climbs K _ V) (S:=fun (i : During K) => K i.i) (t:=c cl)
      (PolyCan.add (Dry.token D K K V (t:=c cl)) ht) fun i => (sum_range_succ ..).symm))

def fairwind (d n : ℕ) := surf d n (stackN n) +
  (if Ports n then 0 else (n+2)^d)

lemma fairwind_deg {c d : ℕ} (n : ℕ) (h : c≤d) : fairwind c n≤fairwind d n := by
  unfold fairwind
  refine add_le_add (surf_deg _ _ h) ?_
  split
  · exact le_rfl
  · exact Small.pow_mono_degree n h
lemma fairwind_left (n d : ℕ) : n + (stackN n+2)^d ≤ fairwind d n := by unfold fairwind surf; omega
lemma fairwind_n (n d : ℕ) : n≤fairwind d n := (Nat.le_add_right _ _).trans (fairwind_left n d)

def Breezy (b : Bench m ι) (n : ι→ℕ) (t : Ty) (x : ι→T t) : Prop :=
  ∃ d : ℕ,b.Moves (fun i => fairwind d (n i)) t x

namespace Breezy
variable {x y : ι→T t}
lemma of_moves {W} (h : b.Moves W t x) (g : Dom n W) : b.Breezy n t x :=
  ⟨0,h.weaken ((Dom.of_le fun i => fairwind_n (n i) 0).trans g)⟩
lemma congr (h : b.Breezy n t x) (g : ∀ i, x i=y i) : b.Breezy n t y :=
  let ⟨d,hd⟩ := h
  ⟨d,hd.congr g⟩
lemma pair {v : ι→T s} (h : b.Breezy n t x) (g : b.Breezy n s v) :
    b.Breezy n (p t s) fun i => (x i,v i) :=
  let ⟨d,hd⟩ := h
  let ⟨l,hl⟩ := g
  ⟨d+l, (hd.weaken (Dom.of_le fun i => fairwind_deg (n i) (by omega))).pair
    (hl.weaken (Dom.of_le fun i => fairwind_deg (n i) (by omega)))⟩
lemma bind {v : ι→T s} (h : b.Breezy n t x) (g : (b.extend t x).Breezy n s v) :
    b.Breezy n s v :=
  let ⟨d,hd⟩ := h
  let ⟨l,hl⟩ := g
  ⟨d+l, caseM (hd.weaken (Dom.of_le fun i => fairwind_deg (n i) (by omega)))
    (hl.weaken (Dom.of_le fun i => fairwind_deg (n i) (by omega)))⟩
lemma flagtest {f : ι→ℕ} (h : b.Breezy n w f)
    (g : (b.along (Subtype.val (p:=fun i => f i = 0))).Breezy (fun i => n i.val) t fun i => x i.val)
    (j : (b.along (Subtype.val (p:=fun i => f i ≠ 0))).Breezy (fun i => n i.val) t fun i => x i.val) :
    b.Breezy n t x := by
  obtain ⟨d,hd⟩ := h
  obtain ⟨l,hl⟩ := g
  obtain ⟨k,hk⟩ := j
  let s := d+l+k
  refine ⟨s,Can.testz (W:=fun i => fairwind s (n i)) (n:=f) ?_ ?_ ?_⟩
  · exact Can.mono hd (fun i => fairwind_deg _ (by unfold s; omega))
  · exact Can.mono hl (fun i => fairwind_deg _ (by unfold s; omega))
  · exact Can.mono hk (fun i => fairwind_deg _ (by unfold s; omega))
end Breezy

lemma Neaps.course (h : b.Neaps (fun i => stackN (n i)) n)
    (hz : b.Moves (fun _ => 0) sc fun i => root (receipt (n i)))
    (r : Bool) {x : ι→Line} {cl} (hx : b.Moves (fun _ => 0) (a (c cl)) fun i =>
      Tape.tab (n i) (x i)) :
    b.Breezy n (a (c cl)) fun i => Tape.tab (n i) (freq (n i) (pr r (n i)) (x i)) := by
  let f (i : ι) := if Ports (n i) then 0 else 1
  have HH : b.Breezy n w f := by
    obtain ⟨d,hd⟩ := h.portG.dry
    exact ⟨d,hd.mono fun i => (Nat.le_add_left _ _).trans (fairwind_left _ d)⟩
  refine Breezy.flagtest HH ?_ ?_
  · let P i := f i=0
    have F := Instant.along b (Subtype.val (p:=P))
    have hp : ∀ i : Subtype P, Ports (n i.val) := fun i => by
      by_contra k; have hi : f i.val=0 := i.property; simp [f,k] at hi
    obtain ⟨d,hd⟩ := (h.transfer F).swift hp ((hz.transfer F).dunes _) r (hx.transfer F)
    exact ⟨d,hd.weaken (Dom.of_le fun i => Nat.le_add_right _ _)⟩
  · let P i := f i≠0
    have F := Instant.along b (Subtype.val (p:=P))
    have hp : ∀ i : Subtype P, ¬ Ports (n i.val) := fun i g => i.property (by simp [f,g])
    let H := h.transfer F
    have ht := signP r H.pos ((hz.transfer F).dunes (fun i => n i.val) |>.congr
      (y:=fun i : Subtype P => root (n i.val)) fun i => by rw [receipt,ite_eq_right (hp i)])
    obtain ⟨d,hd⟩ := Dry.dire H.num ((hx.transfer F).dunes _) ht
    exact ⟨d,Can.mono hd (fun i => by unfold fairwind; rw [ite_eq_right (hp i)]; exact Nat.le_add_left _ _)⟩

lemma Nick.landOrder (h : b.Nick N) (g : ∀ i, 0<N i) :
    b.Breezy N w fun i => receipt (N i) :=
  let ⟨d,hd⟩ := h.planOrder g
  ⟨d, hd.weaken (Dom.of_le fun i => fairwind_left (N i) d)⟩
lemma Nick.land (h : b.Nick N) (g : ∀ i, 0<N i)
    (hz : b.Moves (fun _ => 0) sc fun i => root (receipt (N i)))
    (r : Bool) {x : ι→Line} {cl} (hx : b.Moves (fun _ => 0) (a (c cl)) fun i =>
      Tape.tab (N i) (x i)) :
    b.Breezy N (a (c cl)) fun i => Tape.tab (N i) (freq (N i) (pr r (N i)) (x i)) := by
  obtain ⟨hu,hk⟩ := h.stackH g
  have H := Instant.extend b (fun i => stackN (N i)) (t:=w)
  exact (Breezy.of_moves hu (Dom.self N)).bind (hk.course (hz.transfer H) r (hx.transfer H))
lemma Nick.land' (h : b.Nick N) (g : ∀ i, 0<N i)
    (hz : b.Moves (fun _ => 0) sc fun i => root (receipt (N i)))
    (r : Bool) {x : ι→Line} {cl} (hx : b.Breezy N (a (c cl)) fun i =>
      Tape.tab (N i) (x i)) :
    b.Breezy N (a (c cl)) fun i => Tape.tab (N i) (freq (N i) (pr r (N i)) (x i)) := by
  let V (i : ι) : T (a (c cl)) := Tape.tab (N i) (x i)
  have F := Instant.extend b V (t:=a (c cl))
  exact hx.bind ((h.transfer F).land g (hz.transfer F) r (x:=x) (cherry b V (t:=a (c cl))))
end Bench
end
end PowerSaving.RAM

end OAI
