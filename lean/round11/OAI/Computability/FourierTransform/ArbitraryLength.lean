import OAI.Computability.FourierTransform.PowerTables
import OAI.Computability.FourierTransform.WorkingPreparation

namespace OAI

/- The working length chirp algorithm. Broad branch. -/
namespace PowerSaving.RAM
open Ty Selection Spectral
noncomputable section
namespace Bench
universe U V
variable {ι : Type U} {κ : Type V} {m : Bool} {b : Bench m ι} {q : Bench m κ}
  {s t : Ty} {S n N : ι→ℕ} {ret : Bool}

def surf (d n s : ℕ) := n+leg n+(s+2)^d
lemma surf_deg (s n : ℕ) {c d : ℕ} (h : c≤d) : surf c n s ≤ surf d n s :=
  Nat.add_le_add_left (Small.pow_mono_degree _ h) _

def Swift (b : Bench m ι) (n S : ι→ℕ) (t : Ty) (x : ι→T t) : Prop :=
  ∃ d : ℕ,b.Moves (fun i => surf d (n i) (S i)) t x

namespace Swift
variable {x y : ι→T t}
lemma of_moves {W} (h : b.Moves W t x) (g : Dom n W) :
    b.Swift n S t x :=
  ⟨0,h.weaken ((Dom.of_le fun i => by unfold surf; omega).trans g)⟩
lemma of_dry (h : b.Dry S t x) : b.Swift n S t x :=
  let ⟨d,hd⟩ := h
  ⟨d, hd.mono fun _ => Nat.le_add_left _ _⟩
lemma pair {v : ι→T s} (h : b.Swift n S t x) (g : b.Swift n S s v) :
    b.Swift n S (p t s) fun i => (x i,v i) :=
  let ⟨d,hd⟩ := h
  let ⟨l,hl⟩ := g
  ⟨d+l, (hd.weaken (Dom.of_le fun i => surf_deg (S i) (n i) (by omega))).pair
    (hl.weaken (Dom.of_le fun i => surf_deg (S i) (n i) (by omega)))⟩
lemma bind {v : ι→T s} (h : b.Swift n S t x) (g : (b.extend t x).Swift n S s v) :
    b.Swift n S s v :=
  let ⟨d,hd⟩ := h
  let ⟨l,hl⟩ := g
  ⟨d+l, caseM (hd.weaken (Dom.of_le fun i => surf_deg (S i) (n i) (by omega)))
    (hl.weaken (Dom.of_le fun i => surf_deg (S i) (n i) (by omega)))⟩
end Swift

def tailVol (n : ℕ) : ℕ := (barge n).vol

structure Cruise (b : Bench m ι) (n S N : ι→ℕ) : Prop where
  dims : b.Neaps S n
  port : ∀ i, Ports (n i)
  rootP : b.Dry S sc fun i => root (receipt (n i))
  ac : ∀ i, tailVol (n i)=N i
  sizeL : b.Nick N

lemma signP (ret : Bool) (h : ∀ i,0<n i) (g : b.Dry S sc fun i => root (n i)) :
    b.Dry S sc fun i => pr ret (n i) := by
  cases ret
  · exact g
  · exact g.inv fun i => (root_primitive _ (h i)).ne_zero (Nat.ne_of_gt (h i))

lemma table_scale {x y : ι→Line} {cl} (h : b.Nick N)
    (hx : b.Moves (fun _ => 0) (a sc) fun i => Tape.tab (N i) (x i))
    (hy : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (N i) (y i)) :
    b.Moves N (a (c cl)) fun i => Tape.tab (N i) fun j => x i j*y i j := by
  have F := Instant.scan b N
  refine arrayNow h _ ((Moves.pick (t:=sc) (n:=fun i : During N => N i.i)
    (k:=During.j) (fun i j => x i.i j) (hx.transfer F) (chop h).close During.hj).mul
    (Moves.pick (t:=c cl) (n:=fun i : During N => N i.i) (k:=During.j) (fun i j => y i.i j)
      (hy.transfer F) (chop h).close During.hj))

namespace Cruise
variable {cl : Paint} {x y : ι→Line}

lemma transfer {S n N : κ→ℕ} (h : q.Cruise n S N) {f} (g : b.Instant q f) :
    b.Cruise (fun i => n (f i)) (fun i => S (f i)) (fun i => N (f i)) :=
  ⟨h.dims.transfer g,fun _ => h.port _,h.rootP.transfer g,fun _ => h.ac _,h.sizeL.transfer g⟩

lemma volume_ge (h : b.Cruise n S N) (i) : 2*n i ≤ N i :=
  h.ac i ▸ (barge_spec _ (h.dims.pos i)).lower
lemma volume_lt (h : b.Cruise n S N) (i) : N i < 4*n i :=
  h.ac i ▸ (barge_spec _ (h.dims.pos i)).upper
lemma volume_pos (h : b.Cruise n S N) (i) : 0<N i := by
  have hh := h.volume_ge i; have hk := h.dims.pos i; omega

lemma dom (h : b.Cruise n S N) : Dom n N :=
  ⟨4,fun i => by have := h.volume_lt i; omega⟩

lemma flood (h : b.Cruise n S N) (r : Bool)
    (hx : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (N i) (x i)) :
    b.Swift n S (a (c cl)) fun i => Tape.tab (N i) (freq (N i) (pr r (N i)) (x i)) := by
  let z (i) := pr r (N i)
  have H (i) : (barge (n i)).vol=N i := h.ac i
  have hu := signP r h.volume_pos ((h.dims.mediumP h.port h.rootP).congr fun i =>
    congrArg root (H i))
  obtain ⟨d,hd⟩ := h.dims.streamP h.port h.rootP (z:=z) (x:=x) hu
    (fun i => (H i).symm ▸ show IsPrimitiveRoot (z i) (N i) from primitive_pr _ (h.volume_pos i) r)
    (hx.congr fun i => congrArg (fun u => Tape.tab u (x i)) (H i).symm)
  refine ⟨d,?_⟩
  refine (hd.weaken (Dom.of_le fun i => ?_)).congr fun i => ?_
  · unfold surf; omega
  · rw [H]

lemma flood' (h : b.Cruise n S N) (r : Bool) (hx : b.Swift n S (a (c cl)) fun i =>
    Tape.tab (N i) (x i)) :
    b.Swift n S (a (c cl)) fun i => Tape.tab (N i) (freq (N i) (pr r (N i)) (x i)) := by
  let V (i : ι) : T (a (c cl)) := Tape.tab (N i) (x i)
  exact hx.bind ((h.transfer (Instant.extend b V)).flood r (x:=x) (cherry b V (t:=a (c cl))))

lemma posts (h : b.Cruise n S N) (r : Bool) :
    b.Swift n S (a sc) fun i => tablePow (pr r (2*n i)) (S i) := by
  let z (i) : T sc := pr r (2*n i)
  have hh : b.Swift n S sc z :=
    Swift.of_dry (signP r (fun i => by have := h.dims.pos i; omega)
      (h.dims.etaP h.port h.rootP))
  have F := Instant.extend b z (t:=sc)
  exact hh.bind (Swift.of_moves (pylon (h.dims.tidal.transfer F)
    (g:=h.dims.stackPow) (cherry b z (t:=sc))) ⟨4,fun i => by
    dsimp only [id]
    have hh : 2^S i ≤ 4*n i := h.dims.stack_eq i ▸ stack_pow (n i) (h.dims.pos i); omega⟩)

lemma pearl (h : b.Cruise n S N) (r : Bool)
    (hp : b.Moves (fun _ => 0) (a sc) fun i => tablePow (pr r (2*n i)) (S i))
    {k} (hk : b.Nick k) :
    b.Moves (fun _ => 0) sc fun i => epschirp (pr r (2*n i)) (k i) :=
  square_pow h.dims.stackPow hp ((Nick.wc 2).mul h.dims.num)
    (fun i => ⟨by have := h.dims.pos i; omega,h.dims.stack_eq i ▸ (stack_above (n i)).le⟩)
    (fun i => (primitive_pr (2*n i) (by have := h.dims.pos i; omega) r).pow_eq_one) hk

-- two prep arrays
lemma risen (h : b.Cruise n S N) (r : Bool)
    (hp : b.Moves (fun _ => 0) (a sc) fun i => tablePow (pr r (2*n i)) (S i))
    (hx : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (n i) (x i)) :
    b.Swift n S (a (c cl)) fun i => Tape.tab (N i) (chirp_seed (n i) (pr r (2*n i)) (x i)) := by
  have F := Instant.scan b N
  have hh := h.transfer F
  have hj := chop h.sizeL
  have H := (hh.pearl r (hp.transfer F) hj).mul (pick_all (t:=c cl)
    (n:=fun i : During N => n i.i) (fun (i : During N) j => x i.i j) (hx.transfer F) hj)
  refine Swift.of_moves (arrayNow h.sizeL _ (H.congr fun i => ?_)) h.dom
  simp only [chirp_seed,mul_ite]; congr 1
  exact mul_zero _

lemma fallen (h : b.Cruise n S N) (r : Bool)
    (hp : b.Moves (fun _ => 0) (a sc) fun i => tablePow (pr r (2*n i)) (S i)) :
    b.Swift n S (a sc) fun i => Tape.tab (N i) (fall (n i) (N i) (pr r (2*n i))) := by
  let z i := pr r (2*n i)
  have F := Instant.scan b N
  have hh := h.transfer F
  have hj := chop h.sizeL
  have hg := hh.sizeL.sub hj
  have hk := (((hj.cmp hh.dims.num).branch hg hj)).congr
    (y:=fun i => legdist (n i.i) (N i.i) i.j) (fun i => by
    by_cases e : i.j < n i.i <;> simp [legdist,e])
  refine Swift.of_moves (arrayNow h.sizeL _ ((hh.pearl r (hp.transfer F) hk).inv fun i => ?_)) h.dom
  have Hu : 0<2*n i.i := by have := h.dims.pos i.i; omega
  exact pow_ne_zero _ ((primitive_pr _ Hu r).ne_zero (Nat.ne_of_gt Hu))

lemma pyramid (h : b.Cruise n S N) (r : Bool)
    (hp : b.Moves (fun _ => 0) (a sc) fun i => tablePow (pr r (2*n i)) (S i))
    (hx : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (n i) (x i)) :
    b.Swift n S (a (c cl)) fun i =>
      Tape.tab (N i) (fetchC (N i) (pr false (N i))
        (fall (n i) (N i) (pr r (2*n i)))
        (chirp_seed (n i) (pr r (2*n i)) (x i))) := by
  let z i := pr r (2*n i)
  let A i := freq (N i) (pr false (N i)) (fall (n i) (N i) (z i))
  let B i := freq (N i) (pr false (N i)) (chirp_seed (n i) (z i) (x i))
  let V (i) : T (p (a sc) (a (c cl))) := (Tape.tab (N i) (A i),Tape.tab (N i) (B i))
  have H := (h.flood' false (h.fallen r hp)).pair (h.flood' false (h.risen r hp hx))
  have F := Instant.extend b V
  have hk := cherry b V (W:=fun _ => 0)
  exact h.flood' true (x:=fun i => pointC (N i) (pr false (N i))
        (fall (n i) (N i) (z i)) (chirp_seed (n i) (z i) (x i)))
    (H.bind (Swift.of_moves (table_scale (h.sizeL.transfer F) (x:=A) (y:=B) hk.fst hk.snd) h.dom))

lemma singing (h : b.Cruise n S N) (r : Bool)
    (hp : b.Moves (fun _ => 0) (a sc) fun i => tablePow (pr r (2*n i)) (S i))
    (hx : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (n i) (x i)) :
    b.Swift n S (a (c cl)) fun i =>
      Tape.tab (n i) (freq (n i) (pr r (n i)) (x i)) := by
  let z i := pr r (2*n i)
  let B i := fetchC (N i) (pr false (N i)) (fall (n i) (N i) (z i))
    (chirp_seed (n i) (z i) (x i))
  have H := Swift.pair (h.pyramid r hp hx) (Swift.of_moves h.sizeL.numeralM h.dom)
  let V (i : ι) : T (p (a (c cl)) sc) := (Tape.tab (N i) (B i),(N i:ℂ))
  have F := Instant.extend b V
  have G := Instant.scan (b.extend _ V) n
  have hh := h.transfer (G.next F)
  have hk := Moves.transfer (cherry b V (W:=fun _ => 0)) G
  have hj := h.dims.num.transfer F
  have HL := chop hj
  have HS := Moves.pick (n:=fun i : During n => N i.i) (k:=During.j) (t:=c cl)
    (fun i => B i.i) hk.fst HL.close (fun i => by
      have hh := h.volume_ge i.i; have hk := i.hj; omega)
  have hd := (hh.pearl r (hp.transfer (G.next F)) HL).mul
    ((hk.snd.inv fun i => Nat.cast_ne_zero.mpr (Nat.ne_of_gt (h.volume_pos i.i))).mul HS)
  exact H.bind (Swift.of_moves (arrayNow hj _ (hd.congr fun i =>
    chirps _ _ (h.dims.pos i.i) (h.volume_ge i.i) r _ _ i.hj)) (Dom.self n))

lemma deliver (h : b.Cruise n S N) (r : Bool)
    (hx : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (n i) (x i)) :
    b.Swift n S (a (c cl)) fun i =>
      Tape.tab (n i) (freq (n i) (pr r (n i)) (x i)) := by
  let V i := tablePow (pr r (2*n i)) (S i)
  have F := Instant.extend b V (t:=a sc)
  exact (h.posts r).bind ((h.transfer F).singing r (cherry b V (t:=a sc)) (hx.transfer F))

end Cruise

lemma Neaps.swift (h : b.Neaps S n) (g : ∀ i,Ports (n i))
    (hz : b.Dry S sc fun i => root (receipt (n i))) (r : Bool)
    {x : ι→Line} {cl} (hx : b.Moves (fun _ => 0) (a (c cl)) fun i =>
      Tape.tab (n i) (x i)) :
    b.Swift n S (a (c cl)) fun i =>
      Tape.tab (n i) (freq (n i) (pr r (n i)) (x i)) := by
  let N i := tailVol (n i)
  have F := Instant.extend b N (t:=w)
  have hh : (b.extend w N).Cruise n S N :=
    ⟨h.transfer F,g,hz.transfer F,fun i => rfl,⟨cherry b N (t:=w),h.bargeL.volume⟩⟩
  exact (Swift.of_dry h.bargeL.volL.dry).bind (hh.deliver r (hx.transfer F))

end Bench
end
end PowerSaving.RAM

end OAI
