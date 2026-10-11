import OAI.Computability.FourierTransform.RootPreparation
import OAI.Computability.FourierTransform.WorkingCompiler

namespace OAI

/- Binary powers for the index and coefficient preparatory scan, and application of
synchronized working transform. -/
namespace PowerSaving.RAM
open Ty Selection Grove Spectral
noncomputable section

namespace Bench
universe U V
variable {ι : Type U} {κ : Type V} {m : Bool} {b : Bench m ι} {q : Bench m κ}
  {n k S : ι→ℕ} {t : Ty}

-- count halving powers
abbrev shiftTy := p w (p sc sc)
def shiftP (n : ℕ) (x : ℂ) : ℕ→T shiftTy
  | 0 => (n,x,1)
  | j+1 =>
    let (s,u,b) := shiftP n x j
    (s/2,u*u, if s%2=0 then b else b*u)

namespace shiftP
lemma stepP (n : ℕ) (x : ℂ) (j : ℕ) :
    shiftP n x (j+1)=((shiftP n x j).1/2,(shiftP n x j).2.1*(shiftP n x j).2.1,
      if (shiftP n x j).1%2=0 then (shiftP n x j).2.2
      else (shiftP n x j).2.2*(shiftP n x j).2.1) := rfl

lemma real (n : ℕ) (x : ℂ) (j : ℕ) :
    (shiftP n x j).2.2 * (shiftP n x j).2.1^(shiftP n x j).1=x^n := by
  induction j with
  | zero => exact one_mul _
  | succ j ih =>
    let s : ℕ := (shiftP n x j).1
    let a := (shiftP n x j).2.1
    let b := (shiftP n x j).2.2
    rw [stepP]; rw [← ih]
    change (if s%2=0 then b else b*a)*(a*a)^(s/2)=b*a^s
    rw [← pow_two,← pow_mul]
    split
    · rename_i H; rw [show 2*(s/2)=s by omega]
    · rename_i H; rw [mul_assoc,show a * a ^ (2*(s/2)) = a^s by
        simpa only [pow_succ'] using
          (show a^(2*(s/2)+1)=a^s by rw [show 2*(s/2)+1=s by omega])]
lemma countP (n : ℕ) (x : ℂ) (j : ℕ) :
    (shiftP n x j).1=n/2^j := by
  induction j with
  | zero => simp [shiftP]
  | succ j ih => rw [stepP]; simp [ih,Nat.div_div_eq_div_mul,pow_succ]

lemma endP (n : ℕ) (x : ℂ) (j : ℕ) (h : n<2^j) :
    (shiftP n x j).2.2=x^n := by
  simpa only [countP, Nat.div_eq_of_lt h, pow_zero,mul_one] using real n x j
end shiftP

lemma halveP (h : b.Grain S k) (g : b.Grain S n) (hs : Small S n)
    (hh : ∀ i,k i<2^n i) {x : ι→ℂ} (hp : b.Dry S sc x) :
    b.Dry S sc fun i => x i^k i := by
  let V (i : ι) (j) := shiftP (k i) (x i) j
  have ht := Dry.token b n S V (t:=shiftTy)
  have hk : (b.climbs n shiftTy V).Grain (fun i => S i.i) fun i => (V i.i i.j).1 :=
    ⟨ht.fst,(h.small.reindex _).mono fun i => by
      simp only [V,shiftP.countP]; apply Nat.div_le_self⟩
  have hx := ht.snd.fst
  have hy := ht.snd.snd
  have HU := cycleG g hs V (h.dry.pair (hp.pair Dry.one))
    ((hk.div (Grain.wc 2)).dry.pair ((hx.mul hx).pair
      ((hk.residue (Grain.wc 2)).dry.branch hy (hy.mul hx))))
  exact HU.snd.snd.congr fun i => shiftP.endP _ _ _ (hh i)

namespace Neaps

lemma n_lt (h : b.Neaps S n) (i) :
    n i < 2^S i := by
  have hh := stack_above (n i)
  rw [h.stack_eq] at hh
  omega

def layersP (S : ℕ) : ℕ := 3*S+4
lemma layersG (h : b.Neaps S n) :
    b.Grain S fun i => layersP (S i) :=
  (((Grain.wc 3).mul (h.tidal.grain S)).add (Grain.wc 4))
lemma layersS (S : ι→ℕ) : Small S fun i => layersP (S i) :=
  ((Small.const _ 3).mul (Small.self S)).add (Small.const _ 4)
lemma layersBound (h : b.Neaps S n) (i) :
    8*(n i)^3 < 2^layersP (S i) := by
  have he : 0<n i := h.pos _
  rw [layersP,pow_add,Nat.mul_comm 3,pow_mul]
  calc
    _ ≤ 8*((2^S i)^3) := by gcongr; exact (h.n_lt i).le
    _ < _ := by
      have hh : 0 < (2^S i)^3 := by positivity
      norm_num
      omega

lemma extractP (h : b.Neaps S n) (g : ∀ i,Ports (n i)) (u : b.Grain S k)
    (hk : ∀ i,k i ∣ express (n i))
    (hz : b.Dry S sc fun i => root (receipt (n i))) :
    b.Dry S sc fun i => root (k i) := by
  have hp : ∀ i,k i∣receipt (n i) := fun i => by
    simpa [receipt,g i] using hk i
  have H := halveP (h.receiptG.div u) h.layersG (layersS _) (x:=fun i => root (receipt (n i)))
    (fun i => lt_trans (lt_of_le_of_lt (Nat.div_le_self ..)
      (receipt_bound _ (h.pos _)).2) (h.layersBound i)) hz
  exact H.congr fun i => root_factor (receipt_bound _ (h.pos _)).1 (hp i)

lemma etaP (h : b.Neaps S n) (g : ∀ i,Ports (n i))
    (hz : b.Dry S sc fun i => root (receipt (n i))) :
    b.Dry S sc fun i => root (2*n i) :=
  h.extractP g ((Grain.wc 2).mul (h.num.grain S)) (fun i => express_eta (n i)) hz

lemma mediumP (h : b.Neaps S n) (g : ∀ i,Ports (n i))
    (hz : b.Dry S sc fun i => root (receipt (n i))) :
    b.Dry S sc fun i => root (barge (n i)).vol :=
  h.extractP g h.bargeL.volL (fun _ => express_volume _) hz

lemma ratioSq {a b n : ℕ} (h : a<4*n) (g : 2 ≤ b) :
    (a/b)*(a/b) ≤ 8*n^3 := by
  have H : (a/b)*2 ≤ a := le_trans (Nat.mul_le_mul_left _ g)
    (Nat.div_mul_le_self a b)
  have hh : a/b ≤ 2*n := by omega
  calc
    _ ≤ (2*n)*(2*n) := Nat.mul_le_mul hh hh
    _ = n^2*4 := by ring
    _ ≤ n^2*(8*n) := Nat.mul_le_mul_left _ (by omega)
    _ = 8*n^3 := by ring

lemma ladeGrain {X : ι→Cart} {e : ι→ℕ}
    (h : b.Lade S X) (g : Small b.size e) (hk : ∀ i, ∀ j<(X i).l, (X i).q j ≤ e i) :
    (b.scan fun i => (X i).l).Grain (fun i => S i.i) fun i => (X i.i).q i.j := by
  let L i := (X i).l
  have H := h.dataL.transfer (Instant.scan b L)
  refine ⟨Dry.pick (t:=w) (k:=During.j) (n:=fun i : During L => L i.i)
    (x:=fun i j => (X i.i).q j) H (chopG h.dimL).dry During.hj,
    (g.reindex _).mono (fun i => hk _ i.j i.hj)⟩

lemma kilnP (h : b.Neaps S n) (g : ∀ i,Ports (n i))
    {z : ι→ℂ} (hu : b.Dry S sc z)
    (hz : b.Dry S sc fun i => root (receipt (n i))) :
    b.Dry S forgeTy fun i =>
      forge (barge (n i)).l (orderE (n i)) (barge (n i)).q (z i) := by
  let X i := barge (n i)
  let e i := orderE (n i)
  let L i := (X i).l
  have hh (i) := barge_spec (n i) (h.pos _)
  have H := h.bargeL
  have hI : b.Dry S sc fun i => Complex.I :=
    (h.extractP g (Grain.wc 4) (fun i => express_I (n i)) hz).congr (fun _ => root_four)
  let Y i := e i+1
  have hY : b.Grain S Y := h.orderG.add (Grain.wc 1)
  have hSY : Small S Y := h.orderS.add (Small.const _ 1)
  have F := Instant.scan b Y
  have hj := chopG hY
  have hE : Small (b.scan Y).size (fun i => 2^i.j) :=
    ((h.powOrderS.trans h.tidal.small).reindex _).mono (fun i =>
      Nat.pow_le_pow_right (by omega) (Nat.le_of_lt_succ i.hj))
  have hk := hj.twoPow ((hSY.reindex _).mono fun i => i.hj.le) hE
  have hv := arrayG hY hSY (fun _ => halos) (t:=sc)
    ((h.transfer F).extractP (fun i => g i.i) hk
      (fun i => express_halo _ _ (Nat.le_of_lt_succ i.hj)) (hz.transfer F))
  have G := Instant.scan b L
  let A (i : During L) := (X i.i).vol
  let B (i : During L) := (X i.i).q i.j
  have hb : (b.scan L).Grain (fun i => S i.i) B :=
    ladeGrain (X:=X) H h.powOrderG.small (fun i => (hh i).sizes)
  have Ha : (b.scan L).Grain (fun i => S i.i) A := H.volL.transfer G
  have HG := h.transfer G
  have HE (i : During L) : (A i / B i)*(A i / B i) < 2 ^ layersP (S i.i) := by
    have He : 2 ≤ B i := (hh _).square.isles.good i.j i.hj
    have Hh : A i < 4*n i.i := (hh _).upper
    exact lt_of_le_of_lt (ratioSq Hh He) (HG.layersBound i)
  have HD := halveP ((Ha.div hb).mul (Ha.div hb)) HG.layersG (layersS _) HE (hu.transfer G)
  have HS := arrayG H.dimL H.countS
    (fun i j => spray (z i) (extent (X i).q (X i).l) ((X i).q j)) (t:=sc)
    (HD.congr fun i => by rw [spray,show extent (X i.i).q (X i.i).l=(X i.i).vol
      from (hh _).square.agrees.symm])
  exact H.dimL.dry.pair (h.orderG.dry.pair (H.dataL.pair (hI.pair (hv.pair HS))))

-- adjusted budget name
end Neaps

open Slant
def leg (n : ℕ) := (score (orderE n)+1)*((barge n).vol*hills (barge n).l)

theorem Neaps.streamP (h : b.Neaps S n) (g : ∀ i,Ports (n i))
    (hz : b.Dry S sc fun i => root (receipt (n i)))
    {z : ι→ℂ} (hu : b.Dry S sc z)
    (hp : ∀ i, IsPrimitiveRoot (z i) (barge (n i)).vol)
    {x : ι→Line} {cl} (hx : b.Moves (fun _ => 0) (a (c cl)) fun i =>
      Tape.tab (barge (n i)).vol (x i)) :
    ∃ d : ℕ,b.Moves (fun i => leg (n i)+(S i+2)^d)
      (a (c cl)) fun i => Tape.tab (barge (n i)).vol
        (freq (barge (n i)).vol (z i) (x i)) := by
  let X i := barge (n i)
  have hX i := barge_spec (n i) (h.pos _)
  have he i : (X i).vol=extent (X i).q (X i).l := (hX _).square.agrees
  have hh := effuse (r:=fun i => (X i).q) (l:=fun i => (X i).l) (fun i => (hX _).square.isles)
    (fun i => (hX _).sizes) (fun i => he i ▸ hp i) h.bargeL.countS h.powOrderS h.tidal.small
    (h.bargeL.volume.mono (fun i => (he i).symm.le)) (b:=b) (x:=x)
    (h.kilnP g hu hz) (hx.congr fun i => congrArg (fun d => Tape.tab d (x i)) (he i))
  obtain ⟨d,hd⟩ := hh
  refine ⟨d, (hd.weaken (Dom.of_le fun i => ?_)).congr fun i => ?_⟩
  · simp only [leg, ← he]; exact le_rfl
  · simp only [← he, X]

end Bench
end
end PowerSaving.RAM

end OAI
