import OAI.Computability.FourierTransform.LocalPreparation
import OAI.Computability.FourierTransform.LengthSelection

namespace OAI

/- Broad length selection bench algorithms. -/
namespace PowerSaving.RAM
open Ty Selection Grove
noncomputable section

namespace Bench
universe U V
variable {ι : Type U} {κ : Type V} {m : Bool} {b : Bench m ι} {q : Bench m κ}
  {N k S : ι→ℕ}

-- check nondivisibility for j = 2 to n-1
def clearP (n : ℕ) : ℕ→ℕ
  | 0 => 1
  | j+1 => if 1<j ∧ n%j=0 then 0 else clearP n j

lemma clearP_eq (n k : ℕ) :
    clearP n k = if ∀ j<k,2 ≤ j → ¬ j ∣ n then 1 else 0 := by
  induction k with
  | zero => simp [clearP]
  | succ k ih =>
    have hh : (∀ j<k+1,2≤j → ¬ j∣n) ↔ ((∀ j<k,2≤j → ¬ j∣n) ∧ ¬ (1<k ∧ n%k=0)) := by
      simp only [Nat.dvd_iff_mod_eq_zero]
      constructor
      · intro h
        exact ⟨fun j hj => h j (by omega),fun ⟨hk,ht⟩ => h k (by omega) hk ht⟩
      · rintro ⟨h,g⟩ j hj ht
        obtain e|e : j<k ∨ j=k := by omega
        · exact h j e ht
        · subst j; exact fun hp => g ⟨ht,hp⟩
    rw [clearP,ih]
    simp_rw [hh]
    split_ifs <;> tauto

lemma Grain.isBar (h : b.Grain S k) (g : Small S k) :
    b.Grain S fun i => if Bar (k i) then 1 else 0 := by
  refine ⟨?_,(Small.const _ 1).mono fun i => by split <;> omega⟩
  let f (i : ι) (j) : T w := clearP (k i) j
  have F := Instant.climbs b k f (t:=w)
  have hu := strideG h f
  have hp := Dry.token b k S f
  have HH := cycleG h g f (Dry.wc 1)
    ((((Grain.wc 1).cmp hu).dry.branch hp
      (((h.transfer F).residue hu).dry.branch (Dry.wc 0) hp)).congr (fun i => by
      by_cases e : 1 < i.j <;> by_cases e' : k i.i % i.j=0 <;>
        simp [f,clearP,e,e']))
  refine ((((Grain.wc 2).cmp h).dry.branch (Dry.wc 0) HH)).congr fun i => ?_
  dsimp only [f]; rw [clearP_eq]
  simp_rw [Bar,Nat.prime_def_lt']
  by_cases e : 2 < k i
  · have H : (∀ j < k i, 2 ≤ j → ¬ j ∣ k i) ↔ (∀ j, 2 ≤ j → j < k i → ¬ j∣k i) :=
      ⟨fun h j hj hg => h j hg hj,fun h j hj hg => h j hg hj⟩
    simp [e,e.le,H]
  · simp [e]

def cartTy := p (p w w) (a w)
def cartT (x : Cart) : T cartTy := ((x.l,x.vol),Tape.tab x.l x.q)

structure Lade (b : Bench m ι) (S : ι→ℕ) (x : ι→Cart) : Prop where
  tape : b.Dry S cartTy fun i => cartT (x i)
  countB : Small b.size fun i => (x i).l
  volume : Small b.size fun i => (x i).vol
  countS : Small S fun i => (x i).l

namespace Lade

variable {x : ι→Cart}
lemma emptyL (b : Bench m ι) (S : ι→ℕ) :
    b.Lade S fun _ => Cart.empty :=
  ⟨((Dry.wc 0).pair (Dry.wc 1)).pair (arrayG (t:=w) (Grain.wc 0) (Small.const _ 0)
     (fun _ => Cart.empty.q) (Dry.wc 0)),Small.const _ 0,Small.const _ 1,Small.const _ 0⟩

lemma dimL (h : b.Lade S x) : b.Grain S fun i => (x i).l :=
  ⟨(Dry.fst (t:=a w) h.tape).fst,h.countB⟩
lemma volL (h : b.Lade S x) : b.Grain S fun i => (x i).vol :=
  ⟨(Dry.fst (t:=a w) h.tape).snd,h.volume⟩
lemma dataL (h : b.Lade S x) :
    b.Dry S (a w) fun i => Tape.tab (x i).l (x i).q :=
  (Dry.snd h.tape)

lemma push (h : b.Lade S x) (g : b.Grain S k) :
    b.Lade S fun i => (x i).pushQ (k i) := by
  let l i := (x i).l
  let e i := l i+1
  have hk := h.dimL.add (Grain.wc 1)
  have hs := h.countS.add (Small.const S 1)
  have F := Instant.scan b e
  have hj := chopG hk
  refine ⟨(hk.dry.pair (h.volL.mul g).dry).pair (arrayG hk hs
    (t:=w) (fun i => ((x i).pushQ (k i)).q)
    (((hj.cmp (h.dimL.transfer F)).dry.branch (g.transfer F).dry
      ((h.dataL.transfer F).look hj.dry)).congr ?_)),hk.small,(h.volL.mul g).small,hs⟩
  intro i
  simp only [Tape.look_tab, Cart.pushQ]
  have HH : i.j < (x i.i).l+1 := i.hj
  by_cases e : i.j < (x i.i).l
  · simp [e,Nat.ne_of_lt e]
  · simp [show i.j=(x i.i).l by omega]
end Lade

lemma reapL (h : b.Grain S N) (hp : ∀ i, 0 < N i) (g : b.Grain S k) (u : Small S k) :
    b.Lade S fun i => reap (N i) (k i) := by
  have hh (i) (j) := reap_baler (N i) j (hp i)
  let R (i : ι) (j) := reap (N i) j
  let f (i : ι) (j) : T cartTy := cartT (R i j)
  have F := Instant.climbs b k f (t:=cartTy)
  have B := (h.transfer F)
  have hj := strideG g f
  let D := b.climbs k cartTy f
  have hy : Small (fun i : During k => S i.i) During.j :=
    (u.reindex _).mono (fun i => i.hj.le)
  have ht : D.Lade (fun i => S i.i) fun i => R i.i i.j :=
    ⟨Dry.token b k S f,hj.small.mono (fun i => (hh _ _).count),
      B.small.mono fun i => (hh _ _).top, hy.mono fun i => (hh _ _).count⟩
  refine ⟨cycleG g u f (Lade.emptyL b S).tape
    ((((hj.isBar hy).dry.branch ht.tape
      ((B.cmp (ht.volL.mul hj)).dry.branch (ht.push hj).tape ht.tape))).congr ?_),
    g.small.mono fun i => (hh _ _).count,h.small.mono fun i => (hh _ _).top,
    u.mono fun i => (hh _ _).count⟩
  intro i
  by_cases e : Bar i.j
  · by_cases H : (reap (N i.i) i.j).vol * i.j ≤ N i.i
    · simp [f,R,reap,e,H,not_lt.mpr H]
    · simp [f,R,reap,e,H,Nat.lt_of_not_ge H]
  · simp [f,R,reap,e]

lemma fillerL (h : b.Grain S N) (g : b.Grain S k) {v : ι→ℕ} (u : b.Grain S v)
    (hh : Small S v) (hk : Small b.size fun i => 2^v i) :
    b.Grain S fun i => fill (N i) (k i) (v i) := by
  let f (i : ι) (j) : T w := fill (N i) (k i) j
  have F := Instant.climbs b v f (t:=w)
  have hg : (b.climbs v w f).Grain (fun i => S i.i) fun i => f i.i i.j :=
    ⟨Dry.token b v S f,(hk.reindex _).mono (fun i => (Fill.capacity _ _ _).trans
      (Nat.pow_le_pow_right (by omega) i.hj.le))⟩
  refine ⟨cycleG u hh f (Dry.wc 1)
    (((((g.transfer F).mul hg).cmp (h.transfer F)).dry.branch hg.dry
      (hg.mul (Grain.wc 2)).dry).congr ?_),hk.mono (fun i => Fill.capacity _ _ _)⟩
  intro i
  by_cases H : k i.i*fill (N i.i) (k i.i) i.j < N i.i <;> simp [f,fill,H]

structure Neaps (b : Bench m ι) (S n : ι→ℕ) : Prop where
  num : b.Nick n
  tidal : b.Nick S
  stack_eq : ∀ i, stackN (n i)=S i
  pos : ∀ i, 0<n i

namespace Neaps
variable {n : ι→ℕ} {f : ι→κ}

lemma transfer {S n : κ→ℕ} (h : q.Neaps S n) (g : b.Instant q f) :
    b.Neaps (fun i => S (f i)) fun i => n (f i) :=
  ⟨h.num.transfer g,h.tidal.transfer g,fun _ => h.stack_eq _,fun _ => h.pos _⟩

lemma stackPow (h : b.Neaps S n) : Small b.size fun i => 2^S i :=
  ((Small.const _ 4).mul h.num.small).mono fun i => h.stack_eq i ▸ stack_pow _ (h.pos _)

lemma siloS (h : b.Neaps S n) : Small S fun i => harvestN (n i) :=
  (((Small.const _ 16).mul ((Small.self S).add (Small.const _ 4))).pow 2).mono
    fun i => by rw [harvestN,silo,h.stack_eq]
lemma siloG (h : b.Neaps S n) : b.Grain S fun i => harvestN (n i) := by
  have hg := (Nick.wc 16).mul (h.tidal.add (Nick.wc 4))
  exact ((hg.mul hg).grain S).congr fun i => by rw [harvestN,silo,h.stack_eq,pow_two]

lemma powOrderS (h : b.Neaps S n) : Small S fun i => 2^orderE (n i) :=
  ((Small.const _ 8).mul h.siloS).mono fun _ => orderE_small _

lemma orderS (h : b.Neaps S n) : Small S fun i => orderE (n i) :=
  h.powOrderS.mono fun _ => Nat.lt_two_pow_self.le
lemma orderG (h : b.Neaps S n) : b.Grain S fun i => orderE (n i) :=
  (((Grain.wc 2).mul h.siloG).logtwo ((Small.const _ 2).mul h.siloS)).add (Grain.wc 2)
lemma powOrderG (h : b.Neaps S n) : b.Grain S fun i => 2^orderE (n i) :=
  h.orderG.twoPow h.orderS (h.powOrderS.trans h.tidal.small)

lemma bedL (h : b.Neaps S n) : b.Lade S fun i => bed (n i) :=
  reapL ((Grain.wc 2).mul (h.num.grain S)) (fun i => by have := h.pos i; omega)
    (h.siloG.add (Grain.wc 1)) (h.siloS.add (Small.const _ 1))

lemma bargeL (h : b.Neaps S n) : b.Lade S fun i => barge (n i) :=
  h.bedL.push ((fillerL ((Grain.wc 2).mul (h.num.grain S)) h.bedL.volL
    (h.tidal.grain S) (Small.self S) h.stackPow).congr fun i => by rw [bead,h.stack_eq])

lemma expressG (h : b.Neaps S n) :
    b.Grain S fun i => express (n i) :=
  (((Grain.wc 2).mul (h.num.grain S)).mul h.bargeL.volL).mul h.powOrderG

lemma portG (h : b.Neaps S n) :
    b.Grain S fun i => if Ports (n i) then 0 else 1 :=
  ((h.num.grain S).cmp h.powOrderG).congr fun i => by
    by_cases hn : n i < 2^orderE (n i)
    · simp [Ports, hn, show ¬2^orderE (n i) ≤ n i from (by omega)]
    · simp [Ports, hn, show 2^orderE (n i) ≤ n i from (by omega)]

lemma receiptG (h : b.Neaps S n) :
    b.Grain S fun i => receipt (n i) :=
  ⟨(h.portG.dry.branch h.expressG.dry (h.num.grain S).dry).congr fun i => by
    by_cases H : Ports (n i) <;> simp [receipt,H],
   ((Small.const _ 8).mul (h.num.small.pow 3)).mono fun i => (receipt_bound _ (h.pos _)).2.le⟩
end Neaps

lemma Nick.stackH (h : b.Nick N) (g : ∀ i, 0<N i) :
    b.Moves N w (fun i => stackN (N i)) ∧
    (b.extend w (fun i => stackN (N i))).Neaps (fun i => stackN (N i)) N := by
  have hk := (Nick.wc 2).mul h
  have hu := ((Small.const _ 4).mul h.small).mono (G:=fun i => stackN (N i))
    (fun i => stack_le _ (g i))
  have hd := Can.wadd hk.logM (Can.wc 1) hu
  exact ⟨Can.weaken hd ⟨2,fun i => by dsimp; omega⟩,
    ⟨h.transfer (Instant.extend b _),⟨cherry b _ (t:=w),hu⟩,fun i => rfl,g⟩⟩

lemma Nick.planOrder (h : b.Nick N) (g : ∀ i,0<N i) :
    ∃ d : ℕ,b.Moves (fun i => N i + (stackN (N i)+2)^d) w fun i => receipt (N i) := by
  obtain ⟨hu,hk⟩ := h.stackH g
  obtain ⟨d,hd⟩ := hk.receiptG.dry
  exact ⟨d,Can.save hu hd⟩
end Bench
end
end PowerSaving.RAM

end OAI
