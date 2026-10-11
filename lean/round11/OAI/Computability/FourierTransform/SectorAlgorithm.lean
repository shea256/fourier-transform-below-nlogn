import OAI.Computability.FourierTransform.TensorProgram
import OAI.Computability.FourierTransform.SectorPrograms
import OAI.Computability.FourierTransform.SectorIdentities

namespace OAI

/-! Sector algorithm. -/
namespace PowerSaving.RAM
open Ty Finset Grove Shard Binary
noncomputable section

universe U V

-- prepare data structure pack (stamped fields plus x entries). Also need original chips tape.
def upholstery (n : ℕ) (f : ℕ→Shard) :=
  Tape.tab n fun i => chip (f i)

abbrev ragTy (cl : Paint) := p chipTy (c cl)

def rag (n : ℕ) (f : ℕ→Shard) (x : Line) (j : ℕ) :=
  (chip (patch n f j),stow n f x j)

def rolls (n : ℕ) (f : ℕ→Shard) (x : Line) (j : ℕ) :=
  if (patch n f j).seat=0 then Tape.tab (patch n f j).width (glimpse n f x j)
  else Tape.tab 0 (fun _ => (0:ℂ))

namespace Bench
variable {m : Bool} {ι : Type U} {κ : Type V} {b : Bench m ι} {q : Bench m κ}
  {cl : Paint} {k l n : ι → ℕ} {x : ι→Line} {f : ι → ℕ→Shard}

-- cost-sensitive use of binary kernel, when input generated within budget
theorem gleamT (hw : ∀ i,n i=2^k i) (hg : ∀ i,k i≤l i) (hn : b.Nick n) (hk : b.Nick k)
    (hI : b.Moves (fun _ => 0) sc fun _ => Complex.I)
    (hx : b.Moves n (a (c cl)) fun i => Tape.tab (n i) (x i)) :
    b.Moves (fun i => n i*hills (l i)) (a (c cl)) fun i =>
      Tape.tab (n i) (gleam (k i) (x i)) := by
  let W i := n i*hills (l i)
  let v i (d : Bits (k i)) := x i ((bits (k i)).loc d)
  have ht : Dom W n := Dom.of_le (fun i => Nat.le_mul_of_pos_right _ (hills_pos _))
  have hx' : b.Moves W (a (c cl)) fun i => (bits (k i)).tape (v i) := by
    refine (hx.weaken ht).congr ?_
    intro i
    refine Layout.verify _ _ 0 (v i) (hw i) ?_
    intro d; rw [Tape.look_tab, hw,ite_eq_left (show (bits (k i)).loc d < 2^k i from (bits _).bd d)]
  have hi := hills_program cl m k v
  have he : b.Moves W (a (c cl)) fun i => (bits (k i)).tape (ripple (k i) (v i)) := by
    have hu : Small b.size (fun i => 2^k i) := hn.small.mono fun i => (hw i).ge
    have hj : ∀ i, 2^k i*hills (k i) ≤ W i := fun i => Nat.mul_le_mul (by rw [hw])
      (hills_mono (hg i))
    exact Can.then_do ((hk.close.ease W).pair ((hI.ease W).pair hx')) ((hi.ambient hu).mono hj)
  refine he.congr ?_
  intro i; symm
  apply Layout.verify _ _ 0 (ripple (k i) (v i)) (hw i)
  intro d
  rw [Tape.look_tab, hw,ite_eq_left (show (bits (k i)).loc d < 2^k i from (bits _).bd d)]
  exact gleam_loc _ _ d

structure Matting (b : Bench m ι) (n l : ι→ℕ) (f : ι → ℕ→Shard) : Prop where
  length : b.Nick n
  shape : ∀ i, Quilt (n i) (l i) (f i)
  cover : b.Moves (fun _ => 0) (a chipTy) fun i => upholstery (n i) (f i)

namespace Matting
variable {j : ι→ℕ}

lemma transfer {n l : κ→ℕ} {f : κ→ℕ→Shard} (h : q.Matting n l f) {p}
    (g : b.Instant q p) :
    b.Matting (fun i => n (p i)) (fun i => l (p i)) (fun i => f (p i)) :=
  ⟨h.length.transfer g,fun _ => h.shape _,h.cover.transfer g⟩

lemma kitOf (h : b.Matting n l f) (hj : b.Nick j) (hg : ∀ i,j i<n i) :
    b.Kit fun i => f i (j i) :=
  Kit.grab h.length.small (fun i => (h.shape i).mark _ (hg i))
    (Moves.pick (n:=n) (t:=chipTy) _ h.cover hj.close hg)

/-- pack via linear scatter, along with all sector tags -/
lemma packT (h : b.Matting n l f)
    (hx : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (n i) (x i)) :
    b.Moves n (a (ragTy cl)) fun i => Tape.tab (n i) (rag (n i) (f i) (x i)) := by
  let Tchip (i : ι) (j : ℕ) : T (ragTy cl) := (chip (f i j),x i j) -- τ?
  have F := Instant.scan b n
  have hh := chop h.length
  have hp := (h.transfer F).kitOf hh During.hj
  have hs : (b.scan n).Moves (fun _ => 0) (c cl) fun i => x i.i i.j :=
    Moves.pick (n:=fun i => n i.i) (t:=c cl) _ (hx.transfer F) hh.close During.hj
  have ht := scatterNow (t:=ragTy cl) h.length
    (fun i j => ((f i j).addr,Tchip i j)) (hp.addr.close.pair (hp.lend.pair hs))
  exact ht.congr (fun i => (h.shape i).reloc.sow (Tchip i) _)

end Matting

variable (cl) in
structure Weft (b : Bench m ι) (n l : ι→ℕ) (f : ι → ℕ→Shard) (x : ι → Line) : Prop where
  mat : b.Matting n l f
  packed : b.Moves (fun _ => 0) (a (ragTy cl)) fun i =>
    Tape.tab (n i) (rag (n i) (f i) (x i))
  unitI : b.Moves (fun _ => 0) sc fun _ => Complex.I

namespace Weft
variable {j : ι→ℕ}

lemma transfer {n l : κ→ℕ} {f : κ→ℕ→Shard} {x : κ→Line}
    (h : q.Weft cl n l f x) {p} (g : b.Instant q p) :
    b.Weft cl (fun i => n (p i)) (fun i => l (p i)) (fun i => f (p i)) (fun i => x (p i)) :=
  ⟨h.mat.transfer g,h.packed.transfer g,h.unitI.transfer g⟩

lemma kitOf (h : b.Weft cl n l f x) (hj : b.Nick j) (hg : ∀ i,j i<n i) :
    b.Kit fun i => patch (n i) (f i) (j i) :=
  Kit.grab h.mat.length.small (fun i => (h.mat.shape i).patch_mark (hg i))
    (Moves.pick (n:=n) (t:=ragTy cl) _ h.packed hj.close hg).fst
lemma stowOf (h : b.Weft cl n l f x) (hj : b.Nick j) (hg : ∀ i,j i<n i) :
    b.Moves (fun _ => 0) (c cl) fun i => stow (n i) (f i) (x i) (j i) :=
  (Moves.pick (n:=n) (t:=ragTy cl) _ h.packed hj.close hg).snd

-- rolls at a sector start.
lemma shine (h : b.Weft cl n l f x) (hj : b.Nick j) (hg : ∀ i,j i<n i)
    (hz : ∀ i,(patch (n i) (f i) (j i)).seat=0) :
    b.Moves (fun i => seatfare (n i) (f i) (j i) * hills (l i)) (a (c cl))
      fun i => rolls (n i) (f i) (x i) (j i) := by
  let B i := patch (n i) (f i) (j i)
  let Q i := (B i).width
  have HK := h.kitOf hj hg
  have he (i : ι) : (B i).Mark (n i) (l i) := (h.mat.shape i).patch_mark (hg i)
  have hh (i : ι) : j i+Q i ≤ n i := by
    have A : (B i).tip ≤ n i := (he i).endsBy
    have hx : (B i).addr=j i := (h.mat.shape i).patch_addr (hg i)
    have hy : (B i).seat=0 := hz i
    unfold tip at A; unfold addr at hx; dsimp only [Q]; omega
  let S i := slit (n i) (f i) (x i) (j i)
  have ht : b.Moves Q (a (c cl)) fun i => Tape.tab (Q i) (S i) := by
    have F := Instant.scan b Q
    have hi := chop HK.widths
    have hw := (hj.transfer F).add hi
    exact arrayNow HK.widths (t:=c cl) S ((h.transfer F).stowOf hw fun i =>
      lt_of_lt_of_le (Nat.add_lt_add_left i.hj _) (hh _))
  simp only [seatfare,rolls,hz,ite_true]
  exact gleamT (fun i => (he i).size) (fun i => (he i).tall)
    HK.widths HK.tall h.unitI ht

lemma arrays (h : b.Weft cl n l f x) :
    b.Moves (fun i => n i*hills (l i)) (a (a (c cl)))
      fun i => Tape.tab (n i) (rolls (n i) (f i) (x i)) := by
  let W (i : ι) := n i*hills (l i)
  let D := b.scan n
  let C (i : ι) j := seatfare (n i) (f i) j*hills (l i)
  let Y (i : ι) := rolls (n i) (f i) (x i)
  have hn := h.mat.length
  have F := Instant.scan b n
  have hk := h.transfer F
  have hs := chop hn
  have hb := (hk.kitOf hs During.hj).seat
  have ht : D.Moves (fun d => C d.i d.j) (a (c cl)) fun d => Y d.i d.j := by
    let Q (i : During n) := (patch (n i.i) (f i.i) i.j).seat
    refine inspectz (n:=Q) hb ?_ ?_
    · have ha := Instant.along D (Subtype.val (p:=fun i => Q i=0))
      exact (hk.transfer ha).shine (hs.transfer ha) (fun i => i.val.hj)
        (fun i => i.property)
    · let A := {i // Q i ≠ 0}
      let M := D.along (Subtype.val (p:=fun i => Q i≠0))
      have hh := arrayNow (b:=M) (t:=c cl) (Nick.wc 0) (fun _ _ => 0) Moves.zero
      refine (hh.weaken (Dom.const _ _)).congr ?_
      intro i
      have hB : Q i.val ≠ 0 := i.property
      simp only [Q] at hB
      simp only [Y,rolls,hB,↓reduceIte]
  have he := arrayM (t:=a (c cl)) hn Y ht (u:=C)
  refine he.weaken ?_
  refine ⟨3,fun i => ?_⟩
  dsimp only [C]
  rw [← sum_mul, fare_sum _ _ _ (h.mat.shape i)]
  have hm := Nat.le_mul_of_pos_right (n i) (hills_pos (l i))
  omega

lemma woven (h : b.Weft cl n l f x) :
    b.Moves (fun i => n i*hills (l i)) (a (c cl))
      fun i => Tape.tab (n i) fun j =>
        glimpse (n i) (f i) (x i) (f i j).start (f i j).seat := by
  let W i := n i*hills (l i)
  let T i := rolls (n i) (f i) (x i)
  let V i := Tape.tab (n i) (T i)
  let D := b.extend (a (a (c cl))) V
  have F := Instant.extend b (t:=a (a (c cl))) V
  have G := Instant.scan D n
  have HK : Dom W n := Dom.of_le (fun i => Nat.le_mul_of_pos_right _ (hills_pos _))
  let B (d : During n) := f d.i d.j
  have hn := (h.mat.length.transfer F)
  have hh := (h.mat.transfer (G.next F)).kitOf (chop hn) During.hj
  have hg (d : During n) := (h.mat.shape d.i).mark d.j d.hj
  have hm (d : During n) : (B d).start < n d.i := (hg d).starts.trans_le (hg d).endsBy
  have ht := Moves.pick (t:=a (c cl)) (n:=fun d : During n => n d.i) (fun d j => T d.i j)
    ((cherry (W:=fun _ => 0) b (t:=a (a (c cl))) V).transfer G)
    hh.starts.close hm
  have he (d : During n) :
      T d.i (B d).start = Tape.tab (B d).width
        (glimpse (n d.i) (f d.i) (x d.i) (B d).start) := by
    have hM := (h.mat.shape d.i).patch_align d.hj (le_refl (B d).start) (hg d).starts
    have he : (patch (n d.i) (f d.i) (B d).start).seat=0 := hM.2.trans (Nat.sub_self _)
    simp only [T,rolls,he,ite_true]
    rw [hM.1.2.1]
  have hj := Moves.pick (b:=D.scan n) (n:=fun d => (B d).width) (t:=c cl)
    (fun d => glimpse (n d.i) (f d.i) (x d.i) (B d).start) (ht.congr he) hh.seat.close
    (fun d => (hg d).place)
  exact caseM h.arrays ((arrayNow (t:=c cl) hn (fun i j => glimpse (n i) (f i) (x i) (f i j).start (f i j).seat) hj).weaken HK)

end Weft

lemma Matting.cardT (h : b.Matting n l f)
    (hx : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (n i) (x i))
    (hI : b.Moves (fun _ => 0) sc fun _ => Complex.I) :
    b.Moves (fun i => n i*hills (l i)) (a (c cl))
      fun i => Tape.tab (n i) fun j =>
        glimpse (n i) (f i) (x i) (f i j).start (f i j).seat := by
  let V i := Tape.tab (n i) (rag (n i) (f i) (x i))
  let D := b.extend (a (ragTy cl)) V
  have F := Instant.extend b (t:=a (ragTy cl)) V
  have hk : D.Weft cl n l f x := ⟨h.transfer F,cherry (t:=a (ragTy cl)) b V,hI.transfer F⟩
  refine caseM ((h.packT hx).weaken (Dom.of_le (fun i =>
    Nat.le_mul_of_pos_right _ (hills_pos _)))) hk.woven

end Bench
end
end PowerSaving.RAM

end OAI
