import OAI.Computability.FourierTransform.ParameterPrograms
import OAI.Computability.FourierTransform.ChirpConvolution

namespace OAI

/- Linear preparation of power tables. -/
namespace PowerSaving.RAM
open Ty Finset Spectral
noncomputable section

namespace Bench
universe U V
variable {ι : Type U} {κ : Type V} {m : Bool} {b : Bench m ι}
  {n k S : ι→ℕ} {t : Ty}

lemma Moves.branch {W : ι→ℕ} {x y : ι→T t}
    (h : b.Moves W w n) (g : b.Moves W t x) (j : b.Moves W t y) :
    b.Moves W t fun i => if n i=0 then x i else y i := by
  let v (i : ι) : T t := if n i=0 then x i else y i
  change b.Moves W t v
  refine Can.testz h ?_ ?_
  · exact Moves.congr (g.transfer (Instant.along b (Subtype.val (p:=fun i => n i=0))))
      fun i => (ite_eq_left i.property).symm
  · exact Moves.congr (j.transfer (Instant.along b (Subtype.val (p:=fun i => n i≠0))))
      fun i => (ite_eq_right i.property).symm

lemma Nick.branch {x y : ι→ℕ} (h : b.Nick n) (g : b.Nick x) (j : b.Nick y) :
    b.Nick fun i => if n i=0 then x i else y i :=
  ⟨h.close.branch g.close j.close,(g.small.add j.small).mono fun i => by split <;> omega⟩

lemma tape_congr_sized {n : ℕ} {α : Type*} {f g : ℕ→α} (h : ∀ j<n,f j=g j) :
    Tape.tab n f=Tape.tab n g :=
  congrArg (fun x : Fin n→α => (⟨n,x⟩:Tape α)) (funext fun i => h i.val i.isLt)

lemma pick_all {n k : ι→ℕ} (x : ι→ℕ→T t)
    (h : b.Moves (fun _ => 0) (a t) fun i => Tape.tab (n i) (x i)) (g : b.Nick k) :
    b.Moves (fun _ => 0) t fun i => if k i<n i then x i (k i) else t.blank :=
  Can.cong (Can.look h g.close) (fun _ => rfl) fun _ => Tape.look_tab _ _ _ _

def tablePow (z : ℂ) (k : ℕ) : T (a sc) :=
  Tape.tab (2^k) fun i => z^i

lemma unit_doubling (k : ℕ) :
    ∑ j ∈ range k,2^(j+1)=2*2^k-2 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [sum_range_succ,ih,pow_succ]
    have : 0 < 2^k := by positivity
    omega

lemma pylon (h : b.Nick k)
    (g : Small b.size fun i => 2^k i) {z : ι→ℂ} (hz : b.Moves (fun _ => 0) sc z) :
    b.Moves (fun i => 2^k i) (a sc) fun i => tablePow (z i) (k i) := by
  let V i j : T (a sc) := tablePow (z i) j
  have F := Instant.climbs b k V (t:=a sc)
  have HB : b.Moves (fun _ => 0) (a sc) fun i => V i 0 :=
    ((arrayNow (Nick.wc 1) (t:=sc) (fun _ _ => 1) Moves.one).weaken (Dom.const _ _)).congr
      fun i => by
        simp only [V,tablePow,pow_zero]
        exact tape_congr_sized fun j hj => by simp [show j=0 by omega]
  have hm := tokenNow b k V
  let R (i : During k) := 2^i.j
  let D := b.climbs k (a sc) V
  have hu : Small D.size R := (g.reindex _).mono fun i =>
    Nat.pow_le_pow_right (by omega) i.hj.le
  have hh : D.Nick R := ⟨hm.len hu,hu⟩
  let Y (i : During k) := 2^(i.j+1)
  have hY : D.Nick Y :=
    (hh.mul (Nick.wc 2)).congr fun i => (pow_succ _ _).symm
  have G := Instant.scan D Y
  have hp := chop hY
  have hr := Moves.pick (t:=sc) (n:=fun i => R i.i) (k:=fun i : During Y => i.j/2)
    (fun i j => z i.i.i ^ j) (hm.transfer G) (hp.div (Nick.wc 2)).close (fun i => by
      have hpp : i.j < Y i.i := i.hj
      simp only [R,Y,pow_succ] at *
      omega)
  have hk := repeatM h V HB (u:=fun _ j => 2^(j+1))
    (arrayNow hY (t:=sc) (fun i j => z i.i ^ j) ((((hp.residue (Nick.wc 2)).close.branch
      (hr.mul hr) ((hr.mul hr).mul (hz.transfer (G.next F))))).congr fun i => by
      let x := z i.i.i
      change (if i.j%2=0 then x^(i.j/2)*_ else _)=_
      by_cases H : i.j%2=0
      · rw [ite_eq_left H,← pow_add,show i.j / 2 + i.j/2=i.j by omega]
      · rw [ite_eq_right H,← pow_add,← pow_succ,show i.j/2+i.j/2+1=i.j by omega]))
  exact hk.weaken ⟨4,fun i => by
    dsimp
    rw [unit_doubling]
    have hh : k i < 2^k i := Nat.lt_two_pow_self
    omega⟩

-- index z^(j*j) for root z order d ≤ table length
lemma square_pow (_h : Small b.size fun i => 2^k i)
    {z : ι→ℂ} {u : ι→ℕ}
    (g : b.Moves (fun _ => 0) (a sc) fun i => tablePow (z i) (k i)) (hk : b.Nick n)
    (hn : ∀ i,0<n i ∧ n i≤2^k i) (hz : ∀ i, z i^n i=1) (hu : b.Nick u) :
    b.Moves (fun _ => 0) sc fun i => epschirp (z i) (u i) :=
  (Moves.pick (t:=sc) (n:=fun i => 2^k i)
    (k:=fun i => (u i*u i)%n i) (fun i j => z i^j) g
    ((hu.mul hu).residue hk).close
    (fun i => lt_of_lt_of_le (Nat.mod_lt _ (hn i).1) (hn i).2)).congr
    fun i => power_mod (hz i) _

-- simple padded array
lemma padM (_h : b.Nick n) (g : b.Nick k) {cl} {x : ι→Line}
    (hx : b.Moves (fun _ => 0) (a (c cl)) fun i => Tape.tab (n i) (x i)) :
    b.Moves k (a (c cl)) fun i => Tape.tab (k i) (padline (n i) (x i)) :=
  arrayNow g _ (pick_all (t:=c cl) (n:=fun i : During k => n i.i)
    (x:=fun (i : During k) j => x i.i j)
    (hx.transfer (Instant.scan b k)) (chop g))
end Bench
end
end PowerSaving.RAM

end OAI
