import OAI.Computability.FourierTransform.WorkBounds

namespace OAI

/-! Primitive O(n) and O(polylog(n)) algorithms for parameters. -/
namespace PowerSaving.RAM
open Ty Finset
noncomputable section

-- halving and log. All-natural iterations.
def tallyH (n : ℕ) : ℕ → ℕ×ℕ
  | 0 => (n,0)
  | k+1 => let p := tallyH n k
           (p.1 / 2,p.2+(if 1<p.1 then 1 else 0))

namespace tallyH

lemma small (n k : ℕ) : (tallyH n k).1 ≤ n ∧ (tallyH n k).2 ≤ k := by
  induction k with
  | zero => exact ⟨le_rfl,le_rfl⟩
  | succ k ih => simp only [tallyH]; split <;> omega

lemma tally (n k : ℕ) :
    Nat.log 2 n = Nat.log 2 (tallyH n k).1 + (tallyH n k).2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [tallyH]; split
    · rename_i H
      conv_lhs => rw [ih,Nat.log_of_one_lt_of_le Nat.one_lt_two H]
      omega
    · rename_i H
      rw [Nat.log_of_lt (show (tallyH n k).1/2<2 by omega)]
      have hx := Nat.log_of_lt (b:=2) (show (tallyH n k).1<2 by omega)
      rw [hx] at ih; omega

lemma quota (n k : ℕ) :
    (tallyH n k).1 ≤ n-k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [tallyH]; omega

lemma end_eq (n : ℕ) : (tallyH n n).2 = Nat.log 2 n := by
  have H := tally n n
  rw [Nat.log_of_lt (show (tallyH n n).1<2 by have := quota n n; omega)] at H
  omega
end tallyH

universe U V
namespace Bench
variable {m : Bool} {ι : Type U} {b : Bench m ι} {n k : ι→ℕ}

lemma Nick.cmp (h : b.Nick n) (g : b.Nick k) :
    b.Nick fun i => if n i < k i then 1 else 0 :=
  ⟨Can.wlt h.close g.close,(Small.const _ 1).mono fun i => by split <;> omega⟩

lemma Nick.logM (h : b.Nick n) :
    b.Moves n w fun i => Nat.log 2 (n i) := by
  let V (i : ι) j : T (p w w) := tallyH (n i) j
  have F := Instant.climbs b n V (t:=p w w)
  have hk := tokenNow b n V
  have hb := (h.transfer F).small
  let D := b.climbs n (p w w) V
  have hx : D.Nick fun i => (V i.i i.j).1 :=
    ⟨hk.fst,hb.mono fun i => (tallyH.small _ _).1⟩
  have hy : D.Nick fun i => (V i.i i.j).2 :=
    ⟨hk.snd,hb.mono fun i => ((tallyH.small _ _).2).trans i.hj.le⟩
  have hh := repeatM h V (h.close.pair (Moves.wc 0)) (u:=fun _ _ => 0)
    ((hx.div (Nick.wc 2)).close.pair (hy.add ((Nick.wc 1).cmp hx)).close)
  simp only [sum_const_zero,Nat.add_zero] at hh
  exact hh.snd.congr fun i => tallyH.end_eq _

lemma Nick.numeralM (h : b.Nick n) :
    b.Moves n sc fun i => (n i:ℂ) := by
  let V (i : ι) (j : ℕ) : T sc := (j:ℂ)
  have H := repeatM h V (u:=fun _ _ => 0)
    (Moves.zero.congr (fun _ => by simp [V])) (((tokenNow b n V).add Moves.one).congr
      (fun _ => by simp [V]))
  simpa only [sum_const_zero,Nat.add_zero] using H
end Bench
end
end PowerSaving.RAM

end OAI
