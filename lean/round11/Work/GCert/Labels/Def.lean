import Work.GCert.Data.Raw
import Work.Combine.SplitDef

/-!
# (key: gx-labels) The label check of a `gcert/1` certificate: kernel terms (core Lean only)

A frame is ONE natural number, its CODE: for a reduced echelon basis `b_p` (pivot `p`)

    code = dim + 2^8 * M + 2^(8+h) * P,   M = ∑ 2^p,   P = ∑ b_p * 2^(h*p)

(the basis vector of pivot `p` is DIGIT `p` of `P`, digit width `h`).  The frame table `tab`
(frame id ↦ code) and the states (register ↦ frame id) are `SSC.Trie`s.

* `tabK h t`              every leaf of `t` is a code (E0);
* `segK p gs S S' rs`     replay of the gates `gs` from the state `S`: every register named is
                          `< n` and moves to the frame of its gate (containment and strictly
                          larger dimension, E1); the state afterwards is `S'`; the block ranks,
                          in order, are `rs`.  ALL climbs of one gate are tested by ONE packed
                          elimination (`elimK`: `h` big-number steps).
* `wfK`, `noAdds`         shape of a state trie; a gate list without adds (the final climbs).

Segments compose (`GLab.Run.append`, `Work.GCert.Labels.Sound`): the only data passed from one
kernel evaluation to the next is the explicit state `S'`.
-/

namespace GLab
open SSC GXD

/-- `h` label dimension, `n` registers (`n ≤ 2^d`), `d` depth of the state tries, `K` digits of
the selector (at least `h` times the largest number of climbing registers of one gate),
`tab` the frame table. -/
structure Par where
  h : Nat
  n : Nat
  d : Nat
  K : Nat
  tab : Trie

/-- digit `p` (width `h`, `hm = 2^h - 1`) of `P` -/
noncomputable def digK (h hm P p : Nat) : Nat := Nat.land (Nat.shiftRight P (Nat.mul h p)) hm

noncomputable def goodLoop (h hm P M dm : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun cnt => Nat.beq cnt dm)
    (fun p ih cnt => Nat.rec (motive := fun _ => Bool) (ih cnt)
      (fun m _ => guard (Nat.beq (Nat.land (Nat.succ m) M) (Nat.pow 2 p)) (ih (Nat.succ cnt)))
      (digK h hm P p))

/-- `c` is the code of a reduced echelon basis -/
noncomputable def goodK (h c : Nat) : Bool :=
  forceN (Nat.sub (Nat.pow 2 h) 1) fun hm =>
  forceN (Nat.shiftRight c (Nat.add 8 h)) fun P =>
  guard (Nat.ble (Nat.succ P) (Nat.pow 2 (Nat.mul h h)))
    (goodLoop h hm P (Nat.land (Nat.shiftRight c 8) hm) (Nat.land c 255) h 0)

/-- E0 for a (part of a) frame table -/
noncomputable def tabK (h : Nat) : Trie → Bool :=
  Trie.rec (motive := fun _ => Bool) (fun v => goodK h v) (fun _ _ a b => guard a b)

/-- a trie of depth exactly `d` -/
noncomputable def wfK : Trie → Nat → Bool :=
  Trie.rec (motive := fun _ => Nat → Bool) (fun _ d => Nat.beq d 0)
    (fun _ _ a b d => Nat.rec (motive := fun _ => Bool) false (fun m _ => guard (a m) (b m)) d)

/-- packed elimination: for every digit `w` (pivot `p`) of `Pb`, add `w` to every digit of `A`
that has bit `p`; succeed if nothing is left -/
noncomputable def elimK (h hm O Pb : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun A => Nat.beq A 0)
    (fun p ih A => Nat.rec (motive := fun _ => Bool) (ih A)
      (fun m _ => forceN (Nat.xor A (Nat.mul (Nat.land (Nat.shiftRight A p) O) (Nat.succ m))) ih)
      (digK h hm Pb p))

/-- every digit of `A` lies in the span of the digits of `Pb` -/
noncomputable def elimT (h hm O Pb A : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun _ _ => elimK h hm O Pb h A) A

/-- one register `r` named by a gate at frame `f` (dimension `db`): if it stands elsewhere it
climbs: strictly smaller dimension, rank as listed, its basis is appended to `A` -/
noncomputable def visitK (n : Nat) (tab : Trie) (hh sh f db r : Nat) (S : Trie) (A : Nat)
    (rs : List Nat) (k : Trie → Nat → List Nat → Bool) : Bool :=
  guard (Nat.ble (Nat.succ r) n)
    (S.getK r fun a =>
      Bool.rec
        (tab.getK a fun ca =>
          forceN (Nat.land ca 255) fun da =>
          guard (Nat.ble (Nat.succ da) db)
            (List.rec (motive := fun _ => Bool) false
              (fun r0 rs' _ => guard (Nat.beq r0 (Nat.sub db da))
                (forceN (Nat.add (Nat.shiftLeft A hh) (Nat.shiftRight ca sh)) fun A' =>
                  k (S.set r f) A' rs')) rs))
        (k S A rs)
        (Nat.beq a f))

noncomputable def loopN (n : Nat) (tab : Trie) (hh sh f db : Nat) :
    List Nat → Trie → Nat → List Nat → (Trie → Nat → List Nat → Bool) → Bool :=
  List.rec (motive := fun _ => Trie → Nat → List Nat → (Trie → Nat → List Nat → Bool) → Bool)
    (fun S A rs k => k S A rs)
    (fun r _ ih S A rs k => visitK n tab hh sh f db r S A rs fun S1 A1 rs1 => ih S1 A1 rs1 k)

noncomputable def loopP (n : Nat) (tab : Trie) (hh sh f db : Nat) :
    List (Nat × Co) → Trie → Nat → List Nat → (Trie → Nat → List Nat → Bool) → Bool :=
  List.rec (motive := fun _ => Trie → Nat → List Nat → (Trie → Nat → List Nat → Bool) → Bool)
    (fun S A rs k => k S A rs)
    (fun x _ ih S A rs k => visitK n tab hh sh f db x.1 S A rs fun S1 A1 rs1 => ih S1 A1 rs1 k)

/-- one gate: all its registers move to its frame; one elimination for all climbs -/
noncomputable def gateK (p : Par) (hm hh sh O : Nat) (g : Gate) (S : Trie) (rs : List Nat)
    (k : Trie → List Nat → Bool) : Bool :=
  Gate.rec (motive := fun _ => Bool)
    (fun f s ts ex => p.tab.getK f fun cb => forceN (Nat.land cb 255) fun db =>
      visitK p.n p.tab hh sh f db s S 0 rs fun S1 A1 rs1 =>
      loopP p.n p.tab hh sh f db ts S1 A1 rs1 fun S2 A2 rs2 =>
      loopN p.n p.tab hh sh f db ex S2 A2 rs2 fun S3 A3 rs3 =>
      guard (elimT p.h hm O (Nat.shiftRight cb sh) A3) (k S3 rs3))
    (fun f t ss => p.tab.getK f fun cb => forceN (Nat.land cb 255) fun db =>
      visitK p.n p.tab hh sh f db t S 0 rs fun S1 A1 rs1 =>
      loopP p.n p.tab hh sh f db ss S1 A1 rs1 fun S3 A3 rs3 =>
      guard (elimT p.h hm O (Nat.shiftRight cb sh) A3) (k S3 rs3)) g

noncomputable def gatesK (p : Par) (hm hh sh O : Nat) :
    List Gate → Trie → List Nat → (Trie → List Nat → Bool) → Bool :=
  List.rec (motive := fun _ => Trie → List Nat → (Trie → List Nat → Bool) → Bool)
    (fun S rs k => k S rs)
    (fun g _ ih S rs k => gateK p hm hh sh O g S rs fun S1 rs1 => ih S1 rs1 k)

/-- **the label replay of one segment** (see the file header) -/
noncomputable def segK (p : Par) (gs : List Gate) (S S' : Trie) (rs : List Nat) : Bool :=
  guard (Nat.ble 1 p.h) <|
  forceN (Nat.sub (Nat.pow 2 p.h) 1) fun hm =>
  forceN (Nat.div (Nat.sub (Nat.pow 2 (Nat.mul p.h p.K)) 1) hm) fun O =>
  guard (Nat.beq (Nat.mul O hm) (Nat.sub (Nat.pow 2 (Nat.mul p.h p.K)) 1))
    (gatesK p hm (Nat.mul p.h p.h) (Nat.add 8 p.h) O gs S rs fun S1 rs1 =>
      guard (Trie.beqK S1 S') (List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) rs1))

/-- a gate list without adds (the final climbs) -/
def noAdds : List Gate → Bool
  | [] => true
  | .out _ _ [] _ :: gs => noAdds gs
  | _ :: _ => false

end GLab
