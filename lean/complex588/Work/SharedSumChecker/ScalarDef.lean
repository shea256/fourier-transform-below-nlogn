import Work.SharedSumChecker.PCert

/-!
# Shared-sum checker: the kernel check of the scalar identity `J L V = 1` (functions)

Core Lean only.  The addition circuit is run symbolically on SUPPORTS: every helper slot holds
the set of input triples whose sum it contains (a bit mask); a gate `t += s` is accepted only
if the two sets are disjoint.  Then, for every target `S`, the read-out
`∑ coef * (slot)` is compared with `x_S` by counting, with bit-sliced counters, how often each
input occurs with positive and with negative sign (weights are doubled, so they are integers).
Soundness: `Work.SharedSumChecker.Scalar`.
-/

namespace SSC

/-- for each target part `t`: `sup t := sup t ∪ A` (the two sets must be disjoint) -/
noncomputable def supTgts (A : Nat) (tgts : List Part) : Trie → (Trie → Bool) → Bool :=
  List.rec (motive := fun _ => Trie → (Trie → Bool) → Bool) (fun t k => k t)
    (fun pt _ ih t k => t.getK pt.role fun B => guard (Nat.beq (Nat.land B A) 0)
      (forceN (Nat.lor B A) fun C => ih (t.set pt.role C) k)) tgts

/-- one gate op of the circuit: exactly one source, all coefficients one -/
noncomputable def supOp (op : Op) (t : Trie) (k : Trie → Bool) : Bool :=
  Op.rec (motive := fun _ => Bool)
    (fun srcs tgts coefs => List.rec (motive := fun _ => Bool) false
      (fun s rest _ => List.rec (motive := fun _ => Bool)
        (List.rec (motive := fun _ => Bool) (t.getK s.role fun A => supTgts A tgts t k)
          (fun _ _ _ => false) coefs)
        (fun _ _ _ => false) rest) srcs)
    (fun _ _ => false) (fun _ _ => false) (fun _ => false) (fun _ _ => false) op

noncomputable def supOps (ops : List Op) : Trie → (Trie → Bool) → Bool :=
  List.rec (motive := fun _ => Trie → (Trie → Bool) → Bool) (fun t k => k t)
    (fun op _ ih t k => supOp op t fun t' => ih t' k) ops

noncomputable def supChunks (cs : List (List Op)) : Trie → (Trie → Bool) → Bool :=
  List.rec (motive := fun _ => Trie → (Trie → Bool) → Bool) (fun t k => k t)
    (fun ops _ ih t k => supOps ops t fun t' => ih t' k) cs

/-- initial supports: the source slot of triple `i` holds `{i}` (source slots distinct) -/
noncomputable def supInit (v : Nat) (src : List Nat) : Nat → Trie → (Trie → Bool) → Bool :=
  List.rec (motive := fun _ => Nat → Trie → (Trie → Bool) → Bool) (fun _ t k => k t)
    (fun s _ ih i t k => t.getK (Nat.add v s) fun B => guard (Nat.beq B 0)
      (forceN (Nat.shiftLeft 1 i) fun bit => forceN (Nat.succ i) fun i2 =>
        ih i2 (t.set (Nat.add v s) bit) k)) src

/-! ## bit-sliced counters -/

/-- add the mask `c` once (plane `j` has weight `2^j`; no carry may leave the last plane) -/
noncomputable def addPK (ps : List Nat) : Nat → (List Nat → Bool) → Bool :=
  List.rec (motive := fun _ => Nat → (List Nat → Bool) → Bool)
    (fun c k => guard (Nat.beq c 0) (k []))
    (fun p _ ih c k => forceN (Nat.xor p c) fun p' => forceN (Nat.land p c) fun c' =>
      ih c' fun ps' => k (p' :: ps')) ps

/-- add the mask `c` `n` times -/
noncomputable def addNK (n : Nat) : List Nat → Nat → (List Nat → Bool) → Bool :=
  Nat.rec (motive := fun _ => List Nat → Nat → (List Nat → Bool) → Bool) (fun ps _ k => k ps)
    (fun _ ih ps c k => addPK ps c fun ps' => ih ps' c k) n

/-- sign and doubled absolute value of a coefficient with denominator 1 or 2 -/
noncomputable def weightK (cf : Coef) (k : Bool → Nat → Bool) : Bool :=
  Coef.rec (motive := fun _ => Bool)
    (fun ng num den => Bool.rec (Bool.rec false (k ng (Nat.mul 2 num)) (Nat.beq den 1)) (k ng num)
      (Nat.beq den 2)) cf

/-- accumulate the terms `(index, coef)`; the support is that of the slot `look index` -/
noncomputable def accK (v : Nat) (tS : Trie) (look : Nat → Nat) (l : List (Nat × Coef)) :
    List Nat → List Nat → (List Nat → List Nat → Bool) → Bool :=
  List.rec (motive := fun _ => List Nat → List Nat → (List Nat → List Nat → Bool) → Bool)
    (fun pos neg k => k pos neg)
    (fun x _ ih pos neg k => tS.getK (Nat.add v (look x.1)) fun A => weightK x.2 fun ng w =>
      Bool.rec (addNK w pos A fun pos' => ih pos' neg k) (addNK w neg A fun neg' => ih pos neg' k)
        ng) l

noncomputable def eqK (a : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun b => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) b)
    (fun x _ ih b => List.rec (motive := fun _ => Bool) false
      (fun y ys _ => guard (Nat.beq x y) (ih ys)) b) a

/-- the read-out of target `S` is `x_S` -/
noncomputable def rowK (v : Nat) (tS : Trie) (ret zeros : List Nat) (S : Nat)
    (pc sc : List (Nat × Coef)) : Bool :=
  accK v tS (fun q => q) pc zeros zeros fun pos neg =>
    accK v tS (fun k => ret.getD k 0) sc pos neg fun pos' neg' =>
      addNK 2 neg' (Nat.shiftLeft 1 S) fun neg'' => eqK pos' neg''

noncomputable def rowsK (v : Nat) (tS : Trie) (ret zeros : List Nat)
    (rows : List (List (Nat × Coef) × List (Nat × Coef))) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih S => guard (rowK v tS ret zeros S x.1 x.2) (forceN (Nat.succ S) fun S2 => ih S2))
    rows

/-- **The scalar check of a certificate.** -/
noncomputable def PCert.scalarCheck (c : PCert) : Bool :=
  guard (decide (c.scat.length = c.v) &&
      c.scat.all (fun l => l.all fun x => decide (x.1 < c.p.h)))
    (supInit c.v c.src 0 (Trie.mk c.p.d) fun t0 => supChunks c.F5 t0 fun tS =>
      rowsK c.v tS c.ret (List.replicate 10 0) (c.pieces.zip c.scat) 0)

end SSC
