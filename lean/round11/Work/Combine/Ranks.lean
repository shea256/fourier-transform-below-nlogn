import Work.SharedSumChecker.PCert

/-!
# (key: combine) Block ranks of a helper-circuit certificate (plain data, core Lean only)

Every frame change of a helper slot (role `v ≤ r < v + R`) written in a certificate `PCert` --
one part of a gate op, or one final entry -- is ONE block of the whole-block engine; its rank is
the number of kernel moves of that frame change.  This file only COUNTS them; that the blocks
are legal and that these are their ranks is proved in `Work.Combine.Chunks` / `.XCirc`.

* `Op.ranks`, `FinE.ranks`, `opsRanks`, `finsRanks`   the ranks read off the certificate text;
* `PCert.invRanks`   the ranks of the blocks of ONE invocation on helper slots and scratch copies;
* `PCert.sumW c wt`   `∑ wt (rank)` over those blocks, written for evaluation by the Lean kernel
                     (`by decide +kernel`); its meaning is proved in `Work.Combine.Hist`.

No Mathlib, so that the kernel-check modules stay small.
-/

namespace SSC

/-- rank of the block of one frame change (helper slots only) -/
def moveRanks (v R r : Nat) (dirs : List Nat) : List Nat :=
  if v ≤ r ∧ r < v + R then [dirs.length] else []

def Part.ranks (v R : Nat) : Part → List Nat
  | .old r dirs _ => moveRanks v R r dirs
  | .new r dirs _ => moveRanks v R r dirs
  | .stay _ => []

/-- the ranks of the blocks of an op: one per frame change of a helper slot -/
def Op.ranks (v R : Nat) : Op → List Nat
  | .bip srcs tgts _ => (srcs ++ tgts).flatMap (Part.ranks v R)
  | _ => []

def opsRanks (v R : Nat) (ops : List Op) : List Nat := ops.flatMap (Op.ranks v R)

def FinE.ranks (v R : Nat) (fe : FinE) : List Nat := moveRanks v R fe.r fe.dirs
def finsRanks (v R : Nat) (fs : List FinE) : List Nat := fs.flatMap (FinE.ranks v R)

namespace PCert
variable (c : PCert)

/-- block ranks of the helper slots in the loading phase -/
def ranks4 : List Nat := opsRanks c.v c.R c.F4.flatten
/-- block ranks of the helper slots in the addition circuit -/
def ranks5 : List Nat := opsRanks c.v c.R c.F5.flatten
/-- block ranks of the helper slots in the piece phase -/
def ranks7 : List Nat := opsRanks c.v c.R c.F7.flatten
/-- block ranks of the last frame changes of the helper slots -/
def ranksF : List Nat := finsRanks c.v c.R c.fins.flatten
/-- block ranks of the scratch copies: the dimensions of the labels of the retained totals -/
def cenRanks : List Nat := c.retLab.map fun L => cntOf c.p (dec L)
/-- **the ranks of the blocks of one invocation** on helper slots and scratch copies -/
def invRanks : List Nat := c.ranks4 ++ c.ranks5 ++ c.ranks7 ++ c.ranksF ++ c.cenRanks

end PCert

/-! ## counting for the kernel

`PCert.sumW c wt` is `∑ wt (rank)` over the blocks of `c.invRanks`, computed in ONE pass over the
certificate, tail recursively with a forced accumulator (no intermediate lists), so that the
Lean kernel can evaluate it cheaply (`by decide +kernel`).  With `wt = wEq r` it counts the blocks
of rank `r`; with `wt = wGt B` it counts the blocks of rank above `B`.  Meaning proved in
`Work.Combine.Hist` (`PCert.sumW_eq`). -/

/-- `acc` + length of the list -/
noncomputable def lenK {α : Type} (l : List α) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc) (fun _ _ ih acc => ih (Nat.succ acc)) l

/-- one frame change of the role `r` (`e = v + R`): a helper slot adds the weight of its rank -/
noncomputable def moveW (wt : Nat → Nat) (v e r : Nat) (dirs : List Nat) (acc : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) acc (Nat.add acc (wt (lenK dirs 0)))
    (Bool.rec (motive := fun _ => Bool) false (Nat.ble (Nat.succ r) e) (Nat.ble v r))

noncomputable def partW (wt : Nat → Nat) (v e : Nat) (pt : Part) (acc : Nat) : Nat :=
  Part.rec (motive := fun _ => Nat) (fun r dirs _ => moveW wt v e r dirs acc)
    (fun r dirs _ => moveW wt v e r dirs acc) (fun _ => acc) pt

noncomputable def partsW (wt : Nat → Nat) (v e : Nat) (pts : List Part) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun pt _ ih acc => forceN (partW wt v e pt acc) ih) pts

noncomputable def opW (wt : Nat → Nat) (v e : Nat) (op : Op) (acc : Nat) : Nat :=
  Op.rec (motive := fun _ => Nat) (fun srcs tgts _ => partsW wt v e tgts (partsW wt v e srcs acc))
    (fun _ _ => acc) (fun _ _ => acc) (fun _ => acc) (fun _ _ => acc) op

noncomputable def opsW (wt : Nat → Nat) (v e : Nat) (ops : List Op) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun op _ ih acc => forceN (opW wt v e op acc) ih) ops

noncomputable def chunksW (wt : Nat → Nat) (v e : Nat) (cs : List (List Op)) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun ops _ ih acc => forceN (opsW wt v e ops acc) ih) cs

noncomputable def finW (wt : Nat → Nat) (v e : Nat) (fe : FinE) (acc : Nat) : Nat :=
  FinE.rec (motive := fun _ => Nat) (fun r dirs _ _ => moveW wt v e r dirs acc) fe

noncomputable def finsW (wt : Nat → Nat) (v e : Nat) (fs : List FinE) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun fe _ ih acc => forceN (finW wt v e fe acc) ih) fs

noncomputable def finChunksW (wt : Nat → Nat) (v e : Nat) (fs : List (List FinE)) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun fl _ ih acc => forceN (finsW wt v e fl acc) ih) fs

/-- the scratch copies: the weight of the move count of every retained label -/
noncomputable def cenW (wt : Nat → Nat) (p : Par) (ls : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun L _ ih acc => forceN (Nat.add acc (wt (cntOf p (dec L)))) ih) ls

/-- **`∑ wt (rank)` over the blocks of one invocation** (helper slots and scratch copies) -/
noncomputable def PCert.sumW (c : PCert) (wt : Nat → Nat) : Nat :=
  cenW wt c.p c.retLab (finChunksW wt c.v (Nat.add c.v c.R) c.fins
    (chunksW wt c.v (Nat.add c.v c.R) c.F7 (chunksW wt c.v (Nat.add c.v c.R) c.F5
      (chunksW wt c.v (Nat.add c.v c.R) c.F4 0))))

/-- weight `1` at rank `r`, `0` elsewhere -/
noncomputable def wEq (r : Nat) : Nat → Nat :=
  fun n => Bool.rec (motive := fun _ => Nat) 0 1 (Nat.beq n r)

/-- weight `1` above rank `B`, `0` up to `B` -/
noncomputable def wGt (B : Nat) : Nat → Nat :=
  fun n => Bool.rec (motive := fun _ => Nat) 1 0 (Nat.ble n B)

end SSC
