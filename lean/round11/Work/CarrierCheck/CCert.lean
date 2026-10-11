import Work.SharedSumChecker.PCert
import Work.Combine.Ranks

/-!
# (key: carrier-check) Certificate of a CARRIER helper circuit: data, label check, shape check

Core Lean only (no Mathlib), so that the kernel-check modules stay small.

A carrier circuit is ONE labelled micro-program on the roles

* `0 .. v-1`            the bank roles `x_t`   (first label: the line of the triple `t`),
* `v .. v+R-1`          the helper slots       (first label: zero),
* `v+R .. v+R+v-1`      the bank roles `y_S`   (first label: zero),

in which EVERY role is a track with explicit frame changes and gates (the op format of
`Work.SharedSumChecker.Check`, unchanged).  New against `PCert`: the bank roles take part in
gates (x roles as sources at every label of their climb, y roles as targets at every label of
theirs), and their climbs are written in the certificate, in several blocks.

The program has two phases, cut at the SCATTER of the retained totals:

* `A`   before the scatter (loads, addition circuit);
* at the cut: the slot `ret k` stands at the stored label `retLab k`, every `y_S` still stands
  at the zero label (`expect`s, generated);  the scatter itself (`scat`) is not an op: the
  invocation theorem does it through scratch copies;
* `B`   after the scatter (bank steps, pieces);
* `fins`  the last frame changes of the x roles and of the slots (real blocks), to the full
  label `eF`;
* `ysh`   for every `y_S` one FICTITIOUS last move along its triple, to the full label: it is
  not part of the word, it only tells the checker that `y_S` ends at `t_S^⊥` (and makes every
  role complete: `h` moves, projector `1`).

Conditions on the gates (`Op.carrier`): all roles below `v + R + v`, no gate INTO an x role,
no gate READING a y role, sources and targets different.  That every gate joins equal labels
is the label check (`SSC.check`, unchanged).  The scalar identity is `Work.CarrierCheck.ScalDef`.
-/

namespace SSC

/-- a gate op of a carrier circuit: all roles below `v + R + v`; for every gate `t += c * s` of
the op the source is an x role or a slot (`s < v + R`), the target a slot or a y role (`v ≤ t`),
and `s ≠ t`.  (An op without targets has no gate: it only moves its "source" parts.) -/
def Op.carrier (v R : Nat) : Op → Bool
  | .bip srcs tgts _ =>
    (srcs ++ tgts).all (fun pt => decide (pt.role < v + R + v)) &&
      srcs.all (fun s => tgts.all (fun t =>
        decide (s.role < v + R ∧ v ≤ t.role ∧ s.role ≠ t.role)))
  | _ => false

/-- the fictitious completions of the y roles `r, r+1, ..`: one move along the triple, one
shift, arrival at `e` -/
def yfinsFrom (e : Nat) : Nat → List Nat → List Nat → List FinE
  | _, [], _ => []
  | r, z :: zs, [] => ⟨r, [z], 0, e⟩ :: yfinsFrom e (r+1) zs []
  | r, z :: zs, s :: ss => ⟨r, [z], s, e⟩ :: yfinsFrom e (r+1) zs ss

structure CCert where
  p : Par
  v : Nat
  R : Nat
  /-- digit width of the scalar check -/
  sw : Nat
  trips : List Nat
  A : List (List Op)
  B : List (List Op)
  fins : List (List FinE)
  ysh : List Nat
  N : Nat
  ret : List Nat
  retLab : List Nat
  scat : List (List (Nat × Coef))
  eF : Nat

namespace CCert
variable (c : CCert)

/-- number of roles -/
def n : Nat := c.v + c.R + c.v

/-- stored first labels: the lines for the x roles, zero for all others -/
def inits : List Nat :=
  (c.trips.map fun z => enc (upd c.p 0 (spread c.p z) z)) ++ List.replicate (c.R + c.v) 0

/-- at the scatter: the retained slots at their stored labels, every y role at zero -/
def eA : List (Nat × Nat) :=
  ((c.ret.zip c.retLab).map fun x => (c.v + x.1, x.2)) ++
    (List.range c.v).map fun S => (c.v + c.R + S, 0)

def cs : List (List Op) := c.A ++ [expOps c.eA] ++ c.B

def yfins : List FinE := yfinsFrom c.eF (c.v + c.R) c.trips c.ysh

/-- the label part of the kernel check: every gate at one common label, every role ends at
`eF`, `N` kernel moves (the `v` fictitious ones included) -/
noncomputable def labelCheck : Bool := check c.p c.inits c.cs (c.fins ++ [c.yfins]) c.N

/-- the shape tests -/
def shapeCheck : Bool :=
  decide (0 < c.p.h) && decide (c.p.h < c.p.w) && decide (c.p.cnt = 1) && decide (0 < c.v) &&
  decide (0 < c.R) && decide (c.trips.length = c.v) && decide (c.ysh.length = c.v) &&
  decide (c.retLab.length = c.ret.length) && decide (c.scat.length = c.v) &&
  c.A.flatten.all (Op.carrier c.v c.R) && c.B.flatten.all (Op.carrier c.v c.R) &&
  c.ret.all (fun x => decide (x < c.R)) &&
  c.scat.all (fun l => l.all fun x => decide (x.1 < c.ret.length)) &&
  covB c.fins.flatten 0 (c.v + c.R) c.eF &&
  c.fins.flatten.all (fun fe => decide (fe.r < c.v + c.R)) &&
  fullB c.p (dec c.eF)

/-! ## block ranks (plain data) and their kernel count

Every frame change written in the certificate (one part of a gate op, one real final entry) is
ONE block; its rank is the number of its kernel moves.  `ranksOf lo len` lists the ranks of the
blocks of the roles `lo ≤ r < lo + len`. -/

def ranksOf (lo len : Nat) : List Nat :=
  opsRanks lo len c.A.flatten ++ opsRanks lo len c.B.flatten ++ finsRanks lo len c.fins.flatten

/-- ranks of the blocks of the scratch copies: the dimensions of the retained labels -/
def cenRanks : List Nat := c.retLab.map fun L => cntOf c.p (dec L)

/-- **the ranks of the blocks of one invocation**: all bank roles, all slots, the copies -/
def invRanks : List Nat := c.ranksOf 0 c.n ++ c.cenRanks

/-- `∑ wt (rank)` over the blocks of the roles `lo ≤ r < hi`, for the kernel -/
noncomputable def sumWK (wt : Nat → Nat) (lo hi : Nat) : Nat :=
  finChunksW wt lo hi c.fins (chunksW wt lo hi c.B (chunksW wt lo hi c.A 0))

/-- `∑ wt (rank)` over `c.invRanks`, for the kernel -/
noncomputable def sumW (wt : Nat → Nat) : Nat :=
  cenW wt c.p c.retLab (finChunksW wt 0 (Nat.add 0 c.n) c.fins
    (chunksW wt 0 (Nat.add 0 c.n) c.B (chunksW wt 0 (Nat.add 0 c.n) c.A 0)))

end CCert

end SSC
