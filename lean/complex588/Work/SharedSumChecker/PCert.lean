import Work.SharedSumChecker.Check

/-!
# Shared-sum checker: the certificate of a helper circuit (data and Boolean shape tests)

Core Lean only.  `PCert` is the data of the helper circuit of ONE invocation: the triples, the
labelled programs of the loading phase (`F4`), of the addition circuit (`F5`), of the piece
phase (`F7`), the final frame changes, and the tables of the scalar read-out (`src`, `ret`,
`pieces`, `scat`).  What follows from an accepted certificate is proved in
`Work.SharedSumChecker.Circ` (labels) and `Work.SharedSumChecker.Scalar` (scalar identity).

Roles of the certificate: `0 .. v-1` = the inputs `X_t` (first label: the line of `t`),
`v .. v+R-1` = the helper slots, `v+R+S` = a reference role per target `S` (it only serves to
compute the label of `t_S^⊥`).
-/

namespace SSC

def expOps (l : List (Nat × Nat)) : List Op := l.map fun x => Op.expect x.1 x.2

/-- reference roles `r, r+1, ..` expected at the stored labels of the list -/
def refE : Nat → List Nat → List (Nat × Nat)
  | _, [] => []
  | r, P :: ps => (r, P) :: refE (r+1) ps

/-- a gate op or an `expect` (no copy, no erase) -/
def Op.plain : Op → Bool
  | .bip _ _ _ => true
  | .expect _ _ => true
  | _ => false

/-- a gate op all of whose roles are helper slots, sources and targets different -/
def Op.slotGate (v R : Nat) : Op → Bool
  | .bip srcs tgts _ =>
    (srcs ++ tgts).all (fun pt => decide (v ≤ pt.role ∧ pt.role < v + R)) &&
      srcs.all (fun s => tgts.all (fun t => decide (s.role ≠ t.role)))
  | _ => false

/-- the entries are the roles `r, r+1, ..` (`n` of them) and all end at the stored label `e` -/
def covB : List FinE → Nat → Nat → Nat → Bool
  | _, _, 0, _ => true
  | [], _, _+1, _ => false
  | fe :: fs, r, n+1, e => decide (fe.r = r) && decide (fe.e = e) && covB fs (r+1) n e

/-- the entries are the reference roles `r, r+1, ..`: one move along the triple, end at `e` -/
def refB : List FinE → Nat → List Nat → Nat → Bool
  | _, _, [], _ => true
  | [], _, _ :: _, _ => false
  | fe :: fs, r, z :: zs, e =>
    decide (fe.r = r) && decide (fe.dirs = [z]) && decide (fe.e = e) && refB fs (r+1) zs e

/-- the stored label `P` is a full label: projector `1`, `h` moves -/
def fullB (p : Par) (L : Nat) : Bool :=
  (List.range p.h).all (fun i => (List.range p.h).all fun j =>
    L.testBit (p.K2 + p.w * i + j) == decide (i = j)) && decide (cntOf p L = p.h)

structure PCert where
  p : Par
  v : Nat
  R : Nat
  trips : List Nat
  F4 : List (List Op)
  F5 : List (List Op)
  F7 : List (List Op)
  fins : List (List FinE)
  N : Nat
  src : List Nat
  ret : List Nat
  retLab : List Nat
  pieces : List (List (Nat × Coef))
  scat : List (List (Nat × Coef))
  perps : List Nat
  eF : Nat

namespace PCert
variable (c : PCert)

def inits : List Nat := c.trips.map fun z => enc (upd c.p 0 (spread c.p z) z)
def e4 : List (Nat × Nat) := (c.src.zip c.inits).map fun x => (c.v + x.1, x.2)
def e5 : List (Nat × Nat) := (c.ret.zip c.retLab).map fun x => (c.v + x.1, x.2)
def e7 : List (Nat × Nat) :=
  (c.pieces.zip c.perps).flatMap (fun x => x.1.map fun y => (c.v + y.1, x.2))
    ++ refE (c.v + c.R) c.perps
def cs : List (List Op) :=
  c.F4 ++ [expOps c.e4] ++ c.F5 ++ [expOps c.e5] ++ c.F7 ++ [expOps c.e7]

/-- the label part of the kernel check -/
noncomputable def labelCheck : Bool := check c.p c.inits c.cs c.fins c.N

/-- the shape tests -/
def shapeCheck : Bool :=
  decide (0 < c.p.h) && decide (c.p.h < c.p.w) && decide (c.p.cnt = 1) && decide (0 < c.R) &&
  decide (c.trips.length = c.v) && decide (c.src.length = c.v) && decide (c.ret.length = c.p.h) &&
  decide (c.retLab.length = c.p.h) && decide (c.pieces.length = c.v) &&
  decide (c.perps.length = c.v) &&
  c.cs.flatten.all Op.plain && c.F5.flatten.all (Op.slotGate c.v c.R) &&
  c.src.all (fun x => decide (x < c.R)) && c.ret.all (fun x => decide (x < c.R)) &&
  c.pieces.all (fun l => l.all fun x => decide (x.1 < c.R)) &&
  covB c.fins.flatten 0 (c.v + c.R) c.eF &&
  refB (c.fins.flatten.drop (c.v + c.R)) (c.v + c.R) c.trips c.eF &&
  fullB c.p (dec c.eF)

end PCert

end SSC
