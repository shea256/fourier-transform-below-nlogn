import Lean
open Lean

/-!
Independent stand-in for the `comparator` statement check (which needs Linux-only `landrun`).

Usage (from the project root, after `lake build`):

  lake env lean --run checks/Compare.lean <challengeModule> <solutionModule> <theorem>...

It loads the challenge module and the solution module as two separate environments and, for
each named theorem, checks that

1. the solution declares it as a `theorem` whose statement is the same kernel term as the
   challenge's (the challenge proves it by `sorry`);
2. every constant the statement depends on, transitively through types, definition bodies,
   inductive types, constructors and recursors, is present in the solution environment with an
   identical kernel declaration;
3. the solution's proof, followed transitively through every proof and definition it uses,
   rests only on the permitted axioms `propext`, `Quot.sound`, `Classical.choice`.
-/

deriving instance BEq for Lean.QuotKind

namespace Cmp

def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

/-- Names an expression refers to without a `const` node: the structure of a primitive
projection, and `Nat` / `String` behind literals. -/
partial def implicitGo (e : Expr) : StateM (Std.HashSet Expr × Array Name) Unit := do
  if (← get).1.contains e then return
  modify fun (seen, out) => (seen.insert e, out)
  match e with
  | .proj s _ b => modify (fun (seen, out) => (seen, out.push s)); implicitGo b
  | .lit (.natVal _) => modify fun (seen, out) => (seen, out.push ``Nat)
  | .lit (.strVal _) => modify fun (seen, out) => (seen, out.push ``String)
  | .app f a => implicitGo f; implicitGo a
  | .lam _ t b _ => implicitGo t; implicitGo b
  | .forallE _ t b _ => implicitGo t; implicitGo b
  | .letE _ t v b _ => implicitGo t; implicitGo v; implicitGo b
  | .mdata _ b => implicitGo b
  | _ => pure ()

def implicitNames (e : Expr) : Array Name :=
  ((implicitGo e).run ({}, #[])).2.2

/-- Every constant an expression refers to. -/
def exprNames (e : Expr) : Array Name := e.getUsedConstants ++ implicitNames e

/-- Constants a declaration refers to. Theorem proofs are followed only if `withProofs`. -/
def deps (ci : ConstantInfo) (withProofs : Bool) : Array Name := Id.run do
  let mut out := exprNames ci.type
  match ci with
  | .defnInfo v => out := out ++ exprNames v.value
  | .opaqueInfo v => out := out ++ exprNames v.value
  | .thmInfo v => if withProofs then out := out ++ exprNames v.value
  | .inductInfo v => out := out ++ v.ctors.toArray ++ v.all.toArray
  | .ctorInfo v => out := out.push v.induct
  | .recInfo v =>
    out := out ++ v.all.toArray
    for r in v.rules do
      out := (out ++ exprNames r.rhs).push r.ctor
  | .axiomInfo _ => pure ()
  | .quotInfo _ => pure ()
  return out

/-- Transitive closure of `deps` from `roots`. Returns the closure and any unresolved names. -/
def closure (env : Environment) (roots : Array Name) (withProofs : Bool) :
    NameSet × Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut missing : Array Name := #[]
  let mut stack := roots
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    match env.find? n with
    | none => missing := missing.push n
    | some ci => stack := stack ++ deps ci withProofs
  return (seen, missing)

/-- `none` if the two declarations are the same kernel object, else a description. -/
def differ (a b : ConstantInfo) (checkProof : Bool) : Option String :=
  if kind a != kind b then some s!"kind: {kind a} vs {kind b}"
  else if a.levelParams != b.levelParams then some "universe parameters differ"
  else if !(a.type == b.type) then some "type differs"
  else match a, b with
    | .defnInfo x, .defnInfo y =>
      if !(x.value == y.value) then some "definition body differs"
      else if x.safety != y.safety then some "safety differs" else none
    | .opaqueInfo x, .opaqueInfo y =>
      if !(x.value == y.value) then some "opaque body differs"
      else if x.isUnsafe != y.isUnsafe then some "unsafe flag differs" else none
    | .thmInfo x, .thmInfo y =>
      if checkProof && !(x.value == y.value) then some "proof differs" else none
    | .axiomInfo x, .axiomInfo y =>
      if x.isUnsafe != y.isUnsafe then some "unsafe flag differs" else none
    | .quotInfo x, .quotInfo y =>
      if x.kind != y.kind then some "quot kind differs" else none
    | .inductInfo x, .inductInfo y =>
      if x.numParams != y.numParams then some "numParams differs"
      else if x.numIndices != y.numIndices then some "numIndices differs"
      else if x.all != y.all then some "mutual block differs"
      else if x.ctors != y.ctors then some "constructor list differs"
      else if x.isRec != y.isRec then some "isRec differs"
      else if x.isUnsafe != y.isUnsafe then some "unsafe flag differs"
      else if x.isReflexive != y.isReflexive then some "isReflexive differs"
      else if x.numNested != y.numNested then some "numNested differs" else none
    | .ctorInfo x, .ctorInfo y =>
      if x.induct != y.induct then some "parent inductive differs"
      else if x.cidx != y.cidx then some "constructor index differs"
      else if x.numParams != y.numParams then some "numParams differs"
      else if x.numFields != y.numFields then some "numFields differs"
      else if x.isUnsafe != y.isUnsafe then some "unsafe flag differs" else none
    | .recInfo x, .recInfo y =>
      if x.all != y.all then some "mutual block differs"
      else if x.numParams != y.numParams then some "numParams differs"
      else if x.numIndices != y.numIndices then some "numIndices differs"
      else if x.numMotives != y.numMotives then some "numMotives differs"
      else if x.numMinors != y.numMinors then some "numMinors differs"
      else if x.k != y.k then some "K flag differs"
      else if x.isUnsafe != y.isUnsafe then some "unsafe flag differs"
      else if x.rules.length != y.rules.length then some "number of recursor rules differs"
      else if (x.rules.zip y.rules).any (fun (r, s) =>
          r.ctor != s.ctor || r.nfields != s.nfields || !(r.rhs == s.rhs)) then
        some "recursor rules differ"
      else none
    | _, _ => some "unreachable kind mismatch"

def moduleOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some i => toString (env.header.moduleNames[i.toNat]!)
  | none => "<none>"

def permitted : List Name := [``propext, ``Quot.sound, ``Classical.choice]

end Cmp

open Cmp in
unsafe def main (args : List String) : IO UInt32 := do
  let chal :: sol :: thms := args
    | IO.eprintln "usage: Compare <challengeModule> <solutionModule> <theorem>..."; return 2
  initSearchPath (← findSysroot)
  let envC ← importModules #[{ module := chal.toName }] {} (trustLevel := 0)
  let envS ← importModules #[{ module := sol.toName }] {} (trustLevel := 0)
  IO.println s!"challenge module: {chal}   ({envC.header.moduleNames.size} modules loaded)"
  IO.println s!"solution module:  {sol}   ({envS.header.moduleNames.size} modules loaded)"
  -- Sanity: proofs of imported theorems must be visible, or the axiom walk would be meaningless.
  -- (`Real.exp_pos` is checked whenever Mathlib is among the imports.)
  match envS.find? ``Nat.add_comm, envS.find? `Real.exp_pos with
  | some (.thmInfo a), some (.thmInfo b) =>
    IO.println s!"sanity: imported proofs are loaded (Nat.add_comm uses {a.value.getUsedConstants.size} constants, Real.exp_pos uses {b.value.getUsedConstants.size})"
  | some (.thmInfo a), none =>
    IO.println s!"sanity: imported proofs are loaded (Nat.add_comm uses {a.value.getUsedConstants.size} constants; Mathlib not imported)"
  | a, b =>
    IO.println s!"FAIL sanity: Nat.add_comm is {a.map kind}, Real.exp_pos is {b.map kind}; expected theorems with bodies"
    return 1
  let mut ok := true
  for t in thms do
    let T := t.toName
    IO.println s!"\n=== {T} ==="
    let some cC := envC.find? T
      | IO.println "FAIL: not declared in challenge"; ok := false; continue
    let some cS := envS.find? T
      | IO.println "FAIL: not declared in solution"; ok := false; continue
    IO.println s!"challenge: {kind cC} in {moduleOf envC T};  solution: {kind cS} in {moduleOf envS T}"
    unless kind cS == "theorem" do
      IO.println "FAIL: solution does not declare it as a theorem"; ok := false
    if cC.levelParams != cS.levelParams || !(cC.type == cS.type) then
      IO.println "FAIL: statement (type) differs between challenge and solution"; ok := false
    else
      IO.println "OK: statement is the same kernel term in both"
    -- Challenge proof must be the placeholder, solution proof must not be.
    let (axC, _) := closure envC #[T] true
    IO.println s!"challenge proof uses sorryAx: {axC.contains ``sorryAx}"
    -- 2. statement dependencies
    let (cl, missC) := closure envC (exprNames cC.type) false
    unless missC.isEmpty do
      IO.println s!"FAIL: unresolved in challenge env: {missC}"; ok := false
    let mut bad := 0
    let mut own : Array (Name × String) := #[]
    for n in cl.toList do
      let some a := envC.find? n | continue
      let inChal := moduleOf envC n == chal
      match envS.find? n with
      | none =>
        IO.println s!"FAIL: {n} missing from solution"; bad := bad + 1
      | some b =>
        match differ a b (checkProof := false) with
        | some why => IO.println s!"FAIL: {n}: {why}"; bad := bad + 1
        | none => if inChal then own := own.push (n, moduleOf envS n)
    IO.println s!"statement depends on {cl.size} constants; {own.size} are declared in the challenge file itself"
    let ownSorted := own.qsort (fun a b => a.1.toString < b.1.toString)
    for (n, m) in ownSorted do
      IO.println s!"  identical: {n}   [solution: {m}]"
    if bad == 0 then IO.println "OK: every statement dependency is identical in the solution"
    else IO.println s!"FAIL: {bad} statement dependencies differ"; ok := false
    -- 3. axioms behind the solution's proof
    let (all, missS) := closure envS #[T] true
    unless missS.isEmpty do
      IO.println s!"FAIL: unresolved in solution env: {missS}"; ok := false
    let axioms := all.toList.filter (fun n => match envS.find? n with
      | some (.axiomInfo _) => true | _ => false)
    let axSorted := (axioms.map toString).toArray.qsort (· < ·)
    IO.println s!"solution proof reaches {all.size} constants; axioms: {axSorted}"
    let extra := axioms.filter (fun n => !permitted.contains n)
    if extra.isEmpty then IO.println "OK: only permitted axioms"
    else IO.println s!"FAIL: non-permitted axioms: {extra}"; ok := false
  IO.println (if ok then "\nRESULT: PASS" else "\nRESULT: FAIL")
  return (if ok then 0 else 1)
