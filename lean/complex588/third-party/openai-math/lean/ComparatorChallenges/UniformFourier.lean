import Mathlib

namespace OAI

namespace ExactFourier
noncomputable def zeta (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / (n : ℂ))
end ExactFourier

/-!
# Exact scalar and index RAM used for the algorithm

Finite, first-order, expression/program syntax. Arrays below are random-access arrays of
registers (an array-valued register holds its address). An expression building an array uses
a fresh array; `sow` builds by a loop of writes instead of a loop supplying consecutive
entries. Programs have their usual sequential stack evaluation. Evaluation here records work
(including stack, index and array work), the high water mark on produced/logically looped-over
integer values (addresses *within* arrays are integers too), the value, and the side condition
required along the executed path (in particular no division by zero). The charged units of
work are constant time; as usual constant rescalings between ways to charge a fixed number
of scalar or address operations are immaterial.

Enough address bits must be provided BOTH for the integer high water mark (and inputs), AND
for the work bound together with input size, as will be required in the theorem. Indeed we
use the particularly simple RAM convention where temporaries aren't reused: one work unit can
leave at most a constant number of cells (stack, pairs or array cells); whenever many array
entries are made their number is charged. So a constant number of words of those sizes also
suffices for arena addresses. Nothing charges constant work for changing an already published
array to a different array as a whole. Register and stack layouts, and the convention whether
registers hold pairs or addresses of pairs, only have constant factors (the program is fixed).

Scalar and data field registers are separated. Tests and loop/request sizes are on nonnegative
integer registers. There is no instruction for an arbitrary complex constant. A supplied
specified root will be an input. Divisions are on prepared scalars; valid runs require every
such denominator nonzero; the side condition is *not* a test performed by the algorithm.
The Bool mode on the syntax allows or prohibits general products (two-input convolution
versus the transform); even when allowed we use separate register kinds before and after
the bilinear products.

Definitions are mathematical operation-count semantics, not a model of running Lean code.
E.g. a function on Fin n represents the n cells of a random-access array, not a function
closure at runtime.
-/

namespace PowerSaving

universe u v

variable {α : Type u} {β : Type v}

/-- Register arrays. -/
structure Tape (α : Type u) where
  len : ℕ
  pos : Fin len → α

namespace Tape

def empty (α : Type u) : Tape α := ⟨0, Fin.elim0⟩

/-- Materialized array. -/
def tab (n : ℕ) (f : ℕ → α) : Tape α := ⟨n, fun i => f i.val⟩

/-- Read with fixed out of bounds default. -/
def look (v : Tape α) (i : ℕ) (z : α) : α :=
  if h : i < v.len then v.pos ⟨i,h⟩ else z

@[simp] theorem look_of_lt (v : Tape α) (z : α) {i} (h : i < v.len) :
    v.look i z = v.pos ⟨i,h⟩ := by simp [look, h]

@[simp] theorem look_of_le (v : Tape α) (z : α) {i} (h : v.len ≤ i) :
    v.look i z = z := by simp [look, Nat.not_lt.mpr h]

/-- Semantics of a write into fresh storage; out-of-range writes are ignored. Only used
  during construction, never a whole-tape functional update instruction. -/
def set (v : Tape α) (i : ℕ) (x : α) : Tape α :=
  ⟨v.len, fun j => if j.val = i then x else v.pos j⟩

def sow (len count : ℕ) (z : α) (f : ℕ → ℕ × α) : Tape α :=
  iter count
where
  iter : ℕ → Tape α
  | 0 => tab len (fun _ => z)
  | i+1 => (iter i).set (f i).1 (f i).2

def map (f : α → β) (v : Tape α) : Tape β := ⟨v.len, fun i => f (v.pos i)⟩

end Tape

namespace RAM

inductive Paint
  | scalar
  | left
  | right
  | both

inductive Ty
  | w
  | c : Paint → Ty
  | p : Ty → Ty → Ty
  | a : Ty → Ty

open Ty

abbrev sc := c .scalar

@[reducible] def Ty.T : Ty → Type
  | w => ℕ
  | c _ => ℂ
  | p s b => s.T × b.T
  | a b => Tape b.T

noncomputable def Ty.blank : (t : Ty) → t.T
  | w => 0
  | c _ => 0
  | p s t => (s.blank, t.blank)
  | a b => Tape.empty b.T

/-- One basic work unit below pays for O(1) primitive RAM operations; includes loop and
  stack overhead. `peak` tracks produced/needed integer quantities beyond inputs
  (total allocation for stack and array bases is covered separately by work). -/
structure Bill (α : Type u) where
  val : α
  work : ℕ
  peak : ℕ
  valid : Prop

namespace Bill

/-- Charge some work and optionally a new word bound. -/
def pay (b : Bill α) (n : ℕ) (m : ℕ) : Bill α :=
  ⟨b.val, b.work+n, max b.peak m, b.valid⟩

/-- Both computations are evaluated. -/
def pass (b : Bill α) (f : α → Bill β) : Bill β :=
  let d := f b.val
  ⟨d.val, b.work+d.work, max b.peak d.peak, b.valid ∧ d.valid⟩

def one (x : α) : Bill α := ⟨x,1,0,True⟩
def word (x : ℕ) : Bill ℕ := ⟨x,1,x,True⟩

/-- Execute f 0 through f (n-1), iterating an accumulator. -/
def steps (init : α) (f : ℕ → α → Bill α) : ℕ → Bill α
  | 0 => Bill.one init
  | i+1 => ((steps init f i).pass (f i)).pay 1 (i+1)

/-- Build Tape len by count writes (initialized with a blank z). -/
def sow (len count : ℕ) (z : α) (f : ℕ → Bill (ℕ × α)) : Bill (Tape α) :=
  (steps (Tape.tab len (fun _ => z))
    (fun i v => (f i).pass (fun s => one (v.set s.1 s.2))) count).pay (1+len) len

/-- Build Tape len. As for sow we can first allocate then perform writes. -/
def tab (len : ℕ) (z : α) (f : ℕ → Bill α) : Bill (Tape α) :=
  sow len len z (fun i => (f i).pass (fun y => one (i,y)))

end Bill

inductive NOp
  | add | sub | mul | div | mod | lt  -- truncated subtraction; compare returns 1 or 0

inductive Atom (allow : Bool) : Ty → Ty → Type
  | lit {a} (n : ℕ) : Atom allow a w
  | int (f : NOp) : Atom allow (p w w) w
  | cz (t) {a} : Atom allow a (c t)
  | cone {a} : Atom allow a sc
  | add (t) : Atom allow (p (c t) (c t)) (c t)
  | sub (t) : Atom allow (p (c t) (c t)) (c t)
  | scale (t) : Atom allow (p sc (c t)) (c t)
  | inv : Atom allow sc sc
  | cross (h : allow = true) :
      Atom allow (p (c .left) (c .right)) (c .both)
  | id {a} : Atom allow a a
  | fst {a b} : Atom allow (p a b) a
  | snd {a b} : Atom allow (p a b) b
  | len {s} : Atom allow (a s) w
  | look {s} : Atom allow (p (a s) w) s

noncomputable def NOp.run : NOp → (ℕ × ℕ) → Bill ℕ
  | .add, (i,j) => Bill.word (i+j)
  | .sub, (i,j) => Bill.word (i-j)
  | .mul, (i,j) => Bill.word (i*j)
  | .div, (i,j) => Bill.word (i/j) -- includes usual guard (returns zero)
  | .mod, (i,j) => Bill.word (i%j) -- like Lean: returns i if j=0
  | .lt, (i,j) => Bill.word (if i<j then 1 else 0)

noncomputable def Atom.run {allow a b} : Atom allow a b → a.T → Bill b.T
  | .lit n, _ => Bill.word n
  | .int f, x => f.run x
  | .cz _, _ => Bill.one 0
  | .cone, _ => Bill.one 1
  | .add _, (x,y) => Bill.one (x+y)
  | .sub _, (x,y) => Bill.one (x-y)
  | .scale _, (x,y) => Bill.one (x*y)
  | .inv, x => ⟨x⁻¹,1,0,x ≠ 0⟩
  | .cross _, (x,y) => Bill.one (x*y)
  | .id, x => Bill.one x
  | .fst, x => Bill.one x.1
  | .snd, x => Bill.one x.2
  | .len, x => Bill.word x.len
  | @Atom.look _ s, (x,i) => Bill.one (x.look i s.blank)

abbrev Port := Option (Ty × Ty)

/-- `call` is internal for bounded recursion; a program has Port = none. `loop`, `tab`
  and `sow` retain the input to access parameters in the body. `descend` sets up bounded
  recursion, reading fuel and initial argument. -/
inductive Code (allow : Bool) : Port → Ty → Ty → Type
  | atom {r s t} (op : Atom allow s t) : Code allow r s t
  | comp {r s t u} (f : Code allow r s t) (g : Code allow r t u) : Code allow r s u
  | fork {r s t u} (f : Code allow r s t) (g : Code allow r s u) : Code allow r s (p t u)
  | ifz {r s t} (q : Code allow r s w) (f g : Code allow r s t) : Code allow r s t
  | loop {r s t} (n : Code allow r s w) (init : Code allow r s t)
      (body : Code allow r (p s (p w t)) t) : Code allow r s t
  | tab {r s t} (n : Code allow r s w)
      (body : Code allow r (p s w) t) : Code allow r s (a t)
  | sow {r s t} (n count : Code allow r s w)
      (body : Code allow r (p s w) (p w t)) : Code allow r s (a t)
  | importClosed {r s t} (f : Code allow none s t) : Code allow r s t
  | call {s t} : Code allow (some (s,t)) s t
  | descend {r s t} (base : Code allow none s t)
      (body : Code allow (some (s,t)) s t) : Code allow r (p w s) t

@[reducible] def Handler : Port → Type
  | none => Unit
  | some (s,t) => s.T → Bill t.T

def depthRun (base : α → Bill β)
    (step : (α → Bill β) → (α → Bill β)) : ℕ → α → Bill β
  | 0, x => (base x).pay 1 0
  | n+1, x => (step (depthRun base step n) x).pay 1 (n+1)

noncomputable def Code.run {allow r s t} : Code allow r s t → Handler r → s.T → Bill t.T
  | .atom op, _, x => op.run x
  | .comp f g, h, x => ((f.run h x).pass (g.run h)).pay 1 0
  | .fork f g, h, x => (f.run h x).pass (fun y => (g.run h x).pass (fun z => Bill.one (y,z)))
  | .ifz q f g, h, x => ((q.run h x).pass (fun y =>
      if (y : ℕ) = 0 then f.run h x else g.run h x)).pay 1 0
  | .loop n init body, h, x =>
      ((n.run h x).pass (fun l => (init.run h x).pass (fun y =>
        Bill.steps y (fun i z => body.run h (x,(i,z))) l))).pay 1 0
  | @Code.tab _ _ _ t n body, h, x =>
      ((n.run h x).pass (fun l =>
        Bill.tab l t.blank (fun i => body.run h (x,i)))).pay 1 0
  | @Code.sow _ _ _ t n count body, h, x =>
      ((n.run h x).pass (fun l => (count.run h x).pass (fun k =>
        Bill.sow l k t.blank (fun i => body.run h (x,i))))).pay 1 0
  | .importClosed f, _, x => (f.run () x).pay 1 0
  | .call, h, x => (h x).pay 1 0
  | .descend base step, _, (k,x) =>
      (depthRun (base.run ()) (step.run) k x).pay 1 k

abbrev Prog (allow : Bool) (s t : Ty) := Code allow none s t

noncomputable abbrev run {allow s t} (f : Prog allow s t) (x : s.T) : Bill t.T :=
  f.run () x

end RAM
end PowerSaving


namespace PowerSaving
noncomputable section
open RAM RAM.Ty Filter Asymptotics

def paperM : ℝ := 1000000
def paperW : ℝ := ((2 : ℕ) : ℝ) ^ (71:ℕ)
def paperDelta : ℝ := 6871402692000000
def paperMultiplier := paperM - paperDelta / paperW
def theta : ℝ := Real.log paperMultiplier / Real.log paperM
def decimalExponent : ℝ := 1 - 1/(10^(13:ℕ))

def paperTime (n : ℕ) : ℝ :=
  (n:ℝ) * (Real.log (n:ℝ)) ^ theta * (Real.log (Real.log (n:ℝ))) ^ (4-theta)

def decimalTime (n : ℕ) : ℝ := (n:ℝ) * (Real.log (n:ℝ)) ^ decimalExponent

def nlogn (n : ℕ) : ℝ := (n:ℝ) * Real.log (n:ℝ)

abbrev root := ExactFourier.zeta

abbrev Vec (n : ℕ) := Fin n → ℂ

def dft (n : ℕ) (x : Vec n) : Vec n :=
  fun j => ∑ k, (root n) ^ (j.val*k.val) * x k

def conv (n : ℕ) (x y : Vec n) : Vec (2*n-1) :=
  fun k => ∑ r : Fin n, ∑ s : Fin n, if r.val+s.val=k.val then x r*y s else 0

abbrev dftInKind := p w (p sc (a (c Paint.left)))
abbrev dftOutKind := a (c Paint.left)
abbrev convInKind := p w (p sc (p (a (c Paint.left)) (a (c Paint.right))))
abbrev convOutKind := a (c Paint.both)

def DFTProgram (order : Prog false w w) (solve : Prog false dftInKind dftOutKind)
    (W : ℕ → ℕ) : Prop :=
  ∃ cBound : ℕ, ∀ n : ℕ, 0<n →
    let cap := (n+2)^cBound
    let d := run order n
    W n + 10*(n+2) ≤ cap ∧ d.peak ≤ cap ∧ d.valid ∧
    0 < d.val ∧ d.val < 1024*n^3 ∧ d.val ≤ cap ∧
    ∀ x : Vec n,
      let result := run solve (n, root d.val, (⟨n,x⟩ : Tape ℂ))
      result.valid ∧ result.peak ≤ cap ∧ d.work+1+result.work ≤ W n ∧
      result.val = (⟨n, dft n x⟩ : Tape ℂ)

def ConvProgram (order : Prog false w w) (solve : Prog true convInKind convOutKind)
    (W : ℕ → ℕ) : Prop :=
  ∃ cBound : ℕ, ∀ n : ℕ, 0<n →
    let cap := (n+2)^cBound
    let d := run order n
    W n + 10*(n+2) ≤ cap ∧ d.peak ≤ cap ∧ d.valid ∧
    0 < d.val ∧ d.val < 1024*(2*n-1)^3 ∧ d.val ≤ cap ∧
    ∀ x y : Vec n,
      let result := run solve (n, root d.val, (⟨n,x⟩ : Tape ℂ),(⟨n,y⟩ : Tape ℂ))
      result.valid ∧ result.peak ≤ cap ∧ d.work+1+result.work ≤ W n ∧
      result.val = (⟨2*n-1, conv n x y⟩ : Tape ℂ)

def TimeBounds (W : ℕ → ℕ) : Prop :=
  let W' := fun n : ℕ => (W n : ℝ)
  W' =O[atTop] paperTime ∧ W' =O[atTop] decimalTime ∧ W' =o[atTop] nlogn

def DFTGoal : Prop := ∃ order solve W, DFTProgram order solve W ∧ TimeBounds W

def ConvGoal : Prop := ∃ order solve W, ConvProgram order solve W ∧ TimeBounds W

/-- One fixed program computes every positive-length canonical DFT, including preparation. -/
theorem transform_main : DFTGoal := by
  sorry

/-- One fixed bilinear program computes convolution with the same asymptotic bounds. -/
theorem convolution_main : ConvGoal := by
  sorry

end
end PowerSaving

end OAI
