import OAI.Computability.FourierTransform.RAM
import OAI.Computability.FourierCircuit.Core

namespace OAI

/-! Main proof targets. -/
namespace PowerSaving
noncomputable section
open RAM RAM.Ty Filter Asymptotics

/-- Positive-sign, canonical roots. Need only at positive order. -/
abbrev root := ExactFourier.zeta

abbrev Vec (n : ℕ) := Fin n → ℂ

abbrev dftMatrix := ExactFourier.fourierMatrix

def dft (n : ℕ) (x : Vec n) : Vec n :=
  fun j => ∑ k, (root n) ^ (j.val*k.val) * x k

def conv (n : ℕ) (x y : Vec n) : Vec (2*n-1) :=
  fun k => ∑ r : Fin n, ∑ s : Fin n, if r.val+s.val=k.val then x r*y s else 0

/-- Exact exponent from the TeX (natural logarithms). -/
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

abbrev dftInKind := p w (p sc (a (c Paint.left)))
abbrev dftOutKind := a (c Paint.left)
abbrev convInKind := p w (p sc (p (a (c Paint.left)) (a (c Paint.right))))
abbrev convOutKind := a (c Paint.both)

/-- Include an integer and address bound polynomial in n. Constants inside this bound are
  immaterial (a constant number of logarithmic sized words is allowed). W n is the work
  allowance, including the order program, one root primitive and the transform program.
  The order program takes only the length, so its result specifies the root explicitly. -/
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

/-- Convolution in the same model extended by pointwise field multiplication for two
  inputs. We even require the bound on the supplied root from the proof of the corollary. -/
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

/-- Thm 1 (intro main) and decimal corollary estimates. -/
def TimeBounds (W : ℕ → ℕ) : Prop :=
  let W' := fun n : ℕ => (W n : ℝ)
  W' =O[atTop] paperTime ∧ W' =O[atTop] decimalTime ∧ W' =o[atTop] nlogn

def DFTGoal : Prop := ∃ order solve W, DFTProgram order solve W ∧ TimeBounds W

def ConvGoal : Prop := ∃ order solve W, ConvProgram order solve W ∧ TimeBounds W

end
end PowerSaving

end OAI
