import OAI.Computability.FourierTransform.NetworkRoles

namespace OAI

/-! Scalar portion of one invocation. -/
namespace PowerSaving.Cluster
open Finset Binary Matrix
noncomputable section

abbrev Center := Unit ⊕ H
abbrev Side := Trip × Trip  -- ordered X trip, Y trip, including inactive pairs
abbrev Aux := Side ⊕ Center
abbrev XY := Trip ⊕ Trip
abbrev Box := XY ⊕ Aux
instance boxDec : DecidableEq Box := inferInstance

abbrev bx (i : Trip) : Box := .inl (.inl i)
abbrev byy (i : Trip) : Box := .inl (.inr i)
abbrev bs (s : Side) : Box := .inr (.inl s)
abbrev bc (i : Center) : Box := .inr (.inr i)

def vlocal : Matrix Side Trip ℚ := fun a b =>
  if (neighbor a.1 a.2 ∧ a.1 = b) then 1 else 0

def wgt (a b : Trip) : ℚ := ((meet a b:ℚ)-1)/2

def jlocal : Matrix Trip Side ℚ := fun a b =>
  if (neighbor b.1 b.2 ∧ a = b.2) then -wgt b.1 b.2 else 0

def glocal : Matrix Center Trip ℚ
  | .inl (), _ => 1
  | .inr i, b => if i∈b.val then 1 else 0

def rlocal (b : Trip) : Center → ℚ
  | .inl () => -1/2
  | .inr i => (if i∈b.val then 1 else 0)/2

abbrev rmat : Matrix Trip Center ℚ := Matrix.of rlocal

theorem rg_entry (x y : Trip) :
    (rmat * glocal) x y = wgt y x := by
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [rlocal, rmat, Matrix.of_apply, glocal, Finset.univ_unique,
    Finset.sum_singleton]
  unfold wgt
  rw [← meet_ind (R:=ℚ) y x]
  have ht (i : H) :
      ((if i∈x.val then (1:ℚ) else 0)/2)*(if i∈y.val then 1 else 0)
      = ((if i∈y.val then 1 else 0)*(if i∈x.val then 1 else 0))/2 := by ring
  simp_rw [ht]
  rw [← Finset.sum_div]
  ring

theorem jv_entry (x y : Trip) :
    (jlocal * vlocal) x y = if neighbor y x then -wgt y x else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (y,x)]
  · by_cases h : neighbor y x <;> simp [jlocal, vlocal,h]
  · intro b _ hb
    by_cases h : x=b.2
    · have hh : b.1 ≠ y := fun g => hb (Prod.ext g h.symm)
      simp [vlocal, hh]
    · simp [jlocal, h]
  · simp

/-- Crucial projection identity. -/
theorem rg_jv : rmat * glocal + jlocal * vlocal = 1 := by
  ext x y
  rw [Matrix.add_apply, rg_entry, jv_entry, one_apply]
  by_cases h : x=y
  · subst y
    norm_num [wgt, neighbor,meet_self]
  · rw [ite_eq_right h]
    split
    next hh => ring
    next hh =>
      have hj := meet_le y x (Ne.symm h)
      unfold neighbor at hh
      have eq : meet y x=1 := by omega
      simp [wgt,eq]

abbrev Q := Matrix Box Box ℚ

def takeAux (M : Matrix Aux XY ℚ) : Q := fromBlocks 0 0 M 0
def giveAux (M : Matrix XY Aux ℚ) : Q := fromBlocks 0 M 0 0

def eV : Q := takeAux (fromBlocks vlocal 0 0 0)
def eG : Q := takeAux (fromBlocks 0 0 glocal 0)
def eJ : Q := giveAux (fromBlocks 0 0 jlocal 0)
def eR : Q := giveAux (fromBlocks 0 0 0 rmat)

def eXY : Q := fromBlocks (fromBlocks 0 0 1 0 : Matrix XY XY ℚ) 0 0 0

theorem zero_VV : eV*eV=0 := by
  simp [eV, takeAux, fromBlocks_multiply]
theorem zero_GG : eG*eG=0 := by
  simp [eG, takeAux, fromBlocks_multiply]
theorem zero_JJ : eJ*eJ=0 := by
  simp [eJ, giveAux, fromBlocks_multiply]
theorem zero_RR : eR*eR=0 := by
  simp [eR, giveAux, fromBlocks_multiply]
theorem zero_XX : eXY*eXY=0 := by
  simp [eXY, fromBlocks_multiply]

/-- Multiplier from the eight rows (chronologically right to left). -/
def net : Q :=
  (((1-eV)*(1-eG))*((1+eJ)*(1+eR))) * (((1+eG)*(1+eV))*((1-eR)*(1-eJ)))

private theorem rect_commute {X Y : Q} (a : X*X=0) (b : Y*Y=0) (h : X*Y=0) :
    ((1-X)*(1+Y))*((1+X)*(1-Y))= 1+ Y*X := by
  simp only [_root_.add_mul, _root_.mul_add, _root_.sub_mul, _root_.mul_sub, one_mul, mul_one, h,b,a,zero_mul,mul_zero]
  abel

theorem net_eq : net = 1 + eXY := by
  let A := eG+eV
  let B := eJ+eR
  have ha : ((1-eV)*(1-eG):Q)=1-A := by
    have hh : eV*eG=0 := by simp [eV,eG,takeAux,fromBlocks_multiply]
    dsimp [A]
    simp [_root_.sub_mul,_root_.mul_sub,hh]; abel
  have hb : ((1+eJ)*(1+eR):Q)=1+B := by
    have hh : eJ*eR=0 := by simp [eR,eJ,giveAux,fromBlocks_multiply]
    dsimp [B]
    simp [_root_.add_mul,_root_.mul_add,hh]; abel
  have hc : ((1+eG)*(1+eV):Q)=1+A := by
    have hh : eG*eV=0 := by simp [eV,eG,takeAux,fromBlocks_multiply]
    dsimp [A]
    simp [_root_.add_mul,_root_.mul_add,hh]; abel
  have hd : ((1-eR)*(1-eJ):Q)=1-B := by
    have hh : eR*eJ=0 := by simp [eR,eJ,giveAux,fromBlocks_multiply]
    dsimp [B]
    simp [_root_.sub_mul,_root_.mul_sub,hh]; abel
  have ae : A = takeAux (fromBlocks vlocal 0 glocal 0) := by
    simp only [A, takeAux, eG,eV]; simp [fromBlocks_add]
  have be : B = giveAux (fromBlocks 0 0 jlocal rmat) := by
    simp only [B, giveAux, eJ,eR]; simp [fromBlocks_add]
  have h0 : A*A=0 := by rw [ae]; simp [takeAux,fromBlocks_multiply]
  have h1 : B*B=0 := by rw [be]; simp [giveAux,fromBlocks_multiply]
  -- A*B: B outputs only Y, ignored
  have hh : A*B=0 := by rw [ae,be]; simp [giveAux,takeAux,fromBlocks_multiply]
  have hj : B*A=eXY := by
    rw [ae,be]
    simp [giveAux,takeAux,fromBlocks_multiply, eXY, ← rg_jv, add_comm]
  rw [net,ha,hb,hc,hd,rect_commute h0 h1 hh,hj]

/-- Inverse partner. -/
theorem inv_one_add {X : Q} (hh : X*X=0) : (1+X)*(1-X)=1 := by
  simp [_root_.mul_sub, _root_.add_mul, hh]
theorem inv_one_sub {X : Q} (hh : X*X=0) : (1-X)*(1+X)=1 := by
  simp [_root_.mul_add, _root_.sub_mul, hh]

end
end PowerSaving.Cluster

end OAI
