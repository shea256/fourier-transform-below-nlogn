import Work.GCert.Data.Gen.C588Scal0
import Work.GCert.Data.Gen.C588Sched
set_option maxRecDepth 100000
namespace GXD.C588Controls
open GXD
def doubleFirst : Gate → Gate
  | .out f s ((t,k)::rest) ex => .out f s ((t,{k with num := 2*k.num})::rest) ex
  | g => g
noncomputable def badRaw : Raw := {C588.raw with A := match C588.raw.A with
  | (g::gs)::tail => (doubleFirst g::gs)::tail
  | other => other}
theorem bad_scalar_rejected : GS.scalCheck badRaw ⟨10,21,1,8,8⟩ 0 28 = false := by decide +kernel
noncomputable def badRows : List (List Nat) := match C588.schedRows with
  | (x::_y::xs)::rs => (x::x::xs)::rs
  | other => other
theorem duplicate_owner_rejected : OAI.PowerSaving.GX.schedK 5040 C588.raw.R badRows C588.schedPad C588.schedRes = false := by decide +kernel
end GXD.C588Controls
#print axioms GXD.C588Controls.bad_scalar_rejected
#print axioms GXD.C588Controls.duplicate_owner_rejected
