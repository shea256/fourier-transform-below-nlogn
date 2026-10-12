import Work.Gauge.ECheck
import Work.GCert.Data.Gen.C588Gl
set_option maxRecDepth 100000
namespace GXD.C588
open GXD
theorem echk0_ok : GS.eCheck raw ⟨10, 8, 1, 8, 8⟩ glb0 = true := by decide +kernel
theorem echk1_ok : GS.eCheck raw ⟨10, 8, 1, 8, 8⟩ glb1 = true := by decide +kernel
theorem echk2_ok : GS.eCheck raw ⟨10, 8, 1, 8, 8⟩ glb2 = true := by decide +kernel
end GXD.C588
#print axioms GXD.C588.echk0_ok
#print axioms GXD.C588.echk1_ok
#print axioms GXD.C588.echk2_ok
