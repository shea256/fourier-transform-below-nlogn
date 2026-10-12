import Work.GFrame.Labels.Conj
import Work.GFrame.Labels.Maps
import Work.Reframe.GeomNet
import Work.BridgeGeom.Stage

/-!
# GFrame labels, part 18 (key: eng-labels): the old block frame maps ARE the generalised ones

The four block frame maps of the network (`CB.xmap1`, `CB.xmap2`, `RF.fmapQ`, `BG.fmapB`) are
literally `GXMap.toXMap` of the generalised frame maps of `Maps.lean` and `Conj.lean`
(same `Φ`; the other fields are proofs).  So every old theorem stated for one of them applies
unchanged to the generalised map.  No `sorry`.
-/

namespace OAI
namespace PowerSaving.GF
open Binary Matrix Finset RAM CB SS

section
variable {B H : Type} [Fintype B] [DecidableEq B] [Fintype H] [DecidableEq H]

theorem gxmap1_toXMap (hH : 2 ≤ Fintype.card H) (A : OBase H) (k : H) :
    (gxmap1 hH (A.v k) (A.self k)).toXMap = xmap1 hH A k := rfl

theorem gxmap2_toXMap (hH : 2 ≤ Fintype.card H) (A : OBase H) (k : H) :
    (gxmap2 hH (A.v k) (A.self k)).toXMap = xmap2 hH A k := rfl

theorem gxmapQ_toXMap (hH : 1 ≤ Fintype.card H) (d : RF.Orth (RF.L3 H))
    (q : Finset (Bool × H)) : (gxmapQ hH d q).toXMap = RF.fmapQ hH d q := rfl

theorem gxmapB_toXMap (hB : 1 ≤ Fintype.card B) (hH : 1 ≤ Fintype.card H)
    (d : RF.Orth (BG.LB B H)) (q : Finset (B × H)) :
    (gxmapB hB hH d q).toXMap = BG.fmapB hB hH d q := rfl

end
end PowerSaving.GF
end OAI

#print axioms OAI.PowerSaving.GF.gxmapQ_toXMap
#print axioms OAI.PowerSaving.GF.gxmapB_toXMap
