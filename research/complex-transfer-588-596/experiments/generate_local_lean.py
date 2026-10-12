#!/usr/bin/env python3
"""Generate C588 local checks using Sussman's generator and unchanged Lean predicates.

Adaptations are confined to Python preflight/parameters and generated witness
modules: cyclic target products, eighths, entrance gauges, rank-8 centres.
All proof obligations are evaluated by `decide +kernel` in the upstream Lean
checkers. No soundness theorem or checker definition is patched.
"""
import argparse
import gzip
import importlib
import json
import os
from pathlib import Path
import sys


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("certificate",type=Path)
    ap.add_argument("--toolkit",type=Path,required=True)
    ap.add_argument("--out",type=Path,required=True)
    a=ap.parse_args()
    c=json.loads(gzip.decompress(a.certificate.read_bytes()))
    sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"verification"))
    from scalar_audit import audit
    result=audit(c)
    os.environ["GX_OUT"]=str(a.out.resolve())
    sys.path.insert(0,str(a.toolkit.resolve()))
    import gxcore as gc
    import gxgen as gen
    import gxbind as gb
    import gsmirror as sm
    # Replay every target basis vector (above), rather than the narrower
    # acyclic-pivot sufficient condition in the historical Python mirror.
    gc.SC=8
    gc.chk_shape=lambda D:result["checks"][1]["updates"]
    d,sw,ux,us,uy=result["SPar"]
    sm.replay(c,(ux,us,uy),"x")
    sm.replay(c,(ux,us,uy),"y")
    sm.bigreplay(c,(d,sw,ux,us,uy),0,c["v"],[c["A"]],[c["B"]])
    gb.spar=lambda D,path:dict(d=d,sw=sw,ux=ux,us=us,uy=uy,source="exact rational and packed preflight",digits=gc.digits(D))
    gb.LAB["end_imports"]=["Work.Gauge.Labels","Work.GCert.Data.Gen.C588Gl"]
    gb.LAB["end"]="GLab.endKE par %(v)d ports (raw.ret.map Prod.fst) gl st0 st%(a)d st%(f)d"
    sys.argv=["gxgen.py",str(a.certificate.resolve()),"C588","gseg=2000","batches=4","frames=1"]
    gen.main()
    base=a.out/"Work/GCert/Data"
    cert=base/"C588Cert.lean"
    s=cert.read_text().replace("import Work.GCert.Labels.Main","import Work.Gauge.Labels\nimport Work.GCert.Data.Gen.C588Gl")
    s=s.replace("theorem valid : GLab.Valid raw aux where","theorem validE : GLab.ValidE raw aux gl where")
    s=s.split("/-- price of the label half over ANY scalar half -/")[0]
    cert.write_text(s+"end GXD.C588\n#print axioms GXD.C588.validE\n")
    price=base/"C588Price.lean"
    s=price.read_text()
    # Entrance gauges omit their initial ranks from the movement invoice.
    old=f'{c["R"]} * {c["h"]} + 2 * {c["v"]} * ({c["h"]} - 1) + {c["cst"]}'
    s=s.replace(old,str(c["N"]))
    s=s.replace('R h + 2 v (h - 1) + cst =',
                'R h + 2 v (h - 1) + cst - sum_q rank(ent q) =')
    price.write_text(s)
    gl=[r for r,f in c["ext"]]
    batches=[gl[i:i+80] for i in range(0,len(gl),80)]
    head="namespace GXD.C588\nopen GXD\n"
    defs=[f"noncomputable def gl : List Nat := {gl}"]
    defs += [f"noncomputable def glb{i} : List Nat := {b}" for i,b in enumerate(batches)]
    (base/"Gen/C588Gl.lean").write_text("import Work.GCert.Data.Gen.C588\n"+head+"\n".join(defs)+"\nend GXD.C588\n")
    checks=[f"theorem echk{i}_ok : GS.eCheck raw ⟨{d}, 8, {ux}, {us}, {uy}⟩ glb{i} = true := by decide +kernel" for i in range(len(batches))]
    (base/"Gen/C588EChk.lean").write_text("import Work.Gauge.ECheck\nimport Work.GCert.Data.Gen.C588Gl\nset_option maxRecDepth 100000\n"+head+"\n".join(checks)+"\nend GXD.C588\n"+"\n".join(f"#print axioms GXD.C588.echk{i}_ok" for i in range(len(batches)))+"\n")
    (a.out/"logs/preflight-C588.json").write_text(json.dumps(result,indent=2)+"\n")


if __name__=="__main__": main()
