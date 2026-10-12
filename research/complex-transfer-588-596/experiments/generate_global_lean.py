#!/usr/bin/env python3
"""Generate the explicit bank witness, rate, and all-length Fourier instance.

Uses the unchanged #401 bank checker and engine from Nil Mamano's submission,
and Jacob Sussman's rational rate-proof generator. The Fourier transfer files
are renamed instances of that submission, with changed instance constants.
Every generated fact still requires a successful Lean build.
"""
import argparse
from collections import Counter
import gzip
import hashlib
import json
from pathlib import Path
import re
import sys


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("price",type=Path)
    ap.add_argument("--toolkit",type=Path,required=True)
    ap.add_argument("--record",type=Path,required=True)
    ap.add_argument("--out",type=Path,required=True)
    a=ap.parse_args()
    p=json.loads(a.price.read_text())
    sched=json.loads(gzip.decompress(a.price.with_suffix(".schedule.json.gz").read_bytes()))
    sys.path.insert(0,str(a.toolkit))
    import foldlib as fl
    import foldgen as fg
    u=dict(m=p["m"],W=p["W"],D=p["deficit"],H={int(k):v for k,v in p["profile"].items()})
    assert (u["m"],p["v"],len(sched["widths"]))==(73,112,616)
    from fractions import Fraction as Q
    A=int(Q(p["exact_rate"]["root_lower"])*10**10)
    while fl.plan_block(u,A,10,40) is None: A-=1
    delta=A-1
    base=a.out/"Work/GCert/Data"
    base.mkdir(parents=True,exist_ok=True)
    body,plan=fg.block_text("C588x",u,A,10,40)
    rate="import Work.BlockAccounting.Moment\nset_option maxRecDepth 4000\nnamespace OAI.PowerSaving.BlockAccounting\nopen Finset\n"
    rate+=fg.list_text("C588x",u,"72 copies of PR588 atm3 with source copies, #401 dedicated banks, and an explicit cyclic schedule.")
    rate+="\n"+body+"\nend OAI.PowerSaving.BlockAccounting\n#print axioms OAI.PowerSaving.BlockAccounting.fold_C588x\n"
    (base/"RateC588x.lean").write_text(rate)
    rows,pads,widths=sched["rows"],sched["pads"],sched["widths"]
    nb=len(pads);top=max(pads);counts=Counter(pads)
    imports=[];parts=[]
    for i,lo in enumerate(range(0,72,4)):
        mod=f"Work.GCert.Data.Gen.C588Rows{i}"
        imports.append("import "+mod)
        parts.append(f"rows{i}")
        txt="import Work.GCert.Data.Gen.C588\nnamespace GXD.C588\n"
        txt+=f"noncomputable def rows{i} : List (List Nat) := {rows[lo:lo+4]}\nend GXD.C588\n"
        (base/f"Gen/C588Rows{i}.lean").write_text(txt)
    txt="\n".join(imports)+"\nimport Work.Bridge401.SchedK\nimport Work.GCert.Data.Count\nset_option maxRecDepth 100000\nnamespace GXD.C588\nopen GXD OAI.PowerSaving\n"
    txt+="noncomputable def schedRows : List (List Nat) := "+" ++ ".join(parts)+"\n"
    txt+=f"noncomputable def schedPad : List Nat := {pads}\nnoncomputable def schedRes : List Nat := {widths}\n"
    txt+=f"theorem sched_ok : GX.schedK {nb} raw.R schedRows schedPad schedRes = true := by decide +kernel\n"
    txt+=f"theorem rankBoundP : wsumK (SSC.wGt {top}) schedPad 0 = 0 := by decide +kernel\n"
    txt+="\n".join(f"theorem rankP{r}_ok : wsumK (SSC.wEq {r}) schedPad 0 = {counts[r]} := by decide +kernel" for r in range(top+1))
    txt+="\nend GXD.C588\n#print axioms GXD.C588.sched_ok\n"
    (base/"Gen/C588Sched.lean").write_text(txt)
    inv=" + ".join(f"{n} * φ {r}" for r,n in sorted((int(r),n) for r,n in p["local_profile"].items()))
    pad=" + ".join(f"{n} * bcost φ {r}" for r,n in sorted(counts.items()) if r and n)
    txt=f'''import Work.Bridge377.Bank
import Work.FoldRate.Group
import Work.GCert.Data.RateC588x
namespace OAI.PowerSaving.BridgeRate.C588
open Finset Binary Matrix RAM CB FoldRate
noncomputable section
def invPrice (φ : ℕ → ℝ) : ℝ := {inv}
def padPrice (φ : ℕ → ℝ) : ℝ := {pad}
def unitPrice (φ : ℕ → ℝ) : ℝ := 72 * invPrice φ + ((112:ℕ):ℝ) * GX.bankPrice377 φ + padPrice φ
theorem unit_cost_x (φ : ℕ → ℝ) : unitPrice φ = listCost φ BlockAccounting.blocksC588x := by
  unfold unitPrice invPrice padPrice
  simp only [GX.bankPrice377, listCost, BlockAccounting.blocksC588x, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  norm_num [bcost]
  try ring
theorem unit_tally : unitPrice (fun r => (r:ℝ)) = (({p['W']}:ℕ):ℝ) * 73 - 2560 := by
  rw [unit_cost_x]
  exact BlockAccounting.blocksC588x_tally
end
end OAI.PowerSaving.BridgeRate.C588
#print axioms OAI.PowerSaving.BridgeRate.C588.unit_cost_x
'''
    (base/"InstC588.lean").write_text(txt)
    src=a.record/"Work/GCert/Data/G5Glue401.lean"
    txt=src.read_text().replace("import Submission.","import ").replace("C401Gg5","C588").replace("G5","C588")
    txt=txt.replace("6673",str(nb)).replace("14353",str(p["W"])).replace("Fin 772","Fin 616").replace("2 * 120","2 * 112")
    txt=txt.replace("bcost φ 9 :=","bcost φ 8 :=")
    txt=re.sub(r"def es : List \(GS.SPar × List Nat\) := .*", "def es : List (GS.SPar × List Nat) := [(⟨10, 8, 1, 8, 8⟩, glb0), (⟨10, 8, 1, 8, 8⟩, glb1), (⟨10, 8, 1, 8, 8⟩, glb2)]",txt)
    txt=txt.replace("  exact absurd he List.not_mem_nil","  rcases List.mem_cons.mp he with h | he\n  · subst h; exact echk2_ok\n  exact absurd he List.not_mem_nil")
    txt=txt.replace("schedPad 46 rankBoundP",f"schedPad {top} rankBoundP")
    txt=re.sub(r"rankP0_ok, .*rankP46_ok",", ".join(f"rankP{r}_ok" for r in range(top+1)),txt)
    txt=txt.replace("(SPar ⟨10, 6, 1, 4, 4⟩, ⟨10, 5, 1, 4, 4⟩)","(three batches, SPar ⟨10, 8, 1, 8, 8⟩)")
    txt=txt.replace("Generated by tools/gx/gxgen401.py (DFT Lean).", "Adapted from the G5 glue by DFT Lean in Nil Mamano's record submission; generated by generate_global_lean.py.")
    (base/"C588Glue401.lean").write_text(txt)
    mapping={"C401Gg5":"C588","C401G5":"C588","GXD.G5":"GXD.C588",".G5":".C588","/G5":"/C588","10221077":str(A),"10221076":str(delta),"14353":str(p["W"])}
    dst=a.out/"Work/FourierC588"
    dst.mkdir(exist_ok=True)
    provenance={}
    for source in sorted((a.record/"Work/FourierC401G5").glob("*.lean")):
        txt=source.read_text().replace("import Submission.","import ")
        for k,v in mapping.items(): txt=txt.replace(k,v)
        (dst/source.name).write_text(txt)
        provenance[source.name]=hashlib.sha256(source.read_bytes()).hexdigest()
    (a.out/"logs/global-C588.json").write_text(json.dumps(dict(kernel_numerator=A,dft_numerator=delta,denominator=10**10,
        rational_slack=plan["slack_rel"],fourier_source_sha256=provenance,fourier_substitutions=mapping),indent=2)+"\n")
    print(f"kernel saving {A}/10^10; DFT saving {delta}/10^10; rational slack {plan['slack_rel']}")


if __name__=="__main__": main()
