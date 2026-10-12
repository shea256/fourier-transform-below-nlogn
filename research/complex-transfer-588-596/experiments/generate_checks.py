#!/usr/bin/env python3
"""Instantiate the original full Fourier challenge and adversarial controls."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out",type=Path,required=True)
    ap.add_argument("--original-challenge",type=Path,required=True)
    ap.add_argument("--comparator",type=Path,required=True)
    a=ap.parse_args()
    info=json.loads((a.out/"logs/global-C588.json").read_text())
    numerator=info["dft_numerator"]
    source=a.original_challenge.read_text()
    needle="1 - 1/(10^(13:ℕ))"
    assert source.count(needle)==1
    names=["decimalExponent","decimalTime","TimeBounds","DFTGoal","ConvGoal","transform_main","convolution_main"]
    for negative in (False,True):
        txt=source.replace(needle,f"1 - {numerator+int(negative)}/(10^(10:ℕ))")
        for name in names: txt=re.sub(r"\b"+name+r"\b",name+"C588",txt)
        directory=a.out/"Work"/("FourierC588Neg" if negative else "FourierC588")
        directory.mkdir(exist_ok=True)
        (directory/"UniformFourierChallenge.lean").write_text(txt)
    p=a.out/"Work/FourierC588/Axioms.lean"
    p.write_text("import Work.FourierC588.Main\n"+"\n".join("#print axioms "+n for n in [
        "OAI.PowerSaving.transform_mainC588","OAI.PowerSaving.convolution_mainC588","OAI.PowerSaving.RAM.hillsC588_program"])+"\n")
    controls='''import Work.GCert.Data.Gen.C588Scal0
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
'''
    (a.out/"Work/GCert/Data/C588Controls.lean").write_text(controls)
    (a.out/"tools").mkdir(exist_ok=True)
    shutil.copy2(a.comparator,a.out/"tools/Compare.lean")
    (a.out/"logs/challenge-provenance.json").write_text(json.dumps(dict(
        source=str(a.original_challenge),source_sha256=hashlib.sha256(a.original_challenge.read_bytes()).hexdigest(),
        changes={"exponent":f"1 - {numerator}/10^10","seven_names_suffix":"C588"},
        negative_control=f"one unit stronger: {numerator+1}/10^10"),indent=2)+"\n")


if __name__=="__main__": main()
