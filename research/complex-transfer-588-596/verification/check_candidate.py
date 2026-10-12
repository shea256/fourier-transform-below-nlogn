#!/usr/bin/env python3
"""Recalculate the finite construction and meaningful adversarial controls."""
import argparse
from copy import deepcopy
from fractions import Fraction as Q
import gzip
import importlib.util
import json
from pathlib import Path
import sys


def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
    return mod


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--artifacts",type=Path,required=True)
    ap.add_argument("--gx",type=Path,required=True)
    ap.add_argument("--out",type=Path,required=True)
    a=ap.parse_args()
    root=Path(__file__).resolve().parents[1]
    converter=module("convert",root/"experiments/canonical_to_gcert_probe.py")
    bank=module("bank",root/"experiments/bank_reprice.py")
    gx=module("reference_gx",a.gx)
    from scalar_audit import audit,replay
    from exact_moment import moment as moment_interval,log_interval,exp_interval
    raw=lambda name:json.loads(gzip.decompress((a.artifacts/name).read_bytes()))
    canonical=raw("CANONICAL-WORD.json.gz")
    expected=raw("candidate.gcert.json.gz")
    converted,oldchecks=converter.probe(canonical,gx,True)
    assert converted==expected,"converter output changed"
    result=audit(converted)
    s=raw("schedule.json.gz")
    rebuilt=bank.cyclic_schedule(s["widths"])
    assert rebuilt==(s["rows"],s["pads"])
    bank.validate(s["rows"],s["pads"],s["widths"])
    controls=[]
    def reject(label,fn):
        try:fn()
        except AssertionError:controls.append(label)
        else:raise AssertionError("mutation accepted: "+label)
    bad=deepcopy(converted);bad["A"][0][3][0][1]*=2
    reject("doubled source-copy coefficient",lambda:replay(bad,"x"))
    bad=deepcopy(converted)
    for g in bad["B"]:
        if 112<=g[2]<224 and g[3]:
            g[3][0][1]*=2;break
    reject("broken target-precondition cancellation",lambda:replay(bad,"y"))
    rows=deepcopy(s["rows"]);rows[0][1]=rows[0][0]
    reject("duplicate owner",lambda:bank.validate(rows,s["pads"],s["widths"]))
    pads=s["pads"].copy();pads[0]+=1
    reject("incorrect padding",lambda:bank.validate(s["rows"],pads,s["widths"]))
    # Boundary identities and monotonicity of the exact interval engine.
    assert log_interval(Q(1))==(Q(0),Q(0))
    lo,hi=exp_interval(Q(0),Q(0));assert lo<=1<=hi
    p=json.loads((a.artifacts/"price.json").read_text())
    H={int(r):n for r,n in p["profile"].items()}
    lo,hi=moment_interval(H,73,12208,Q(0))
    assert lo<=Q(888624,12208*73)<=hi
    at_record=moment_interval(H,73,12208,Q(2555269,2500000000))
    at_claim=moment_interval(H,73,12208,Q(12331685,10**10))
    above_root=moment_interval(H,73,12208,Q(123317,10**8))
    assert at_record[1]<at_claim[0]<at_claim[1]<1<above_root[0]
    a.out.write_text(json.dumps(dict(status="PASS_FINITE_CHECKS",scalar=result,
        historical_gx_rejection=oldchecks["unchanged_full_checker"],
        controls_rejected=controls,interval_boundary_checks=True,
        scope="Finite checks; universal conclusions require the separately built Lean theorem."),indent=2)+"\n")
    print("PASS: exact regeneration, three scalar identities, schedule, four mutation controls and interval boundaries")


if __name__=="__main__":main()
