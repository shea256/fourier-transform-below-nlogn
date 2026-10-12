#!/usr/bin/env python3
"""Exact rational preflight for GS.scalCheck, GS.yCheck and GS.eCheck.

This replaces the reference Python checker's sufficient, acyclic E4 shortcut
with the actual product identity required by Lean's unchanged GS.yCheck.
It is NOT a Lean proof. Both positive and negative accumulators are retained
to select safe packed-integer parameters without relying on cancellation.
"""
import argparse
from collections import Counter
from fractions import Fraction as Q
import gzip
import hashlib
import json
from math import lcm
from pathlib import Path


def adds(g):
    if g[0] == "out":
        return [(t, g[2], Q(a,b)) for t,a,b in g[3]]
    assert g[0] == "in"
    return [(g[2], s, Q(a,b)) for s,a,b in g[3]]


def replay(c, mode):
    v, nr = c["v"], 2*c["v"] + c["R"]
    cls = lambda r: "x" if r<v else "y" if r<2*v else "s"
    sources = list(range(v)) if mode=="x" else list(range(v,2*v)) if mode=="y" else [r for r,f in c["ext"]]
    P,N = [dict() for _ in range(nr)], [dict() for _ in range(nr)]
    den, mx = {k:1 for k in "xys"}, {k:Q(1) for k in "xys"}
    updates = Counter()
    for r in sources: P[r][r] = Q(1)

    def add(t,s,a,phase):
        assert 0<=t<nr and 0<=s<nr and t!=s
        if phase=="A": assert t>=2*v and (s<v or s>=2*v), (phase,t,s)
        elif phase=="S": assert v<=t<2*v and s>=2*v, (phase,t,s)
        else: assert (t>=v or s<v) and (s<v or s>=2*v or v<=t<2*v), (phase,t,s)
        # yCheck reads only target-to-target adds in B.
        if mode=="y" and not (phase=="B" and v<=s<2*v): return
        pos,neg = (P[s],N[s]) if a>=0 else (N[s],P[s])
        for dst,src in ((P[t],pos),(N[t],neg)):
            for key,value in src.items():
                z=dst.get(key,Q(0)) + abs(a)*value
                if z:
                    dst[key]=z
                    k=cls(t)
                    den[k]=lcm(den[k],z.denominator)
                    mx[k]=max(mx[k],z)
                    updates[key]+=1
    if mode!="y":
        for g in c["A"]:
            for t,s,a in adds(g): add(t,s,a,"A")
        for t,row in enumerate(c["scat"]["table"]):
            for k,a,b in row: add(v+t,c["ret"][k][1],Q(a,b),"S")
    for g in c["B"]:
        for t,s,a in adds(g): add(t,s,a,"B")
    def net(r):
        return {k:z for k in P[r].keys()|N[r].keys() if (z:=P[r].get(k,Q(0))-N[r].get(k,Q(0)))}
    if mode=="x":
        assert all(net(t)=={t:1} for t in range(v)), "source identity"
        assert all(net(v+t)=={t:1} for t in range(v)), "source-to-target identity"
    elif mode=="y":
        assert all(net(v+t)=={v+t:1} for t in range(v)), "target-to-target identity"
    else:
        assert all(not net(v+t) for t in range(v)), "entrance dirt cancellation"
    return {"mode":mode,"pass":True,"source_count":len(sources),"denominators":den,
            "maximum_uncancelled_entry":{k:str(z) for k,z in mx.items()},
            "updates":sum(updates.values())}


def audit(c):
    modes=[replay(c,m) for m in ("x","y","e")]
    units={k:lcm(*(m["denominators"][k] for m in modes)) for k in "xys"}
    largest=max(Q(m["maximum_uncancelled_entry"][k])*units[k] for m in modes for k in "xys")
    assert largest.denominator==1
    sw=largest.numerator.bit_length()+1
    d=(2*c["v"]+c["R"]-1).bit_length()
    return {"checks":modes,"SPar":[d,sw,units["x"],units["s"],units["y"]],
            "largest_uncancelled_digit":int(largest),"scope":"Exact rational preflight only; Lean kernel checks still required."}


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("certificate",type=Path)
    ap.add_argument("--out",type=Path,required=True)
    a=ap.parse_args()
    data=a.certificate.read_bytes()
    c=json.loads(gzip.decompress(data) if a.certificate.suffix==".gz" else data)
    result=audit(c)
    result["certificate_sha256"]=hashlib.sha256(data).hexdigest()
    a.out.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result,indent=2))


if __name__=="__main__": main()
