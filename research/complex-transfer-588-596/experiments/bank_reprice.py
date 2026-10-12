#!/usr/bin/env python3
"""Price explicit dedicated-bank schedules on freshly emitted local ledgers.

No data-hosting assumption is used for this *arithmetic* schedule. The local
invocation theorem is an outstanding obligation: do not call this a DFT result.
Data idle ranks come from Bridge377/Bank.lean, not the hosted global ledger.
"""
import argparse
from collections import Counter
import gzip
import hashlib
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]/"verification"))
from exact_moment import certify


def read(p):
    raw=p.read_bytes()
    return json.loads(gzip.decompress(raw) if p.suffix==".gz" else raw)


def schedule(widths, count=72, m=73):
    bins=[set() for _ in range(m+1)]
    loads=[];rows=[]
    for _ in range(count):
        available=[set(s) for s in bins]
        row=[None]*len(widths)
        for q in sorted(range(len(widths)),key=lambda q:(-widths[q],q)):
            w=widths[q]
            for load in range(m-w,-1,-1):
                if available[load]:
                    b=min(available[load]);available[load].remove(b)
                    bins[load].remove(b)
                    break
            else:
                b=len(loads);loads.append(0);load=0
            loads[b]+=w;bins[load+w].add(b);row[q]=b
        rows.append(row)
    return rows,[m-load for load in loads]


def cyclic_schedule(widths, count=72, m=73):
    """Pack one copy, then rotate each bin's distinct helpers over 72 banks.

    At call t, helper j in bin b uses bank (b, (t+j) mod 72).
    Thus every helper occurs once in every call, every call is injective,
    and each physical bank receives precisely its bin's total load.
    """
    remaining=sorted(range(len(widths)),key=lambda q:(-widths[q],q))
    groups=[]
    while remaining:
        dp={0:[]}
        for q in remaining:
            for load in sorted(list(dp),reverse=True):
                s=load+widths[q]
                if s<=m and s not in dp: dp[s]=dp[load]+[q]
            if m in dp: break
        best=dp[max(dp)]
        assert best and len(best)<=count
        groups.append(best)
        taken=set(best)
        remaining=[q for q in remaining if q not in taken]
    rows=[[None]*len(widths) for _ in range(count)]
    pads=[]
    for b,group in enumerate(groups):
        pads.extend([m-sum(widths[q] for q in group)]*count)
        for t in range(count):
            for j,q in enumerate(group): rows[t][q]=b*count+(t+j)%count
    return rows,pads


def validate(rows,pads,widths):
    recomputed=[0]*len(pads)
    assert len(rows)==72
    for row in rows:
        assert len(row)==len(widths) and len(set(row))==len(row)
        for q,b in enumerate(row):
            assert 0<=b<len(pads)
            recomputed[b]+=widths[q]
    assert all(0<=p<73 and load+p==73 for load,p in zip(recomputed,pads))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("local",type=Path)
    parser.add_argument("--out",type=Path,required=True)
    parser.add_argument("--source-copies",action="store_true")
    parser.add_argument("--schedule",choices=("greedy","cyclic"),default="greedy")
    a=parser.parse_args()
    c=read(a.local/"CANONICAL-WORD.json.gz")
    programs=read(a.local/"LOCAL-PROGRAMS.json.gz")
    expected={int(r):n for r,n in c["local_profile"].items()}
    for side,events in programs.items():
        actual=Counter()
        for e in events:
            if e[0]=="climb":actual[e[5]]+=1
            elif e[0]=="center":actual[e[4]]+=1
        assert dict(actual)==expected,(side,actual,expected)
    v,h,R=c["v"],c["h"],c["R"]
    assert h==9
    widths=[len(c["frames"][c["final"][r]])-len(c["frames"][c["start"][r]]) for r in range(2*v,2*v+R)]
    if a.source_copies:
        widths += [9]*v
        for r in (1,8): expected[r]=expected.get(r,0)+v
    rows,pads=(schedule if a.schedule=="greedy" else cyclic_schedule)(widths)
    validate(rows,pads,widths)
    bad=json.loads(json.dumps(rows));bad[0][1]=bad[0][0]
    try:validate(bad,pads,widths)
    except AssertionError:pass
    else:raise AssertionError("duplicate-owner control accepted")
    badpads=pads.copy();badpads[0]+=1
    try:validate(rows,badpads,widths)
    except AssertionError:pass
    else:raise AssertionError("padding control accepted")
    hist=Counter({r:72*n for r,n in expected.items()})
    hist.update({48:32*v,32:32*v,16:32*v,8:48*v})
    hist.update(p for p in pads if p)
    W=64*v+len(pads);mass=sum(r*n for r,n in hist.items())
    cst=sum(len(c["frames"][f]) for f in c["center_frames"])
    assert 73*W-mass==64*v-72*cst==2560
    schedule_path=a.out.with_suffix(".schedule.json.gz")
    schedule_path.write_bytes(gzip.compress(json.dumps(dict(rows=rows,pads=pads,widths=widths),separators=(',',':')).encode(),mtime=0))
    result=dict(status="EXACT_ARITHMETIC_CANDIDATE_LOCAL_LEAN_BRIDGE_UNPROVED",source_copies=a.source_copies,schedule=a.schedule,
                source_sha256=hashlib.sha256((a.local/"CANONICAL-WORD.json.gz").read_bytes()).hexdigest(),
                schedule_sha256=hashlib.sha256(schedule_path.read_bytes()).hexdigest(),
                h=h,m=73,v=v,local_profile=expected,local_residual_count=len(widths),
                banks=len(pads),W=W,deficit=2560,profile=dict(sorted(hist.items())),
                exact_rate=certify(hist,73,W),negative_controls_rejected=["duplicate owner in one call","wrong padding"])
    a.out.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result,indent=2))


if __name__=="__main__":main()
