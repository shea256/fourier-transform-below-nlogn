#!/usr/bin/env python3
"""Attempt an exact local lowering into Sussman's existing gcert/1 checker.

This is a diagnostic, not an accepted certificate exporter. Target-only
preconditioning P is moved across the scatter S by replacing S with P^-1 S.
Nonzero register scales are absorbed into rational register units. Full source
and helper cleanup is explicit at the actual terminal frames. The unchanged
checker decides whether its invocation theorem applies to this representation.
"""
import argparse
from collections import Counter
from fractions import Fraction as Q
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path


def read(path):
    raw = path.read_bytes()
    return json.loads(gzip.decompress(raw) if path.suffix == ".gz" else raw)


def probe(c, gx, source_copies=False):
    if source_copies:
        # Add one zero-start helper per source. Move each mutable original
        # source to that helper, keeping the real x roles read-only in A.
        c = json.loads(json.dumps(c))
        v, R = c["v"], c["R"]
        base = 2*v + R
        remap = lambda r: base+r if r < v else r
        for part in ("A", "B", "precondition", "cleanup", "compensation", "cut"):
            for e in c[part]:
                e[1] = remap(e[1])
                if e[0] == "add": e[2] = remap(e[2])
        c["A"] = [["add", base+r, r, 1, 1, c["start"][r]] for r in range(v)] + c["A"]
        c["start"] += [0]*v
        c["final"] += [1]*v
        c["R"] += v
        for rank in (1, c["h"]-1):
            c["local_profile"][str(rank)] = c["local_profile"].get(str(rank), 0) + v
    v, h, R = c["v"], c["h"], c["R"]
    n = 2 * v + R
    units = [Q(1)] * n
    A, B = [], []
    def emit(e, out):
        kind, r = e[:2]
        if kind == "scale":
            out.append(["out", e[-1], r, [], []])
            factor = Q(e[2], e[3])
            assert factor
            units[r] *= factor
        else:
            assert kind == "add"
            _, t, s, num, den, f = e
            factor = Q(num, den) * units[s] / units[t]
            out.append(["out", f, s, [[t, factor.numerator, factor.denominator]], []])

    # A and P commute because A never reads or writes a target.
    for e in c["A"]:
        regs = e[1:3] if e[0] == "add" else e[1:2]
        assert all(not v <= r < 2 * v for r in regs)
        emit(e, A)
    ret = [[k, r, c["center_frames"][k]] for k, r in enumerate(c["centers"])]
    for _, r, f in ret:
        A.append(["out", f, r, [], []])
    centres = {r: k for k, r, _ in ret}
    S = [[Q(0)] * len(ret) for _ in range(v)]
    for _, target, centre, num, den, _ in c["cut"]:
        assert v <= target < 2*v and centre in centres
        S[target-v][centres[centre]] += Q(num, den)
    for e in reversed(c["precondition"]):
        regs = e[1:3] if e[0] == "add" else e[1:2]
        assert all(v <= r < 2*v for r in regs) and e[-1] == 0
        if e[0] == "scale":
            S[e[1]-v] = [x / Q(e[2], e[3]) for x in S[e[1]-v]]
        else:
            _, t, s, num, den, _ = e
            S[t-v] = [x - Q(num, den)*y for x, y in zip(S[t-v], S[s-v])]
    scatter = []
    for row in S:
        out = []
        for k, value in enumerate(row):
            value *= units[ret[k][1]]
            if value:
                out.append([k, value.numerator, value.denominator])
        scatter.append(out)
    for e in c["precondition"] + c["B"]:
        emit(e, B)
    for r, f in enumerate(c["final"]):
        B.append(["out", f, r, [], []])
    if source_copies:
        # Once every mutable original source lives in a helper, cleanup only
        # writes helpers. Invocation helpers need not be restored. Omitting
        # these terminal adds changes no x/y output and removes no climbs:
        # all registers have already reached their charged final frames.
        assert all(e[1] >= 2*v for e in c["cleanup"])
    else:
        for e in c["cleanup"]:
            emit(e, B)
    unit_failures = [[i, str(q)] for i,q in enumerate(units[:2*v]) if q != 1]
    # Such a failure needs explicit output scaling, not permission to ignore it.
    assert not unit_failures, ("nonunit data output", unit_failures[:5])
    dims = [len(f) for f in c["frames"]]
    current = c["start"].copy()
    hist = {k: Counter() for k in ("x", "y", "s", "c")}
    cls = lambda r: "x" if r<v else "y" if r<2*v else "s"
    def climb(r, f):
        if current[r] != f:
            old = current[r]
            assert dims[f] > dims[old] and gx.inside(c["frames"][old], c["frames"][f]), (r, old, f)
            hist[cls(r)][dims[f]-dims[old]] += 1
            current[r] = f
    for phase, gates in (("A", A), ("B", B)):
        if phase == "B":
            for _, r, f in ret:
                assert current[r] == f
                hist["c"][dims[f]] += 1
        for gate in gates:
            for r in gx.gate_regs(gate)[0]:
                climb(r, gate[1])
    for r, f in enumerate(c["final"]):
        climb(r, f)
    total = Counter()
    for part in hist.values(): total.update(part)
    assert dict(total) == {int(r):count for r,count in c["local_profile"].items()}, "local histogram changed"
    cert = dict(format="gcert/1", h=h, v=v, R=R,
                N=sum(r*count for r,count in total.items()),
                cst=sum(dims[f] for _,_,f in ret), ports=c["ports"], frames=c["frames"],
                start=c["start"], final=c["final"],
                ext=[[r,f] for r,f in enumerate(c["start"]) if r>=2*v and f],
                ret=ret, scat={"table":scatter}, A=A, B=B,
                blocks={k:{str(r):count for r,count in sorted(part.items())} for k,part in hist.items()})
    checks = {}
    for label, check in (("unchanged_full_checker", lambda:gx.check1(cert)),
                         ("clean_source_scalar_identity_only", lambda:gx.scal(cert)),
                         ("entrance_dirt_cancellation_only", lambda:gx.q2(cert))):
        try:
            check()
            checks[label] = {"pass":True}
        except AssertionError as exc:
            checks[label] = {"pass":False, "error":str(exc)}
    return cert, checks


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("canonical",type=Path)
    parser.add_argument("--gx",type=Path,required=True)
    parser.add_argument("--out",type=Path,required=True)
    parser.add_argument("--source-copies",action="store_true")
    args=parser.parse_args()
    spec=importlib.util.spec_from_file_location("gx",args.gx)
    gx=importlib.util.module_from_spec(spec);spec.loader.exec_module(gx)
    result={"canonical_sha256":hashlib.sha256(args.canonical.read_bytes()).hexdigest(),
            "gx_sha256":hashlib.sha256(args.gx.read_bytes()).hexdigest()}
    try:
        cert, checks=probe(read(args.canonical),gx,args.source_copies)
        args.out.with_suffix(".gcert.json.gz").write_bytes(gzip.compress(json.dumps(cert,sort_keys=True).encode(),mtime=0))
        result.update(checks=checks,local_histogram_preserved=True)
    except AssertionError as exc:
        result.update(lowering_failed=True,error=str(exc))
    args.out.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result,indent=2))


if __name__=="__main__": main()
