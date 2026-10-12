#!/usr/bin/env python3
"""Build a dependency closure, reusing only byte-identical compiled closures.

The optional baseline cache is a local speedup, not part of the certificate.
An old .olean is reused only when its source AND every local dependency are
byte-identical. Newly generated or changed modules always compile separately.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--project",type=Path,required=True)
    ap.add_argument("--record",type=Path,required=True)
    ap.add_argument("--baseline",type=Path,required=True)
    ap.add_argument("targets",nargs="+")
    a=ap.parse_args()
    root,record,old=map(Path.resolve,(a.project,a.record,a.baseline))
    cache=root/".lake/build/lib/lean"
    cache.mkdir(parents=True,exist_ok=True)
    logdir=root/"logs/build"
    logdir.mkdir(parents=True,exist_ok=True)
    imports=lambda s:re.findall(r"^import\s+([\w.]+)",s,re.M)
    done,order,provenance={},[],{}

    def visit(mod):
        if mod in done: return done[mod]
        rel=Path(*mod.split(".")).with_suffix(".lean")
        dst=root/rel
        if not dst.exists():
            src=record/rel
            if not src.exists():
                if (old/rel).exists(): src=old/rel
                else:
                    done[mod]=True
                    return True # toolchain or locked Mathlib dependency
            data=src.read_text().replace("import Submission.","import ")
            dst.parent.mkdir(parents=True,exist_ok=True)
            dst.write_text(data)
            provenance[mod]={"source":str(src),"source_sha256":hashlib.sha256(src.read_bytes()).hexdigest(),
                             "transformation":"strip Submission. from imports"}
        same=all([visit(dep) for dep in imports(dst.read_text())])
        prior=old/rel
        same=bool(same and prior.exists() and dst.read_bytes()==prior.read_bytes())
        ole=cache/rel.with_suffix(".olean")
        cached=old/".lake/build/lib/lean"/rel.with_suffix(".olean")
        same=bool(same and cached.exists())
        done[mod]=same
        if same and not ole.exists():
            ole.parent.mkdir(parents=True,exist_ok=True)
            ole.symlink_to(cached)
            for ext in (".ilean",):
                p=cached.with_suffix(ext)
                if p.exists(): ole.with_suffix(ext).symlink_to(p)
        if not same: order.append(mod)
        return same

    for mod in a.targets: visit(mod)
    for name in ("lean-toolchain","lake-manifest.json","lakefile.lean"):
        shutil.copy2(old/name,root/name)
    env=os.environ.copy()
    env["PATH"]=str(Path.home()/".elan/bin")+":"+env["PATH"]
    lp=subprocess.check_output(["lake","env","printenv","LEAN_PATH"],cwd=old,env=env,text=True).strip()
    paths=[str((old/p).resolve()) if not Path(p).is_absolute() else p for p in lp.split(":")]
    # No fallback to the old package cache: every reused local module has
    # passed the recursive equality check above and has its own symlink.
    paths=[p for p in paths if p!=str(old/".lake/build/lib/lean")]
    env["LEAN_PATH"]=":".join([str(cache)]+paths)
    env["LEAN_NUM_THREADS"]="1"
    lean=subprocess.check_output(["elan","which","lean"],cwd=root,env=env,text=True).strip()
    run={"targets":a.targets,"reused_modules":sorted(k for k,v in done.items() if v and (root/Path(*k.split('.')).with_suffix('.lean')).exists()),
         "build_order":order,"provenance":provenance,"results":[]}
    receipt=root/"logs/build-receipt.json"
    print(f"reused={len(run['reused_modules'])}; compile={len(order)}",flush=True)
    for mod in order:
        rel=Path(*mod.split(".")).with_suffix(".lean")
        ole=cache/rel.with_suffix(".olean")
        ole.parent.mkdir(parents=True,exist_ok=True)
        stamp=ole.with_suffix(".source-sha256")
        digest=hashlib.sha256((root/rel).read_bytes()).hexdigest()
        if ole.is_file() and not ole.is_symlink() and stamp.exists() and stamp.read_text()==digest:
            continue
        assert not ole.is_symlink(), "never overwrite baseline cache"
        cmd=["/usr/bin/time","-f","TIME %e MAXRSS_KB %M",lean,"-j1","-DautoImplicit=false","-o",str(ole),str(rel)]
        before=time.monotonic()
        with (logdir/(mod+".log")).open("w") as log:
            proc=subprocess.run(cmd,cwd=root,env=env,stdout=log,stderr=subprocess.STDOUT)
        result={"module":mod,"exit":proc.returncode,"seconds":time.monotonic()-before,"source_sha256":digest}
        run["results"].append(result)
        receipt.write_text(json.dumps(run,indent=2)+"\n")
        print(json.dumps(result),flush=True)
        if proc.returncode:
            print((logdir/(mod+".log")).read_text()[-6000:],flush=True)
            raise SystemExit(proc.returncode)
        stamp.write_text(digest)
    print("ALL REQUESTED MODULES BUILT",flush=True)


if __name__=="__main__": main()
