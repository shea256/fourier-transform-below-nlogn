#!/usr/bin/env python3
"""Check the new exact-DFT instantiation's finite witness and source bindings.

This command does not run Lean. Its separately retained Lean receipt is checked
by scripts/result_registry.py; full rebuild commands are in lean/complex588.
"""
from pathlib import Path
from copy import deepcopy
import json
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parents[1]
PROOF=ROOT/'lean/complex588'


def main():
    subprocess.run([sys.executable,str(PROOF/'scripts/check_provenance.py')],check=True)
    with tempfile.TemporaryDirectory(prefix='complex588-finite-') as tmp:
        subprocess.run([sys.executable,str(ROOT/'research/complex-transfer-588-596/verification/check_candidate.py'),
            '--artifacts',str(PROOF/'artifacts'),'--gx',str(PROOF/'tools/gx/gx.py'),
            '--out',str(Path(tmp)/'finite.json')],check=True)
    sys.path.insert(0,str(ROOT/'scripts'))
    import result_registry
    registry,current=result_registry.load()
    result=next(r for r in registry['results'] if r['id']=='complex588')
    assert result['status']=='formalized'
    source=json.loads((ROOT/result['source_manifest']).read_text())
    receipt=json.loads((ROOT/result['lean_receipt']).read_text())
    bad_delta=deepcopy(receipt);bad_delta['fourier_saving']='12331686/10000000000'
    bad_axiom=deepcopy(receipt);bad_axiom['axioms'][source['fourier_proof']['axiom_theorems'][0]].append('sorryAx')
    bad_log=deepcopy(receipt);bad_log['commands'][0]['log_sha256']='0'*64
    bad_control=deepcopy(receipt)
    next(c for c in bad_control['commands'] if c['label']=='negative_control')['exit_code']=0
    with tempfile.TemporaryDirectory(prefix='complex588-receipt-') as tmp:
        p=Path(tmp)/'receipt.json'
        candidate=dict(result,lean_receipt=str(p))
        for bad in (bad_delta,bad_axiom,bad_log,bad_control):
            p.write_text(json.dumps(bad))
            try:result_registry.validate_local_formal(candidate,source)
            except ValueError:pass
            else:raise AssertionError('corrupted proof receipt was accepted')
    print('PASS: complex588 finite checks, source bundle, retained formal receipt and four corrupted-receipt controls')


if __name__=='__main__':main()
