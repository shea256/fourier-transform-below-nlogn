#!/usr/bin/env python3
"""Round-eleven finite geometry, full rational scalar map, and moment checks.

The scalar map is checked for every input, initial dirty register and dirty
target coefficient. This does not prove the arbitrary-dimensional frame lift
or the Fourier theorem. The geometric replay is explicitly imported code.
"""
from collections import defaultdict
from contextlib import redirect_stdout
from fractions import Fraction as Q
from math import prod
from pathlib import Path
import gzip
import hashlib
import io
import json
import sys

from network_contract import moment_bounds
from rational_bounds import decimal, frac_json
from verify_round10 import add, exact_decoder

BASE = Path(__file__).resolve().parent
VENDOR = BASE / 'vendor/jain_round11'
TENSOR_SAVING = Q(67147467, 100000000000)
FOURIER_SAVING = Q(67, 100000)


def manifests():
    pins = {}
    for name in ('jain_round11', 'jain_round10', 'cover_frames'):
        directory = BASE / 'vendor' / name
        source = json.loads((directory / 'SOURCE.json').read_text())
        for entry in source['files']:
            assert hashlib.sha256((directory / entry['path']).read_bytes()).hexdigest() == entry['sha256']
        pins[name] = {'commit': source['commit'], 'files': len(source['files'])}
    return pins


def upstream():
    args, stream = sys.argv, io.StringIO()
    path = VENDOR / 'check_word.py'
    ns = {'__name__': '__main__', '__file__': str(path)}
    try:
        sys.argv = [str(path), str(VENDOR / 'word.json.gz')]
        with redirect_stdout(stream):
            try:
                exec(compile(path.read_text(), str(path), 'exec'), ns)
            except SystemExit as e:
                assert e.code == 0, stream.getvalue()
    finally:
        sys.argv = args
    print(stream.getvalue(), end='', flush=True)
    assert ns['OK'] and all(ns['OK'].values())
    return ns


def decoder_rows(j):
    forms = [{}]
    for node in range(1, len(j['args'])):
        if j['args'][node] is None:
            forms.append({node-1: 1})
        else:
            a, b = j['args'][node]
            row = dict(forms[a]); add(row, forms[b], j['signs'][node]); forms.append(row)
    out = [{} for _ in range(j['v'])]
    for root in j['roots']:
        for t, c in zip(root['targets'], root['coefficients']):
            coefficient = 6*Q(c); assert coefficient.denominator == 1
            add(out[t], forms[root['node']], coefficient.numerator)
    return out


def exact_transcript(ns, control=None):
    """Pull all target coefficients back through the actual aliased program.

    Integer vectors are six times the rational map. Target-to-target shears
    are integral; read coefficients have denominator dividing six. Scratch
    restoration follows by reversing every physical mixer and source load.
    """
    roots, rootroles = ns['roots'], ns['rootroles']
    ops, sched, coef, cut = ns['ops'], ns['sched'], ns['coef'], ns['cut']
    R, v = ns['R'], ns['v']
    seeds = []
    for root, sr in zip(roots, rootroles):
        row = {}
        for t, c in zip(root['targets'], root['coefficients']):
            x = 6*Q(c); assert x.denominator == 1
            add(row, {t: x.numerator})
        seeds.append((sr, root['kind'], row))
    # Exact original-decoder responses after inserting the retirement mixes.
    cf = [{} for _ in range(R)]
    def seed(kind):
        for sr, k, row in seeds:
            if k == kind: add(cf[sr], row)
    seed('side')
    if cut == len(sched): seed('center')
    for clock in range(len(sched)-1, -1, -1):
        if clock == cut-1 and cut != len(sched): seed('center')
        i = sched[clock]; d, c, _ = ops[i]; ca, cb = coef[i]
        add(cf[c], cf[d], cb)
        if ca == -1: cf[d] = {t: -x for t, x in cf[d].items()}
    if cut == 0: seed('center')
    for gauge in ns['gauges']:
        assert set(cf[gauge['role']]) <= set(gauge['targets']), 'unframed compensation'
    for sr, row in enumerate(cf):
        modular = {t: x for t, x in ns['CF'][sr].items() if x}
        assert {t: (x*pow(6, ns['P']-2, ns['P'])) % ns['P'] for t,x in row.items()} == modular
    assert all(not cf[s] for s in ns['UNUSED'])

    S = {x['s']: x for x in ns['sel']}
    recip = ns['recip']
    def physical(sr):
        seen = set()
        while sr in recip:
            assert sr not in seen; seen.add(sr); sr = recip[sr]
        return sr
    slot = {sr: physical(sr) for sr in range(R) if sr not in S and sr not in ns['UNUSED']}
    phys = set(slot.values())
    assert len(phys)+2*v == ns['W1']
    events, gates = [], []
    def read(sr, row, sign=1): events.append(('read', slot[sr], row, sign))
    for sr in slot:
        if sr not in ns['gauged']: read(sr, cf[sr], -1)
    for node, sr in ns['sources'].items(): events.append(('load', slot[sr], node-1))
    clocks = defaultdict(list)
    # Match the declared order, including distinct reads at the same clock.
    for gauge in reversed(ns['gauges']): clocks[ns['tau'][gauge['role']]].append(gauge['role'])
    last = {ns['rops'][s][-1]: x for s,x in S.items()}
    def shear(x, sign):
        for t in x['T']:
            if t != x['c']: events.append(('shear', t, x['c'], sign))
    def center():
        for sr, kind, row in seeds:
            if kind == 'center': read(sr, row)
        for x in S.values(): shear(x, -1)
    first_mix = min(ns['MIX'])
    for clock, i in enumerate(sched):
        if clock == cut: center()
        for b in clocks[clock]:
            if control != 'omit_gauge' or b != ns['gauges'][0]['role']: read(b, cf[b], -1)
        d,c,_ = ops[i]; ca,cb = coef[i]
        if control == 'wrong_mix' and i == first_mix: cb = 1
        if d in S:
            assert ca == 1
            x = S[d]; c6 = 6*Q(roots[x['j']]['coefficients'][0]); assert c6.denominator == 1
            events.append(('read', slot[c], {x['c']: c6.numerator*cb}, 1))
        else:
            dd,cc = slot[d],slot[c]; assert dd != cc and ca in (-1,1)
            event = ('gate', dd,cc,ca,cb); events.append(event); gates.append(event)
        if i in last:
            if control != 'drop_post' or i != next(iter(last)): shear(last[i], 1)
    if cut == len(sched): center()
    for b in clocks[len(sched)]: read(b, cf[b], -1)
    for sr,kind,row in seeds:
        if kind == 'side' and sr not in S: read(sr,row)

    ya = [{t:6} for t in range(v)]
    za = {s:{} for s in phys}
    xa = [{} for _ in range(v)]
    for event in reversed(events):
        kind = event[0]
        if kind == 'read':
            _,s,row,sign = event
            for t,c in row.items():
                assert all(x % 6 == 0 for x in ya[t].values())
                add(za[s], {q:x//6 for q,x in ya[t].items()}, sign*c)
        elif kind == 'gate':
            _,d,c,ca,cb = event
            add(za[c],za[d],cb)
            if ca == -1: za[d] = {t:-x for t,x in za[d].items()}
        elif kind == 'load':
            _,s,node = event; add(xa[node],za[s])
        else:
            _,t,c,sign = event; add(ya[c],ya[t],sign)
    assert all(not row for row in za.values()), 'initial dirty scratch affects output'
    assert all(row == {t:6} for t,row in enumerate(ya)), 'dirty target map is not identity'
    want = [{} for _ in range(v)]
    for t,row in enumerate(decoder_rows(ns['J'])):
        for node,c in row.items(): want[node][t] = c
    assert xa == want, 'input coefficients differ from original decoder'
    return {'physical_auxiliaries':len(phys), 'source_columns':v, 'dirty_columns':len(phys),
            'target_columns':v, 'target_coefficient_entries':v*(2*v+len(phys)),
            'scheduled_operations':len(sched), 'invertible_physical_gates':len(gates),
            'gauges':len(ns['gauges']), 'recycling_hosts':len(ns['HOSTS']),
            'terminal_deletions':len(S), 'events':len(events),
            'exact_gauge_compensation_coefficients':sum(len(cf[g['role']]) for g in ns['gauges'])}


def main():
    pins = manifests()
    j = json.load(gzip.open(VENDOR/'word.json.gz','rt'))
    source_roles = set(j['sources'].values())
    gauges = {g['role'] for g in j['gauges']}
    sinks = {s['role'] for s in j['sinks']}
    assert gauges == {b for _,b in j['pairs']}, 'unpaired gauge tail'
    for host in j['hosts']:
        assert host['birth'] not in source_roles | gauges | sinks
        assert {host['pivot'],host['control']}.isdisjoint(gauges | set(j['rootroles']))
    decoder = exact_decoder(j)
    ns = upstream()
    print('Checking every rational input, dirty-scratch and target coefficient...',flush=True)
    transcript = exact_transcript(ns)
    for control in ('wrong_mix','omit_gauge','drop_post'):
        try: exact_transcript(ns,control)
        except AssertionError: pass
        else: raise AssertionError('negative control accepted: '+control)
    hist, roles, m = ns['C1'],ns['W1'],ns['m']
    inventory = json.load(gzip.open(VENDOR/'inventory.json.gz','rt'))
    lean = json.loads((VENDOR/'round11-histograms.json').read_text())['cx']
    assert dict(hist) == {int(r):int(n) for r,n in inventory['child_histogram'].items()} == dict(lean['hist'])
    assert roles == int(inventory['W_per_vertex']) == lean['W'] == 12922
    assert ns['a'] == TENSOR_SAVING == Q(*lean['a'])
    rank_mass = sum(r*n for r,n in hist.items())
    assert rank_mass == lean['s'] == 851532 and roles*m-rank_mass == 1320
    lo,hi = moment_bounds(hist,m,roles,TENSOR_SAVING)
    next_lo,_ = moment_bounds(hist,m,roles,TENSOR_SAVING+Q(1,10**12))
    assert hi < 1 and next_lo > 1 and 0 < FOURIER_SAVING < TENSOR_SAVING
    order = 2**(m-1+(m//2-1)**2)*prod(4**i-1 for i in range(1,m//2))
    report = {'schema':1,'result_id':'round11','sources':pins,'m':m,
              'roles_per_vertex':roles,'cover_group_order':str(order),'full_roles':str(order*roles),
              'histogram':{str(r):int(n) for r,n in sorted(hist.items())},
              'rank_mass_per_vertex':rank_mass,'deficit_per_vertex':roles*m-rank_mass,'max_child':max(hist),
              'tensor_saving':str(TENSOR_SAVING),'fourier_saving':str(FOURIER_SAVING),
              'absorption_slack':str(TENSOR_SAVING-FOURIER_SAVING),
              'moment_lower':frac_json(lo),'moment_upper':frac_json(hi),'moment_gap_lower':frac_json(1-hi),
              'next_point_lower':frac_json(next_lo),'decoder':decoder,'exact_transcript':transcript,
              'upstream_check_count':len(ns['OK']),
              'extra_negative_controls':['wrong_mix','omit_gauge','drop_post','next_tensor_grid_point'],
              'scope':'All scalar output coefficients exact over Q; imported finite geometry; conditional written Fourier transfer, not formal verification.'}
    (BASE/'round11_certificate.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    ref = BASE/'certificates/round11_reference.json'
    if ref.exists(): assert report == json.loads(ref.read_text()), 'round-eleven reference mismatch'
    print('Tensor moment gap >',decimal(1-hi))
    print('Fourier saving',FOURIER_SAVING,'with slack',TENSOR_SAVING-FOURIER_SAVING)
    print('Round-eleven finite checks passed.')


if __name__ == '__main__': main()
