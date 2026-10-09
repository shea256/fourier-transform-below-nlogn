#!/usr/bin/env python3
"""Check the pinned round-ten complex witness and proposed Fourier saving.

Upstream geometry/replay is deliberately identified as imported code. Additional
checks use exact integer coefficient vectors, our earlier logarithm routine, and
small exact Clifford matrices. None constitutes a formal Fourier theorem.
"""
from collections import Counter
from contextlib import redirect_stdout
from fractions import Fraction as Q
from pathlib import Path
import gzip
import hashlib
import io
import json
import sys

from network_contract import moment_bounds
from rational_bounds import decimal, frac_json

BASE = Path(__file__).resolve().parent
VENDOR = BASE / 'vendor' / 'jain_round10'
TENSOR_SAVING = Q(15402419, 25000000000)
FOURIER_SAVING = Q(61, 100000)


def manifests():
    pins = {}
    for name in ('jain_round10', 'cover_frames'):
        directory = BASE / 'vendor' / name
        source = json.loads((directory / 'SOURCE.json').read_text())
        for entry in source['files']:
            digest = hashlib.sha256((directory / entry['path']).read_bytes()).hexdigest()
            assert digest == entry['sha256'], (name, entry['path'], 'source hash')
        pins[name] = {'commit': source['commit'], 'files': len(source['files'])}
    return pins


def add(dst, src, scale=1):
    for key, value in src.items():
        v = dst.get(key, 0) + scale * value
        if v:
            dst[key] = v
        else:
            dst.pop(key, None)


def exact_decoder(j):
    """All coefficient entries of 6(H+B+K)=6I, over the integers."""
    v = j['v']
    forms = [{}]
    for node in range(1, len(j['args'])):
        args = j['args'][node]
        if args is None:
            assert 1 <= node <= v
            forms.append({node - 1: 1})
        else:
            a, b = args
            assert 0 < a < node and 0 < b < node and j['signs'][node] in (-1, 1)
            row = dict(forms[a])
            add(row, forms[b], j['signs'][node])
            forms.append(row)
    out = [{} for _ in range(v)]
    for root in j['roots']:
        assert len(root['targets']) == len(root['coefficients'])
        for target, coefficient in zip(root['targets'], root['coefficients']):
            c = 6 * Q(coefficient)
            assert c.denominator == 1
            add(out[target], forms[root['node']], c.numerator)
    # Each consecutive octet must be precisely the eight selectors of one cube.
    q = j['inputs']
    assert len(set(q)) == v and v == 8 * __import__('math').comb(j['p'], 3)
    for start in range(0, v, 8):
        group = q[start:start+8]
        pairs = {bit//2 for bit in range(j['h']) if group[0] >> bit & 1}
        assert len(pairs) == 3
        for label in group:
            assert label.bit_count() == 3
            assert {b//2 for b in range(j['h']) if label >> b & 1} == pairs
        k = [[0]*8 for _ in range(8)]  # 2K, so K^2=I iff (2K)^2=4I.
        for t in range(8):
            for s in range(8):
                distance = (group[t] ^ group[s]).bit_count()
                k[t][s] = 1 if distance == 6 else -1 if distance == 2 else 0
                add(out[start+t], {start+s: 1}, 3*k[t][s])
        assert all(sum(k[t][u]*k[u][s] for u in range(8)) == 4*(t == s)
                   for t in range(8) for s in range(8))
    assert all(row == {i: 6} for i, row in enumerate(out)), 'exact decoder identity'
    return {'coefficient_entries': v*v, 'dag_nodes': len(forms)-1, 'cube_blocks': v//8}


def exact_compiled_reads(j):
    """Check carrier chronology and exact adjoint coefficients of dirty reads.

This checks finite prerequisites for the written arbitrary-scratch lemma. It
does not substitute finitely many trials for that lemma.
"""
    hold = {int(x): node for node, x in j['sources'].items()}
    hold = {role: int(node) for role, node in hold.items()}
    roots = list(zip(j['roots'], j['rootroles']))
    coefficients = {}
    def roots_at(kind):
        for root, role in roots:
            if root['kind'] == kind:
                assert hold[role] == root['node'], (kind, role, 'carrier payload')
    for clock, index in enumerate(j['sched']):
        if clock == j['cut']:
            roots_at('center')
        dest, control, node = j['ops'][index]
        if dest not in hold:
            assert hold[control] == node
            ca, cb = 1, 1
        else:
            a, b = j['args'][node]
            sign = j['signs'][node]
            if hold[dest] == a:
                assert hold[control] == b
                ca, cb = 1, sign
            else:
                assert hold[dest] == b and hold[control] == a
                ca, cb = sign, 1
        coefficients[index] = ca, cb
        hold[dest] = node
    if j['cut'] == len(j['sched']):
        roots_at('center')
    roots_at('side')
    cf = [{} for _ in range(j['R'])]
    def seed(kind):
        for root, role in roots:
            if root['kind'] == kind:
                for target, coefficient in zip(root['targets'], root['coefficients']):
                    c = 6*Q(coefficient)
                    assert c.denominator == 1
                    add(cf[role], {target: c.numerator})
    seed('side')
    for clock in range(len(j['sched'])-1, -1, -1):
        if clock == j['cut']-1:
            seed('center')
        index = j['sched'][clock]
        dest, control, _ = j['ops'][index]
        ca, cb = coefficients[index]
        add(cf[control], cf[dest], cb)
        if ca == -1:
            cf[dest] = {t: -c for t, c in cf[dest].items()}
    if j['cut'] == 0:
        seed('center')
    actual_reads = 0
    for gauge in j['gauges']:
        targets = set(gauge['targets'])
        assert set(cf[gauge['role']]) <= targets, 'unframed compensation read'
        actual_reads += len(cf[gauge['role']])
    assert len({g['role'] for g in j['gauges']}) == len(j['gauges'])
    assert set(int(x) for x in j['sources'].values()).isdisjoint(g['role'] for g in j['gauges'])
    assert {b for _, b in j['pairs']} == {g['role'] for g in j['gauges']}, 'all gauges paired'
    return {'compiled_operations': len(coefficients), 'gauges': len(j['gauges']),
            'exact_compensation_coefficients': actual_reads}


def main():
    pins = manifests()
    j = json.load(gzip.open(VENDOR / 'word.json.gz', 'rt'))
    print('Checking exact decoder coefficients...', flush=True)
    decoder = exact_decoder(j)
    print('Checking compiled carriers and exact compensation reads...', flush=True)
    compiled = exact_compiled_reads(j)
    changed = dict(j, signs=list(j['signs']))
    changed['signs'][next(k for k, s in enumerate(changed['signs']) if s == -1)] = 1
    try:
        exact_decoder(changed)
    except AssertionError:
        pass
    else:
        raise AssertionError('changed signed decoder accepted')
    changed = dict(j, gauges=[dict(g, targets=[]) for g in j['gauges']])
    try:
        exact_compiled_reads(changed)
    except AssertionError:
        pass
    else:
        raise AssertionError('missing compensation targets accepted')
    # Preserve the external program unmodified, including its explicit modular
    # replay scope. Its chain/histogram variables are inspected after it passes.
    args = sys.argv
    stream = io.StringIO()
    try:
        sys.argv = [str(VENDOR / 'check_word.py'), str(VENDOR / 'word.json.gz')]
        # The source ends in sys.exit: catch it without modifying vendor bytes.
        code = (VENDOR / 'check_word.py').read_text()
        namespace = {'__name__': '__main__', '__file__': str(VENDOR / 'check_word.py')}
        with redirect_stdout(stream):
            try:
                exec(compile(code, str(VENDOR / 'check_word.py'), 'exec'), namespace)
            except SystemExit as e:
                assert e.code == 0, stream.getvalue()
    finally:
        sys.argv = args
    print(stream.getvalue(), end='')
    assert namespace['OK'] and all(namespace['OK'].values())
    hist = namespace['C']
    roles, m = namespace['Wv'], j['m']
    lean = json.loads((VENDOR / 'round10-histograms.json').read_text())
    assert {r: Q(n) for r, n in lean['cx']['hist']} == hist
    assert (lean['cx']['m'], lean['cx']['W'], Q(*lean['cx']['a'])) == (m, roles, TENSOR_SAVING)
    inventory = json.load(gzip.open(VENDOR / 'inventory.json.gz', 'rt'))
    assert {int(r): Q(n) for r, n in inventory['child_histogram'].items()} == hist
    from clifford_checks import verify as verify_cliffords
    clifford = verify_cliffords()
    lo, hi = moment_bounds(hist, m, roles, TENSOR_SAVING)
    next_lo, _ = moment_bounds(hist, m, roles, TENSOR_SAVING + Q(1, 10**12))
    assert hi < 1 and next_lo > 1
    assert 0 < FOURIER_SAVING < TENSOR_SAVING
    assert sum(r*n for r,n in hist.items()) == 961752
    assert roles*m - sum(r*n for r,n in hist.items()) == 1320
    from math import prod
    order = 2**(m-1+(m//2-1)**2) * prod(4**i-1 for i in range(1,m//2))
    report = {'schema': 1, 'result_id': 'round10', 'sources': pins,
              'm': m, 'roles_per_vertex': int(roles), 'cover_group_order': str(order),
              'full_roles': str(order*int(roles)), 'histogram': {str(r): int(n) for r,n in sorted(hist.items())},
              'rank_mass_per_vertex': 961752, 'deficit_per_vertex': 1320, 'max_child': max(hist),
              'tensor_saving': str(TENSOR_SAVING), 'fourier_saving': str(FOURIER_SAVING),
              'absorption_slack': str(TENSOR_SAVING-FOURIER_SAVING),
              'moment_lower': frac_json(lo), 'moment_upper': frac_json(hi),
              'moment_gap_lower': frac_json(1-hi), 'next_point_lower': frac_json(next_lo),
              'decoder': decoder, 'compiled_reads': compiled, 'clifford_small_checks': clifford,
              'upstream_check_count': len(namespace['OK']),
              'extra_negative_controls': ['signed_decoder', 'missing_compensation_targets', 'next_tensor_grid_point'],
              'scope': 'Finite exact checks and imported modular replay; written transfer, not formal verification.'}
    out = BASE / 'round10_certificate.json'
    out.write_text(json.dumps(report, indent=2, sort_keys=True)+'\n')
    ref = BASE / 'certificates' / 'round10_reference.json'
    if ref.exists():
        assert report == json.loads(ref.read_text()), 'round-ten reference mismatch'
    print('Tensor moment gap >', decimal(1-hi))
    print('Fourier saving', FOURIER_SAVING, 'with slack', TENSOR_SAVING-FOURIER_SAVING)
    print('Round-ten finite checks passed.')


if __name__ == '__main__':
    main()
