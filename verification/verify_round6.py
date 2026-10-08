#!/usr/bin/env python3
"""Finite checks for the attributed round-six complex network and Fourier transfer.

The pinned producer is third-party code, not an independent implementation.
This file separately reconstructs coefficients, physical frame paths, residual
histograms, endpoint identities, and a rational moment bound. The all-length
recurrence and Fourier transfer are written proofs in manuscript.md.
"""
from __future__ import annotations

from collections import Counter
from fractions import Fraction as Q
from hashlib import sha256
from pathlib import Path
import json
import random
import sys

BASE = Path(__file__).resolve().parent
VENDOR = BASE / 'vendor' / 'jain_round6'
sys.path.insert(0, str(VENDOR))

from clean_room_audit import Projectors
from rational_bounds import decimal, frac_json, log_bounds


def require(ok, message):
    if not ok:
        raise AssertionError(message)


def bits(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def check_sources():
    manifest = json.loads((VENDOR / 'SOURCE.json').read_text())
    require(manifest['commit'] == 'f2176bc1124821bf17eb63725bd366d7bdc020a3', 'source pin')
    for name, info in manifest['files'].items():
        require(sha256((VENDOR / name).read_bytes()).hexdigest() == info['sha256'],
                f'unmodified upstream source: {name}')
    return {'commit': manifest['commit'], 'files_checked': len(manifest['files'])}


def coefficient_check(c):
    """Rebuild support vectors from circuit arguments, then check every matrix entry."""
    v = len(c.triples)
    supports = [0] + [1 << j for j in range(v)]
    for n in range(v + 1, len(c.args)):
        a, b = c.args[n]
        require(a < n and b < n and not (supports[a] & supports[b]), 'disjoint topological sum')
        supports.append(supports[a] | supports[b])
    require(supports == c.sup, 'all producer supports rederived')
    rows = {t: [0] * v for t in c.triples}
    for target, node, coefficient in c.pieces:
        for j in bits(supports[node]):
            rows[target][j] += coefficient
    for target, row in rows.items():
        target_set = set(target)
        for j, source in enumerate(c.triples):
            # Twice the retained-total scatter has coefficient |S intersect T|-1.
            actual = row[j] + len(target_set.intersection(source)) - 1
            require(actual == 2 * (source == target), 'complete local shear matrix')
    for name, node in c.retained:
        expected = sum(1 << j for j, t in enumerate(c.triples)
                       if name == ('*',) or name[1] not in t)
        require(supports[node] == expected, 'retained total support')
    return {'matrix_entries': v * v, 'producer_nodes': len(supports) - 1,
            'retained_totals': len(c.retained), 'bad': 0}


def label_projectors(c):
    """Construct actual symmetric binary projectors without the upstream frame checker."""
    p = Projectors(c.h)
    triples = [sum(1 << i for i in t) for t in c.triples]
    labels = {}
    for node in sorted(c.active):
        ids = list(bits(c.sup[node]))
        common, cover = (1 << c.h) - 1, 0
        for j in ids:
            common &= triples[j]
            cover |= triples[j]
        vectors = ([triples[j] for j in ids] if len(ids) == 1 or common.bit_count() >= 2
                   else [1 << j for j in bits(cover)])
        labels[node] = p.span(vectors)
    return p, labels, [p.span([t]) for t in triples]


def compiler_check(c, kk):
    """Propagate the fresh input map through the actual compiled role shears."""
    values = [0] * kk['size']
    last_node = {}
    for j, triple in enumerate(c.triples):
        slot = kk['src'][triple]
        require(values[slot] == 0, 'distinct source pivots')
        values[slot] = 1 << j
    for node, ins, outs in kk['gates']:
        pivot = ins[0]
        require(outs[0] == pivot and set(ins) & set(outs) == {pivot}, 'reversible pivot gate')
        if len(ins) == 2:
            require(not values[pivot] & values[ins[1]], 'compiled sum has disjoint fresh supports')
            values[pivot] |= values[ins[1]]
        require(values[pivot] == c.sup[node], 'compiled pivot equals specified DAG node')
        for slot in outs[1:]:
            require(values[slot] == 0, 'fresh fan-out carrier')
            values[slot] = values[pivot]
        for slot in set(ins + outs):
            last_node[slot] = node
    for j, (_, node, _) in enumerate(c.pieces):
        require(values[kk['pout'][j]] == c.sup[node], 'compiled piece output')
    for name, node in c.retained:
        slot = kk['rout'][name]
        require(values[slot] == c.sup[node] and last_node[slot] == node,
                'retained output has no subsequent producer incidence')
    require(set(kk['rout'].values()).isdisjoint(kk['pout'].values()), 'retained/piece output separation')
    return {'roles': kk['size'], 'compiled_gates': len(kk['gates']),
            'terminal_retained_carriers': len(kk['rout']), 'fresh_map_verified': True}


def physical_histogram(c, kk, copied=True):
    """Replay one complete local invocation in each orientation using projectors.

    Distinct terminal retained slots are replaced by a paid temporary read.
    This counts actual role transitions, not differences of guessed dimensions.
    Exterior and data classes are then lifted analytically to F_2^(h*h).
    """
    h, v, R = c.h, len(c.triples), kk['size']
    p, labels, lines = label_projectors(c)
    zero, full = p.zero, p.full
    retained = set(kk['rout'].values())
    require(len(retained) == h, 'distinct retained output carriers')
    pieces = {t: [] for t in c.triples}
    for j, slot in kk['pout'].items():
        pieces[c.pieces[j][0]].append(slot)
    operations = []

    def mix(mode, reverse=False):
        gates = reversed(kk['gates']) if reverse else kk['gates']
        operations.append([(tuple(sorted(set(ins + outs))),
                            zero if mode == 'low' else full if mode == 'high' else labels[node])
                           for node, ins, outs in gates])

    def scatter_retained():
        # All reads commute, so one read event per distinct retained carrier is enough.
        operations.append([((slot,), zero) for slot in sorted(retained)])

    def inject(complement):
        operations.append([(tuple(pieces[t]), p.complement(lines[j]) if complement else zero)
                           for j, t in enumerate(c.triples)])

    def copy_source(high):
        operations.append([((kk['src'][t],), full if high else lines[j])
                           for j, t in enumerate(c.triples)])

    mix('low'); scatter_retained(); inject(False); mix('low', True)
    copy_source(False); mix('label'); scatter_retained(); inject(True)
    mix('high', True); copy_source(True)
    reverse_ops = [[(roles, p.complement(frame)) for roles, frame in reversed(op)]
                   for op in reversed(operations)]
    histograms, checked, copies = [], 0, 0
    for stage, ops, designated in ((1, operations, 6), (2, reverse_ops, 3)):
        current = [zero] * R
        counts = Counter()
        pending = {}

        def edge(a, b):
            nonlocal checked
            residual = p.difference(a, b)
            rank = p.ranks[residual]
            require(not rank or p.nonalt[residual], 'orthonormal residual exists on actual role edge')
            if rank:
                counts[rank] += 1
            checked += 1

        for oi, op in enumerate(ops):
            for roles, frame in op:
                for role in roles:
                    if copied and role in retained and oi == designated:
                        copies += 1
                        if stage == 1:
                            edge(current[role], frame)  # copy moves; original stays
                        else:
                            pending[role] = frame  # next original frame determines advance then copy
                        continue
                    if role in pending:
                        edge(frame, pending.pop(role))
                    edge(current[role], frame)
                    current[role] = frame
        require(not pending, 'every inverse copy has a following original incidence')
        for old in current:
            edge(old, full)
        histograms.append(counts)
    require(histograms[0] == histograms[1], 'complementary orientations have identical histograms')
    ell = (h - 1) ** 2 + h
    local = histograms[0]
    require(sum(r * n for r, n in local.items()) == h * R + (ell if copied else 2 * ell),
            'local internal rank charge')
    H = Counter({r: 2 * v * n for r, n in local.items()})
    H[h * h - h] += 2 * v * R  # stage-one exit and stage-two entrance
    H[(h - 1) ** 2] += 2 * v * v  # two interstage data edges
    H[h - 1] += 4 * v * v  # data fronts
    H[1] += v * v  # paid endpoint correction
    return H, {'local_histogram': dict(sorted(local.items())), 'physical_edges_checked': checked,
               'copy_transforms': copies, 'distinct_projectors': len(p.matrices)}


def scalar_simulation(h=8):
    """Exact dirty-scratch trials of both scalar orientations, including copied reads."""
    from producer import NStar3, compile_roles
    c = NStar3(h)
    kk = compile_roles(c)
    rng = random.Random(130109)
    trials = 0

    def mixer(z, inverse=False):
        for _, ins, outs in (reversed(kk['gates']) if inverse else kk['gates']):
            pivot = ins[0]
            if inverse:
                for slot in outs[1:]:
                    z[slot] -= z[pivot]
                if len(ins) == 2:
                    z[pivot] -= z[ins[1]]
            else:
                if len(ins) == 2:
                    z[pivot] += z[ins[1]]
                for slot in outs[1:]:
                    z[slot] += z[pivot]

    def read(z):
        # Copies have the same scalar value as the terminal retained carriers.
        ret = {name: z[slot] for name, slot in kk['rout'].items()}
        E = [ret['E', j] for j in range(h - 1)]
        E.append((h - 3) * ret['*',] - sum(E))
        out = {t: ret['*',] - sum(E[j] for j in t) / 2 for t in c.triples}
        for j, (target, _, coefficient) in enumerate(c.pieces):
            out[target] += Q(coefficient, 2) * z[kk['pout'][j]]
        return out

    for orientation in (1, -1):
        for _ in range(3):
            x = {t: Q(rng.randrange(-9, 10), 4) for t in c.triples}
            y = {t: Q(rng.randrange(-9, 10), 4) for t in c.triples}
            z = [Q(rng.randrange(-9, 10), 4) for _ in range(kk['size'])]
            original, old_y = z[:], y.copy()
            mixer(z); old = read(z); mixer(z, True)
            for t, slot in kk['src'].items():
                z[slot] += x[t]
            mixer(z); new = read(z); mixer(z, True)
            for t, slot in kk['src'].items():
                z[slot] -= x[t]
            for t in c.triples:
                y[t] += orientation * (new[t] - old[t])
            require(z == original, 'arbitrary dirty scratch restored exactly')
            require(all(y[t] == old_y[t] + orientation * x[t] for t in c.triples), 'signed shear')
            trials += 1
    return {'h': h, 'exact_rational_trials': trials, 'roles': kk['size']}


def endpoint_checks():
    """Gaussian-integer checks of the paid correction and final tensor normalization."""
    # Integer pairs avoid floating point even for fourth roots of unity.
    roots = [(1, 0), (0, 1), (-1, 0), (0, -1)]
    add = lambda a, b: (a[0] + b[0], a[1] + b[1])
    neg = lambda a: (-a[0], -a[1])
    mul = lambda a, b: (a[0]*b[0] - a[1]*b[1], a[0]*b[1] + a[1]*b[0])
    cases = 0
    missing_correction_fails = False
    for e in range(4):
        for t in range(4):
            F, Tinv = roots[e], roots[-t % 4]
            E = mul(F, Tinv)
            for x, y in (((1, 0), (0, 0)), ((0, 0), (1, 0))):
                A = neg(mul(F, y))
                B = add(mul(mul(E, Tinv), x), mul(E, y))
                expected = mul(mul(E, Tinv), x)
                missing_correction_fails |= B != expected
                require(add(B, mul(Tinv, A)) == expected, 'endpoint inverse-phase correction')
                cases += 1
    require(missing_correction_fails, 'negative control: omitting the correction fails')
    # T^2 = X_u, so translating the corrected B by u gives F directly.
    # Check all 2^9 characters on the support of the weight-nine tensor line.
    u = (1 << 9) - 1
    for y in range(1 << 9):
        parity = (y & u).bit_count() & 1
        phase = y.bit_count() - 2 * 9 * parity + 2 * parity
        require(phase % 4 == y.bit_count() % 4, 'weight-nine endpoint translation')
    return {'two_by_two_basis_cases': cases, 'normalization_characters': 512,
            'missing_correction_negative_control': True}


def moment_bound(hist, W, m, saving):
    # Same analytic inequality as the Lean certificate, different log implementation.
    total = Q(0)
    for r, count in hist.items():
        require(0 < r < m and count > 0, 'strictly contracting positive-width children')
        _, upper = log_bounds(Q(m, r))
        # Round upward to control denominator growth, still entirely rational.
        scale = 10 ** 40
        upper = Q(-((-upper.numerator * scale) // upper.denominator), scale)
        x = saving * upper
        require(0 <= x < 1, 'positive geometric denominator')
        total += Q(r * count, W * m) / (1 - x)
    return total


def main():
    source = check_sources()
    from producer import NStar3, compile_roles
    from frames import Checker
    from hist import build
    h = 24
    c = NStar3(h)
    kk = compile_roles(c)
    coefficients = coefficient_check(c)
    compiler = compiler_check(c, kk)
    print('PASS: pinned producer and all local coefficient entries.', flush=True)
    labels = Checker(c).run()
    require(labels['bad'] == 0, 'upstream binary label checks')
    histogram, physical = physical_histogram(c, kk)
    upstream = build(h, copied=True)
    require(histogram == upstream['hist'], 'physical reconstruction matches upstream histogram')
    lean = json.loads((VENDOR / 'round6-histograms.json').read_text())['cx']
    require(histogram == dict(lean['hist']), 'histogram matches pinned Lean input')
    v, m, W, s = len(c.triples), h*h, lean['W'], lean['s']
    R, N = kk['size'], v*v
    L = 2*v*((h-1)**2+h)
    require(W == 2*N + 2*v*R and s == W*m-N+L, 'global physical counts')
    require(sum(r*n for r, n in histogram.items()) == s and W*m-s == 1858032, 'exact rank mass')
    require((R, W, s, max(histogram)) == (49208, 207387136, 119453132304, 552), 'selected parameters')
    print('PASS: both physical schedules, copied-centre charges, and complete rank histogram.', flush=True)
    scalar = scalar_simulation()
    endpoint = endpoint_checks()
    a = Q(*lean['a'])
    delta = Q(73, 10**6)
    M = moment_bound(histogram, W, m, a)
    require(1-M > Q(7, 10**14) and delta < a, 'strict moment and all-length exponent slack')
    require(moment_bound(histogram, W, m, Q(1, 10000)) > 1, 'negative control: excessive saving rejected')
    missing_copy = histogram.copy()
    missing_copy[h-1] -= 2*v*(h-1)
    missing_copy[h] -= 2*v
    require(sum(r*n for r, n in missing_copy.items()) != s, 'negative control: unpaid copies rejected')
    report = {
        'source': source, 'coefficients': coefficients, 'compiler': compiler, 'upstream_labels': labels,
        'physical_schedule': physical, 'scalar_trials': scalar, 'endpoint': endpoint,
        'network': {'h': h, 'v': v, 'm': m, 'R': R, 'N': N, 'W': W, 'L': L, 's': s,
                    'deficit': W*m-s, 'histogram': dict(sorted(histogram.items()))},
        'certificate': {'tensor_saving': frac_json(a), 'fourier_delta': frac_json(delta),
                        'moment_upper': frac_json(M), 'moment_gap': frac_json(1-M),
                        'moment_gap_decimal': decimal(1-M), 'absorption_slack': frac_json(a-delta)},
        'negative_controls': {'unpaid_copies': True, 'excessive_saving': True,
                              'missing_endpoint_correction': True},
        'scope': 'Finite checks plus a written conditional Fourier transfer; not an end-to-end formal proof.',
    }
    out = BASE / 'round6_certificate.json'
    out.write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    reference = BASE / 'certificates' / 'round6_reference.json'
    if reference.exists():
        # JSON object keys are strings, including the integer-keyed histograms.
        require(json.loads(out.read_text()) == json.loads(reference.read_text()),
                'round-six reference certificate')
    print('PASS: scalar/endpoint identities and negative controls.')
    print(f'PASS: a={a}, delta={delta}, rational moment gap={decimal(1-M)}')
    print('Certificate:', out)


if __name__ == '__main__':
    main()
