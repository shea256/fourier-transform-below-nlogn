#!/usr/bin/env python3
"""Check the pinned PR256 program, five-stage ledger and exact Fourier margin.

Standard library only. This is a finite check, not a Lean build. The separate
verify_five_stage_lean.py reproduces the upstream formal proof.
"""
import argparse
import ast
from collections import Counter
from fractions import Fraction as Q
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys
import tarfile

from network_contract import moment_bounds

BASE = Path(__file__).resolve().parent
VENDOR = BASE / 'vendor/five_stage'
PACKAGE = VENDOR / 'gcert-program-233'
REFERENCE = BASE / 'certificates/five_stage_reference.json'
A = Q(7547361, 10**10)
DELTA = Q(7547360, 10**10)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def source_check():
    source = json.loads((VENDOR / 'SOURCE.json').read_text())
    for path, digest in source['files'].items():
        require(hashlib.sha256((VENDOR / path).read_bytes()).hexdigest() == digest,
                'source hash mismatch: ' + path)
    return source


def strip_lean_comments(text):
    # The two fixed challenge files use non-nested block comments.
    text = re.sub(r'/-.*?-/', '', text, flags=re.S)
    return ''.join(re.sub(r'--[^\n]*', '', text).split())


def rounded_down(q):
    grid = 10**30
    return str(Q(q.numerator * grid // q.denominator, grid))


def verify():
    source = source_check()
    spec = importlib.util.spec_from_file_location('five_stage_gx', PACKAGE / 'gx/gx.py')
    gx = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(gx)
    cert = json.loads(gzip.decompress((PACKAGE / 'certificates/gcert1-p11-pr233-flow.json.gz').read_bytes()))
    stats = {}
    gx.check1(cert, scalar=True, stats=stats)
    require((cert['h'], cert['v'], cert['R'], cert['N'], cert['cst']) == (22, 1320, 9412, 262944, 440),
            'unexpected program dimensions')
    require(not cert['ext'], 'exterior gauges are outside this selected theorem')
    inv = Counter()
    for block_class in cert['blocks'].values():
        for width, count in block_class.items():
            inv[int(width)] += count
    require(sum(inv.values()) == 69683, 'invocation count differs')
    require(sum(r*n for r, n in inv.items()) == cert['N'], 'invocation rank differs')
    hist = Counter({r: 5*n for r, n in inv.items()})
    for width in (42, 21, 46, 4):
        hist[width] += 2*cert['v']
    m, roles = 5*cert['h'], 4*cert['v'] + cert['R']
    rank = sum(r*n for r, n in hist.items())
    require((m, roles, rank, m*roles-rank, max(hist), sum(hist.values())) ==
            (110, 14692, 1613040, 3080, 46, 358975), 'five-stage ledger differs')
    expected = json.loads((PACKAGE / 'certificate/expected.json').read_text())['pr233']['five_stage']
    require(dict(hist) == {int(r): n for r, n in expected['child_histogram'].items()},
            'ledger differs from upstream certificate')
    lo, hi = moment_bounds(hist, m, roles, A)
    require(hi < 1, 'tensor moment does not contract')
    require(0 < DELTA < A < 1, 'no Fourier absorption gap')
    # Also check the actual finite-fill inequality of the imported Lean engine.
    _, endpoint_hi = moment_bounds({m-1: 1, 1: 1}, m, 1, A)
    fill = Q(1, 2**40)
    folded_hi = (1-fill)*hi + fill*endpoint_hi
    require(folded_hi < 1, 'finite-fill engine inequality does not contract')
    reject_at = Q(7547365, 10**10)
    reject_lo, _ = moment_bounds(hist, m, roles, reject_at)
    require(reject_lo > 1, 'negative rate control did not reject')

    with tarfile.open(VENDOR / source['fourier_proof']['archive']) as archive:
        def read(path):
            return archive.extractfile(path).read()
        origin = json.loads((BASE/'certificates/five_stage_openai_origin.json').read_text())
        require(origin['success'] and origin['commit'] == 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',
                'unexpected OpenAI source origin')
        oai_paths = {m.name for m in archive.getmembers()
                     if m.isfile() and m.name.startswith('OAI/') and m.name.endswith('.lean')}
        require(oai_paths == {p for p in origin['files'] if p.startswith('OAI/')},
                'OpenAI source-origin ledger does not cover every imported module')
        require(len(origin['files']) == 91, 'unexpected OpenAI source count')
        for path, record in origin['files'].items():
            require(hashlib.sha256(read(path)).hexdigest() == record['sha256'],
                    'archived source differs from checked OpenAI origin: '+path)
        lean_cert = json.loads(gzip.decompress(read('tools/certificate/gcert1-p11-pr233-flow.json.gz')))
        left, right = dict(cert), dict(lean_cert)
        # A descriptive provenance string differs; every mathematical field must agree.
        left.pop('derived_from'); right.pop('derived_from')
        require(left == right, 'Lean input program differs')
        rate = read('Work/GCert/Data/RateB2Gp233x.lean').decode()
        block_list = re.search(r'def blocksB2Gp233x : List \(ℕ × ℕ\) := (\[.*\])', rate).group(1)
        require(dict(ast.literal_eval(block_list)) == dict(hist), 'Lean rate ledger differs')
        seam = read('Work/Fourier233/Seam.lean').decode()
        require('def alphaY : ℝ := 1 - 7547361/(10:ℝ)^10' in seam, 'Lean kernel exponent differs')
        require('def targetExponent : ℝ := 1 - 7547360/(10:ℝ)^10' in seam, 'Lean target exponent differs')
        goal = read('Work/Fourier233/Goal.lean').decode()
        require('def decimalExponentY : ℝ := 1 - 7547360/(10^(10:ℕ))' in goal, 'DFT goal exponent differs')
        original = read('third-party/openai-math/lean/ComparatorChallenges/UniformFourier.lean').decode()
        challenge = read('Work/Fourier233/UniformFourierChallenge.lean').decode()
        for name in ('decimalExponent', 'decimalTime', 'TimeBounds', 'DFTGoal', 'ConvGoal',
                     'transform_main', 'convolution_main'):
            challenge = challenge.replace(name+'Y', name)
        challenge = challenge.replace('1 - 7547360/(10^(10:ℕ))', '1 - 1/(10^(13:ℕ))')
        require(strip_lean_comments(original) == strip_lean_comments(challenge),
                'challenge differs beyond comments, names and exponent')

    return {
        'schema': 1,
        'sources': {'five_stage': {'repository': source['repository'], 'commit': source['commit']},
                    'fourier_proof': source['fourier_proof']},
        'tensor_saving': str(A), 'fourier_saving': str(DELTA), 'absorption_gap': str(A-DELTA),
        'program': {'registers': 2*cert['v']+cert['R'], 'frames': len(cert['frames']),
                    'gates': len(cert['A'])+len(cert['B']), 'invocation_blocks': sum(inv.values()),
                    'invocation_rank': cert['N'], 'reference_checker': 'Jacob Sussman gx.check1',
                    'scalar_scope': 'all source columns; dirty-scratch restoration is proved by the Lean invocation theorem'},
        'network': {'m': m, 'roles_per_vertex': roles, 'rank': rank, 'deficit': m*roles-rank,
                    'max_child': max(hist), 'calls': sum(hist.values()),
                    'child_histogram': {str(r): n for r, n in sorted(hist.items())}},
        'moment_gap_lower_bound': rounded_down(1-hi),
        'finite_fill': {'s': 40, 'gap_lower_bound': rounded_down(1-folded_hi)},
        'negative_control': {'saving': str(reject_at), 'excess_lower_bound': rounded_down(reject_lo-1)},
        'bindings': {'lean_program': True, 'lean_histogram': True, 'lean_exponents': True,
                     'openai_challenge_modulo_exponent_and_names': True,
                     'openai_origin_files': len(origin['files']), 'openai_commit': origin['commit']},
        'scope': 'Finite Python checks only; see five_stage_lean_receipt.json for the separately reproduced Lean build.'
    }


def main():
    if sys.flags.optimize:
        raise SystemExit('Run without -O: the imported checker uses assertions.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true', help='write the reviewed finite reference certificate')
    args = parser.parse_args()
    result = verify()
    if args.write:
        REFERENCE.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    else:
        require(json.loads(REFERENCE.read_text()) == result, 'reference certificate differs')
    print('PASS: explicit PR256 program, five-stage ledger, exact moment, finite fill, absorption gap and Lean source bindings.')
    print('Tensor a = 0.0007547361; Fourier delta = 0.0007547360; gap = 1/10000000000.')


if __name__ == '__main__':
    main()
