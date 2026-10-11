#!/usr/bin/env python3
"""check_conversion.py: reproduce and audit the certificate tools/certificate/gcert1-p11-jain-r11.json.gz.

Run from lean/round11 with Python 3.10+ (standard library only):
    python3 converter/check_conversion.py [WORD.json.gz]
default word: ../../verification/vendor/jain_round11/word.json.gz (Swapnil Jain, integer-mult-kappa @ 1a580dc).

1. converter/word_to_gcert.py rebuilds the certificate; it must equal the committed file byte for byte.
2. Sussman's reference checker gx.check1 (labels and the exact scalar identity) must accept it.
3. Faithfulness of the ledger: 3 x (block histogram) + 2v at rank 2 must equal Jain's own claimed child
   histogram (claim_hosts.C, whose 1e-12 certificate is a_c = 67147467/10^11), and 2v + R must equal his W.
4. Five corrupted conversions (W2G_CONTROL) must each be rejected by gx.check1.
None of this is part of the proof; the Lean kernel checks the generated modules.
"""
import gzip, json, os, subprocess, sys, tempfile
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
CERT = os.path.join(ROOT, 'tools/certificate/gcert1-p11-jain-r11.json.gz')
WORD = sys.argv[1] if len(sys.argv) > 1 else os.path.join(ROOT, '../../verification/vendor/jain_round11/word.json.gz')
sys.path.insert(0, os.path.join(ROOT, 'tools/gx'))
import gx  # noqa: E402

ok = True


def report(name, good):
    global ok
    ok &= bool(good)
    print(('PASS ' if good else 'FAIL ') + name, flush=True)


def emit(out, control=''):
    env = dict(os.environ, W2G_CONTROL=control)
    subprocess.run([sys.executable, os.path.join(HERE, 'word_to_gcert.py'), WORD, out], env=env, check=True,
                   stdout=subprocess.DEVNULL)
    return json.loads(gzip.decompress(open(out, 'rb').read()))


def accepted(c):
    try:
        gx.check1(c)
        return True, ''
    except AssertionError as e:
        return False, str(e)


tmp = tempfile.mkdtemp(prefix='r11-conv-')
path = os.path.join(tmp, 'cert.json.gz')
c = emit(path)
report('converter output identical to the committed certificate', open(path, 'rb').read() == open(CERT, 'rb').read())
good, why = accepted(c)
report('gx.check1 accepts the certificate (labels and exact scalar identity) %s' % why, good)
J = json.load(gzip.open(WORD, 'rt'))
H = Counter()
for w in c['blocks'].values():
    for r, n in w.items():
        H[int(r)] += n
mine = Counter({r: 3 * n for r, n in H.items()})
mine[2] += 2 * J['v']
claim = {int(r): int(k) for r, k in J['claim_hosts']['C'].items()}
report('3 x block histogram + 2v at rank 2 equals Jain\'s claimed child histogram', dict(+mine) == claim)
report('2v + R = %d equals Jain\'s W = %s' % (2 * c['v'] + c['R'], J['claim_hosts']['W']),
       2 * c['v'] + c['R'] == int(J['claim_hosts']['W']))
for ctl in ('gauge_sign', 'sink_sign', 'skip_mix', 'host_plus', 'drop_pre'):
    good, why = accepted(emit(os.path.join(tmp, ctl + '.json.gz'), ctl))
    report('control %s rejected (%s)' % (ctl, why), not good)
print('RESULT: %s' % ('ALL PASS' if ok else 'FAIL'))
sys.exit(0 if ok else 1)
