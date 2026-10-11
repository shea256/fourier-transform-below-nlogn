#!/usr/bin/env python3
"""check_provenance.py: compare this directory with the vendored upstream Lean source.

Run from lean/round11 (Python 3, standard library only):
    python3 scripts/check_provenance.py [ARCHIVE]
default archive: ../../verification/vendor/five_stage/fourier-proof-source.tar.gz, the complete source of
github.com/chafreaky/wht-power-saving-lean @ fd19e46b728faa414cbfbf91b01a6a0b7903375d (Jacob Sussman's framework with
Chafik Boukhalfa's fourth result; its SHA-256 is pinned in ../../verification/vendor/five_stage/SOURCE.json).

Every file here that has a path in the archive must be byte-identical to it.  Every other file must be listed in
ADDED below (new or modified-under-a-new-name files of this directory).  Upstream files that were not needed by the
round-eleven proof were left out; they are counted, not listed.  README.md and .gitignore replace the upstream files
of the same name (the upstream README is at the commit above).
"""
import hashlib, os, sys, tarfile

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ARCHIVE = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, '../../verification/vendor/five_stage/fourier-proof-source.tar.gz')
ADDED_PREFIXES = ('Work/GCert/Data/Gen/R11', 'Work/FourierR11/', 'Work/FourierR11Neg/', 'converter/', 'scripts/', 'receipt/', 'submission/')
ADDED_FILES = {
    'README.md', 'NOTICE.round11', '.gitignore',
    'Work/GCert/Data/B2GR11.lean', 'Work/GCert/Data/B2GR11Main.lean', 'Work/GCert/Data/ChallengeB2GR11.lean',
    'Work/GCert/Data/ChallengeB2GR11x.lean', 'Work/GCert/Data/InstB2GR11.lean', 'Work/GCert/Data/R11Cert.lean',
    'Work/GCert/Data/R11Price.lean', 'Work/GCert/Data/R11ScalOK.lean', 'Work/GCert/Data/RateB2GR11.lean',
    'Work/GCert/Data/RateB2GR11x.lean', 'Work/GCert/Data/SolutionB2GR11.lean', 'Work/GCert/Data/SolutionB2GR11x.lean',
    'tools/certificate/gcert1-p11-jain-r11.json.gz', 'tools/fourier/mkchainR11.py', 'tools/fourier/regen_checkR11.py',
    'comparator/B2GR11x.json', 'comparator/UniformFourierR11.json',
}


def sha(b):
    return hashlib.sha256(b).hexdigest()


up = {}
with tarfile.open(ARCHIVE) as t:
    for m in t.getmembers():
        if m.isfile():
            name = m.name[2:] if m.name.startswith('./') else m.name
            up[name] = sha(t.extractfile(m).read())
here = []
for d, dirs, fs in os.walk(HERE):
    dirs[:] = [x for x in dirs if x not in ('.lake', '__pycache__', 'build-logs')]
    for f in fs:
        here.append(os.path.relpath(os.path.join(d, f), HERE))
same = diff = added = 0
bad = []
for rel in sorted(here):
    h = sha(open(os.path.join(HERE, rel), 'rb').read())
    if rel in up and rel not in ADDED_FILES:
        if h == up[rel]:
            same += 1
        else:
            diff += 1
            bad.append('DIFFERS from upstream: ' + rel)
    elif rel in ADDED_FILES or rel.startswith(ADDED_PREFIXES):
        added += 1
    else:
        bad.append('NOT UPSTREAM AND NOT DECLARED: ' + rel)
print('\n'.join(bad))
print('upstream files byte-identical: %d; differing: %d; declared additions: %d; upstream files left out: %d'
      % (same, diff, added, len(set(up) - set(here))))
ok = not bad
print('RESULT: %s' % ('OK' if ok else 'FAIL'))
sys.exit(0 if ok else 1)
