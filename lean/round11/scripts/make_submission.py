#!/usr/bin/env python3
"""make_submission.py: write the Big O Speedrun verifier folder for this proof (github.com/bigospeedrun/verifier,
docs/targets.md): Submission.lean exporting Race.bound at saving 67/100000, manifest.json, and under Submission/ every
module reachable from Work.FourierR11.Main with `import OAI.|Work.|WHTCheck.` lines prefixed by `Submission.`
(no other change), plus Submission/NOTICE.lean.
Run from lean/round11:  python3 scripts/make_submission.py OUT_DIR"""
import os, re, shutil, sys

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
out = sys.argv[1]
if os.path.exists(out) and os.listdir(out):
    sys.exit('OUT_DIR must be empty or absent')
imp = re.compile(r'^import\s+(\S+)', re.M)
pat = re.compile(r'^(import\s+)((?:OAI|Work|WHTCheck)\.)', re.M)
path = lambda m: os.path.join(HERE, *m.split('.')) + '.lean'
seen, stack = set(), ['Work.FourierR11.Main']
while stack:
    m = stack.pop()
    if m in seen or not os.path.exists(path(m)):
        continue
    seen.add(m)
    stack += [x for x in imp.findall(open(path(m)).read()) if x.split('.')[0] in ('OAI', 'Work', 'WHTCheck')]
for m in sorted(seen):
    dst = os.path.join(out, 'Submission', *m.split('.')) + '.lean'
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    open(dst, 'w').write(pat.sub(r'\1Submission.\2', open(path(m)).read()))
shutil.copyfile(os.path.join(HERE, 'submission/Submission.lean'), os.path.join(out, 'Submission.lean'))
shutil.copyfile(os.path.join(HERE, 'submission/manifest.json'), os.path.join(out, 'manifest.json'))
shutil.copyfile(os.path.join(HERE, 'submission/NOTICE.lean'), os.path.join(out, 'Submission/NOTICE.lean'))
print('%d modules written to %s' % (len(seen), out))
