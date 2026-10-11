#!/usr/bin/env python3
"""word_to_gcert.py: lower a frozen check_word2 complex word (Swapnil Jain's round-eleven export: paired-cube word with
birth reuse, terminal sinks and dead-copy recycling hosts) to Jacob Sussman's certificate format gcert/1.

Conventions follow tools/emit/gcert_emit.py of wht-power-saving-lean:
  x_j = j (sources at their port line), y_t = v + t (targets, frame 0 -> port^perp), slots 2v.. (one per physical
  register: a birth-reuse recipient continues its donor's slot, a recycling birth continues its pivot's slot).
  A sign flip d := -d + c changes the unit of the slot (wanted = lam * stored), as gxconv.py does.
Semantics of the word follow its own checker (check_word.py / check_word2.py: replay()), read as a specification:
  phase A = schedule before the cut (source copies, ops); scatter = the 22 centre totals; phase B = pre-shears,
  gauge (birth) reads at their clocks, ops (sink writes go straight to the sink's pivot target), post-shears,
  side-root reads, then the K blocks of the #144 decoder as in gcert_emit.py.
The frame-0 compensation reads, the source undo and the slot undo are not written: the invocation theorem derives them.
usage: word_to_gcert.py WORD.json.gz OUT.json.gz
"""
import sys, gzip, json, os
CTL = os.environ.get('W2G_CONTROL', '')  # negative controls only; the default build uses none
from fractions import Fraction as F
from collections import Counter, defaultdict


def rref(rows):
    piv = {}
    for x in rows:
        for k in sorted(piv, reverse=True):
            if x >> k & 1:
                x ^= piv[k]
        if x:
            k = x.bit_length() - 1
            for kk in list(piv):
                if piv[kk] >> k & 1:
                    piv[kk] ^= x
            piv[k] = x
    return tuple(piv[k] for k in sorted(piv, reverse=True))


def perp(rows, h):
    B = rref(rows)
    piv = [b.bit_length() - 1 for b in B]
    out = []
    for k in [k for k in range(h) if k not in piv]:
        u = 1 << k
        for b in B:
            if b >> k & 1:
                u |= 1 << (b.bit_length() - 1)
        out.append(u)
    return rref(out)


def enc(x):
    x = F(x)
    return [x.numerator, x.denominator]


def main():
    J = json.load(gzip.open(sys.argv[1], 'rt'))
    h, v, R = J['h'], J['v'], J['R']
    args, signs, inputs = J['args'], J['signs'], J['inputs']
    roots = J['roots']; ops = [tuple(o) for o in J['ops']]; sched = list(J['sched']); cut = J['cut']
    sources = {int(x): s for x, s in J['sources'].items()}
    gauges = J['gauges']
    frames_w = [tuple(f) for f in J['frames']]
    # ---- recycling hosts: exactly the transformation of check_word2.py
    HOSTS = J.get('hosts', []); MIX = set(); UNUSED = set()
    rootroles = J['rootroles']; tau = {int(b): t for b, t in J['tau'].items()}; pairs = [tuple(q) for q in J['pairs']]
    if HOSTS:
        ren = {z['birth']: z['pivot'] for z in HOSTS}
        firstk = {}
        for k, i in enumerate(sched):
            for r_ in ops[i][:2]:
                if r_ in ren and r_ not in firstk:
                    firstk[r_] = k
        ins = defaultdict(list)
        for z in HOSTS:
            k = firstk[z['birth']]; j = len(ops); ops.append((z['pivot'], z['control'], -1)); frames_w.append(frames_w[sched[k]])
            ins[k].append(j); MIX.add(j)
        ops = [(ren.get(d, d), ren.get(c, c), x) for d, c, x in ops]
        newsched = []; fmap = {}
        for k, i in enumerate(sched):
            fmap[k] = len(newsched); newsched += ins.get(k, []); newsched.append(i)
        fmap[len(sched)] = len(newsched)
        sched = newsched; cut = fmap[cut]
        tau = {b: fmap[t] for b, t in tau.items()}
        rootroles = [ren.get(s_, s_) for s_ in rootroles]
        pairs = [(ren.get(a_, a_), ren.get(b_, b_)) for a_, b_ in pairs]
        UNUSED = set(ren)
    n = len(args)
    spans = [()] * n
    for x in range(1, n):
        spans[x] = (inputs[x - 1],) if args[x] is None else rref(spans[args[x][0]] + spans[args[x][1]])
    pos = {i: k for k, i in enumerate(sched)}
    rops = [[] for _ in range(R)]
    for i in sched:
        a, b, _ = ops[i]; rops[a].append(i); rops[b].append(i)
    hold = {sr: xx for xx, sr in sources.items()}; coef = {}
    for i in sched:
        d, c, xx = ops[i]
        if i in MIX:
            assert hold.get(d) is not None and hold[d] == hold[c]; hold[d] = None; coef[i] = (1, -1); continue
        if hold.get(d) is None:
            assert hold[c] == xx; coef[i] = (1, 1)
        else:
            aa, bb = args[xx]; sg = signs[xx]
            if hold[d] == aa:
                assert hold[c] == bb; coef[i] = (1, sg)
            else:
                assert hold[d] == bb and hold[c] == aa; coef[i] = (sg, 1)
        hold[d] = xx
    rootframe, rootkind, rootann = {}, {}, {}
    for r, sr in zip(roots, rootroles):
        rootkind[sr] = r['kind']
        if r['kind'] == 'center':
            rootframe[sr] = spans[r['node']]
        else:
            rootann[sr] = rref([inputs[t] for t in r['targets']]); rootframe[sr] = perp(rootann[sr], h)
    gsig = {z['role']: perp(z['A'], h) for z in gauges}
    gauged = set(gsig); donor = {a: b for a, b in pairs}; recip = {b: a for a, b in pairs}
    assert all(b in recip for b in gauged), 'exterior gauge: not supported on the rate path'
    # ---- exact compensation coefficients (check_word2.compensation over Q)
    seeds = [(sr, r['kind'], {t: F(c) for t, c in zip(r['targets'], r['coefficients'])}) for r, sr in zip(roots, rootroles)]
    cf = [dict() for _ in range(R)]

    def addto(dst, src, k):
        for t, u in src.items():
            w = dst.get(t, 0) + k * u
            if w:
                dst[t] = w
            else:
                dst.pop(t, None)
    for sr, kind, sd in seeds:
        if kind == 'side':
            addto(cf[sr], sd, 1)
    for k in range(len(sched) - 1, -1, -1):
        i = sched[k]; d, c, _ = ops[i]; ca, cb = coef[i]
        if k == cut - 1:
            for sr, kind, sd in seeds:
                if kind == 'center':
                    addto(cf[sr], sd, 1)
        addto(cf[c], cf[d], cb)
        if ca != 1:
            cf[d] = {t: ca * u for t, u in cf[d].items()}
    assert cut > 0
    # ---- sinks (eligibility is checked by check_word2; here only the data the program needs)
    S = {}
    for z in J.get('sinks', []):
        j = rootroles.index(z['role']); r = roots[j]
        assert r['kind'] == 'side' and len(set(r['coefficients'])) == 1
        assert all(ops[i][0] == z['role'] and coef[i][0] == 1 and pos[i] >= cut for i in rops[z['role']])
        S[z['role']] = dict(T=list(r['targets']), c=z['pivot'], u=F(r['coefficients'][0]),
                            L=pos[rops[z['role']][-1]], frame=rootframe[z['role']])
    # ---- frames table
    frames = [(), tuple(1 << i for i in range(h - 1, -1, -1))]
    fid = {frames[0]: 0, frames[1]: 1}

    def frame(rows):
        key = rref(rows)
        if key not in fid:
            fid[key] = len(frames); frames.append(key)
        return fid[key]
    ports = inputs
    xstart = [frame((q,)) for q in ports]
    caps = [frame(perp((q,), h)) for q in ports]
    # ---- physical slots
    def rs(sr):
        while sr in recip:
            sr = recip[sr]
        return sr
    phys = sorted(set(rs(sr) for sr in range(R) if sr not in S and sr not in UNUSED))
    slot_of = {p: 2 * v + k for k, p in enumerate(phys)}
    slot = lambda sr: slot_of[rs(sr)]
    nR = len(phys)
    lam = defaultdict(lambda: F(1))
    A, B = [], []
    # source copies at the port line
    for xx, sr in sorted(sources.items()):
        A.append(['out', xstart[xx - 1], xx - 1, [[slot(sr), 1, 1]], []])
    # gauge reads by clock, in the exporter's same-clock order (reverse list order)
    rt = defaultdict(list)
    for k_, z in enumerate(gauges):
        rt[tau[z['role']]].append((len(gauges) - 1 - k_, z))
    for k_ in rt:
        rt[k_].sort(key=lambda e: e[0])
    lastw = {rops[s][-1]: s for s in S}
    ret = []

    def op_gate(i, gates):
        d, c, _ = ops[i]; ca, cb = coef[i]; f = frame(frames_w[i])
        if d in S:
            x = S[d]; sc = slot(c)
            w = x['u'] * cb * lam[sc] * (-1 if CTL == 'sink_sign' and i == min(rops[d]) else 1)
            gates.append(['out', f, sc, [[v + x['c'], *enc(w)]], []])
            return
        sd, sc = slot(d), slot(c); assert sd != sc
        if CTL == 'skip_mix' and i == min(MIX):
            return
        if CTL == 'host_plus' and i == min(MIX):
            cb = -cb
        if ca != 1:
            assert ca == -1
            lam[sd] = -lam[sd]
        gates.append(['out', f, sc, [[sd, *enc(cb * lam[sc] / lam[sd])]], []])

    def shear(x, sg):
        tg = [[v + t, sg, 1] for t in x['T'] if t != x['c']]
        return tg
    for k, i in enumerate(sched):
        if k == cut:
            # the centre totals rest at their frames; then the scatter cut
            for r, sr in zip(roots, rootroles):
                if r['kind'] == 'center':
                    assert all(pos[i_] < cut for i_ in rops[sr]), 'centre role touched after the cut'
                    s = slot(sr); f = frame(rootframe[sr])
                    A.append(['out', f, s, [], []])
                    ret.append([r['coordinate'], s, f, lam[s]])
            for s_, x in S.items():
                if len(x['T']) > 1 and not (CTL == 'drop_pre' and s_ == next(iter(S))):
                    B.append(['out', 0, v + x['c'], shear(x, -1), []])
        gates = A if k < cut else B
        for _, z in rt.get(k, ()):
            b = z['role']; s = slot(b); f = frame(gsig[b])
            assert set(cf[b]) <= set(z['targets']), 'gauge response outside its targets'
            tg = [[v + t, *enc(-cf[b][t] * lam[s])] for t in sorted(cf[b])]
            if CTL == 'gauge_sign' and k == min(rt):
                tg[0][1] = -tg[0][1]
            extra = [v + t for t in z['targets'] if t not in cf[b]]
            gates.append(['out', f, s, tg, extra])
        op_gate(i, gates)
        if i in lastw:
            x = S[lastw[i]]
            if len(x['T']) > 1:
                B.append(['out', frame(x['frame']), v + x['c'], shear(x, +1), []])
    assert not rt.get(len(sched))
    for r, sr in zip(roots, rootroles):
        if r['kind'] == 'side' and sr not in S:
            s = slot(sr)
            B.append(['out', frame(rootframe[sr]), s, [[v + t, *enc(F(c) * lam[s])] for t, c in zip(r['targets'], r['coefficients'])], []])
    # ---- K blocks, direct reads, inverse K blocks (gcert_emit.py, unchanged)
    for cube in range(v // 8):
        ids8 = list(range(8 * cube, 8 * cube + 8))
        for parity in range(2):
            ids = [j for j in ids8 if bin(j).count('1') % 2 == parity]
            Sf = frame(tuple(ports[j] for j in ids)); assert len(frames[Sf]) == 3
            x1, rest = ids[0], ids[1:]
            B.append(['in', Sf, x1, [[r_, 1, 1] for r_ in rest]])
            B.append(['out', Sf, x1, [[r_, -1, 2] for r_ in rest], []])
            B.append(['in', Sf, x1, [[r_, 1, 1] for r_ in rest]])
    for cube in range(v // 8):
        ids8 = list(range(8 * cube, 8 * cube + 8))
        for j in ids8:
            anti = [t for t in ids8 if bin(ports[t] ^ ports[j]).count('1') == 6]; assert len(anti) == 1
            t = anti[0]
            x1 = [jj for jj in ids8 if bin(jj).count('1') % 2 == bin(j).count('1') % 2][0]
            B.append(['out', caps[t], j, [[v + t, -1 if j == x1 else 1, 1]], []])
    for cube in range(v // 8):
        ids8 = list(range(8 * cube, 8 * cube + 8))
        for parity in range(2):
            ids = [j for j in ids8 if bin(j).count('1') % 2 == parity]
            x1, rest = ids[0], ids[1:]
            B.append(['in', 1, x1, [[r_, -1, 1] for r_ in rest]])
            B.append(['out', 1, x1, [[r_, 1, 2] for r_ in rest], []])
            B.append(['in', 1, x1, [[r_, -1, 1] for r_ in rest]])
    # ---- scatter (star, or a table when a total is stored in a flipped unit)
    ret.sort()
    assert [z[0] for z in ret] == list(range(h))
    sin, sout = F(1, 3), F(-1, 6)
    if all(z[3] == 1 for z in ret):
        scat = dict(inside=[1, 3], outside=[-1, 6])
    else:
        scat = dict(table=[[[k, *enc((sin if ports[t] >> k & 1 else sout) * ret[k][3])] for k in range(h)] for t in range(v)])
    ret = [[k, s, f] for k, s, f, _ in ret]
    nreg = 2 * v + nR
    start = [0] * nreg; final = [1] * nreg
    for j in range(v):
        start[j] = xstart[j]; final[v + j] = caps[j]
    cst = sum(len(frames[f]) for _, _, f in ret)
    # ---- block histogram (the climb count of gx.check1)
    dim = [len(f) for f in frames]
    cur = list(start)
    H = {'x': Counter(), 'y': Counter(), 's': Counter(), 'c': Counter()}
    cls = lambda r_: 'x' if r_ < v else 'y' if r_ < 2 * v else 's'

    def climb(r_, f):
        o = cur[r_]
        if o != f:
            assert dim[o] < dim[f], ('step not increasing', r_, o, f)
            H[cls(r_)][dim[f] - dim[o]] += 1; cur[r_] = f
    for ph, gates in (('A', A), ('B', B)):
        if ph == 'B':
            for k, s, f in ret:
                assert cur[s] == f
                H['c'][dim[f]] += 1
        for gg in gates:
            regs = [gg[2]] + ([x for x, _, _ in gg[3]] + list(gg[4]) if gg[0] == 'out' else [x for x, _, _ in gg[3]])
            for r_ in regs:
                climb(r_, gg[1])
    for r_ in range(nreg):
        climb(r_, final[r_])
    blocks = {k: {str(r_): n_ for r_, n_ in sorted(w.items())} for k, w in H.items()}
    Nn = sum(r_ * n_ for w in H.values() for r_, n_ in w.items())
    assert Nn == nR * h + 2 * v * (h - 1) + cst, (Nn, nR * h + 2 * v * (h - 1) + cst)
    c1 = dict(format='gcert/1', derived_from='%s (word_to_gcert.py from the frozen check_word2 word)' % J['name'],
              p=J['p'], h=h, v=v, R=nR, cst=cst, N=Nn, ports=ports, frames=[list(f) for f in frames], start=start,
              final=final, ext=[], ret=ret, scat=scat, A=A, B=B, blocks=blocks)
    data = json.dumps(c1, separators=(',', ':')).encode()
    open(sys.argv[2], 'wb').write(gzip.compress(data, mtime=0) if sys.argv[2].endswith('.gz') else data)
    print(json.dumps(dict(R=nR, N=Nn, cst=cst, gates_A=len(A), gates_B=len(B), frames=len(frames),
                          scatter='table' if 'table' in scat else 'star', blocks=blocks)))


if __name__ == '__main__':
    main()
