#!/usr/bin/env python3
"""Exact audit of a related complex-network count model.

This does NOT verify OpenAI #130, its all-length reduction, or the unchanged-loss
assumption for the proposed circuit replacement. No floating-point value is used
for the certified comparisons. Python 3.10+; standard library only.
"""
from __future__ import annotations
import argparse
import json
from decimal import Decimal, localcontext
from fractions import Fraction as F
from math import comb
from pathlib import Path
from typing import Sequence

Poly = tuple[F, ...]  # increasing powers

def trim(p: Sequence[F | int]) -> Poly:
    q = [F(x) for x in p]
    while len(q) > 1 and q[-1] == 0:
        q.pop()
    return tuple(q or [F(0)])

def add(a: Poly, b: Poly) -> Poly:
    return trim([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
                 for i in range(max(len(a), len(b)))])

def scale(a: Poly, c: F | int) -> Poly:
    return trim([c*x for x in a])

def mul(a: Poly, b: Poly) -> Poly:
    r = [F(0)]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            r[i+j] += x*y
    return trim(r)

def power(a: Poly, n: int) -> Poly:
    r = trim([1])
    for _ in range(n):
        r = mul(r, a)
    return r

def derivative(a: Poly) -> Poly:
    return trim([i*a[i] for i in range(1, len(a))])

def shift(a: Poly, c: int) -> Poly:
    r = trim([0])
    for coefficient in reversed(a):
        r = add(mul(r, trim([c, 1])), trim([coefficient]))
    return r

def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)

def counts(h: int, replacement: bool = False) -> dict:
    if not isinstance(h, int) or h < 6:
        raise ValueError('h must be an integer >= 6')
    v, m = comb(h, 3), h**3
    N = v**3
    original_R2 = v*3*(h-3)
    R2 = comb(h, 2)*(4*h-14) if replacement else original_R2
    side_roles = v*comb(h-3, 3) + R2
    W = 2*N + 3*v*v*(side_roles+h+1)
    # For replacement=True, retaining this L is a hypothesis, NOT a checked theorem.
    L = 3*v*v*h*(h+1)
    s = W*m - 2*N + 2*L
    return dict(h=h, v=v, m=m, N=N, W=W, L=L, s=s,
                intersection_two_roles=R2, side_roles=side_roles,
                eta=F(2*(N-L), W*m))

def series_bounds(y: F, terms: int) -> tuple[F, F]:
    """Rigorous natural-log enclosure for rational 1 <= y <= 2."""
    if not (1 <= y <= 2) or terms < 1:
        raise ValueError('series requires 1 <= y <= 2 and terms >= 1')
    z = (y-1)/(y+1)
    z2 = z*z
    t, s = z, F(0)
    for j in range(terms):
        s += t/(2*j+1)
        t *= z2
    lo = 2*s
    tail = 2*t/((2*terms+1)*(1-z2))
    return lo, lo+tail

def log_bounds(x: F) -> tuple[F, F]:
    """Range reduction plus exact atanh series; x is rational and >= 1."""
    if x < 1:
        raise ValueError('x must be >= 1')
    y, k = x, 0
    while y > 2:
        y /= 2
        k += 1
    t = 6 if y < F(1001,1000) else 40
    lo, hi = series_bounds(y, t)
    l2, u2 = series_bounds(F(2), 40)
    return lo+k*l2, hi+k*u2

def saving_bounds(c: dict) -> tuple[F, F]:
    eta = c['eta']
    if not (0 < eta < 1):
        raise ValueError('positive contraction required')
    nl, nu = log_bounds(1/(1-eta))
    dl, du = log_bounds(F(c['m']))
    return nl/du, nu/dl

def decimal(x: F, precision: int = 36) -> str:
    with localcontext() as ctx:
        ctx.prec = precision
        return str(Decimal(x.numerator)/Decimal(x.denominator))

def frac_json(x: F) -> dict:
    return {'numerator': str(x.numerator), 'denominator': str(x.denominator)}

def audit_symbolic_model() -> list[int]:
    x = trim([0,1])
    v = scale(mul(mul(x, trim([-1,1])), trim([-2,1])), F(1,6))
    z = add(scale(mul(mul(trim([-3,1]), trim([-4,1])), trim([-5,1])), F(1,6)),
            trim([-9,3]))
    N = power(v,3)
    L = scale(mul(mul(power(v,2), x), trim([1,1])), 3)
    W = add(scale(N,2), scale(mul(power(v,2), add(mul(v,z),trim([1,1]))),3))
    f = trim([-64,-84,4])
    P = trim([36,-184,460,-329,103,-15,1])
    g = mul(power(x,2),P)
    require(mul(scale(add(N,scale(L,-1)),2),g) == mul(f,mul(W,power(x,3))),
            'simplified eta polynomial identity')
    Q = trim([-576,4038,-10856,-1422,9334,-5061,1087,-111,3])
    require(add(mul(derivative(f),g), scale(mul(f,derivative(g)),-1)) ==
            scale(mul(x,Q),-8), 'eta derivative identity')
    shifted = shift(Q,26)
    require(all(c > 0 and c.denominator == 1 for c in shifted),
            'Q(t+26) has strictly positive integer coefficients')
    return [int(c) for c in shifted]

def audit() -> dict:
    shifted = audit_symbolic_model()
    baseline = counts(25)
    expected = dict(m=15625,v=2300,N=12167000000,W=58645352620000,
                    L=10315500000,s=916333630984500000)
    require(all(baseline[k] == v for k,v in expected.items()), 'published h=25 counts')
    require(baseline['eta'] == F(14,3464399375), 'published normalized saving')
    require(all(counts(h)['eta'] <= 0 for h in range(6,22)), 'no saving below 22')
    bounds = {h:saving_bounds(counts(h)) for h in range(22,27)}
    l25,u25 = bounds[25]
    require(all(l25 > bounds[h][1] for h in (22,23,24,26)), 'finite strict comparisons')
    require(F(41847990372,10**20) < l25 < u25 < F(41847990373,10**20),
            'baseline displayed enclosure')
    proposed = counts(25, replacement=True)
    lp,up = saving_bounds(proposed)
    require(F(43325243376,10**20) < lp < up < F(43325243377,10**20),
            'conditional displayed enclosure')
    require(lp > F(43325,10**14), 'conditional rational witness')
    old_slack = (l25/F(418,10**12)-1, u25/F(418,10**12)-1)
    proposed_gain = (lp/u25-1, up/l25-1)
    rows = []
    for h in range(22,29):
        base, prop = counts(h), counts(h,True)
        lb,ub = saving_bounds(base)
        ll,uu = saving_bounds(prop)
        rows.append({'h':h,'baseline_a_lower_decimal':decimal(lb),
                     'baseline_a_upper_decimal':decimal(ub),
                     'conditional_candidate_a_lower_decimal':decimal(ll),
                     'conditional_candidate_a_upper_decimal':decimal(uu)})
    clean = lambda c:{k:frac_json(v) if isinstance(v,F) else v for k,v in c.items()}
    return {
        'status':'EXACT COUNT AUDIT; NO IMPROVED FOURIER THEOREM CLAIMED',
        'baseline_global_optimum':{'domain':'integers h >= 6 in unchanged symmetric count model',
                                   'h':25,'proof':'negative deficits below 22; exact comparisons 22..26; decreasing for all real h >= 26',
                                   'Q_shift_26_coefficients_increasing_powers':shifted},
        'baseline_h25':clean(baseline),
        'baseline_a_bounds':{'lower':frac_json(l25),'upper':frac_json(u25)},
        'baseline_a_decimal_enclosure':[decimal(l25),decimal(u25)],
        'rounding_slack_vs_doug_witness_percent':[decimal(100*old_slack[0]),decimal(100*old_slack[1])],
        'candidate_h25_conditional':clean(proposed),
        'candidate_assumption':'The new circuit must preserve L and the full phase-frame interface; NOT established by this script.',
        'candidate_a_bounds_conditional':{'lower':frac_json(lp),'upper':frac_json(up)},
        'candidate_a_decimal_enclosure_conditional':[decimal(lp),decimal(up)],
        'candidate_gain_percent_conditional':[decimal(100*proposed_gain[0]),decimal(100*proposed_gain[1])],
        'table':rows,
        'sources':[
            'https://github.com/CrocSwap/integer-mult-bounds/blob/main/notes/independent-complex.tex',
            'https://github.com/CrocSwap/integer-mult-bounds/blob/main/patches/compact-control-34.patch'],
        'not_verified':['OpenAI #130 full manuscript','Transfer to an all-length DFT exponent',
                        'Global phase-frame telescoping and rank loss for replacement',
                        'Research priority or novelty']}

def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path, default=Path(__file__).with_name('counts_certificate.json'))
    args=p.parse_args()
    result=audit()
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print('PASS: exact baseline identities, global symmetric optimum, and conditional projection arithmetic.')
    print('Baseline a:',result['baseline_a_decimal_enclosure'])
    print('Candidate a (CONDITIONAL):',result['candidate_a_decimal_enclosure_conditional'])
    print('Gain percent (CONDITIONAL):',result['candidate_gain_percent_conditional'])
    print('Certificate:',args.output)
if __name__ == '__main__':
    main()
