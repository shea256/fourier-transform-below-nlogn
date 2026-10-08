#!/usr/bin/env python3
"""Second implementation of finite checks for the proposed Fourier extension.

Standard library only. No imports from the earlier research/verifier package.
This is a second implementation by the SAME assistant, NOT independent review
and NOT a formal proof of the all-length theorem or the upstream manuscript.

It uses allocation in topological order (not union-find), sparse rational linear
operators, and binary orthogonal PROJECTORS (not the old nullspace edge checker).
"""
from __future__ import annotations
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations
from math import comb, factorial
from pathlib import Path
import hashlib
import json
import time


def check(ok: bool, msg: str) -> None:
    if not ok:
        raise AssertionError(msg)


def xor_rows(mask: int, rows: tuple[int, ...]) -> int:
    ans = 0
    while mask:
        bit = mask & -mask
        ans ^= rows[bit.bit_length() - 1]
        mask ^= bit
    return ans


def parity(n: int) -> int:
    return n.bit_count() & 1


def rank_and_basis(rows) -> tuple[int, tuple[int, ...]]:
    pivots = {}
    for row in rows:
        while row:
            i = row.bit_length() - 1
            if i in pivots:
                row ^= pivots[i]
            else:
                pivots[i] = row
                break
    return len(pivots), tuple(pivots.values())


def add_sparse(dst: dict[int, F], src: dict[int, F], scale: F = F(1)) -> None:
    for col, value in src.items():
        new = dst.get(col, F(0)) + scale * value
        if new:
            dst[col] = new
        else:
            dst.pop(col, None)


@dataclass
class Graph:
    h: int
    triples: list[tuple[int, int, int]]
    labels: list[int]
    children: list[tuple[int, int] | None]
    supports: list[tuple[int, ...]]
    outputs: list[tuple[int, int]]  # (target index, DAG node)
    roles: int
    sources: list[int]
    reads: list[int]
    gates: list[tuple[int, int, int]]  # destination role, source role, DAG label node


def make_graph(h: int) -> Graph:
    check(h >= 7, 'h must be at least seven')
    triples = list(combinations(range(h), 3))
    index = {t: j for j, t in enumerate(triples)}
    labels = [sum(1 << k for k in t) for t in triples]
    v = len(triples)
    children = [None] * v
    supports = [(j,) for j in range(v)]
    outputs = []

    def node(a, b):
        children.append((a, b))
        supports.append(tuple(sorted(supports[a] + supports[b])))
        check(len(set(supports[-1])) == len(supports[-1]), 'DAG inputs do not repeat')
        return len(children) - 1

    for pair in combinations(range(h), 2):
        ids = [index[tuple(sorted(pair + (k,)))] for k in range(h) if k not in pair]
        r = len(ids)
        pref = [ids[0]]
        for k in range(1, r - 2):
            pref.append(node(pref[-1], ids[k]))
        suffix = {r - 1: ids[-1]}
        for k in range(r - 2, 1, -1):
            suffix[k] = node(ids[k], suffix[k + 1])
        for k, target in enumerate(ids):
            parts = (ids[1], suffix[2]) if k == 0 else (pref[-1], ids[-2]) if k == r - 1 else (pref[k - 1], suffix[k + 1])
            outputs.extend((target, part) for part in parts)

    # Each DAG node's outgoing USE is a separate role, except that an addition
    # reuses its first incoming role for its first outgoing use. Allocate in
    # topological order, rather than identify edge slots with union-find.
    uses = [[] for _ in children]
    for j, pair in enumerate(children):
        if pair is not None:
            for operand, source in enumerate(pair):
                uses[source].append(('gate', j, operand))
    for j, (_, source) in enumerate(outputs):
        uses[source].append(('read', j, 0))
    incoming = {}
    reads = [None] * len(outputs)
    sources, gates = [], []
    role_count = 0

    def allocate():
        nonlocal role_count
        role_count += 1
        return role_count - 1

    def assign(use, role):
        kind, j, operand = use
        if kind == 'read':
            reads[j] = role
        else:
            incoming[j, operand] = role

    for j, pair in enumerate(children):
        check(bool(uses[j]), 'every source and addition is used')
        if pair is None:
            pivot = allocate()
            sources.append(pivot)
        else:
            pivot = incoming[j, 0]
            other = incoming[j, 1]
            check(pivot != other, 'addition is an invertible shear')
            gates.append((pivot, other, j))
        assign(uses[j][0], pivot)
        for use in uses[j][1:]:
            out = allocate()
            gates.append((out, pivot, j))
            assign(use, out)

    check(len(set(sources)) == v, 'distinct source pivots')
    check(len(set(reads)) == len(reads), 'distinct readout roles')
    check(role_count == comb(h, 2) * (4*h - 14), 'derived role count')
    return Graph(h, triples, labels, children, supports, outputs,
                 role_count, sources, reads, gates)


def coefficient_check(g: Graph) -> dict:
    # Exact ordinary integer coefficients, not Boolean union used as addition.
    state = [{} for _ in range(g.roles)]
    for j, role in enumerate(g.sources):
        state[role] = {j: 1}
    for dst, src, _ in g.gates:
        for col, value in state[src].items():
            state[dst][col] = state[dst].get(col, 0) + value
    out = [Counter() for _ in g.triples]
    for slot, (target, _) in zip(g.reads, g.outputs):
        out[target].update(state[slot])
    for target, T in enumerate(g.labels):
        expected = {j: 1 for j, S in enumerate(g.labels) if (T & S).bit_count() == 2}
        check(dict(out[target]) == expected, 'entire H2 matrix, including zero entries')
    return {'h': g.h, 'inputs': len(g.triples), 'roles': g.roles,
            'forward_shears': len(g.gates), 'reads': len(g.reads),
            'matrix_entries_covered': len(g.triples)**2,
            'nonzero_entries': sum(len(row) for row in out), 'pass': True}


class Projectors:
    """Exact binary symmetric idempotent matrices, stored as packed bit rows."""
    def __init__(self, h):
        self.h = h
        self.matrices, self.lookup, self.ranks, self.nonalt = [], {}, [], []
        self.zero = self.register((0,)*h)
        self.full = self.register(tuple(1 << j for j in range(h)))
        self.residuals = set()

    def register(self, rows):
        rows = tuple(rows)
        if rows in self.lookup:
            return self.lookup[rows]
        h = self.h
        check(all(((rows[i] >> j) & 1) == ((rows[j] >> i) & 1)
                  for i in range(h) for j in range(h)), 'symmetric projector')
        check(all(xor_rows(row, rows) == row for row in rows), 'idempotent projector')
        r, basis = rank_and_basis(rows)
        # For a symmetric idempotent, range and kernel are perpendicular;
        # verify Gram nondegeneracy independently on an actual range basis.
        gram = [sum(parity(u & w) << j for j, w in enumerate(basis)) for u in basis]
        check(rank_and_basis(gram)[0] == r, 'nondegenerate projected subspace')
        odd = any(parity(row) for row in basis)
        check(odd == any((rows[j] >> j) & 1 for j in range(h)), 'nonalternation diagonal test')
        k = len(self.matrices)
        self.lookup[rows] = k
        self.matrices.append(rows)
        self.ranks.append(r)
        self.nonalt.append(odd)
        return k

    def span(self, vectors):
        vectors = tuple(vectors)
        check(all(parity(u & v) == int(i == j)
                  for i, u in enumerate(vectors) for j, v in enumerate(vectors)),
              'orthonormal vectors defining a projection')
        rows = [0]*self.h
        for u in vectors:
            for i in range(self.h):
                if (u >> i) & 1:
                    rows[i] ^= u
        pid = self.register(rows)
        check(self.ranks[pid] == len(vectors), 'span dimension')
        return pid

    @lru_cache(None)
    def complement(self, p):
        return self.register(tuple(row ^ (1 << j) for j, row in enumerate(self.matrices[p])))

    @lru_cache(None)
    def included(self, p, q):
        if self.ranks[p] > self.ranks[q]:
            return False
        Q = self.matrices[q]
        return all(xor_rows(row, Q) == row for row in self.matrices[p])

    @lru_cache(None)
    def difference(self, p, q):
        check(self.included(p, q) or self.included(q, p), 'nested projection spaces')
        out = self.register(tuple(x ^ y for x, y in zip(self.matrices[p], self.matrices[q])))
        check(self.ranks[out] == abs(self.ranks[p] - self.ranks[q]), 'actual residual rank')
        self.residuals.add(out)
        return out


def full_shared_frame_check(g: Graph) -> dict:
    h, v, R = g.h, len(g.triples), g.roles
    p = Projectors(h)
    Z, D = p.zero, p.full
    node_space = [p.span(g.labels[i] for i in S) for S in g.supports]
    line = node_space[:v]
    rows = []
    for stage in (1, 2, 3):
        b = h**(stage - 1) - 1
        states = [(Z, Z)]*R + [(u, u) for u in line] + [(u, Z) for u in line] + [(Z, Z)]*h
        X = lambda i: R + i
        Y = lambda i: R + v + i
        center = list(range(R + 2*v, R + 2*v + h))
        low, high = (D, Z), (D, D)
        touched, absolute, signed, drops = 0, 0, 0, Counter()

        def touch(wires, frame):
            nonlocal touched, absolute, signed
            for wire in wires:
                old = states[wire]
                active = [(old[1], frame[1])]
                if b:
                    active.append((old[0], frame[0]))
                up = all(p.included(a, z) for a, z in active)
                down = all(p.included(z, a) for a, z in active)
                check(up or down, 'physical wire endpoint frames are nested')
                ra = p.difference(old[0], frame[0]) if b else Z
                rz = p.difference(old[1], frame[1])
                dim = b*p.ranks[ra] + p.ranks[rz]
                check(not dim or (b and p.nonalt[ra]) or p.nonalt[rz],
                      'nonzero TOTAL residual is nonalternating')
                delta = b*(p.ranks[frame[0]] - p.ranks[old[0]]) + p.ranks[frame[1]] - p.ranks[old[1]]
                check(abs(delta) == dim, 'dimension accounting agrees with projectors')
                if delta < 0:
                    kind = 'scratch' if wire < R else 'bank' if wire < R + 2*v else 'center'
                    drops[kind] += -delta
                states[wire] = frame
                absolute += dim
                signed += delta
                touched += 1

        def A(mode, reverse=False):
            for dst, src, node in (reversed(g.gates) if reverse else g.gates):
                U = node_space[node]
                frame = low if mode == 'low' else high if mode == 'high' else (U, Z) if mode == 'low-span' else (D, U) if mode == 'high-span' else (D, p.complement(U))
                touch((dst, src), frame)

        def V(bank, mode):
            for j, role in enumerate(g.sources):
                u = line[j]
                frame = high if mode == 'high' else (u, Z) if mode == 'low-span' else (D, u) if mode == 'high-span' else (D, p.complement(u))
                touch((role, bank(j)), frame)

        def J(bank, mode):
            for role, (target, _) in zip(g.reads, g.outputs):
                u = line[target]
                frame = low if mode == 'low' else high if mode == 'high' else (D, u) if mode == 'high-span' else (D, p.complement(u))
                touch((role, bank(target)), frame)

        def bank_rows(bank, mode):
            # These bank touches include the unchanged disjointness gates;
            # disjointness scratch paths are checked separately by symmetry.
            for j, u in enumerate(line):
                frame = high if mode == 'high' else (u, Z) if mode == 'low-span' else (D, u) if mode == 'high-span' else (D, p.complement(u))
                touch((bank(j),), frame)

        def central(bank, frame):
            touch([bank(i) for i in range(v)] + center, frame)

        if stage != 2:
            bank_rows(Y, 'low-span')
            A('low'); J(Y, 'low'); A('low', True)
            central(Y, low)
            bank_rows(X, 'high-span'); V(X, 'high-span'); A('high-span')
            central(X, high); central(Y, low)
            bank_rows(Y, 'high-perp'); J(Y, 'high-perp')
            central(X, high); A('high', True)
            bank_rows(X, 'high'); V(X, 'high')
        else:
            bank_rows(Y, 'low-span'); V(Y, 'low-span'); A('low-span')
            central(Y, low)
            bank_rows(X, 'high-span'); J(X, 'high-span')
            central(X, high); central(Y, low)
            A('high-perp', True)
            bank_rows(Y, 'high-perp'); V(Y, 'high-perp')
            central(X, high)
            A('high'); J(X, 'high'); A('high', True)
            bank_rows(X, 'high')

        for i, u in enumerate(line):
            touch((X(i),), high)
            touch((Y(i),), (D, p.complement(u)))
        touch(range(R), high)
        touch(center, high)
        expected = (R+h)*h*(b+1) + 2*v*(b+1)*(h-1)
        check(signed == expected, 'local terminal dimensions telescope')
        check(drops == Counter(center=h*h), 'only h central wires decrease, by h each')
        check(absolute == expected + 2*h*h, 'absolute dimension sum includes twice the loss')
        rows.append({'stage': stage, 'B_dimension': b, 'wire_edges_checked': touched,
                     'signed_dimension_sum': signed, 'absolute_dimension_sum': absolute,
                     'decreased_dimension_by_role_type': dict(drops)})

    # Unchanged disjointness scratch: the pair (012),(345) represents all pairs
    # by coordinate permutation. Check the actual projector path at all stages.
    tx = p.span([7]); ty = p.span([56])
    disjoint = []
    for stage in (1,2,3):
        b = h**(stage-1)-1
        path = [(Z,Z),(ty,Z),(D,tx),(D,p.complement(ty)),(D,D)]
        total = 0
        for old, new in zip(path, path[1:]):
            active = [(old[1],new[1])] + ([(old[0],new[0])] if b else [])
            check(all(p.included(a,z) for a,z in active),'disjointness path monotonicity')
            ra = p.difference(old[0],new[0]) if b else Z
            rz = p.difference(old[1],new[1])
            dim = b*p.ranks[ra]+p.ranks[rz]
            check(not dim or (b and p.nonalt[ra]) or p.nonalt[rz],'disjointness residual nonalternating')
            total += dim
        check(total == (b+1)*h, 'disjointness scratch local dimension sum')
        disjoint.append({'stage':stage,'dimension_sum':total,'negative_dimension':0})

    return {'h':h,'coverage':'ALL shared-scratch, bank, and reduced-center paths in one full multi-pair invocation per stage; disjointness by coordinate permutation; earlier/future factors by written tensor argument',
            'rows':rows,'disjointness_representative':disjoint,
            'distinct_projector_matrices_checked':len(p.matrices),
            'distinct_residual_projectors_checked':len(p.residuals),'pass':True}


def scalar_word(g: Graph):
    v, h = len(g.triples), g.h
    disjoint = [(i,j) for i,T in enumerate(g.labels) for j,S in enumerate(g.labels) if not (T&S)]
    a0 = 2*v; z0 = a0+len(disjoint); c0 = z0+g.roles; size=c0+h
    ops=[]
    def put(d,s,a=F(1)):
        check(d!=s, 'distinct scalar shear endpoints'); ops.append((d,s,F(a)))
    def A(rev=False):
        for d,s,_ in (reversed(g.gates) if rev else g.gates):put(z0+d,z0+s,-1 if rev else 1)
    def J0(sign):
        for j,(target,source) in enumerate(disjoint):put(v+target,a0+j,F(sign,2))
    def J2(sign):
        for s,(target,node) in zip(g.reads,g.outputs):put(v+target,z0+s,F(-sign,2))
    def V(sign):
        for j,(target,source) in enumerate(disjoint):put(a0+j,source,sign)
        for j,s in enumerate(g.sources):put(z0+s,j,sign)
    def G(sign):
        for i,T in enumerate(g.triples):
            for j in T:put(c0+j,i,sign)
    def R(sign):
        for i,T in enumerate(g.triples):
            for j in range(h):put(v+i,c0+j,sign*(F(int(j in T),2)-F(1,6)))
    J0(-1);A();J2(-1);A(True);R(-1);V(1);A();G(1);R(1);J0(1);J2(1);G(-1);A(True);V(-1)
    swap=lambda k:k+v if k<v else k-v if k<2*v else k
    inv=[(swap(d),swap(s),-a) for d,s,a in reversed(ops)]
    return size,ops,inv


def symbolic_scalar_check(h):
    g=make_graph(h);v=len(g.triples);size,word,inv=scalar_word(g)
    state=[{j:F(1)} for j in range(size)]
    def run(ops):
        for d,s,a in ops:add_sparse(state[d],state[s],a)
    run(word)
    for j,row in enumerate(state):
        expected={j:F(1)}
        if v<=j<2*v:expected[j-v]=F(1)
        check(row==expected,'exact complete forward operator on all inputs AND all dirty scratch')
    run(inv)
    for j,row in enumerate(state):
        expected={v+j:F(-1)} if j<v else {j:F(1),j-v:F(1)} if j<2*v else {j:F(1)}
        check(row==expected,'exact complete middle word after first stage')
    run(word)
    for j,row in enumerate(state):
        expected={v+j:F(-1)} if j<v else {j-v:F(1)} if j<2*v else {j:F(1)}
        check(row==expected,'full signed bank exchange and arbitrary scratch restoration')
    return {'h':h,'registers':size,'forward_elementary_shears':len(word),
            'coefficient_entries_covered_per_checkpoint':size**2,
            'exact_operator_checkpoints':3,'random_sampling':False,'pass':True}


def scalar_rank_obstruction():
    # G G^t = ((h-2)(h-3)/2) I + (h-2) J; both eigenvalues positive.
    # R'G = G^t ((1/2)I-(1/18)J) G. Middle factor singular only at h=9.
    records=[]
    for h in (24,25):
        a=F((h-2)*(h-3),2);b=F(h-2)
        check(a>0 and a+h*b>0,'incidence G has full row rank over Q')
        check(F(1,2)-F(h,18)!=0,'middle factor invertible')
        records.append({'h':h,'central_matrix_rank':h,'incidence_gram_eigenvalues':[str(a),str(a+h*b)],
                        'central_middle_eigenvalues':['1/2',str(F(1,2)-F(h,18))]})
    return records


def negative_controls():
    # 1. Complete leave-one-out family at odd h: forbidden alternating residual.
    P=Projectors(25)
    full_pair=P.span([3|(1<<j) for j in range(2,25)])
    complement=P.complement(full_pair)
    check(P.ranks[complement]==2 and not P.nonalt[complement], 'negative control: unsplit odd-h residual must fail')
    # 2. Blindly reverse a strictly growing support label.
    one=P.span([7]); two=P.span([7,11])
    check(P.included(one,two) and not P.included(two,one), 'negative control: reversed labels must consume loss')
    # 3. Wrong central coefficient and uncorrected dirty scratch.
    wrong=[F(j,2)-F(3,3)+(F(1,2) if j==0 else -F(1,2) if j==2 else 0) for j in range(4)]
    check(wrong!=[0,0,0,1], 'negative control: incorrect central coefficient rejected')
    g=make_graph(7)
    # Choose dirty scratch in a readout role; omit the compensating pass.
    dirty=[0]*g.roles; dirty[g.reads[0]]=1
    for d,s,_ in g.gates:dirty[d]+=dirty[s]
    leaked=[0]*len(g.triples)
    for role,(target,_) in zip(g.reads,g.outputs):leaked[target]+=dirty[role]
    check(any(leaked), 'negative control: a lone dirty replay leaks scratch')
    return {'unsplit_h25_residual_dimension':2,'unsplit_h25_residual_is_alternating':True,
            'blind_reversed_labels_decrease':True,'wrong_center_coefficient_rejected':True,
            'missing_dirty_compensation_rejected':True}


def log_bounds(x: F, terms=80):
    """Independent rational enclosure: direct series after power-of-two reduction."""
    check(x>=1,'log input >= 1')
    k=0
    while x>=2:x/=2;k+=1
    def part(y):
        z=(y-1)/(y+1);t=z;s=F(0)
        for i in range(terms):s+=2*t/(2*i+1);t*=z*z
        return s,s+2*t/((2*terms+1)*(1-z*z))
    a,b=part(x);c,d=part(F(2))
    return a+k*c,b+k*d


def arithmetic_and_batching():
    h=24;v=comb(h,3);m=h**3;N=v**3;I=3*v*v;loss=I*h*h;Delta=2*(N-loss)
    variants=[]
    for shared,padded,witness in [(False,True,F(52,10**11)),(False,False,F(53,10**11)),(True,False,F(55,10**11))]:
        R2=comb(h,2)*(4*h-14) if shared else v*3*(h-3)
        W=2*N+I*(v*comb(h-3,3)+R2+h)
        width=1<<(W-1).bit_length() if padded else W
        epsilon=F(Delta,m*width)
        x=F(477,50)
        exp_lower=sum((x**j/F(factorial(j)) for j in range(41)), F(0))
        check(exp_lower>m,'exact proof log(m)<9.54')
        check(epsilon>witness*x,'exact exponent witness')
        nl,nu=log_bounds(1/(1-epsilon),20);dl,du=log_bounds(F(m),80)
        lo,hi=nl/du,nu/dl
        check(lo>witness,'independent logarithm enclosure exceeds witness')
        variants.append({'shared':shared,'padded':padded,'W':W,'effective_width':width,'m':m,'Delta':Delta,
                         's':W*m-Delta,'epsilon':str(epsilon),'delta_witness':str(witness),
                         'a_rational_lower':str(lo),'a_rational_upper':str(hi)})
    # Exercise actual floor/remainder arithmetic across small toy batch sizes.
    # These are accounting tests, not assertions that these toy interfaces exist.
    cases=0
    for W in range(2,30):
        for m0 in range(2,9):
            for k in range(m0,100):
                f=k//m0;Fcount=1<<(k-f);q,r=divmod(Fcount,W)
                check(q*W+r==Fcount and 0<=r<W,'all fibers accounted for exactly once')
                check(F(q,Fcount)<=F(1,W),'full-batch coefficient upper bound')
                check(f<=(1<<((m0-1)*f)),'normalized remainder bounded')
                cases+=1
    return {'variants':variants,'batching_integer_cases_checked':cases}


def main():
    start=time.time()
    result={'scope':'Same-assistant second implementation and written proof audit. No independent referee and no Lean proof.', 'source_imports':'standard library only'}
    result['negative_controls']=negative_controls()
    print('PASS negative controls', flush=True)
    result['arithmetic']=arithmetic_and_batching()
    result['central_rank_lower_bound']=scalar_rank_obstruction()
    print('PASS exact constants, exponent bounds, batching accounting, central rank bound',flush=True)
    result['symbolic_scalar_operators']=[symbolic_scalar_check(h) for h in (7,8)]
    print('PASS full symbolic scalar operators at h=7,8',flush=True)
    result['graphs']=[]
    for h in (24,25):
        g=make_graph(h)
        out={'coefficients':coefficient_check(g),'frames':full_shared_frame_check(g)}
        result['graphs'].append(out)
        print('PASS full multi-pair graph coefficients and projector-based frame paths at h='+str(h),flush=True)
    result['wall_seconds']=round(time.time()-start,3)
    result['script_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    result['not_proved_by_this_program']=['upstream exact-width compiler and all-length theorem',
        'asymptotic recurrence theorem','all enormous tensor-space frames by enumeration',
        'publication priority','human/independent review','practical speedup']
    destination=Path(__file__).with_name('clean_room_certificate.json')
    destination.write_text(json.dumps(result,indent=2)+'\n')
    print('ALL CHECKS PASSED. Certificate:',destination,'seconds:',result['wall_seconds'])

if __name__=='__main__':main()
