#!/usr/bin/env python3
"""Construct and check an intersection-two correction circuit.

Verified: exact linear map, reversible role compiler, arbitrary dirty-scratch
restoration, and specified local binary-label residual conditions.
NOT verified: full phase-frame schedule/rank loss or transfer to OpenAI #130.
Python 3.10+; standard library only.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import random
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations
from math import comb
from pathlib import Path


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def bits(mask: int):
    while mask:
        lowest = mask & -mask
        yield lowest.bit_length()-1
        mask ^= lowest


def dot(a: int, b: int) -> int:
    return (a & b).bit_count() & 1


def nullspace(rows: list[int], n: int) -> list[int]:
    pivots: dict[int,int] = {}
    for row in rows:
        r = row
        while r:
            p = r.bit_length()-1
            if p in pivots:
                r ^= pivots[p]
            else:
                pivots[p] = r
                break
    answer = []
    for f in range(n):
        if f in pivots:
            continue
        x = 1 << f
        for p in sorted(pivots):
            if dot(x,pivots[p]):
                x ^= 1 << p
        require(all(dot(x,r)==0 for r in rows), 'nullspace equation')
        answer.append(x)
    return answer


def orthonormalize(vectors: list[int]) -> list[int]:
    """Exact F2 diagonalization, including line + alternating-plane conversion."""
    todo = vectors[:]
    out: list[int] = []
    while todo:
        pivot = next((i for i,v in enumerate(todo) if dot(v,v)), None)
        if pivot is not None:
            u = todo.pop(pivot)
            todo = [w ^ (u if dot(w,u) else 0) for w in todo]
            out.append(u)
            continue
        if not out:
            raise ValueError('alternating form: no orthonormal basis')
        u = todo.pop()
        j = next((j for j,v in enumerate(todo) if dot(u,v)), None)
        if j is None:
            raise ValueError('degenerate form')
        v = todo.pop(j)
        todo = [w ^ (u if dot(w,v) else 0) ^ (v if dot(w,u) else 0)
                for w in todo]
        b = out.pop()
        out.extend([b^u, b^v, b^u^v])
    require(len(out)==len(vectors), 'orthonormal dimension')
    require(all(dot(u,v)==int(i==j) for i,u in enumerate(out) for j,v in enumerate(out)),
            'orthonormal Gram matrix')
    return out


@dataclass
class Node:
    support: int
    children: tuple[int,int] | None = None
    pair: tuple[int,int] | None = None


@dataclass
class Injection:
    target: int
    node: int
    pair: tuple[int,int]


class Circuit:
    def __init__(self, h: int):
        if h < 7:
            raise ValueError('h must be >= 7')
        self.h = h
        self.triples = list(combinations(range(h),3))
        self.index = {t:i for i,t in enumerate(self.triples)}
        self.labels = [sum(1<<j for j in t) for t in self.triples]
        self.nodes = [Node(1<<i) for i in range(len(self.triples))]
        self.injections: list[Injection] = []
        n = h-2
        for pair in combinations(range(h),2):
            variables = [j for j in range(h) if j not in pair]
            ids = [self.index[tuple(sorted((*pair,j)))] for j in variables]
            prefix={0:ids[0]}
            for k in range(1,n-2):
                prefix[k] = self.add(prefix[k-1],ids[k],pair)
            suffix={n-1:ids[n-1]}
            for k in range(n-2,1,-1):
                suffix[k] = self.add(ids[k],suffix[k+1],pair)
            for k,target in enumerate(ids):
                if k==0:
                    outputs=(ids[1],suffix[2])
                elif k==n-1:
                    outputs=(prefix[n-3],ids[n-2])
                else:
                    outputs=(prefix[k-1],suffix[k+1])
                for node in outputs:
                    self.injections.append(Injection(target,node,pair))

    def add(self,a:int,b:int,pair:tuple[int,int]) -> int:
        require(self.nodes[a].support & self.nodes[b].support == 0, 'disjoint input supports')
        support=self.nodes[a].support | self.nodes[b].support
        require(support.bit_count() <= self.h-4, 'partial support leaves two third coordinates unused')
        self.nodes.append(Node(support,(a,b),pair))
        return len(self.nodes)-1

    @property
    def addition_count(self) -> int:
        return len(self.nodes)-len(self.triples)

    def verify_supports(self) -> list[int]:
        actual=[0]*len(self.triples)
        for inj in self.injections:
            support=self.nodes[inj.node].support
            require(support.bit_count() <= self.h-4, 'injection support-size bound')
            require(actual[inj.target] & support == 0, 'no duplicate target coefficients')
            actual[inj.target] |= support
            union_labels=0
            for i in bits(support):
                require(set(inj.pair).issubset(self.triples[i]), 'fixed-pair source')
                require(dot(self.labels[i],self.labels[inj.target])==0, 'source-target label orthogonality')
                union_labels |= self.labels[i]
            spare=((1<<self.h)-1) & ~(union_labels | self.labels[inj.target])
            require(spare != 0, 'terminal residual has a spare norm-one coordinate')
        expected=[]
        for target in self.labels:
            e=0
            for i,source in enumerate(self.labels):
                if (source & target).bit_count()==2:
                    e |= 1<<i
            expected.append(e)
        require(actual==expected, 'all coefficients of H2 exactly verified')
        require(all(mask.bit_count()==3*(self.h-3) for mask in actual), 'row degree')
        require(self.addition_count==comb(self.h,2)*(2*self.h-10), 'addition formula')
        require(len(self.injections)==comb(self.h,2)*2*(self.h-2), 'partial-output formula')
        return expected

    def compile(self) -> tuple[int,list[tuple[int,int]],list[int],list[int]]:
        """Compile to reversible additions using one role per edge minus pivots."""
        n_inputs=len(self.triples)
        outgoing=[[] for _ in self.nodes]
        incoming={}
        edge_count=0
        for node_id,node in enumerate(self.nodes):
            if node.children is None:
                continue
            pair=[]
            for child in node.children:
                outgoing[child].append(edge_count)
                pair.append(edge_count)
                edge_count+=1
            incoming[node_id]=tuple(pair)
        output_edges=[]
        for inj in self.injections:
            outgoing[inj.node].append(edge_count)
            output_edges.append(edge_count)
            edge_count+=1
        parent=list(range(edge_count))
        def root(i:int) -> int:
            while parent[i]!=i:
                parent[i]=parent[parent[i]]
                i=parent[i]
            return i
        for node_id,(first,second) in incoming.items():
            require(bool(outgoing[node_id]), 'all addition nodes used')
            a,b=root(first),root(outgoing[node_id][0])
            require(a!=b, 'pivot identification reduces roles by one')
            parent[b]=a
        roots=sorted({root(i) for i in range(edge_count)})
        ids={r:i for i,r in enumerate(roots)}
        slot=[ids[root(i)] for i in range(edge_count)]
        gates=[]
        source_slots=[]
        for i in range(n_inputs):
            pivot=slot[outgoing[i][0]]
            source_slots.append(pivot)
            for edge in outgoing[i][1:]:
                gates.append((slot[edge],pivot))
        for i in range(n_inputs,len(self.nodes)):
            first,second=incoming[i]
            pivot=slot[first]
            require(pivot==slot[outgoing[i][0]], 'addition output pivot')
            gates.append((pivot,slot[second]))
            for edge in outgoing[i][1:]:
                gates.append((slot[edge],pivot))
        require(all(a!=b for a,b in gates), 'all elementary additions invertible')
        require(len(set(source_slots))==n_inputs, 'distinct input pivots')
        n_roles=len(roots)
        require(n_roles==self.addition_count+len(self.injections), 'c+q role formula')
        # Propagate every coefficient exactly. OR is used only after checking
        # coefficient supports are disjoint, so it equals ordinary integer addition.
        values=[0]*n_roles
        for i,s in enumerate(source_slots):
            values[s]=1<<i
        for dest,src in gates:
            require(values[dest]&values[src]==0, 'compiler delta additions remain disjoint')
            values[dest] |= values[src]
        out_slots=[slot[e] for e in output_edges]
        require(all(values[s]==self.nodes[inj.node].support
                    for s,inj in zip(out_slots,self.injections)), 'compiled exact outputs')
        return n_roles,gates,source_slots,out_slots

    def verify_dirty(self, compiled, expected:list[int], trials:int=3) -> None:
        n_roles,gates,source_slots,out_slots=compiled
        rng=random.Random(1302026)
        def run_L(z:list[int], inverse:bool=False) -> None:
            if inverse:
                for dest,src in reversed(gates):
                    z[dest]-=z[src]
            else:
                for dest,src in gates:
                    z[dest]+=z[src]
        for trial in range(trials):
            x=[rng.randrange(-1000,1001) for _ in self.triples]
            z0=[rng.randrange(-1000,1001) for _ in range(n_roles)]
            y0=[rng.randrange(-1000,1001) for _ in self.triples]
            z,y=z0[:],y0[:]
            # y represents twice the scalar output; alpha=-1 means coefficient -1/2.
            alpha=(-1,3,-7)[trial%3]
            run_L(z)
            for slot,inj in zip(out_slots,self.injections):
                y[inj.target]-=alpha*z[slot]
            run_L(z,True)
            for s,value in zip(source_slots,x):
                z[s]+=value
            run_L(z)
            for slot,inj in zip(out_slots,self.injections):
                y[inj.target]+=alpha*z[slot]
            run_L(z,True)
            for s,value in zip(source_slots,x):
                z[s]-=value
            desired=[old+alpha*sum(x[j] for j in bits(mask))
                     for old,mask in zip(y0,expected)]
            require(z==z0, 'arbitrary dirty scratch restored')
            require(y==desired, 'dirty-scratch output identity')


def verify_binary_residuals(h:int) -> dict:
    all_bases=[]
    pairmask=3
    for k in range(1,h-3):
        labels=[pairmask|(1<<a) for a in range(2,k+2)]
        target=pairmask|(1<<(k+2))
        require(all(dot(a,b)==int(i==j) for i,a in enumerate(labels) for j,b in enumerate(labels)),
                'fixed-pair labels are orthonormal')
        complement=orthonormalize(nullspace(labels,h))
        residual=orthonormalize(nullspace(labels+[target],h))
        require(len(complement)==h-k and len(residual)==h-k-1, 'residual dimensions')
        all_bases.append({'k':k,'U_perp_basis':complement,'terminal_residual_basis':residual})
    # The naive unsplit full leave-one-out output fails at odd h.
    labels=[pairmask|(1<<a) for a in range(2,h-1)]
    target=pairmask|(1<<(h-1))
    naive=nullspace(labels+[target],h)
    alternating=all(dot(v,v)==0 for v in naive)
    require(alternating==(h%2==1), 'parity obstruction for full leave-one-out output')
    return {'local_residual_cases':len(all_bases),
            'explicit_binary_bases':all_bases,
            'naive_full_output_alternating':alternating,
            'naive_full_output_residual_basis':naive}


def audit(h:int=25) -> dict:
    circuit=Circuit(h)
    expected=circuit.verify_supports()
    compiled=circuit.compile()
    circuit.verify_dirty(compiled,expected)
    binary=verify_binary_residuals(h)
    for j in range(4):
        center=Fraction(j-1,2)
        correction=Fraction(1,2) if j==0 else Fraction(-1,2) if j==2 else 0
        require(center+correction==int(j==3), 'intersection coefficient identity')
    n_roles,gates,source_slots,out_slots=compiled
    digest=hashlib.sha256()
    for node in circuit.nodes:
        digest.update(str((node.children,node.pair,node.support)).encode())
    for inj in circuit.injections:
        digest.update(str((inj.target,inj.node,inj.pair)).encode())
    return {
        'status':'LOCAL CIRCUIT AND LABEL CHECKS ONLY; NOT AN IMPROVED FOURIER THEOREM',
        'h':h,'inputs':len(circuit.triples),'additions':circuit.addition_count,
        'partial_output_injections':len(circuit.injections),
        'reversible_roles':n_roles,'reversible_L_elementary_gates':len(gates),
        'original_dedicated_intersection_two_roles':comb(h,3)*3*(h-3),
        'exact_nonzero_coefficients_verified':sum(x.bit_count() for x in expected),
        'all_other_coefficients_verified_zero':True,
        'dirty_scratch_integer_trials':3,
        'dirty_scratch_general_argument':'L^-1 L z = z; net injection alpha J L (z+Vx) - alpha J L z = alpha J L Vx.',
        'binary_residuals':binary,
        'deterministic_construction_sha256':digest.hexdigest(),
        'proof_boundary':['Local label properties do not alone establish the global phase-frame telescoping schedule.',
                          'Unchanged total loss L remains an integration obligation.',
                          'No DFT all-length exponent follows from this verifier alone.']}


def main() -> None:
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--h',type=int,default=25)
    p.add_argument('--output',type=Path,default=Path(__file__).with_name('circuit_certificate.json'))
    args=p.parse_args()
    result=audit(args.h)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    for k in ['status','h','inputs','additions','partial_output_injections','reversible_roles',
              'reversible_L_elementary_gates','exact_nonzero_coefficients_verified']:
        print(f'{k}: {result[k]}')
    print('Naive unsplit-output obstruction:',result['binary_residuals']['naive_full_output_alternating'])
    print('PASS: exact coefficients, role compiler, dirty scratch, and local binary residuals.')
    print('Certificate:',args.output)
if __name__=='__main__':
    main()
