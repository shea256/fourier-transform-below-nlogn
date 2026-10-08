#!/usr/bin/env python3
"""Exact checks for the October 8 #130 extension.

Checks finite identities, compiler traces, representative binary-frame schedules,
and rational numerical certificates. The asymptotic theorem uses the WRITTEN
proof in PROOF.md and the uploaded OpenAI manuscript; this is not a Lean proof
or an independent verification of that manuscript.
"""
from __future__ import annotations
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations
from math import comb
from pathlib import Path
from types import SimpleNamespace
import json

from local_circuit import Circuit, Node, Injection, bits, dot, nullspace, orthonormalize, require, verify_binary_residuals
from rational_bounds import saving_bounds, decimal, frac_json, log_bounds


def tagged_compile(c):
    """Same role construction as prior compiler, with support of each gate tagged."""
    ni=len(c.triples); outgoing=[[] for _ in c.nodes]; incoming={}; edges=0
    for i,node in enumerate(c.nodes):
        if node.children is None: continue
        ins=[]
        for child in node.children:
            outgoing[child].append(edges); ins.append(edges); edges+=1
        incoming[i]=ins
    oe=[]
    for inj in c.injections:
        outgoing[inj.node].append(edges); oe.append(edges); edges+=1
    parent=list(range(edges))
    def root(i):
        while parent[i]!=i:
            parent[i]=parent[parent[i]]; i=parent[i]
        return i
    for i,ins in incoming.items():
        require(bool(outgoing[i]),'used addition')
        a,b=root(ins[0]),root(outgoing[i][0]); require(a!=b,'distinct pivots');parent[b]=a
    roots=sorted({root(i) for i in range(edges)}); ids={v:i for i,v in enumerate(roots)}
    slot=[ids[root(i)] for i in range(edges)]; gates=[]; sources=[]
    for i in range(ni):
        p=slot[outgoing[i][0]]; sources.append(p)
        for edge in outgoing[i][1:]: gates.append((slot[edge],p,c.nodes[i].support))
    for i in range(ni,len(c.nodes)):
        a,b=incoming[i]; p=slot[a]
        require(p==slot[outgoing[i][0]],'pivot')
        gates.append((p,slot[b],c.nodes[i].support))
        for edge in outgoing[i][1:]: gates.append((slot[edge],p,c.nodes[i].support))
    return len(roots),gates,sources,[slot[e] for e in oe]


def support_trace(c, compiled):
    R,gates,sources,outputs=compiled; state=[0]*R
    for i,s in enumerate(sources):
        require(state[s]==0,'distinct source pivots'); state[s]=1<<i
    for dst,src,U in gates:
        require(dst!=src,'invertible elementary addition')
        require(state[dst]&~U==0 and state[src]&~U==0,'forward support labels nested')
        state[dst]=state[src]=U
    require(len(set(outputs))==len(outputs),'one physical readout per output role')
    require(all(state[s]==c.nodes[inj.node].support for s,inj in zip(outputs,c.injections)), 'readout role final label matches its support')
    # Every growing label is a span of a subset of one orthonormal pair family.
    for node in c.nodes:
        ids=list(bits(node.support))
        labs=[c.labels[i] for i in ids]
        require(all(dot(a,b)==int(i==j) for i,a in enumerate(labs) for j,b in enumerate(labs)), 'gate support is orthonormal')
        require(len(ids)<=c.h-4, 'gate support has spare coordinates')
    return {'roles':R,'tagged_L_gates':len(gates),'readout_roles':len(outputs),'all_role_support_paths_nondecreasing':True,'all_readout_roles_distinct':True}


def one_pair(h):
    """A canonical pair suffices for binary frame checks by coordinate permutation.
    Global fan-out across pair groups is separately checked by support_trace.
    """
    r=h-2
    c=SimpleNamespace(h=h,triples=[(0,1,i+2) for i in range(r)],labels=[3|(1<<(i+2)) for i in range(r)],nodes=[Node(1<<i) for i in range(r)],injections=[])
    def add(a,b):
        c.nodes.append(Node(c.nodes[a].support|c.nodes[b].support,(a,b),(0,1)));return len(c.nodes)-1
    pref={0:0}; suff={r-1:r-1}
    for i in range(1,r-2):pref[i]=add(pref[i-1],i)
    for i in range(r-2,1,-1):suff[i]=add(i,suff[i+1])
    for t in range(r):
        out=(1,suff[2]) if t==0 else (pref[r-3],r-2) if t==r-1 else (pref[t-1],suff[t+1])
        for n in out:c.injections.append(Injection(t,n,(0,1)))
    return c


def frame_check(h, stage, inverse=False):
    """Explicit finite F2 checks on every edge of the canonical pair schedule.
    A label (A,Z) denotes (B tensor A) orthogonal-sum (P tensor Z),
    then tensor the common norm-one future line Q. dim(B)=h^(stage-1)-1.
    """
    c=one_pair(h); R,gates,sources,outputs=tagged_compile(c); n=len(c.triples); bdim=h**(stage-1)-1
    ZERO=(False,0); FULL=(True,0)
    span=lambda mask:(False,mask)
    perp=lambda mask:(True,mask)
    @lru_cache(None)
    def basis(s):
        co,mask=s; v=[c.labels[i] for i in bits(mask)]
        return tuple(nullspace(v,h) if co else v)
    def rank(vs):
        piv={}
        for v in vs:
            while v:
                p=v.bit_length()-1
                if p in piv:v^=piv[p]
                else:piv[p]=v;break
        return len(piv)
    @lru_cache(None)
    def residual(a,z):
        A=basis(a); Z=basis(z)
        # Z and A are nondegenerate, verified independently, not assumed.
        for vs in (A,Z):
            gram=[sum(dot(u,v)<<j for j,v in enumerate(vs)) for u in vs]
            require(rank(gram)==len(vs),'label nondegenerate')
        require(rank(list(Z)+list(A))==len(Z),'actual F2 inclusion')
        equations=[sum(dot(u,v)<<j for j,v in enumerate(Z)) for u in A]
        coords=nullspace(equations,len(Z)); res=[]
        for mask in coords:
            v=0
            for i in bits(mask):v^=Z[i]
            res.append(v)
        require(len(res)==len(Z)-len(A),'residual dimension')
        gram=[sum(dot(u,v)<<j for j,v in enumerate(res)) for u in res]
        require(rank(gram)==len(res),'residual nondegenerate')
        nonalt=any(dot(v,v) for v in res)
        if nonalt:
            on=orthonormalize(res)
            require(len(on)==len(res),'residual explicit orthonormal basis')
        return len(res),nonalt
    states=[(ZERO,ZERO)]*R+[(span(1<<i),span(1<<i)) for i in range(n)]+[(span(1<<i),ZERO) for i in range(n)]
    X=lambda i:R+i
    Y=lambda i:R+n+i
    edge_count=0; total=0
    def touch(wires,label):
        nonlocal edge_count,total
        for s in wires:
            old=states[s]; dB,nB=residual(old[0],label[0]);dP,nP=residual(old[1],label[1])
            dim=bdim*dB+dP
            require(not dim or (bdim>0 and dB>0 and nB) or (dP>0 and nP),'full residual has an orthonormal basis')
            states[s]=label;edge_count+=1;total+=dim
    low=(FULL,ZERO);full=(FULL,FULL)
    def L(mode,reverse=False):
        for dst,src,S in (reversed(gates) if reverse else gates):
            lab={'low':low,'full':full}.get(mode)
            if mode=='span_low':lab=(span(S),ZERO)
            if mode=='span_high':lab=(FULL,span(S))
            if mode=='perp_high':lab=(FULL,perp(S))
            touch([dst,src],lab)
    def V(bank,kind):
        for i,s in enumerate(sources):
            label=full if kind=='full' else (span(1<<i),ZERO) if kind=='span_low' else (FULL,span(1<<i)) if kind=='span_high' else (FULL,perp(1<<i))
            touch([s,bank(i)],label)
    def J(bank,kind):
        for s,inj in zip(outputs,c.injections):
            t=inj.target
            label=full if kind=='full' else low if kind=='low' else (FULL,span(1<<t)) if kind=='span_high' else (FULL,perp(1<<t))
            touch([s,bank(t)],label)
    if not inverse:
        L('low');J(Y,'low');L('low',True)
        touch([Y(i) for i in range(n)],low) # center's negative target update
        V(X,'span_high');L('span_high')
        touch([X(i) for i in range(n)],full)
        touch([Y(i) for i in range(n)],low)
        J(Y,'perp_high')
        touch([X(i) for i in range(n)],full)
        L('full',True);V(X,'full')
    else:
        V(Y,'span_low');L('span_low')
        touch([Y(i) for i in range(n)],low)
        J(X,'span_high')
        touch([X(i) for i in range(n)],full)
        touch([Y(i) for i in range(n)],low)
        L('perp_high',True);V(Y,'perp_high')
        touch([X(i) for i in range(n)],full)
        L('full');J(X,'full');L('full',True)
    for i in range(n):
        touch([X(i)],full);touch([Y(i)],(FULL,perp(1<<i)))
    for s in range(R):touch([s],full)
    expected=(R*h+2*n*(h-1))*(bdim+1)
    require(total==expected,'all canonical internal/boundary dimensional changes telescope with zero decreases')
    # Extension to the full future space at auxiliary sinks is unchanged from upstream.
    return dict(h=h,stage=stage,orientation='inverse_source_Y' if inverse else 'forward_source_X',B_dimension=bdim,canonical_pair_roles=R,wire_edges_checked=edge_count,residual_dimension_sum=total,negative_dimension_changes=0,distinct_component_transitions=residual.cache_info().currsize)


def network_counts(h,center_reduced,shared,padded):
    v=comb(h,3); m=h**3; N=v**3; I=3*v*v; centers=h if center_reduced else h+1
    R2=comb(h,2)*(4*h-14) if shared else 3*v*(h-3)
    W=2*N+I*(v*comb(h-3,3)+R2+centers)
    loss=I*centers*h; Delta=2*(N-loss)
    width=(1<<(W-1).bit_length()) if padded else W
    eps=F(Delta,m*width);lo,hi=saving_bounds({'m':m,'eta':eps})
    return dict(h=h,v=v,m=m,N=N,I=I,centers_per_invocation=centers,R2=R2,W=W,effective_width=width,loss=loss,Delta=Delta,s=W*m-Delta,epsilon=eps,a_lower=lo,a_upper=hi)


def check_centers():
    # The new central matrix coefficient is (j - 3/3)/2, without c_*.
    for h in (7,21,24,25,100):
        for T in combinations(range(h),3):
            require(F(sum(int(j in T) for j in range(h)),3)==1,'every input counted three times')
        for j in range(4):
            central=F(j,2)-F(3,6)
            side=F(1,2) if j==0 else -F(1,2) if j==2 else F(0)
            require(central+side==int(j==3),'center plus correction equals identity')
    # Formal block cancellation proves restoration for arbitrary initial center data.
    return {'h_values':[7,21,24,25,100],'coefficient_identity_for_all_four_intersections':True,'arbitrary_scratch_proof':'-Rc + R(c+Gx)=RGx; final center is c+Gx-Gx=c'}


def scalar_schedule_check(h):
    """Execute the entire modified local scalar word and its reversed middle word."""
    import random
    c=Circuit(h); R,gates,sources,outputs=c.compile(); n=len(c.triples)
    pairs=[(i,j) for i,T in enumerate(c.labels) for j,S in enumerate(c.labels) if not (T&S)]
    side0=2*n; z0=side0+len(pairs); center0=z0+R; size=center0+h
    X=lambda i:i
    Y=lambda i:n+i
    op=[]
    def shear(dst,src,alpha=F(1)):
        require(dst!=src,'scalar shear distinct registers');op.append((dst,src,F(alpha)))
    def A(inv=False):
        for d,t in (reversed(gates) if inv else gates):shear(z0+d,z0+t,-1 if inv else 1)
    def J0(sign):
        for j,(target,source) in enumerate(pairs):shear(Y(target),side0+j,F(sign,2))
    def J2(sign):
        for slot,inj in zip(outputs,c.injections):shear(Y(inj.target),z0+slot,F(-sign,2))
    def V(sign):
        for j,(target,source) in enumerate(pairs):shear(side0+j,X(source),sign)
        for i,slot in enumerate(sources):shear(z0+slot,X(i),sign)
    def RG(kind,sign):
        for i,T in enumerate(c.triples):
            if kind=='R':
                for j in range(h):shear(Y(i),center0+j,sign*(F(int(j in T),2)-F(1,6)))
            else:
                for j in T:shear(center0+j,X(i),sign)
    J0(-1);A();J2(-1);A(True);RG('R',-1);V(1);A();RG('G',1)
    RG('R',1);J0(1);J2(1);RG('G',-1);A(True);V(-1)
    def swapped(i):return i+n if i<n else i-n if i<2*n else i
    mid=[(swapped(d),swapped(t),-a) for d,t,a in reversed(op)]
    def execute(arr,word):
        for d,t,a in word:arr[d]+=a*arr[t]
    rng=random.Random(130000+h)
    for trial in range(3):
        original=[F(rng.randrange(-10,11),rng.randrange(1,5)) for _ in range(size)]
        a=original[:];execute(a,op)
        require(a[:n]==original[:n],'forward source unchanged')
        require(a[n:2*n]==[original[n+i]+original[i] for i in range(n)],'forward full scalar shear')
        require(a[2*n:]==original[2*n:],'full scalar dirty-scratch restoration')
        b=original[:];execute(b,mid)
        require(b[:n]==[original[i]-original[n+i] for i in range(n)],'middle reversed scalar shear')
        require(b[n:]==original[n:],'middle preserves Y and all dirty scratch')
        execute(a,mid);execute(a,op)
        require(a[:n]==[-original[n+i] for i in range(n)] and a[n:2*n]==original[:n], 'three local bank shears give signed exchange')
        require(a[2*n:]==original[2*n:],'signed exchange restores all scratch')
    return dict(h=h,scalar_registers=size,forward_elementary_shears=len(op),rational_dirty_trials=3,forward_inverse_and_signed_exchange_pass=True)


def jsonable(x):
    if isinstance(x,F):return frac_json(x)
    if isinstance(x,dict):return {k:jsonable(v) for k,v in x.items()}
    if isinstance(x,list):return [jsonable(v) for v in x]
    return x


def main():
    records=[]
    for h,cr,sh,pad,label in [(100,False,False,True,'uploaded-paper'),(24,False,False,True,'retune-only'),(24,True,False,True,'reduced-center-padded'),(24,True,False,False,'reduced-center-unpadded'),(24,True,True,False,'shared-center-unpadded')]:
        c=network_counts(h,cr,sh,pad);c['label']=label
        c['a_decimal']=[decimal(c['a_lower']),decimal(c['a_upper'])];records.append(c)
        print(label, 'a in',c['a_decimal'],'W',c['W'],'Delta',c['Delta'])
    require(records[0]['W']==1873807244643542670000,'original W')
    require(records[0]['Delta']==6871402692000000,'original Delta')
    require(records[2]['a_lower']>F(52,10**11),'5.2e-10 padded theorem witness')
    require(records[3]['a_lower']>F(53,10**11),'5.3e-10 ragged theorem witness')
    require(records[4]['a_lower']>F(55,10**11),'5.5e-10 shared theorem witness')
    # Elementary alternative: exp(9.54)>13824 by a positive finite sum.
    x=F(477,50);term=F(1);summ=term
    for j in range(1,41):term*=x/j;summ+=term
    require(summ>24**3,'ln(13824)<9.54 exact positive-series certificate')
    for idx,w in ((2,F(52,10**11)),(3,F(53,10**11)),(4,F(55,10**11))):
        require(records[idx]['epsilon']>w*x,'epsilon exceeds delta times certified log upper bound')
    print('PASS: original counts, center identity, three exponent witnesses; no floating point comparisons.')
    traces=[]
    for h in (24,25):
        c=Circuit(h);expected=c.verify_supports();original=c.compile();tagged=tagged_compile(c)
        require(original==(tagged[0],[(d,s) for d,s,_ in tagged[1]],tagged[2],tagged[3]),'tagged compiler matches prior independently run compiler')
        c.verify_dirty(original,expected)
        traces.append(dict(h=h,**support_trace(c,tagged)))
        verify_binary_residuals(h)
        print('PASS: full local coefficient matrix, dirty replay, global role support trace at h=',h)
    frames=[frame_check(h,j,j==2) for h in (24,25) for j in (1,2,3)]
    print('PASS: all canonical frame edges for stages 1,2,3 at h=24,25, with explicit F2 residual checks.')
    # Validate elementary bound used for direct remainders (general proof in note).
    for m in (2,3,24**3):
        for f in range(1,80):
            require(f<=2**((m-1)*f),'f*2^(-(m-1)f)<=1')
    scalar_checks=[scalar_schedule_check(h) for h in (7,8)]
    print('PASS: full reduced-center + shared-sum scalar word, reversed middle word, and signed bank exchange on rational dirty inputs at h=7,8.')
    results=dict(scalar_schedule_checks=scalar_checks,status='CHECKS SUPPORT THE WRITTEN CANDIDATE EXTENSION; NOT AN INDEPENDENT OR FORMAL PROOF OF THE DFT THEOREM',centers=check_centers(),counts=records,global_support_traces=traces,canonical_frame_checks=frames,explicit_log_certificate={'log_upper':x,'positive_exp_partial_sum_terms':40,'sum':summ},not_claimed=['Independent verification of OpenAI Sections 3-5','Lean formalization of the modifications','Novelty or publication priority','Practical FFT speedup','Global optimality of h=24'])
    path=Path(__file__).with_name('certificate.json');path.write_text(json.dumps(jsonable(results),indent=2)+'\n')
    print('Certificate:',path)
if __name__=='__main__':main()
