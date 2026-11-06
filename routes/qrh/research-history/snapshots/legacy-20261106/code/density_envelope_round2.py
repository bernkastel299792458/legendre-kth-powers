"""Exploratory source-checked density envelopes for the QRH k=4 gap.

Floating-point quadrature, NOT a rigorous numerical certificate. This imports
kernel construction from smooth_scan but never mutates or writes its files.
"""
from __future__ import annotations

import csv
import hashlib
import json
import math
import sys
from datetime import datetime, timezone
from functools import lru_cache
from pathlib import Path

import numpy as np
import scipy
from scipy.optimize import brentq

sys.dont_write_bytecode = True
import smooth_scan as base

ROOT = Path(__file__).resolve().parents[1]
H = 3e12
LOG_H = math.log(H)
LOG_2PI = math.log(2*math.pi)
CS_SOURCE = 'https://arxiv.org/html/2507.15184v2'
BW_SOURCE = 'https://arxiv.org/html/2412.15470v2'
CHO_SOURCE = 'https://arxiv.org/pdf/2412.02068v1'
APPENDIX_ROWS = np.array([
    [2.900,5.027], [3.474,4.789], [4.149,4.536], [4.940,4.296],
    [5.860,4.042], [6.925,3.800], [8.148,3.546], [9.543,3.301],
])
MODES = ('cs2','envelope119','envelope_hcap','envelope_monotone')


def count_error(u):
    """BW v2 Theorem 1.1, minimum of its two valid errors, T=exp(u)>=e."""
    u = np.asarray(u,dtype=float)
    if np.any(u < 1):
        raise ValueError('BW total-count domain T>=e')
    return np.minimum(.10076*u+.24460*np.log(u)+8.08344,
                      .11200*u+.12567*np.log(u)+3.77417)


def local_count_cap(u0,u1):
    """Bounds N(sigma,exp(u1))-N(sigma,exp(u0)) for sigma>1/2.

    Uses (N_upper(T1)-N_lower(T0))/2, never upper-minus-upper.
    Main-term subtraction is evaluated with expm1 to avoid cancellation.
    """
    u0,u1 = np.broadcast_arrays(np.asarray(u0,float),np.asarray(u1,float))
    if np.any(u0 < 1) or np.any(u1 < u0):
        raise ValueError('Require 1<=u0<=u1')
    gap = u1-u0
    pdiff = np.exp(u0)/(2*math.pi)*(np.expm1(gap)*(u0-LOG_2PI-1)
                                               +np.exp(gap)*gap)
    return (pdiff+count_error(u0)+count_error(u1))/2


def cs2_log(sigma,u,left_row=False):
    sigma,u=np.broadcast_arrays(np.asarray(sigma,float),np.asarray(u,float))
    if np.any(sigma < .5) or np.any(sigma > .875) or np.any(u < LOG_H):
        raise ValueError('CS v2 domain: .5<=sigma<=.875,T>=H')
    scaled=32*sigma-16
    row=np.ceil(scaled).astype(int)-1 if left_row else np.floor(scaled).astype(int)
    row=np.clip(row,0,11)
    p=3*(1-sigma)/(2-sigma)
    c=base.CS_V2_C1[row]
    d,e=base.ROWS[row,3],base.ROWS[row,4]
    return np.logaddexp(np.log(c)+p*u+(2+p)*np.log(u),np.log(d*u*u+e*u))


def appendix119_log(sigma,u,left_row=False):
    """Eq119/Table4 valid for .625<=sigma<=.875 and T>=H; inf below."""
    sigma,u=np.broadcast_arrays(np.asarray(sigma,float),np.asarray(u,float))
    if np.any(sigma < .5) or np.any(sigma > .875) or np.any(u < LOG_H):
        raise ValueError('Envelope domain: .5<=sigma<=.875,T>=H')
    scaled=32*sigma-20
    row=np.ceil(scaled).astype(int)-1 if left_row else np.floor(scaled).astype(int)
    row=np.clip(row,0,7)
    A,B=APPENDIX_ROWS[row,0],APPENDIX_ROWS[row,1]
    answer=np.logaddexp(np.log(A)+(8/3)*(1-sigma)*u+(6-4*sigma)*np.log(u),
                       np.log(B)+2*np.log(u))
    return np.where(sigma >= .625,answer,np.inf)


def cho_table_log(sigma,u):
    """Only unambiguous Table1 H rows, extended by sigma monotonicity.

    Source counts beta>sigma; strict thresholds below handle the convention.
    No interpolation or unsupported uniform 0.78 constant is used.
    """
    sigma,u=np.broadcast_arrays(np.asarray(sigma,float),np.asarray(u,float))
    answer=np.full(sigma.shape,np.inf)
    for s,c in ((.60,.7756),(.66,.2781)):
        candidate=math.log(c)+4*s*(1-s)*u+(5-2*s)*np.log(u)
        answer=np.minimum(answer,np.where(sigma>s,candidate,np.inf))
    return answer


def log_density_bound(sigma,u,mode='envelope_monotone'):
    """Reusable vectorized log upper envelope of cumulative N(sigma,e^u).

    sigma and u follow numpy broadcasting. All modes use CS v2 and half-total
    count for sigma>1/2; later modes add Eq119, the finite-RH count cap, and
    valid lower-sigma source endpoints. Cho24 is diagnostic only and is not
    included in any envelope. Requires T>=H. At H only off-line
    counts are set to zero, using the independent finite RH input.
    """
    sigma,u=np.broadcast_arrays(np.asarray(sigma,float),np.asarray(u,float))
    if mode not in MODES:
        raise ValueError('Unknown density mode')
    bound=cs2_log(sigma,u)
    if mode!='cs2':
        bound=np.minimum(bound,appendix119_log(sigma,u))
    if mode=='envelope_monotone':
        for i in range(17,28):
            s=i/32
            endpoint=np.minimum(cs2_log(s,u,left_row=True),
                                appendix119_log(s,u,left_row=True))
            bound=np.minimum(bound,np.where(sigma>=s,endpoint,np.inf))
    countcap=u+np.log(u)-LOG_2PI-np.where(sigma>.5,math.log(2),0)
    bound=np.minimum(bound,countcap)
    if mode in ('envelope_hcap','envelope_monotone'):
        local=np.log(local_count_cap(LOG_H,u))
        bound=np.minimum(bound,np.where(sigma>.5,local,np.inf))
    return np.where((u==LOG_H)&(sigma>.5),-np.inf,bound)


@lru_cache(maxsize=None)
def sigma_rule(order):
    nodes,weights=base.legendre_rule(order)
    # Split source-row boundaries and the Cho diagnostic thresholds.
    cuts=sorted(set([i/32 for i in range(16,29)]+[.60,.66,.80]))
    sigmas,ws=[],[]
    for lo,hi in zip(cuts[:-1],cuts[1:]):
        sigmas.extend((lo+hi)/2+(hi-lo)/2*nodes)
        ws.extend((hi-lo)/2*weights)
    return np.array(sigmas),np.array(ws)


def cumulative_terms(L,u,mode='envelope_monotone',sigma_order=16):
    u=np.asarray(u,float)
    if np.min(u)<math.log(64):
        raise ValueError('Inherited total-count simplification requires T>=64')
    baseline=np.exp(u+np.log(u)-LOG_2PI-L/2)
    rows=np.zeros((len(u),12))
    selected=u>LOG_H
    if not np.any(selected):
        return baseline,rows
    sigma,weights=sigma_rule(sigma_order)
    s=sigma[None,:]
    v=u[selected,None]
    logbound=log_density_bound(s,v,mode)
    pairfactor=-np.expm1(-(2*s-1)*L)
    integrand=L*np.exp(logbound-(1-s)*L)*pairfactor*weights[None,:]
    for row in range(12):
        mask=(sigma >= (16+row)/32)&(sigma < (17+row)/32)
        rows[selected,row]=np.sum(integrand[:,mask],axis=1)
    return baseline,rows


def smooth_bound(L,M=2,mode='envelope_monotone',height_order=20,
                 sigma_order=16,max_step=1.):
    if not 100<=L<=500:
        raise ValueError('Round2 exploratory range:100<=L<=500')
    kernel=base.make_kernel(M,True)
    logq=np.logaddexp(0.,L/4-math.log(4))
    J=len(kernel.log_R)-1
    U=max(logq+kernel.segments[-1][0]+40,LOG_H+40,
          (kernel.log_R[-1]+J*logq-L/8+60)/(J-1))
    nodes,weights=base.legendre_rule(height_order)
    baseline_sum=0.
    layer_rows=np.zeros(12)
    for wlo,whi,j in kernel.segments:
        lo,hi=logq+wlo,min(logq+whi,U)
        if lo>=hi:
            continue
        special=[LOG_H+d for d in (0,1e-8,1e-6,1e-5,1e-4,.001,.01,.1)]
        split=sorted([lo,hi]+[t for t in special if lo<t<hi])
        for begin,end in zip(split[:-1],split[1:]):
            cuts=np.linspace(begin,end,max(1,math.ceil((end-begin)/max_step))+1)
            centers,half=(cuts[:-1]+cuts[1:])/2,np.diff(cuts)/2
            u=(centers[:,None]+half[:,None]*nodes).ravel()
            wts=(half[:,None]*weights).ravel()
            measure=np.exp(math.log(j)+kernel.log_R[j]+j*(logq-u))
            baseline,rows=cumulative_terms(L,u,mode,sigma_order)
            baseline_sum+=2*float(np.dot(wts,baseline*measure))
            layer_rows+=2*np.sum((wts*measure)[:,None]*rows,axis=0)
    tail=math.exp(math.log(J/math.pi)+kernel.log_R[J]+J*logq-L/8
                  -(J-1)*U+math.log(U/(J-1)+1/(J-1)**2))
    eps=4*math.exp(-L/4)
    logy=L+math.log1p(eps)
    pp=kernel.max_over_mass*math.sqrt(1+eps)*logy**2/(8*math.log(2))*math.exp(-L/4)
    trivial=math.exp(-3*L)/(-math.expm1(-2*L))
    total=baseline_sum+float(layer_rows.sum())+tail+pp+trivial
    if not math.isfinite(total) or total<0:
        raise FloatingPointError('invalid quadrature result')
    return dict(L=L,M=M,mode=mode,delta=total,baseline=baseline_sum,
                density_layers=float(layer_rows.sum()),row_layers=layer_rows.tolist(),
                height_tail=tail,prime_powers=pp,trivial_zeros=trivial,
                height_order=height_order,sigma_order=sigma_order,max_step=max_step,
                status='EXPLORATORY_NOT_CERTIFIED')


def main():
    output=ROOT/'results'
    results=[]
    for L in (110,115,120,125,130,135,140,145,150,175,200,250,300,350,375,400):
        for M in (2,3,4):
            for mode in MODES:
                result=smooth_bound(L,M,mode)
                results.append(result)
        best={mode:min((r for r in results if r['L']==L and r['mode']==mode),
                       key=lambda r:r['delta']) for mode in MODES}
        print('L='+str(L)+' '+ ' '.join(f'{mode}={r["delta"]:.9g}(M{r["M"]})'
                                         for mode,r in best.items()),flush=True)
    refinements=[]
    for L in (110,120,150):
        coarse=next(r for r in results if r['L']==L and r['M']==2
                    and r['mode']=='envelope_monotone')
        refined=smooth_bound(L,2,'envelope_monotone',32,32,.4)
        refinements.append(dict(L=L,coarse=coarse['delta'],refined=refined['delta'],
            relative_difference=abs(coarse['delta']-refined['delta'])/refined['delta']))
    points=[]
    for s in (.80,.8125,.84,.84375,.85,.86,.87,.875):
        for ratio in (1.000001,1.0001,1.01,2,10):
            u=LOG_H+math.log(ratio)
            points.append(dict(sigma=s,T_over_H=ratio,
                cs2=math.exp(float(cs2_log(s,u))),
                appendix119=math.exp(float(appendix119_log(s,u))),
                cho_table=math.exp(float(cho_table_log(s,u))),
                local_count_cap=float(local_count_cap(LOG_H,u)),
                envelope=math.exp(float(log_density_bound(s,u)))))
    local_windows=[]
    for s in (.80,.85,.875):
        for ratio in (1.00000001,1.000001,1.00001,1.0001,1.001,1.01,1.1,2):
            u=LOG_H+math.log(ratio)
            D=math.exp(float(np.minimum(cs2_log(s,u),appendix119_log(s,u))))
            cap=float(local_count_cap(LOG_H,u))
            local_windows.append(dict(sigma=s,T_over_H=ratio,
                                      density=D,local_count_cap=cap,ratio=cap/D))
    crossovers=[]
    for s in (.80,.85,.875):
        f=lambda d:math.log(float(local_count_cap(LOG_H,LOG_H+d)))-float(
            np.minimum(cs2_log(s,LOG_H+d),appendix119_log(s,LOG_H+d)))
        d=brentq(f,1e-12,.2,xtol=1e-14)
        crossovers.append(dict(sigma=s,log_T_over_H=d,T_over_H=math.exp(d),
                               absolute_height_width=H*math.expm1(d)))
    payload=dict(status='EXPLORATORY_NOT_CERTIFIED',
        created=datetime.now(timezone.utc).isoformat(),
        sources=dict(cs2=CS_SOURCE,bw2=BW_SOURCE,cho24=CHO_SOURCE),
        source_details=dict(appendix='Eq119,Table4,first8rows,T>=3e12',
          bw='Theorem1.1 both two-sided errors; upper at T1 minus lower at T0',
          cho='DIAGNOSTIC ONLY: Table1 at sigma=.60,.66,T0=3e12; excluded from envelopes'),
        appendix_constants=APPENDIX_ROWS.tolist(),modes=list(MODES),
        code_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        imported_smooth_scan_sha256=hashlib.sha256(Path(base.__file__).read_bytes()).hexdigest(),
        numpy=np.__version__,scipy=scipy.__version__,
        results=results,refinement_checks=refinements,point_comparisons=points,
        local_window_comparisons=local_windows,local_count_crossovers=crossovers)
    (output/'density_round2.json').write_text(json.dumps(payload,indent=2)+'\n',encoding='utf-8')
    with (output/'density_round2.csv').open('w',encoding='utf-8',newline='') as stream:
        fields=[k for k in results[0] if k!='row_layers']
        writer=csv.DictWriter(stream,fieldnames=fields)
        writer.writeheader()
        writer.writerows({k:v for k,v in row.items() if k!='row_layers'} for row in results)
    print(json.dumps(dict(refinements=refinements,crossovers=crossovers),indent=2))


if __name__=='__main__':
    main()
