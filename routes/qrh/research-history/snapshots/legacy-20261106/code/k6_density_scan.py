"""Explore CS v2 Corollary 1 / Appendix (119) minimum for k=6.

Floating-point quadrature only. The published inputs are stated on closed
sigma rows and T>=3e12. This does not certify a continuous L range.
"""
from __future__ import annotations
import argparse
import csv
import hashlib
import json
import math
from datetime import datetime, timezone, timedelta
from pathlib import Path
import numpy as np
import smooth_scan as smooth

ROOT = Path(__file__).resolve().parents[1]
APPENDIX_ROWS = (
    ('2.900','5.027'), ('3.474','4.789'), ('4.149','4.536'),
    ('4.940','4.296'), ('5.860','4.042'), ('6.925','3.800'),
    ('8.148','3.546'), ('9.543','3.301'),
)
ORIGINAL_CUMULATIVE = smooth.cumulative_terms

def cumulative_terms(L, u, sigma_order=12, density='cs2_appendix', symmetry=True):
    u = np.asarray(u)
    if np.min(u) < math.log(64):
        raise ValueError('Total-count simplification requires t>=64')
    log_total = u + np.log(u) - smooth.LOG_2PI
    baseline = np.exp(log_total-L/2)
    layers = np.zeros_like(u)
    select = u > smooth.LOG_H
    if not np.any(select):
        return baseline,layers
    v = u[select,None]
    sigma,weights,coeffs = smooth.sigma_rule(sigma_order,2)
    s = sigma[None,:]
    c,d,e = coeffs.T
    p = 3*(1-s)/(2-s)
    log_cs = np.logaddexp(np.log(c)[None,:]+p*v+(2+p)*np.log(v),
                         np.log(d[None,:]*v*v+e[None,:]*v))
    log_bound=log_cs.copy()
    eligible=sigma>=.625
    ss=sigma[eligible][None,:]
    indices=np.floor(sigma[eligible]*32).astype(int)-20
    arr=np.asarray(APPENDIX_ROWS,dtype=float)[indices]
    aa,bb=arr.T
    log_app=np.logaddexp(np.log(aa)[None,:]+(8/3)*(1-ss)*v+(6-4*ss)*np.log(v),
                        np.log(bb)[None,:]+2*np.log(v))
    log_bound[:,eligible]=np.minimum(log_cs[:,eligible],log_app)
    log_bound=np.minimum(log_bound,log_total[select,None]-math.log(2))
    pair_factor=-np.expm1(-(2*s-1)*L) if symmetry else np.ones_like(s)
    layers[select]=L*np.sum(np.exp(log_bound-(1-s)*L)*pair_factor*weights[None,:],axis=1)
    return baseline,layers

def bound(L,M,*,combined=True,height_order=32,sigma_order=32,max_step=1):
    smooth.cumulative_terms=cumulative_terms if combined else ORIGINAL_CUMULATIVE
    try:
        r=smooth.smooth_bound(6,L,M,height_order=height_order,sigma_order=sigma_order,
                              max_step=max_step,density='cs2')
        r['density']='cs2_appendix119_min' if combined else 'cs2'
        return r
    finally:
        smooth.cumulative_terms=ORIGINAL_CUMULATIVE

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--ls',default='167,168,170,172,173,174,175,176,177,178,180,182,185')
    parser.add_argument('--degrees',default='2,3')
    parser.add_argument('--output',default='k6_density_comparison')
    args=parser.parse_args()
    rows=[]
    for L in map(float,args.ls.split(',')):
        group=[]
        for M in map(int,args.degrees.split(',')):
            for combined in (False,True):
                r=bound(L,M,combined=combined)
                rows.append(r);group.append(r)
        print('L',L,[(d,min(r['delta'] for r in group if r['density']==d))
                       for d in ('cs2','cs2_appendix119_min')],flush=True)
    out=ROOT/'results'
    path=out/f'{args.output}.csv'
    with path.open('w',encoding='utf-8',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=list(rows[0]));writer.writeheader();writer.writerows(rows)
    manifest=dict(status='EXPLORATORY',created=datetime.now(timezone(timedelta(hours=8))).isoformat(),
        arguments=vars(args),source='https://arxiv.org/html/2507.15184v2',
        source_formula='Corollary 1, Table 1; Appendix (119), Table 4',
        appendix_constants=[list(r) for r in APPENDIX_ROWS],
        height_order=32,sigma_order=32,max_step=1,
        code_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        dependency_sha256=hashlib.sha256(Path(smooth.__file__).read_bytes()).hexdigest(),
        csv_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
        limitations=['Floating quadrature, no outward rounding',
          'Minimum introduces nonsmooth crossings; convergence must be checked',
          'No continuous L certificate and no full k6 proof'])
    (out/f'{args.output}.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')
    print(path)

if __name__=='__main__':main()
