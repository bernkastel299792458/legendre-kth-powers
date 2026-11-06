"""Floating-point exploration of a trapezoidal weight; NOT a certificate.

The normalized weight is the convolution of uniform densities on [0,a]
and [0,1-a]. Its exact derivative/BV ratios are used, but quadrature and
all subsequent calculations use ordinary floating point.
"""
from __future__ import annotations

import csv
import hashlib
import json
import math
from datetime import datetime, timezone, timedelta
from fractions import Fraction
from pathlib import Path

import numpy as np
from scipy.optimize import minimize_scalar

import smooth_scan as base

ROOT = Path(__file__).resolve().parents[1]


def trap_bound(k, L, width=Fraction(1,32), *, height_order=32,
               sigma_order=24, max_step=1.0):
    width = Fraction(width)
    if not 0 < width <= Fraction(1,2):
        raise ValueError('Require 0<a<=1/2')
    if not 3 <= k <= 8 or not 40 <= L <= 5000:
        raise ValueError('Exploratory domain: 3<=k<=8 and 40<=L<=5000')
    a = float(width)
    b = 1-a
    R1, R2 = 2/b, 4/(a*b)
    eps = k*math.exp(-L/k)
    logq = float(np.logaddexp(0.0, L/k-math.log(k)))
    # g=min(1,R1*q/t,R2*(q/t)^2). The two positive-mass pieces are exact.
    segments = ((math.log(R1),math.log(R2/R1),1,math.log(R1)),
                (math.log(R2/R1),math.inf,2,math.log(R2)))
    U=max(logq+math.log(R2/R1)+40,base.LOG_H+40,
          math.log(R2)+2*logq-L/8+60)
    nodes, weights=base.legendre_rule(height_order)
    baseline_sum=layer_sum=0.0
    for wlo,whi,j,logR in segments:
        lo,hi=logq+wlo,min(logq+whi,U)
        if lo>=hi:
            continue
        split=sorted([lo,hi]+([base.LOG_H] if lo<base.LOG_H<hi else []))
        for begin,end in zip(split[:-1],split[1:]):
            cuts=np.linspace(begin,end,max(1,math.ceil((end-begin)/max_step))+1)
            centers,half=(cuts[:-1]+cuts[1:])/2,np.diff(cuts)/2
            u=(centers[:,None]+half[:,None]*nodes).ravel()
            wts=(half[:,None]*weights).ravel()
            measure=np.exp(math.log(j)+logR+j*(logq-u))
            low,high=base.cumulative_terms(L,u,sigma_order,'cs2',True)
            baseline_sum+=2*float(np.dot(wts,low*measure))
            layer_sum+=2*float(np.dot(wts,high*measure))
    tail=math.exp(math.log(2/math.pi)+math.log(R2)+2*logq-L/8-U+math.log(U+1))
    logy=L+math.log1p(eps)
    pp=(1/b)*math.sqrt(1+eps)*logy**2/(2*k*math.log(2))*math.exp(-(0.5-1/k)*L)
    trivial=math.exp(-3*L)/(-math.expm1(-2*L))
    delta=baseline_sum+layer_sum+tail+pp+trivial
    if not all(math.isfinite(v) and v>=0 for v in (baseline_sum,layer_sum,tail,pp,trivial,delta)):
        raise FloatingPointError('Nonfinite or negative result')
    return dict(k=k,L=float(L),a=str(width),baseline=baseline_sum,
                density_layers=layer_sum,height_tail=tail,prime_powers=pp,
                trivial_zeros=trivial,delta=delta,margin=1-delta,
                height_end=U,height_order=height_order,sigma_order=sigma_order,
                max_height_step=max_step,status='EXPLORATORY')


def contact_L(k,width):
    # Exact relation in real arithmetic; output here is floating point.
    b=1-float(Fraction(width))
    return k*math.log(k*(3e12*b/2-1))


def main():
    width=Fraction(1,32)
    contact=contact_L(6,width)
    points=sorted(set([float(x)/4 for x in range(668,801)]+
                      [contact,225.,250.,275.,300.,350.,400.]))
    rows=[trap_bound(6,L,width) for L in points]
    parameter_scan=[]
    for value in ('1/200','1/100','1/50','3/100','1/32','1/20','3/40','1/10','3/20'):
        a=Fraction(value)
        Lh=contact_L(6,a)
        search=minimize_scalar(lambda L:-trap_bound(6,float(L),a)['delta'],
                               bounds=(177,181),method='bounded',
                               options={'xatol':1e-9})
        parameter_scan.append(dict(a=str(a),contact_L=Lh,
                                   contact_delta=trap_bound(6,Lh,a)['delta'],
                                   optimized_L=float(search.x),
                                   optimized_delta=float(-search.fun)))
    worst=max(rows,key=lambda r:r['delta'])
    # Higher-order quadrature is a stability check, never an interval proof.
    refined=trap_bound(6,contact,width,height_order=48,sigma_order=36,max_step=.5)
    discrepancy=abs(refined['delta']-worst['delta'])/refined['delta']
    out=ROOT/'results'
    csv_path=out/'k6_kernel_trapezoid.csv'
    with csv_path.open('w',encoding='utf-8',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)
    source=Path(__file__)
    dependency=Path(base.__file__)
    manifest=dict(status='EXPLORATORY',
        created=datetime.now(timezone(timedelta(hours=8))).isoformat(),
        fixed_width=str(width),kernel=dict(R0='1',R1='64/31',R2='4096/31',max_over_mass='32/31'),
        interval_sampled=['167','200'],number_of_points=len(rows),worst_sample=worst,
        contact_L=contact,refined_contact=refined,quadrature_relative_difference=discrepancy,
        parameter_scan=parameter_scan,
        code_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
        smooth_scan_sha256=hashlib.sha256(dependency.read_bytes()).hexdigest(),
        csv_sha256=hashlib.sha256(csv_path.read_bytes()).hexdigest(),
        sources=['https://arxiv.org/html/2507.15184v2','https://arxiv.org/abs/2004.09765'],
        limitations=['Floating-point quadrature, not Arb certification',
                     'No proof between sampled L values or of an exact maximum',
                     'Finite-height RH input below H, CSv2 above H',
                     'The source derivation and kernel constants require analytic review'])
    (out/'k6_kernel_trapezoid.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')
    snapshots=out/'code_snapshots'
    snapshots.mkdir(exist_ok=True)
    (snapshots/f"k6_kernel_explore_{manifest['code_sha256']}.py").write_bytes(source.read_bytes())
    print(json.dumps(dict(worst=worst,refined_contact=refined,
                         quadrature_relative_difference=discrepancy,
                         parameter_scan=parameter_scan),indent=2))


if __name__=='__main__':
    main()
