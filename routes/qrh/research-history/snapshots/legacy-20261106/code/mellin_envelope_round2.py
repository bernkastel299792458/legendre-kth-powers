"""A direct Fourier-to-Mellin envelope for the beta(3,3) kernel.

Floating point positive height sums + sigma quadrature: EXPLORATORY.
The analytic envelope is documented separately; these outputs are not proof.
"""
from __future__ import annotations

import hashlib
import json
import math
from datetime import datetime, timezone, timedelta
from pathlib import Path

import numpy as np
from scipy.special import spherical_jn

import smooth_scan as base
import density_envelope_round2 as density_input

ROOT=Path(__file__).resolve().parents[1]


def parameters(L):
    eps=4*math.exp(-L/4)
    j=max(20,math.ceil((math.log(4200)-math.log(eps))/(4*math.log(2))))
    W=2.0**j
    d=eps*(.5+W/7)
    return eps,j,W,d


def kernel_values(L,u,mode='direct'):
    eps,j,W,d=parameters(L)
    logq=math.log1p(eps)-math.log(eps)
    u=np.asarray(u)
    v=np.exp(logq-u)
    old=np.minimum.reduce([np.ones_like(v),15/4*v,24*v*v,300*v*v*v])
    if mode=='old':
        return old
    w=np.exp(u+math.log(eps))
    z=w/2
    A=15*np.sqrt(z**-6+3*z**-8+9*z**-10)
    envelope=A
    if mode=='direct':
        select=w<=2*math.pi
        B=15*spherical_jn(2,z[select])/(z[select]**2)
        c=15*math.sqrt(math.pi**-6+3*math.pi**-8+9*math.pi**-10)
        envelope=A.copy()
        envelope[select]=np.maximum(B,c)
    before=w<=W
    new=old.copy()
    new[before]=np.minimum(old[before],envelope[before]+d)
    if not 300*(1+eps)**3/W**3 <= d:
        raise ValueError('No valid monotone join at cutoff')
    return new


def evaluate(L,mode='direct',height_denominator=128,sigma_order=24,density_mode='cs2'):
    if not 100<=L<=700:
        raise ValueError('Exploratory domain 100<=L<=700')
    eps,j,W,d=parameters(L)
    logq=math.log1p(eps)-math.log(eps)
    start=logq-16
    end=max(logq+40,base.LOG_H+40,(math.log(300)+3*logq-L/8+60)/2,
            math.log(W)-math.log(eps)+1)
    u=np.linspace(start,end,math.ceil((end-start)*height_denominator)+1)
    # Split exactly at finite RH height, preserving its one-sided jump.
    u=np.unique(np.r_[u,base.LOG_H] if start<base.LOG_H<end else u)
    g=kernel_values(L,u,mode)
    dm=g[:-1]-g[1:]
    # Roundoff around the near-one platform is not a rigorous sign check.
    if dm.min() < -1e-13:
        raise ValueError('Nonmonotone numerical kernel')
    dm=np.maximum(dm,0)
    def cumulative(u):
        if density_mode=='cs2':
            return base.cumulative_terms(L,u,sigma_order,'cs2')
        if density_mode=='envelope_monotone':
            b,r=density_input.cumulative_terms(L,u,density_mode,sigma_order)
            return b,r.sum(axis=1)
        raise ValueError('Unknown density mode')
    b0,d0=cumulative(np.array([start]))
    early=2*float(b0[0]+d0[0])*max(0,1-g[0])
    baseline=density=0.0
    # Batching bounds memory at larger quadrature orders.
    for i in range(0,len(dm),512):
        b,h=cumulative(u[i+1:i+513])
        masses=dm[i:i+512]
        baseline+=2*float(np.dot(b,masses))
        density+=2*float(np.dot(h,masses))
    tail=3/math.pi*300*math.exp(3*logq-L/8-2*end)*(end/2+.25)
    pp=15/8*math.sqrt(1+eps)*(L+math.log1p(eps))**2/(8*math.log(2))*math.exp(-L/4)
    trivial=math.exp(-3*L)/(-math.expm1(-2*L))
    return dict(L=L,mode=mode,density_mode=density_mode,delta=early+baseline+density+tail+pp+trivial,
                early_height_bound=early,baseline=baseline,density_layers=density,
                height_tail=tail,prime_powers=pp,trivial=trivial,
                epsilon=eps,cutoff_power_of_two=j,frozen_error=d,
                height_start=start,height_end=end,height_cells=len(dm),
                height_denominator=height_denominator,sigma_order=sigma_order,
                status='EXPLORATORY')


def main():
    results=[]
    for L in [109.46,110,115,120,130,150,200,250,300,325,340,350,360,365,370,375,400]:
        old=evaluate(L,'old')
        amp=evaluate(L,'amplitude')
        direct=evaluate(L,'direct')
        results.extend([old,amp,direct])
        print(f"L={L:g} old={old['delta']:.8g} amplitude={amp['delta']:.8g} direct={direct['delta']:.8g}",flush=True)
    refined=[evaluate(L,'direct',256,32) for L in [120,350,360,365,370]]
    joint=[evaluate(L,'direct',256,64,'envelope_monotone')
           for L in [110,120,150,300,370,375]]
    out=dict(status='EXPLORATORY',created=datetime.now(timezone(timedelta(hours=8))).isoformat(),
        premise='QRH(7/8), finite RH through H=3e12 and CS v2',
        sources=['https://arxiv.org/html/2507.15184v2',
                 'https://arxiv.org/html/2412.15470v2'],
        scripts={name:hashlib.sha256((ROOT/'code'/name).read_bytes()).hexdigest()
                 for name in ['mellin_envelope_round2.py','smooth_scan.py','density_envelope_round2.py']},
        results=results,refined=refined,joint=joint,
        limitations=['Floating point kernels and sigma quadrature',
          'Height positive sums evaluated without directed rounding',
          'No continuous-L certification or full-k4 claim'])
    (ROOT/'results'/'mellin_envelope_round2.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')


if __name__=='__main__':
    main()
