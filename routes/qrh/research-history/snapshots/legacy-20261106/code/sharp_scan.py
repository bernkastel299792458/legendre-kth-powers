"""Exploratory direct short-interval bound, with a shared CHJ cutoff.

Imports only the input-table/cumulative-count model from smooth_scan.
Results are floating point, and optimizing samples does not certify ranges.
"""
import argparse
import csv
import hashlib
import json
import math
from pathlib import Path

import numpy as np
from scipy.optimize import minimize_scalar

from smooth_scan import ROOT, LOG_H, cumulative_terms


def components(k,L,t,sigma_order=24):
    u=t+math.log(2)
    baseline,layers=cumulative_terms(L,np.array([u]),sigma_order,'cs',True)
    zero=float(2*(baseline[0]+layers[0]))
    eps=k*math.exp(-L/k)
    logy=L+math.log1p(eps)
    trunc=2.894/k*((1+eps)*logy+L)*math.exp(L/k-t)
    pp=math.sqrt(1+eps)*logy**2/(2*k*math.log(2))*math.exp(-(0.5-1/k)*L)
    endpoint=logy/k*math.exp(-(1-1/k)*L)
    delta=zero+trunc+pp+endpoint
    if not math.isfinite(delta):
        raise FloatingPointError((k,L,t))
    return dict(k=k,L=L,logT=t,zeros=zero,truncation=trunc,prime_powers=pp,
                endpoint=endpoint,delta=delta,margin=1-delta,status='EXPLORATORY')


def optimize(k,L):
    if not 3<=k<=8 or not 40<=L<=5000:
        raise ValueError('Floating exploration domain: 3<=k<=8, 40<=L<=5000')
    eps=k*math.exp(-L/k)
    logy=L+math.log1p(eps)
    low=max(math.log(max(51,logy*logy))+.01,L/k-120)
    high=min(L/2-math.log(8),L/k+120)
    if high<=low:
        raise ValueError('Empty cutoff domain')
    grid=np.linspace(low,high,150)
    values=[components(k,L,float(t)) for t in grid]
    candidate=min(values,key=lambda r:r['delta'])
    idx=values.index(candidate)
    opt=minimize_scalar(lambda t:components(k,L,t)['delta'],
                        bounds=(grid[max(0,idx-1)],grid[min(len(grid)-1,idx+1)]),
                        method='bounded')
    values.append(components(k,L,float(opt.x)))
    # The verified-height boundary is a discontinuity of our upper bound.
    tH=LOG_H-math.log(2)-1e-9
    if low<tH<high:
        values.append(components(k,L,tH))
    best=min(values,key=lambda r:r['delta'])
    best['search_note']='grid plus local optimization; no global optimum claim'
    return best


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--ks',default='3,4,5,6,7,8')
    p.add_argument('--ls',default='60,75,90,100,109.46,110,120,130,150,200,300,400,450,500,600,700,800')
    p.add_argument('--output',default='sharp_all_k')
    args=p.parse_args()
    results=[]
    for k in map(int,args.ks.split(',')):
        for L in map(float,args.ls.split(',')):
            r=optimize(k,L); results.append(r)
            print(f"k={k} L={L:g} delta={r['delta']:.8g}",flush=True)
    path=ROOT/'results'/f'{args.output}.csv'
    with path.open('w',encoding='utf-8',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(results[0])); w.writeheader(); w.writerows(results)
    manifest=dict(status='EXPLORATORY',arguments=vars(args),
        source_sha256={str(p.name):hashlib.sha256(p.read_bytes()).hexdigest()
                       for p in [Path(__file__),Path(__file__).with_name('smooth_scan.py')]},
        csv_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
        note='No interval certification, no between-sample or infinite-tail inference',
        inputs=['CHJII 2402.04272v3 Thm1.3/Table1','CS 2507.15184v1 Cor1/Table1',
                'QRH beta<=7/8','RH verified to 3e12'])
    path.with_suffix('.json').write_text(json.dumps(manifest,ensure_ascii=False,indent=2),encoding='utf-8')


if __name__=='__main__':
    main()
