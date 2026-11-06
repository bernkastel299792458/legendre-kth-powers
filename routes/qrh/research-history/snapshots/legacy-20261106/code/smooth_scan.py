"""Exploratory QRH(7/8) smooth prime-interval bounds. NOT a certificate.

All quadratures and kernel constants here are floating point. A positive
reported margin is a candidate for rigorous verification, not a theorem.
Run from any directory; outputs are relative to this research project.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
import platform
from dataclasses import dataclass
from datetime import datetime, timezone, timedelta
from functools import lru_cache
from pathlib import Path

import numpy as np
import scipy
from scipy.special import betaln, eval_jacobi, eval_legendre, roots_jacobi

ROOT = Path(__file__).resolve().parents[1]
LOG_H = math.log(3e12)
LOG_2PI = math.log(2 * math.pi)
ROWS = np.array([
    [.50000,.53125,5.360,9.461,167.8],
    [.53125,.56250,6.380,9.168,162.6],
    [.56250,.59375,7.453,8.875,157.4],
    [.59375,.62500,8.604,8.582,152.2],
    [.62500,.65625,9.848,8.290,147.0],
    [.65625,.68750,11.20,7.997,141.9],
    [.68750,.71875,12.65,7.704,136.7],
    [.71875,.75000,14.23,7.411,131.5],
    [.75000,.78125,15.95,7.118,126.3],
    [.78125,.81250,17.84,6.826,121.1],
    [.81250,.84375,19.97,6.533,115.9],
    [.84375,.87500,22.44,6.240,110.7],
], dtype=float)
CS_V2_C1 = np.array([5.069,6.046,7.077,8.185,9.387,10.70,12.11,13.66,15.35,17.21,19.31,21.77])


@lru_cache(maxsize=None)
def legendre_rule(order: int):
    return np.polynomial.legendre.leggauss(order)


def derivative_phi(M: int, j: int, y):
    y = np.asarray(y)
    return ((-1)**j * math.factorial(j) *
            (y * (1-y))**(M-j) * eval_jacobi(j, M-j, M-j, 2*y-1))


@dataclass(frozen=True)
class Kernel:
    degree: int
    log_R: tuple[float, ...]
    max_over_mass: float
    # (left, right, power) in w=log(t/q); power=0 intervals omitted.
    segments: tuple[tuple[float, float, int], ...]


@lru_cache(maxsize=None)
def make_kernel(M: int, use_bv: bool = True) -> Kernel:
    if not 2 <= M <= 32:
        raise ValueError('Require 2 <= M <= 32')
    mass = math.exp(betaln(M+1, M+1))
    ratios = [1.0]
    for j in range(1, M+1):
        roots, _ = roots_jacobi(j, M-j, M-j)
        points = np.r_[0.0, (roots+1)/2, 1.0]
        previous = derivative_phi(M, j-1, points)
        ratios.append(float(np.abs(np.diff(previous)).sum()/mass))
    if use_bv:
        critical, _ = roots_jacobi(M-1, 1, 1)
        values = eval_legendre(M, np.r_[-1.0, critical, 1.0])
        # TV of zero extension includes both jumps, each M!.
        ratios.append(math.factorial(M)*(np.abs(np.diff(values)).sum()+2)/mass)
    logs = np.log(ratios)
    candidates = {0.0}
    for i in range(len(logs)):
        for j in range(i+1, len(logs)):
            cross = float((logs[j]-logs[i])/(j-i))
            if cross > 0:
                candidates.add(cross)
    breaks = sorted(candidates) + [math.inf]
    segments = []
    for left, right in zip(breaks[:-1], breaks[1:]):
        mid = left+10 if math.isinf(right) else (left+right)/2
        active = int(np.argmin(logs-np.arange(len(logs))*mid))
        if active == 0:
            continue
        if segments and segments[-1][2] == active:
            segments[-1] = (segments[-1][0], right, active)
        else:
            segments.append((left, right, active))
    assert segments and segments[-1][2] == len(logs)-1
    return Kernel(M, tuple(logs), 4.0**(-M)/mass, tuple(segments))


@lru_cache(maxsize=None)
def sigma_rule(order: int, version: int = 1):
    nodes, weights = legendre_rule(order)
    sigmas, ws, cs = [], [], []
    for index, (lo, hi, c, d, e) in enumerate(ROWS):
        if version == 2:
            c = CS_V2_C1[index]
        sigmas.extend((lo+hi)/2 + (hi-lo)/2*nodes)
        ws.extend((hi-lo)/2*weights)
        cs.extend([(c,d,e)]*order)
    return np.array(sigmas), np.array(ws), np.array(cs)


def cumulative_terms(L, u, sigma_order=12, density='hybrid', symmetry=True):
    """Upper-bound expressions for cumulative weighted positive-height zeros.

    Outputs are plain floats. Domain u>=log(64) ensures the weak count bound.
    """
    u = np.asarray(u)
    if np.min(u) < math.log(64):
        raise ValueError('Total-count simplification only checked for t>=64')
    log_total = u + np.log(u) - LOG_2PI
    baseline = np.exp(log_total-L/2)
    layers = np.zeros_like(u)
    select = u > LOG_H
    if not np.any(select):
        return baseline, layers
    v = u[select, None]
    version = 2 if density in ('cs2','hybrid2') else 1
    sigma, weights, coeffs = sigma_rule(sigma_order,version)
    s = sigma[None, :]
    c, d, e = coeffs.T
    if density in ('cs', 'hybrid', 'cs2', 'hybrid2'):
        log_power = (7-5*s)/(2-s) if version == 2 else 3
        log_cs = np.logaddexp(
            np.log(c)[None, :] + 3*(1-s)/(2-s)*v + log_power*np.log(v),
            np.log(d[None, :]*v*v + e[None, :]*v))
        log_bound = log_cs
    else:
        log_bound = np.full((len(v),len(sigma)), np.inf)
    if density in ('fks', 'hybrid', 'hybrid2'):
        log_fks = np.logaddexp(
            math.log(17.4194) + (8/3)*(1-s)*v + (5-2*s)*np.log(v),
            math.log(5.2954)+2*np.log(v))
        # Do not extend this input below its declared sigma range.
        log_fks[:, sigma < .625] = np.inf
        log_bound = np.minimum(log_bound, log_fks)
    # For sigma>1/2, pairing gives at most half of all zeros.
    cap = log_total[select, None]-math.log(2)
    log_bound = np.minimum(log_bound, cap)
    if symmetry:
        pair_factor = -np.expm1(-(2*s-1)*L)
    else:
        pair_factor = np.ones_like(s)
    layers[select] = L*np.sum(
        np.exp(log_bound-(1-s)*L)*pair_factor*weights[None, :], axis=1)
    return baseline, layers


def smooth_bound(k, L, M, *, height_order=16, sigma_order=12,
                 max_step=3.0, density='hybrid', symmetry=True, use_bv=True):
    if not 3 <= k <= 8 or not 40 <= L <= 5000:
        raise ValueError('Exploratory floating-point domain: 3<=k<=8, 40<=L<=5000')
    kernel = make_kernel(M, use_bv)
    eps = k*math.exp(-L/k)
    logq = np.logaddexp(0.0, L/k-math.log(k))
    J = len(kernel.log_R)-1
    last_start = logq+kernel.segments[-1][0]
    # Ensure crude QRH/all-count analytic tail is tiny, not silently omitted.
    U = max(last_start+40, LOG_H+40,
            (kernel.log_R[-1]+J*logq-L/8+60)/(J-1))
    nodes, weights = legendre_rule(height_order)
    low_sum = high_sum = 0.0
    for wlo, whi, j in kernel.segments:
        lo, hi = logq+wlo, min(logq+whi, U)
        if lo >= hi:
            continue
        split = [lo, hi]
        if lo < LOG_H < hi:
            split.append(LOG_H)
        split.sort()
        for begin, end in zip(split[:-1], split[1:]):
            cuts = np.linspace(begin, end, max(1,math.ceil((end-begin)/max_step))+1)
            centers, half = (cuts[:-1]+cuts[1:])/2, np.diff(cuts)/2
            u = (centers[:,None]+half[:,None]*nodes).ravel()
            wts = (half[:,None]*weights).ravel()
            log_measure = math.log(j)+kernel.log_R[j]+j*(logq-u)
            baseline, layers = cumulative_terms(L, u, sigma_order, density, symmetry)
            measure = np.exp(log_measure)
            low_sum += 2*float(np.dot(wts, baseline*measure))
            high_sum += 2*float(np.dot(wts, layers*measure))
    logtail = (math.log(J/math.pi)+kernel.log_R[J]+J*logq-L/8
               -(J-1)*U+math.log(U/(J-1)+1/(J-1)**2))
    tail = math.exp(logtail)
    logy = L+math.log1p(eps)
    pp = (kernel.max_over_mass*math.sqrt(1+eps)*logy**2 /
          (2*k*math.log(2))*math.exp(-(0.5-1/k)*L))
    trivial = math.exp(-3*L)/(-math.expm1(-2*L))
    total = low_sum+high_sum+tail+pp+trivial
    if not all(math.isfinite(v) and v >= 0 for v in (low_sum,high_sum,tail,pp,trivial,total)):
        raise FloatingPointError(f'Non-finite or negative bound at k={k}, L={L}, M={M}')
    return dict(k=k,L=float(L),M=M,bv=use_bv,density=density,symmetry=symmetry,
                baseline=low_sum,density_layers=high_sum,height_tail=tail,
                prime_powers=pp,trivial_zeros=trivial,delta=total,margin=1-total,
                height_end=U,height_order=height_order,sigma_order=sigma_order,
                max_height_step=max_step,status='EXPLORATORY')


def self_check():
    k = make_kernel(2, True)
    actual = np.exp(k.log_R)
    expected = np.array([1,15/4,40/math.sqrt(3),300])
    if not np.allclose(actual,expected,rtol=2e-13,atol=1e-13):
        raise AssertionError((actual,expected))
    for M in (2,3,4,6,8):
        kernel=make_kernel(M,True)
        for lo,hi,j in kernel.segments:
            w=lo+1 if math.isinf(hi) else (lo+hi)/2
            active=int(np.argmin(np.array(kernel.log_R)-np.arange(len(kernel.log_R))*w))
            if active != j:
                raise AssertionError('Incorrect lower envelope')
    # Independent high-order quadrature: enough to catch gross integration errors.
    a=smooth_bound(4,150,2,height_order=12,sigma_order=10,max_step=3)
    b=smooth_bound(4,150,2,height_order=28,sigma_order=24,max_step=1)
    relative=abs(a['delta']-b['delta'])/b['delta']
    if relative>3e-4:
        raise AssertionError(f'Quadrature instability {relative}')
    return dict(kernel_M2=actual.tolist(),quadrature_relative_difference=relative,
                note='Numerical consistency checks only; not proof certification')


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--ks',default='3,4,5,6,7,8')
    p.add_argument('--degrees',default='2,3,4,6,8')
    p.add_argument('--ls',default='60,75,90,100,105,109,110,120,130,140,150,175,200,250,300,400,500,600,700,800')
    p.add_argument('--output',default='smooth_scan')
    p.add_argument('--height-order',type=int,default=16)
    p.add_argument('--sigma-order',type=int,default=12)
    p.add_argument('--max-step',type=float,default=3)
    p.add_argument('--density',choices=['hybrid','cs','fks','cs2','hybrid2'],default='hybrid')
    p.add_argument('--no-bv',action='store_true')
    p.add_argument('--no-symmetry',action='store_true')
    p.add_argument('--check-only',action='store_true')
    args=p.parse_args()
    checks=self_check()
    if args.check_only:
        print(json.dumps(checks,indent=2)); return
    ks=[int(x) for x in args.ks.split(',')]
    degrees=[int(x) for x in args.degrees.split(',')]
    ls=[float(x) for x in args.ls.split(',')]
    results=[]
    for k in ks:
        for L in ls:
            group=[]
            for M in degrees:
                result=smooth_bound(k,L,M,height_order=args.height_order,
                    sigma_order=args.sigma_order,max_step=args.max_step,
                    density=args.density,symmetry=not args.no_symmetry,use_bv=not args.no_bv)
                results.append(result); group.append(result)
            best=min(group,key=lambda r:r['delta'])
            print(f"k={k} L={L:g} bestM={best['M']} delta={best['delta']:.8g}",flush=True)
    out=ROOT/'results'
    out.mkdir(parents=True,exist_ok=True)
    csv_path=out/f'{args.output}.csv'
    with csv_path.open('w',encoding='utf-8',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=list(results[0])); writer.writeheader(); writer.writerows(results)
    bests=[]
    for k in ks:
        candidates=[r for r in results if r['k']==k]
        best_each=[min((r for r in candidates if r['L']==L),key=lambda r:r['delta']) for L in ls]
        failing=[r['L'] for r in best_each if r['delta']>=1]
        bests.append(dict(k=k,sampled_failing_L=failing,
                         worst_sample=min(best_each,key=lambda r:-r['delta']),
                         note='Sampling does not certify any continuous range'))
    manifest=dict(status='EXPLORATORY',created=datetime.now(timezone(timedelta(hours=8))).isoformat(),
        arguments=vars(args),python=platform.python_version(),numpy=np.__version__,scipy=scipy.__version__,
        code_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        csv_sha256=hashlib.sha256(csv_path.read_bytes()).hexdigest(),checks=checks,summary=bests,
        sources=[f"https://arxiv.org/html/2507.15184v{2 if args.density in ('cs2','hybrid2') else 1}"]
                +(['https://arxiv.org/html/2204.02588v3'] if args.density in ('fks','hybrid','hybrid2') else []),
        limitations=['Floating-point Jacobi roots and quadrature','No interval proof',
                     'Analytic height-tail expression evaluated in floating point',
                     'No claims between sampled L values'])
    (out/f'{args.output}.json').write_text(json.dumps(manifest,ensure_ascii=False,indent=2),encoding='utf-8')
    snapshots=out/'code_snapshots'
    snapshots.mkdir(exist_ok=True)
    (snapshots/f"smooth_scan_{manifest['code_sha256']}.py").write_bytes(Path(__file__).read_bytes())
    print(f'Saved {csv_path}')


if __name__=='__main__':
    main()
