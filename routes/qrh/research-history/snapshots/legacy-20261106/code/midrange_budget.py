"""Round-two diagnostic quadratures; EXPLORATORY, never a certificate.

Resolve the CS v2 absolute-value bound by sigma and log-height boxes.
Optional stronger beta/finite-RH assumptions are sensitivity experiments only.
The certified project premise remains beta<=7/8 and H=3e12.
"""
from __future__ import annotations

import csv
import hashlib
import json
import math
import platform
from datetime import datetime, timezone, timedelta
from pathlib import Path

import numpy as np
from scipy.optimize import brentq

import smooth_scan as base

ROOT = Path(__file__).resolve().parents[1]
HEIGHT_OFFSETS = [0, math.log(2), math.log(10), math.log(100),
                  math.log(1e4), math.log(1e8), math.log(1e16), math.inf]


def evaluate(L, M=2, *, beta_max=.875, log_rh_height=base.LOG_H,
             height_order=20, sigma_order=16, max_step=1.0, boxes=False):
    if not (100 <= L <= 1000 and .5 <= beta_max <= .875
            and base.LOG_H <= log_rh_height <= 300):
        raise ValueError('Diagnostic parameter outside supported range')
    kernel = base.make_kernel(M, True)
    logq = float(np.logaddexp(0, L/4-math.log(4)))
    J = len(kernel.log_R)-1
    U = max(logq+kernel.segments[-1][0]+40, log_rh_height+20,
            (kernel.log_R[-1]+J*logq-L/8+60)/(J-1))
    nodes, weights = base.legendre_rule(height_order)
    snodes, sweights = base.legendre_rule(sigma_order)
    sigma, sigma_weights, constants, row_ids = [], [], [], []
    for ri, (lo, hi, _, d, e) in enumerate(base.ROWS):
        hi = min(hi, beta_max)
        if hi <= lo:
            continue
        sigma.extend((lo+hi)/2+(hi-lo)/2*snodes)
        sigma_weights.extend((hi-lo)/2*sweights)
        constants.extend([(base.CS_V2_C1[ri],d,e)]*sigma_order)
        row_ids.extend([ri]*sigma_order)
    s = np.asarray(sigma)[None,:]
    sw = np.asarray(sigma_weights)[None,:]
    cs = np.asarray(constants)
    row_ids = np.asarray(row_ids)
    matrix = np.zeros((12,len(HEIGHT_OFFSETS)-1))
    baseline = density_total = 0.0
    boundaries = [base.LOG_H+z for z in HEIGHT_OFFSETS[:-1]]
    for wlo, whi, j in kernel.segments:
        lo, hi = logq+wlo, min(logq+whi,U)
        if hi <= lo:
            continue
        cuts = sorted(set([lo,hi]+[b for b in boundaries+[log_rh_height]
                                   if lo < b < hi]))
        for begin, end in zip(cuts[:-1],cuts[1:]):
            subdiv = np.linspace(begin,end,max(1,math.ceil((end-begin)/max_step))+1)
            center, half = (subdiv[:-1]+subdiv[1:])/2, np.diff(subdiv)/2
            u = (center[:,None]+half[:,None]*nodes).ravel()
            qw = (half[:,None]*weights).ravel()
            measure = np.exp(math.log(j)+kernel.log_R[j]+j*(logq-u))
            nlog = u+np.log(u)-base.LOG_2PI
            baseline += 2*float(np.dot(qw*measure,np.exp(nlog-L/2)))
            if begin < log_rh_height or not sigma:
                continue
            v = u[:,None]
            c,d,e = cs.T
            p = 3*(1-s)/(2-s)
            dc = np.logaddexp(np.log(c)[None,:]+p*v+(2+p)*np.log(v),
                             np.log(d[None,:]*v*v+e[None,:]*v))
            dc = np.minimum(dc,nlog[:,None]-math.log(2))
            integrand = 2*L*np.exp(dc-(1-s)*L)*(-np.expm1(-(2*s-1)*L))*sw
            contributions = np.sum((qw*measure)[:,None]*integrand,axis=0)
            density_total += float(np.sum(contributions))
            if boxes:
                bi = int(np.searchsorted(HEIGHT_OFFSETS,(begin+end)/2-base.LOG_H,
                                         side='right')-1)
                for ri in range(12):
                    matrix[ri,bi] += float(np.sum(contributions[row_ids==ri]))
    tail = math.exp(math.log(J/math.pi)+kernel.log_R[J]+J*logq-L/8
                    -(J-1)*U+math.log(U/(J-1)+1/(J-1)**2))
    eps = 4*math.exp(-L/4)
    logy = L+math.log1p(eps)
    pp = kernel.max_over_mass*math.sqrt(1+eps)*logy**2/(8*math.log(2))*math.exp(-L/4)
    trivial = math.exp(-3*L)/(-math.expm1(-2*L))
    result = dict(L=L,M=M,beta_max=beta_max,log_rh_height=log_rh_height,
                  baseline=baseline,density_layers=density_total,height_tail=tail,
                  prime_powers=pp,trivial_zeros=trivial,
                  delta=baseline+density_total+tail+pp+trivial,
                  status='EXPLORATORY',assumptions_changed=(beta_max!=.875 or log_rh_height!=base.LOG_H))
    if boxes:
        result['boxes']=matrix.tolist()
    if not all(math.isfinite(result[k]) and result[k]>=0 for k in
               ('baseline','density_layers','height_tail','prime_powers','trivial_zeros','delta')):
        raise FloatingPointError(result)
    return result


def main():
    Ls = [109.46,110,115,120,130,150,200,250,300,350,375]
    results, cells, sensitivity = [], [], []
    for L in Ls:
        r=evaluate(L,2,boxes=True)
        check=base.smooth_bound(4,L,2,height_order=24,sigma_order=24,max_step=1,density='cs2')
        relative=abs(r['delta']-check['delta'])/check['delta']
        if relative>2e-5:
            raise ValueError(f'Old implementation mismatch: {L}, {relative}')
        r['crosscheck_relative_difference']=relative
        matrix=np.asarray(r.pop('boxes'))
        for ri,row in enumerate(base.ROWS):
            for bi in range(matrix.shape[1]):
                cells.append(dict(L=L,M=2,sigma_left=row[0],sigma_right=row[1],
                    log_t_over_H_left=HEIGHT_OFFSETS[bi],log_t_over_H_right=HEIGHT_OFFSETS[bi+1],
                    contribution=matrix[ri,bi],fraction_of_density=matrix[ri,bi]/r['density_layers']))
        r['sigma_row_sums']=matrix.sum(axis=1).tolist()
        r['height_band_sums']=matrix.sum(axis=0).tolist()
        r['boxes_relative_sum_error']=abs(matrix.sum()-r['density_layers'])/r['density_layers']
        results.append(r)
        print(f"L={L:g} delta={r['delta']:.9g} crosscheck={relative:.3g}",flush=True)
    # Sensitivity only: none of these stronger assumptions is claimed proven.
    for L in [110,120,130,150]:
        for M in [2,4,8,16]:
            ev=lambda beta: evaluate(L,M,beta_max=beta)['delta']-0.9
            beta=brentq(ev,.5,.875,xtol=1e-7)
            hv=lambda z: evaluate(L,M,log_rh_height=z)['delta']-0.9
            rh=brentq(hv,base.LOG_H,150,xtol=1e-7)
            sensitivity.append(dict(L=L,M=M,target_delta=.9,
                hypothetical_beta_max=beta,hypothetical_log_rh_height=rh,
                hypothetical_rh_height_factor=math.exp(rh-base.LOG_H),
                status='COUNTERFACTUAL_SENSITIVITY_NOT_AN_INPUT'))
    out=ROOT/'results'
    path=out/'midrange_budget_round2.csv'
    with path.open('w',encoding='utf-8',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=list(cells[0]));writer.writeheader();writer.writerows(cells)
    manifest=dict(status='EXPLORATORY',created=datetime.now(timezone(timedelta(hours=8))).isoformat(),
        python=platform.python_version(),source='https://arxiv.org/html/2507.15184v2',
        scripts={name:hashlib.sha256((ROOT/'code'/name).read_bytes()).hexdigest()
                 for name in ['midrange_budget.py','smooth_scan.py']},
        csv_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
        results=results,sensitivity=sensitivity,
        limitations=['Floating point quadrature, no interval certificate',
          'Bins decompose an upper-bound Stieltjes integral, not the actual zeros by height',
          'Cumulative counts in a high-height bin include lower-height zeros',
          'The stronger beta and finite-RH assumptions are explicitly hypothetical',
          'No continuous-L or full-k4 claim'])
    (out/'midrange_budget_round2.json').write_text(json.dumps(manifest,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
    print('Saved midrange_budget_round2.{csv,json}',flush=True)


if __name__=='__main__':
    main()
