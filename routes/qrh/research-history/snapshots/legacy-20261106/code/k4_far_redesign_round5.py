"""Counterfactual full-budget reverse design. Floating exploration, not proof.

The default writes only this round's dedicated JSON. --verify is read-only.
Height integration extends to infinity by the upper incomplete gamma function.
The certified trapezoid and CS v2 rows are copied explicitly, never imported.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path

import numpy as np
import scipy
from numpy.polynomial.legendre import leggauss
from scipy.optimize import brentq, minimize_scalar
from scipy.special import gammaincc, gammaln

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / 'results' / 'k4_far_redesign_round5.json'
PROOF = ROOT / 'research' / 'K4_FAR_REDESIGN_ROUND5.md'
DEPENDENCIES = ['code/certify_k4_round3.py', 'research/K4_MONOTONE_ROUND3.md']
H = 3e12
LOGH = math.log(H)
R1, R2, MAXIMUM = 16/7, 256/7, 8/7
L_FLAT = 4*math.log(4*(H/R1-1))
ANCHORS = [113.1, 120.0, 150.0, 200.0, 250.0, 300.0, 372.0]
CS_ROWS = np.array([
    [5.069,9.461,167.8], [6.046,9.168,162.6],
    [7.077,8.875,157.4], [8.185,8.582,152.2],
    [9.387,8.290,147.0], [10.70,7.997,141.9],
    [12.11,7.704,136.7], [13.66,7.411,131.5],
    [15.35,7.118,126.3], [17.21,6.826,121.1],
    [19.31,6.533,115.9], [21.77,6.240,110.7]])
VARIANTS = {
    'current_CS_v2': {},
    'c_times_0.1': {'scale': .1},
    'c_times_0.01': {'scale': .01},
    'c_times_0.001': {'scale': .001},
    'c_times_0.0001': {'scale': .0001},
    'c_times_0.00001': {'scale': .00001},
    'remove_main_log_squared': {'remove_logs': 2.0},
    'main_log_free': {'main_log_free': True},
    'all_three_log_free': {'main_log_free': True, 'lower_log_free': True},
    'density_hypothesis_old_logs': {'exponent': 'density_hypothesis'},
    'density_hypothesis_matched_logs': {'exponent': 'density_hypothesis', 'matched_logs': True},
    'density_hypothesis_remove_log_squared': {'exponent': 'density_hypothesis', 'remove_logs': 2.0},
    'density_hypothesis_main_log_free': {'exponent': 'density_hypothesis', 'main_log_free': True},
    'huxley_old_logs': {'exponent': 'huxley'},
    'huxley_remove_log_squared': {'exponent': 'huxley', 'remove_logs': 2.0},
    'huxley_main_log_free': {'exponent': 'huxley', 'main_log_free': True},
}
for cutoff in [.625,.6875,.71875,.75]:
    VARIANTS[f'cut_{cutoff}_remove_log_squared'] = {'log_cutoff':cutoff,'remove_logs':2.0}
    VARIANTS[f'cut_{cutoff}_main_log_free'] = {'log_cutoff':cutoff,'main_log_free':True}
for U in [60.0,80.0,100.0]:
    VARIANTS[f'cut_0.625_remove_log_squared_height_{U:g}'] = {
        'log_cutoff':.625,'remove_logs':2.0,'height_log_max':U}
    VARIANTS[f'cut_0.625_main_log_free_height_{U:g}'] = {
        'log_cutoff':.625,'main_log_free':True,'height_log_max':U}
VARIANTS['cut_0.71875_remove_log_squared_height_100'] = {
    'log_cutoff':.71875,'remove_logs':2.0,'height_log_max':100.0}


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


class Budget:
    def __init__(self, order=32):
        z, w = leggauss(order)
        self.sigma = np.concatenate([(i+(z+1)/2)/32 for i in range(16,28)])
        self.sw = np.tile(w/64,12)
        self.c, self.d, self.e = np.repeat(CS_ROWS,order,axis=0).T
        self.pcs = 3*(1-self.sigma)/(2-self.sigma)
        self.z, self.w = leggauss(max(32,order))
        self.order = order

    def parameters(self, v):
        p = self.pcs.copy()
        mode = v.get('exponent', 'cs')
        if mode == 'density_hypothesis':
            p = 2*(1-self.sigma)
        elif mode == 'huxley':
            p = np.minimum(p, 3*(1-self.sigma)/(3*self.sigma-1))
        elif mode != 'cs':
            raise ValueError('Unknown exponent')
        r = (p if v.get('matched_logs') else self.pcs)+2
        r = np.maximum(0, r-v.get('remove_logs',0))
        if v.get('main_log_free'):
            r = np.zeros_like(p)
        if 'log_cutoff' in v:
            r = np.where(self.sigma>=v['log_cutoff'],r,self.pcs+2)
        return p, r, 0 if v.get('lower_log_free') else 2, 0 if v.get('lower_log_free') else 1

    @staticmethod
    def tail(begin, p, r, j=2):
        a = j-np.asarray(p)
        if np.any(a <= 0):
            raise ValueError('Divergent absolute height integral')
        r = np.asarray(r)
        return np.exp(gammaln(r+1)-(r+1)*np.log(a))*gammaincc(r+1,a*begin)

    def moment(self, L, p, r, height_log_min=LOGH):
        q = 1+math.exp(L/4)/4
        u1, u2 = math.log(R1*q), math.log(R2/R1*q)
        begin = max(u1,LOGH,height_log_min)
        p, r = np.broadcast_arrays(np.asarray(p),np.asarray(r))
        ans = 2*R2*q*q*self.tail(max(u2,LOGH,height_log_min),p,r)
        if u2 > begin:
            u = (begin+u2)/2+(u2-begin)/2*self.z
            vals = np.exp((p[...,None]-1)*u+r[...,None]*np.log(u))
            ans += R1*q*(u2-begin)/2*(vals@self.w)
        return ans

    def main_moment(self,L,v):
        p,r,_,_ = self.parameters(v)
        ans = self.moment(L,p,r)
        if 'height_log_max' in v:
            U = v['height_log_max']
            ans += self.moment(L,self.pcs,self.pcs+2,U)-self.moment(L,p,r,U)
        return ans

    def common(self,L):
        q = 1+math.exp(L/4)/4
        gh = min(1,R1*q/H,R2*q*q/(H*H))
        low = 2*math.exp(-L/2)*H*LOGH*(1-gh)
        eps = 4*math.exp(-L/4)
        pp = MAXIMUM*math.sqrt(1+eps)*(L+math.log1p(eps))**2*math.exp(-L/4)/(8*math.log(2))
        trivial = math.exp(-3*L)/(1-math.exp(-2*L))
        return low,pp,trivial

    def evaluate(self,L,variant=None):
        v = variant or {}
        p,r,r2,r3 = self.parameters(v)
        weights = 2*L*self.sw*np.exp((self.sigma-1)*L)
        B1 = float(np.dot(weights*self.c,self.main_moment(L,v)))*v.get('scale',1)
        B2 = float(np.dot(weights,self.d))*float(self.moment(L,0,r2))
        B3 = float(np.dot(weights,self.e))*float(self.moment(L,0,r3))
        baseline = 2*math.exp(-L/2)*float(self.moment(L,1,1))
        low,pp,trivial = self.common(L)
        other = baseline+low+pp+trivial
        floor = B2+B3+other
        return dict(L=L,delta=B1+floor,B1=B1,B2=B2,B3=B3,
                    baseline=baseline,low=low,prime_powers=pp,trivial=trivial,
                    floor_without_main=floor,critical_main_coefficient=(1-floor)/B1)

    def cell_upper(self,left,right,v):
        # This is an analytic endpoint envelope evaluated in floats, not Arb.
        # L*exp((sigma-1)L) decreases for L>=113.1 and sigma<=7/8.
        _,_,r2,r3 = self.parameters(v)
        weights = 2*left*self.sw*np.exp((self.sigma-1)*left)
        B1 = float(np.dot(weights*self.c,self.main_moment(right,v)))*v.get('scale',1)
        B2 = float(np.dot(weights,self.d))*float(self.moment(right,0,r2))
        B3 = float(np.dot(weights,self.e))*float(self.moment(right,0,r3))
        baseline = 2*math.exp(-left/2)*float(self.moment(right,1,1))
        low,_,trivial = self.common(left)
        eps = 4*math.exp(-left/4)
        pp = MAXIMUM*math.sqrt(1+eps)*(right+math.log1p(eps))**2*math.exp(-left/4)/(8*math.log(2))
        floor = B2+B3+baseline+low+pp+trivial
        return dict(left=left,right=right,delta=B1+floor,
                    critical_main_coefficient=(1-floor)/B1)

    def cell_survey(self,left,right,v,width=.125):
        grid = np.r_[np.arange(left,right,width),right]
        rows = [self.cell_upper(float(a),float(b),v) for a,b in zip(grid,grid[1:])]
        return dict(width=width,worst=max(rows,key=lambda d:d['delta']),
                    minimum_coefficient_factor=min(row['critical_main_coefficient'] for row in rows),
                    all_cells_below_one=all(row['delta']<1 for row in rows),
                    float_evaluation_not_certificate=True)

    def threshold(self,v):
        # Above L_FLAT analytic monotonicity is established in the companion note.
        end = max(L_FLAT,113.1)
        transition = minimize_scalar(lambda L: -self.evaluate(L,v)['delta'],
                                     bounds=(113.1,end),method='bounded',
                                     options={'xatol':1e-9})
        candidates = [(113.1,self.evaluate(113.1,v)['delta']),
                      (end,self.evaluate(end,v)['delta']),
                      (float(transition.x),float(-transition.fun))]
        peak = max(candidates,key=lambda pair:pair[1])
        if self.evaluate(end,v)['delta'] >= 1:
            high = end+20
            while self.evaluate(high,v)['delta'] >= 1 and high < 800:
                high += 20
            root = brentq(lambda L:self.evaluate(L,v)['delta']-1,end,high,xtol=2e-9)
        elif peak[1] <= 1:
            root = None
        else:
            root = brentq(lambda L:self.evaluate(L,v)['delta']-1,peak[0],end,xtol=2e-9)
        answer = dict(last_threshold_above_113_1=root,
                    transition_peak_search=dict(L=peak[0],delta=peak[1]),
                    all_ge_113_1_sampled_pass=peak[1]<1,
                    transition_is_float_search_not_certificate=True)
        if 'height_log_max' in v:
            grid = np.r_[np.arange(113.1,372,1.0),372.0]
            values = [self.evaluate(float(L),v)['delta'] for L in grid]
            crossings = []
            for a,b,fa,fb in zip(grid,grid[1:],values,values[1:]):
                if (fa-1)*(fb-1)<0:
                    crossings.append(brentq(lambda L:self.evaluate(L,v)['delta']-1,a,b,xtol=2e-9))
            peak_index = int(np.argmax(values))
            lo,hi = grid[max(0,peak_index-1)],grid[min(len(grid)-1,peak_index+1)]
            opt = minimize_scalar(lambda L:-self.evaluate(L,v)['delta'],bounds=(lo,hi),method='bounded')
            answer.update(last_threshold_above_113_1=max(crossings) if crossings else None,
                          crossings=crossings,finite_height_peak=dict(L=float(opt.x),delta=float(-opt.fun)),
                          all_ge_113_1_sampled_pass=max(values)<1,
                          all_L_monotonicity_not_claimed=True)
        return answer

    def fourier_budget(self,L,v=None,step=1/16,W=512):
        """Sampled monotone envelope of exact sinc factors plus Mellin error.

        Not a rigorous continuous envelope: grid maxima can miss local peaks.
        Positive-height cumulative count is integrated by right endpoint sums;
        the full quadratic tail from W/eps to infinity is included analytically.
        """
        v = v or {}
        eps = 4*math.exp(-L/4)
        q = 1+1/eps
        wh = eps*H
        w = np.unique(np.r_[np.arange(0,W+step/2,step),wh])
        w = w[w <= W]
        old = np.ones_like(w)
        old[1:] = np.minimum(1,np.minimum(R1*(1+eps)/w[1:],R2*(1+eps)**2/w[1:]**2))
        exact = np.abs(np.sinc(w/(16*math.pi))*np.sinc(7*w/(16*math.pi)))
        # M2=1/3-ab/6=121/384. The extra factor 1/2 is from log(1+eps*v).
        raw = np.minimum(old,exact+eps*(.5+w*121/768))
        raw[-1] = old[-1]
        g = np.maximum.accumulate(raw[::-1])[::-1]
        h_index = int(np.flatnonzero(w==wh)[0])
        low = 2*math.exp(-L/2)*H*LOGH*(1-g[h_index])
        positions = w[h_index+1:]
        drops = g[h_index:-1]-g[h_index+1:]
        p,r,r2,r3 = self.parameters(v)
        weights = L*self.sw*np.exp((self.sigma-1)*L)
        C1 = weights*self.c*v.get('scale',1)
        C2,C3 = float(weights@self.d),float(weights@self.e)
        finite = np.zeros(4)
        for offset in range(0,len(positions),512):
            u = np.log(positions[offset:offset+512]/eps)
            mass = drops[offset:offset+512]
            main = np.exp(u[:,None]*p+np.log(u[:,None])*r)@C1
            vals = np.array([main,C2*u**r2,C3*u**r3,np.exp(-L/2+u)*u])
            finite += 2*(vals@mass)
        U = math.log(W/eps)
        factor = 4*R2*q*q
        tail = factor*np.array([C1@self.tail(U,p,r),C2*self.tail(U,0,r2),
                               C3*self.tail(U,0,r3),math.exp(-L/2)*self.tail(U,1,1)])
        _,pp,trivial = self.common(L)
        components = finite+tail
        return dict(L=L,step=step,W=W,delta=float(sum(components)+low+pp+trivial),
                    B1=float(components[0]),B2=float(components[1]),B3=float(components[2]),
                    baseline=float(components[3]),low=low,prime_powers=pp,trivial=trivial,
                    full_height_tail=float(sum(tail)),sampled_envelope_not_certificate=True)


def compute(with_fourier=True):
    budget, refined = Budget(32),Budget(64)
    result = dict(schema='legendre-k4-far-redesign-round5-v1',status='COUNTERFACTUAL_FLOAT_EXPLORATION',
                  no_new_certified_interval=True, H=H,L_flat=L_FLAT,anchors=ANCHORS,
                  kernel=dict(a='1/8',b='7/8',R1='16/7',R2='256/7',maximum='8/7'),
                  sigma_quadrature_orders=[32,64],height_method='finite Gauss-Legendre + full incomplete-gamma tail',
                  versions=dict(numpy=np.__version__,scipy=scipy.__version__),variants={})
    for name,v in VARIANTS.items():
        values = [budget.evaluate(L,v) for L in ANCHORS]
        checks = [refined.evaluate(L,v) for L in ANCHORS]
        threshold = budget.threshold(v)
        root = threshold['last_threshold_above_113_1']
        if root is not None:
            threshold['refined_delta_at_root'] = refined.evaluate(root,v)['delta']
        result['variants'][name] = dict(parameters=v,anchors=values,threshold=threshold,
                  max_relative_order_comparison=max(abs(a['delta']/b['delta']-1) for a,b in zip(values,checks)))
    inverses = []
    for L in ANCHORS[:4]:
        base = budget.evaluate(L)
        logfree = budget.evaluate(L,dict(main_log_free=True))
        loss = None
        if logfree['delta'] < 1:
            loss = brentq(lambda r:budget.evaluate(L,dict(remove_logs=r))['delta']-1,0,3,xtol=1e-10)
        inverses.append(dict(L=L,critical_main_coefficient=base['critical_main_coefficient'],
                             needed_coefficient_reduction_factor=1/base['critical_main_coefficient'],
                             critical_removed_main_log_power=loss,
                             coefficient_floor=base['floor_without_main'],
                             log_free_delta=logfree['delta']))
    result['inverse_targets'] = inverses
    result['global_coefficient_transition'] = budget.cell_survey(113.1,L_FLAT,{},width=1/64)
    result['mixed_transition_cells'] = {name:budget.cell_survey(113.1,L_FLAT,v,width=1/64)
        for name,v in VARIANTS.items() if v.get('main_log_free') and 'height_log_max' not in v}
    result['finite_height_cell_surveys'] = {
        name:budget.cell_survey(113.1,372,v,width=.25)
        for name,v in VARIANTS.items() if 'height_log_max' in v and v.get('main_log_free')}
    result['target_150_finite_height_cells'] = budget.cell_survey(
        150.0,372.0,VARIANTS['cut_0.71875_remove_log_squared_height_100'],width=.25)
    u0 = LOGH
    result['monotone_rates_at_L_flat'] = dict(
        main_cs=1/24-3/(4*u0)-1/L_FLAT,
        main_density_hypothesis=1/16-3/(4*u0)-1/L_FLAT,
        main_huxley=7/104-3/(4*u0)-1/L_FLAT,
        B2=1/8-2/(4*u0)-1/L_FLAT,B3=1/8-1/(4*u0)-1/L_FLAT,
        baseline=1/4-1/(4*u0),prime_powers=1/4-2/L_FLAT)
    if with_fourier:
        result['fourier_comparisons'] = {}
        for name in ['current_CS_v2','remove_main_log_squared','main_log_free',
                     'density_hypothesis_old_logs','huxley_old_logs']:
            result['fourier_comparisons'][name] = [budget.fourier_budget(L,VARIANTS[name]) for L in ANCHORS[:4]]
        result['fourier_refinement'] = [refined.fourier_budget(L,step=1/32) for L in [120.0,200.0]]
        result['fourier_thresholds'] = {}
        for name in ['current_CS_v2','remove_main_log_squared',
                     'density_hypothesis_old_logs','huxley_old_logs']:
            trap = result['variants'][name]['threshold']['last_threshold_above_113_1']
            root = brentq(lambda L:budget.fourier_budget(L,VARIANTS[name])['delta']-1,
                          max(120,trap-15),trap+2,xtol=1e-7)
            result['fourier_thresholds'][name] = dict(
                root=root,refined_delta_at_root=refined.fourier_budget(root,VARIANTS[name],step=1/32)['delta'],
                local_root_only_not_whole_L_certificate=True)
    result['source_hashes'] = {p:digest(ROOT/p) for p in DEPENDENCIES}
    result['script_sha256'] = digest(__file__)
    result['proof_sha256'] = digest(PROOF) if PROOF.exists() else None
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify',action='store_true')
    parser.add_argument('--quick',action='store_true',help='Print anchor/threshold summary without writing')
    args = parser.parse_args()
    fresh = compute(not args.quick)
    if args.quick:
        print(json.dumps({k:dict(delta=[v['delta'] for v in row['anchors']],threshold=row['threshold'])
                          for k,row in fresh['variants'].items()},indent=2))
        print(json.dumps(fresh['inverse_targets'],indent=2))
        print('L_FLAT',L_FLAT,'RATES',fresh['monotone_rates_at_L_flat'])
    elif args.verify:
        saved = json.loads(OUTPUT.read_text(encoding='utf-8'))
        if saved != fresh:
            raise ValueError('Floating replay differs; inspect numerical versions and hashes')
        print('REPLAY_MATCHED; floating counterfactual exploration only, not a certificate')
    else:
        OUTPUT.write_text(json.dumps(fresh,indent=2)+'\n',encoding='utf-8')
        print('SAVED '+str(OUTPUT))


if __name__ == '__main__':
    main()
