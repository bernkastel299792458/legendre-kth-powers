"""Arb point budget for a log-coordinate trapezoid and Fourier step majorant.

This is a separate candidate module, not part of verify_all. Rebased density
mode consumes the separately reviewed CS rebase derivation in ../rebase_density.py.
The global-L implication requires the accompanying analytic argument.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import runpy
import time
from fractions import Fraction
from pathlib import Path
from flint import arb,ctx

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
HELPER=ROOT/'code'/'certify_k4_round3.py'
HELPER_HASH='665413028150b9eafa96d51071e2864da5408086393b91d6ea8e956798e7ea16'
REBASE=HERE.parent/'rebase_density.py'
REBASE_HASH='82f66c796daa445cf7e8acbe9d768029a733c9f15c0253f844e6cf8fc493cc5f'
REBASE_PROOF=HERE.parent/'PROOF.md'
PROOF=HERE/'LOG_KERNEL_CANDIDATE.md'


def A(value):
    v=Fraction(value);return arb(v.numerator)/v.denominator


def upward(value,digits=40):
    n=(value.upper()*10**digits).ceil().unique_fmpz()
    if n is None:raise ValueError('Upper rounding unresolved')
    return Fraction(int(n),10**digits)


def kernel_steps(a=Fraction(1,8),denominator=128):
    b=1-a;delta=Fraction(1,10**38)
    left,right=-4*denominator,6*denominator
    R2=4/(a*b)
    W=arb(6).exp()
    tail=upward(A(1+delta)*A(R2)/W**2)
    raw=[]
    for i in range(left,right):
        lo=(arb(i)/denominator).exp();hi=(arb(i+1)/denominator).exp()
        w=lo.union(hi)
        p=(A(a)*w/2).sin()/(A(a)*w/2)
        p*=(A(b)*w/2).sin()/(A(b)*w/2)
        raw.append(min(1+delta,upward(abs(p)+A(delta))))
    levels=[None]*len(raw);current=tail
    for j in range(len(raw)-1,-1,-1):
        current=max(current,raw[j]);levels[j]=current
    atoms=[];previous=1+delta
    for j,value in enumerate(levels):
        assert previous>=value
        if previous>value:
            atoms.append((Fraction(left+j,denominator),previous-value))
        previous=value
    if previous>tail:atoms.append((Fraction(6),previous-tail))
    assert sum((mass for _,mass in atoms),Fraction(0))+tail==1+delta
    assert A(tail)*W**2>=A(1+delta)*A(R2)
    return atoms,tail,dict(a=str(a),b=str(b),delta=str(delta),log_w_min='-4',log_w_tail='6',
                           log_w_grid_denominator=denominator,raw_cells=len(raw),atoms=len(atoms),
                           finite_levels=[str(v) for v in levels],tail_value=str(tail),
                           atom_data=[dict(log_w=str(w),mass=str(m)) for w,m in atoms])


def calculate(L=360,sigma_denominator=32768,height_denominator=128,mode='rebased'):
    started=time.perf_counter();ctx.prec=256
    assert hashlib.sha256(HELPER.read_bytes()).hexdigest()==HELPER_HASH
    helper=runpy.run_path(str(HELPER))
    if mode=='rebased':
        assert hashlib.sha256(REBASE.read_bytes()).hexdigest()==REBASE_HASH
        rebase=runpy.run_path(str(REBASE))
        rows,details=rebase['constants']()
        helper['sigma_terms'].__globals__['CS_ROWS']=tuple(rows)
        threshold=arb(80)
        density_hash=hashlib.sha256(REBASE.read_bytes()).hexdigest()
    elif mode=='original':
        rows=helper['CS_ROWS'];details={};threshold=arb(3*10**12).log();density_hash=None
    else:raise ValueError('density mode')
    ell=(4*(-arb(L)/4).exp()).log1p();logq=-ell.log()
    epsilon=4*(-arb(L)/4).exp()
    atoms,tail_value,kernel=kernel_steps(denominator=height_denominator)
    delta=A(kernel['delta'])
    assert epsilon<delta and logq-4>threshold
    terms,dsum,esum=helper['sigma_terms'](arb(L),sigma_denominator)
    finite=[arb(0),arb(0),arb(0)]
    for logw,mass in atoms:
        u=logq+A(logw)
        parts=helper['cumulative_parts'](arb(L),u,terms,dsum,esum)
        for j,part in enumerate(parts):finite[j]+=2*A(mass)*part
    # K(w)=tail_value*(exp(6)/w)^2 for w>=exp(6).
    U=logq+6
    main=arb(0)
    for coefficient,p in terms:
        den=2-p-(p+2)/U
        assert den>0
        main+=coefficient*((p-2)*U+(p+2)*U.log()).exp()/den
    lower=(-2*U).exp()*(dsum*(U**2/2+U/2+arb(1)/4)+esum*(U/2+arb(1)/4))
    baseline=(-arb(L)/2-U).exp()*(U+1)
    factor=4*A(tail_value)*(2*U).exp()
    tail=[factor*main,factor*lower,factor*baseline]
    # Integral mass is x*ell*M_phi(ell)>=x*ell. Uniformly bound max phi=8/7.
    pp=A('8/7')*(-arb(L)/2+ell/2).exp()*(arb(L)+ell)**2/(2*arb(2).log()*ell)
    trivial=(-3*arb(L)).exp()/(1-(-2*arb(L)).exp())
    total=sum(finite,arb(0))+sum(tail,arb(0))+pp+trivial
    u0=logq-4
    rates=dict(main=arb(1)/24-3/(4*u0)-1/arb(L),baseline=arb(1)/4-1/(4*u0),
               B2=arb(1)/8-2/(4*u0)-1/arb(L),B3=arb(1)/8-1/(4*u0))
    # B3 includes the same exterior L factor as B2.
    rates['B3']-=1/arb(L)
    rates['prime_powers']=arb(1)/4-2/arb(L)
    assert all(v>0 for v in rates.values())
    return dict(status='POINT_BUDGET_PASSED_CANDIDATE' if total<1 else 'BOUND_NOT_BELOW_ONE',
                schema='k4-log-kernel-candidate-v1',
                full_k4_proved=False,L0=L,mode=mode,precision_bits=256,sigma_denominator=sigma_denominator,
                inputs=['QRH(7/8)','CS v2 Theorem 1, Corollary 5 and first Table 1 row' if mode=='rebased' else 'CS v2 Table 1',
                        'Finite RH to 3e12' if mode=='rebased' else 'Original table assumptions',
                        'Rosser total count and integrated explicit formula'],
                total_ball=total.str(55),upper_rational=str(upward(total,24)),
                finite_balls=[v.str(40) for v in finite],tail_balls=[v.str(40) for v in tail],
                prime_powers=pp.str(40),trivial=trivial.str(40),
                u0=u0.str(40),density_threshold=threshold.str(40),epsilon=epsilon.str(40),
                kernel=kernel,density_rows=[list(r) for r in rows],rebase_details=details,
                analytic_rate_balls={k:v.str(40) for k,v in rates.items()},
                helper_sha256=HELPER_HASH,density_script_sha256=density_hash,
                density_proof_sha256=hashlib.sha256(REBASE_PROOF.read_bytes()).hexdigest() if mode=='rebased' else None,
                proof_sha256=hashlib.sha256(PROOF.read_bytes()).hexdigest(),
                script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                elapsed_seconds=time.perf_counter()-started,
                scope='Arb point/majorant computation with a separate analytic derivation; not accepted into the primary proof chain or independently audited yet.')


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--L',type=int,default=360)
    p.add_argument('--sigma-denominator',type=int,default=32768)
    p.add_argument('--height-denominator',type=int,default=128)
    p.add_argument('--mode',choices=['rebased','original'],default='rebased')
    p.add_argument('--save',action='store_true')
    p.add_argument('--verify',action='store_true');args=p.parse_args()
    if args.save and args.verify:raise ValueError('Choose save or read-only verify')
    data=calculate(args.L,args.sigma_denominator,args.height_denominator,args.mode)
    path=HERE/f'log_kernel_{args.mode}_L{args.L}.json'
    if args.verify:
        saved=json.loads(path.read_text())
        saved.pop('elapsed_seconds');fresh=dict(data);fresh.pop('elapsed_seconds')
        if saved!=fresh:raise ValueError('Candidate replay or dependencies changed')
        print('VERIFIED_CANDIDATE_NOT_PRIMARY',path)
    elif args.save:
        path.write_text(json.dumps(data,indent=2)+'\n')
        print('SAVED',path)
    print(data['status'],data['total_ball'],'atoms',data['kernel']['atoms'],'seconds',data['elapsed_seconds'])


if __name__=='__main__':main()
