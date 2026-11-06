"""Low-dimensional signed Jacobi kernels: exploratory LP and full-budget scan.

NOT A CERTIFICATE: frequency suprema, L1 roots and density quadratures are
floating-point. Finite frequency sampling alone is never claimed to bound
all frequencies. The infinite high-frequency tail is included analytically.
"""
from __future__ import annotations

import hashlib
import json
import math
import sys
import time
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path

import numpy as np
from numpy.polynomial import Polynomial
from scipy import sparse
from scipy.optimize import linprog, minimize
from scipy.special import jacobi, spherical_jn

sys.dont_write_bytecode=True
import density_envelope_round2 as density

ROOT=Path(__file__).resolve().parents[1]
L=120.


def polynomial_basis(dimension):
    """Normalized real-space basis, mass of first element exactly 1 analytically."""
    weight=Polynomial([0,0,30,-60,30])
    z=Polynomial([-1,2])
    return tuple(weight*Polynomial(jacobi(2*j,2,2).coef[::-1])(z)
                 for j in range(dimension+1))


def fourier_basis(w,dimension):
    w=np.asarray(w,float)
    z=w/2
    result=np.zeros((len(w),dimension+1))
    active=w!=0
    for j in range(dimension+1):
        result[active,j]=((-1)**j*7.5*(2*j+1)*(2*j+2)
             *spherical_jn(2*j+2,z[active])/z[active]**2)
    result[~active,0]=1.
    return result


def real_unit_roots(poly):
    roots=poly.roots()
    real=sorted(float(z.real) for z in roots
                if abs(z.imag)<1e-7 and 1e-10<z.real<1-1e-10)
    # Remove duplicated representations of multiple roots.
    return np.array([v for i,v in enumerate(real) if not i or v-real[i-1]>1e-8])


def absolute_integral(poly,extra_weight=None):
    cuts=np.r_[0.,real_unit_roots(poly),1.]
    primitive=(poly if extra_weight is None else poly*extra_weight).integ()
    # extra_weight is nonnegative on the unit interval in all calls.
    return float(np.abs(np.diff(primitive(cuts))).sum())


def kernel_stats(coefficients):
    coefficients=np.asarray(coefficients,float)
    basis=polynomial_basis(len(coefficients))
    poly=sum((c*p for c,p in zip(np.r_[1.,coefficients],basis)),Polynomial([0.]))
    R=[absolute_integral(poly.deriv(j)) for j in range(3)]
    R[0]=max(1.,R[0])
    R3=absolute_integral(poly.deriv(3))+abs(poly.deriv(2)(0))+abs(poly.deriv(2)(1))
    critical=np.r_[0.,real_unit_roots(poly.deriv()),1.]
    positive_max=max(0.,float(np.max(poly(critical))))
    absolute_moment2=absolute_integral(poly,Polynomial([0,0,1]))
    mass=float(poly.integ()(1)-poly.integ()(0))
    return dict(coefficients=coefficients.tolist(),R=R+[R3],
        positive_max=positive_max,absolute_moment2=absolute_moment2,
        mass_by_polynomial_evaluation=mass,
        minimum=float(np.min(poly(critical))),
        positive_mass=(R[0]+1)/2,negative_mass=(R[0]-1)/2)


def frequency_grid(L,end=512.,step=.125):
    epsilon=4*math.exp(-L/4)
    first=64*epsilon
    small=np.geomspace(first,.05,140)
    linear=np.arange(.05,end,step)
    special=[density.H*epsilon*math.exp(d)
             for d in (0,1e-8,1e-6,1e-5,1e-4,.001,.01,.1)]
    return np.unique(np.r_[small,linear,end,[w for w in special if first<w<end]])


def cumulative(L,u,order=16):
    parts=[]
    for i in range(0,len(u),256):
        baseline,rows=density.cumulative_terms(L,u[i:i+256],
                            mode='envelope_monotone',sigma_order=order)
        parts.append(baseline+rows.sum(axis=1))
    return np.concatenate(parts)


@dataclass
class Budget:
    L: float
    end: float
    step: float
    sigma_order: int
    w: np.ndarray
    phi: np.ndarray
    fourier: np.ndarray
    tail_per_R3: float
    tail_adjusted_per_R3: float
    prime_power_per_max: float
    low_height_per_R0: float
    trivial_per_R0: float
    epsilon: float
    height_end: float


def make_budget(L=120.,dimension=3,end=512.,step=.125,sigma_order=16):
    if L!=120. or not 1<=dimension<=3:
        raise ValueError('Focused experiment: L=120, dimension1..3')
    epsilon=4*math.exp(-L/4)
    w=frequency_grid(L,end,step)
    u=np.log(w/epsilon)
    u[0]=math.log(64)  # remove roundoff in a domain guard
    phi=cumulative(L,u,sigma_order)
    if np.min(np.diff(phi)) < -1e-10:
        raise AssertionError('Cumulative majorant must be increasing on this grid')
    U=max(u[-1]+55,(3*math.log((1+epsilon)/epsilon)-L/8+80)/2)
    nodes,weights=np.polynomial.legendre.leggauss(24)
    cuts=np.linspace(u[-1],U,math.ceil(U-u[-1])+1)
    centers,half=(cuts[:-1]+cuts[1:])/2,np.diff(cuts)/2
    us=(centers[:,None]+half[:,None]*nodes).ravel()
    ws=(half[:,None]*weights).ravel()
    values=cumulative(L,us,sigma_order)
    logq=math.log((1+epsilon)/epsilon)
    finite_tail=2*np.dot(ws,values*3*np.exp(3*(logq-us)))
    infinite_tail=math.exp(math.log(3/math.pi)+3*logq-L/8-2*U
                            +math.log(U/2+.25))
    tail_per_R3=float(finite_tail+infinite_tail)
    tail_adjusted=tail_per_R3-2*phi[-1]*(1+epsilon)**3/end**3
    if tail_adjusted<=0:
        raise AssertionError('Tail integration by parts produced a negative coefficient')
    pp=math.sqrt(1+epsilon)*(L+math.log1p(epsilon))**2/(8*math.log(2))*math.exp(-L/4)
    low=2*math.exp(-L/2)*64*math.log(64)/(2*math.pi)
    trivial=math.exp(-3*L)/(-math.expm1(-2*L))
    return Budget(L,end,step,sigma_order,w,phi,fourier_basis(w,dimension),
                   tail_per_R3,tail_adjusted,pp,low,trivial,epsilon,U)


def evaluate(coefficients,budget,use_derivative_min=True):
    stats=kernel_stats(coefficients)
    R=np.array(stats['R'])
    v=np.r_[1.,coefficients]
    B=budget.fourier[:,:len(v)]@v
    error=budget.epsilon*(R[0]/2+budget.w*stats['absolute_moment2']/2)
    pointwise=np.abs(B)+error
    if use_derivative_min:
        ratio=(1+budget.epsilon)/budget.w
        old=np.min(R[:,None]*ratio[None,:]**np.arange(4)[:,None],axis=0)
        pointwise=np.minimum(pointwise,old)
    tail_value=R[3]*(1+budget.epsilon)**3/budget.end**3
    envelope=np.maximum.accumulate(np.r_[pointwise,tail_value][::-1])[::-1][:-1]
    # Right-end positive sum. A possible downward seam jump is included.
    finite=2*float(np.dot(budget.phi[1:],envelope[:-1]-envelope[1:]))
    seam=2*budget.phi[-1]*(envelope[-1]-tail_value)
    tail=R[3]*budget.tail_per_R3
    powers=stats['positive_max']*budget.prime_power_per_max
    low=R[0]*budget.low_height_per_R0
    trivial=R[0]*budget.trivial_per_R0
    total=finite+seam+tail+powers+low+trivial
    if not math.isfinite(total) or min(finite,seam,tail,powers,low,trivial)<-1e-10:
        raise FloatingPointError('Invalid nonnegative budget')
    return dict(**stats,delta=total,finite_zero_sum=finite,seam_jump=seam,
                high_frequency_tail=tail,prime_powers=powers,
                low_height_block=low,trivial_zeros=trivial,
                first_envelope_value=float(envelope[0]),tail_seam_value=tail_value,
                max_fourier_modulus_sample=float(np.max(np.abs(B))),
                sampling_end=budget.end,sampling_step=budget.step,
                sampling_points=len(budget.w),sigma_order=budget.sigma_order,
                derivative_min=use_derivative_min,
                status='EXPLORATORY_SAMPLED_SUP_NOT_CERTIFIED')


def optimize_lp(dimension,budget,nv=80,coefficient_limit=10000.,negative_center=None):
    """Convex finite LP, with all L1/BV/positive-max costs included.

    L1 values are quadrature auxiliary variables only in the LP. All resulting
    coefficients are reevaluated using real polynomial roots in evaluate().
    """
    nodes,weights=np.polynomial.legendre.leggauss(nv)
    v=(nodes+1)/2
    weights=weights/2
    basis=polynomial_basis(dimension)
    f=np.array([p(v) for p in basis]).T
    f3=np.array([p.deriv(3)(v) for p in basis]).T
    endpoint=np.array([p.deriv(2)(0) for p in basis])
    peakv=np.unique(np.r_[v,np.linspace(0,1,201)])
    peak=np.array([p(peakv) for p in basis]).T
    B=budget.fourier[:,:dimension+1]
    nw=len(budget.w)
    sizes=(dimension,nw,nv,nv,1,1)
    starts=np.cumsum((0,)+sizes)
    total=starts[-1]
    def block(rows,a=None,g=None,y=None,z=None,e=None,p=None):
        pieces=(a,g,y,z,e,p)
        return sparse.hstack([sparse.csr_matrix((rows,size)) if part is None
                              else sparse.csr_matrix(part)
                              for size,part in zip(sizes,pieces)],format='csr')
    matrices=[]
    rhs=[]
    err=budget.epsilon/2*(weights[None,:]+budget.w[:,None]*(weights*v*v)[None,:])
    for sign in (1.,-1.):
        matrices.append(block(nw,a=sign*B[:,1:],g=-sparse.eye(nw),y=err))
        rhs.append(-sign*B[:,0])
    monotone=sparse.diags([-np.ones(nw-1),np.ones(nw-1)],[0,1],shape=(nw-1,nw))
    matrices.append(block(nw-1,g=monotone)); rhs.append(np.zeros(nw-1))
    last=sparse.csr_matrix(([-1.],([0],[nw-1])),shape=(1,nw))
    tail_factor=(1+budget.epsilon)**3/budget.end**3
    matrices.append(block(1,g=last,z=(tail_factor*weights)[None,:],e=[[2*tail_factor]]))
    rhs.append(np.zeros(1))
    for sign in (1.,-1.):
        matrices.append(block(nv,a=sign*f[:,1:],y=-sparse.eye(nv))); rhs.append(-sign*f[:,0])
        matrices.append(block(nv,a=sign*f3[:,1:],z=-sparse.eye(nv))); rhs.append(-sign*f3[:,0])
        matrices.append(block(1,a=(sign*endpoint[1:])[None,:],e=[[-1.]])); rhs.append(np.array([-sign*endpoint[0]]))
    matrices.append(block(len(peakv),a=peak[:,1:],p=-np.ones((len(peakv),1))))
    rhs.append(-peak[:,0])
    if negative_center is not None:
        # Genuine signed control: the normalized kernel is <=-C at v=1/2.
        # This constrains the polynomial itself, not inflated L1 auxiliaries.
        center=np.array([p(.5) for p in basis])
        matrices.append(block(1,a=center[1:][None,:]))
        rhs.append(np.array([-float(negative_center)-center[0]]))
    objective=np.zeros(total)
    gweights=np.r_[2*budget.phi[1],2*np.diff(budget.phi[1:]),0.]
    objective[starts[1]:starts[2]]=gweights
    objective[starts[2]:starts[3]]=weights*(budget.low_height_per_R0+budget.trivial_per_R0)
    objective[starts[3]:starts[4]]=weights*budget.tail_adjusted_per_R3
    objective[starts[4]]=2*budget.tail_adjusted_per_R3
    objective[starts[5]]=budget.prime_power_per_max
    bounds=[(-coefficient_limit,coefficient_limit)]*dimension+[(0,None)]*(total-dimension)
    result=linprog(objective,A_ub=sparse.vstack(matrices,format='csr'),
                   b_ub=np.concatenate(rhs),bounds=bounds,method='highs')
    if not result.success:
        raise RuntimeError(result.message)
    a=result.x[:dimension]
    return dict(dimension=dimension,coefficients=a.tolist(),lp_objective=float(result.fun),
                negative_center=negative_center,
                coefficient_limit=coefficient_limit,coefficient_limit_hit=bool(np.any(abs(a)>.999*coefficient_limit)),
                frequency_points=nw,L1_quadrature_points=nv,
                exact_L1_evaluation=evaluate(a,budget,False),
                derivative_min_evaluation=evaluate(a,budget,True),
                solver_message=result.message)


def main():
    started=time.monotonic()
    budget=make_budget(dimension=3,end=512,step=.25,sigma_order=12)
    baseline=evaluate(np.zeros(3),budget)
    results=[]
    for dim in (1,2,3):
        result=optimize_lp(dim,budget)
        results.append(result)
        print('LP',dim,result['coefficients'],result['lp_objective'],
              result['derivative_min_evaluation']['delta'],flush=True)
    signed_control=optimize_lp(3,budget,negative_center=50.)
    print('signed control',signed_control['coefficients'],
          signed_control['derivative_min_evaluation']['delta'],
          'R0',signed_control['derivative_min_evaluation']['R'][0],flush=True)
    best=min(results,key=lambda r:r['derivative_min_evaluation']['delta'])
    start=np.pad(best['coefficients'],(0,3-best['dimension']))
    local=minimize(lambda a:evaluate(a,budget)['delta'],start,method='Nelder-Mead',
                   options={'maxiter':180,'xatol':1e-5,'fatol':1e-5})
    refined_coefficients=local.x
    print('Local',refined_coefficients,evaluate(refined_coefficients,budget)['delta'],flush=True)
    candidates=[('baseline',np.zeros(3))]
    candidates +=[(f'lp{r["dimension"]}',np.pad(r['coefficients'],(0,3-r['dimension']))) for r in results]
    candidates.append(('local3',refined_coefficients))
    candidates.append(('forced_signed3',np.array(signed_control['coefficients'])))
    refinements=[]
    for end,step,order in ((512.,.0625,24),(1024.,.03125,24)):
        fine=make_budget(dimension=3,end=end,step=step,sigma_order=order)
        group=[]
        for label,a in candidates:
            r=evaluate(a,fine)
            r['label']=label
            group.append(r)
            print('refine',end,step,label,r['delta'],'R0',r['R'][0],flush=True)
        refinements.append(dict(end=end,step=step,sigma_order=order,results=group))
    output=dict(status='EXPLORATORY_NOT_CERTIFIED',L=L,
        created=datetime.now(timezone.utc).isoformat(),
        kernel_family='v^2(1-v)^2*(1+sum a_j*P_(2j)^(2,2)(2v-1)); mass=1/30',
        normalized_fourier='(-1)^j*(15/2)*(2j+1)*(2j+2)*spherical_jn(2j+2,w/2)/(w/2)^2',
        mellin_error='epsilon*(R0/2+w*M2abs/2)',
        density='density_envelope_round2 envelope_monotone',
        code_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        density_code_sha256=hashlib.sha256(Path(density.__file__).read_bytes()).hexdigest(),
        baseline=baseline,linear_programs=results,forced_signed_control=signed_control,
        local_optimization=dict(coefficients=refined_coefficients.tolist(),success=bool(local.success),
                                message=str(local.message),evaluations=local.nfev,
                                result=evaluate(refined_coefficients,budget)),
        refinements=refinements,elapsed_seconds=time.monotonic()-started,
        limitations=['Discrete frequency supremum is not a continuous supremum certificate',
                     'LP derivative L1 uses quadrature; candidates reevaluated by floating polynomial roots',
                     'Density quadrature and tail evaluation are floating point',
                     'Finite dimensional and finite optimization only; no theorem about all signed kernels'])
    path=ROOT/'results/signed_kernel_round2.json'
    path.write_text(json.dumps(output,indent=2)+'\n',encoding='utf-8')
    print('Wrote',path,'seconds',output['elapsed_seconds'])


if __name__=='__main__':
    main()
