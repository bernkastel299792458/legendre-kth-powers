"""Arb certificate for QRH(7/8), k=6, 167 <= log(x) <= 400.

Uses a trapezoid weight, explicitly assumes CS v2 Corollary 1, and uses
finite RH through 3e12. CS v2 is a preprint input, not a refereed theorem here.
All cells use common pointwise envelopes and positive Stieltjes upper sums.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import time
from datetime import datetime, timezone, timedelta
from fractions import Fraction
from pathlib import Path

import flint
from flint import arb, ctx

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / 'results' / 'smooth_k6_certificate.json'
SCHEMA = 'legendre-k6-smooth-v2-refined'
SOURCE = 'https://arxiv.org/html/2507.15184v2'
RH_SOURCE = 'https://arxiv.org/abs/2004.09765'
CS_ROWS = (
    ('5.069','9.461','167.8'), ('6.046','9.168','162.6'),
    ('7.077','8.875','157.4'), ('8.185','8.582','152.2'),
    ('9.387','8.290','147.0'), ('10.70','7.997','141.9'),
    ('12.11','7.704','136.7'), ('13.66','7.411','131.5'),
    ('15.35','7.118','126.3'), ('17.21','6.826','121.1'),
    ('19.31','6.533','115.9'), ('21.77','6.240','110.7'),
)
KERNEL = dict(a='1/32', b='31/32', R1='64/31', R2='4096/31', maximum='32/31')
TARGET_UPPER = Fraction(47,50)
CERTIFIED_SCALE = Fraction(53,50)

def require(condition, message):
    if not condition:
        raise ValueError(message)

def A(value):
    value = Fraction(value)
    return arb(value.numerator)/value.denominator

def integer(v, ceiling=False):
    result = (v.ceil() if ceiling else v.floor()).unique_fmpz()
    require(result is not None, 'Unresolved Arb integer rounding')
    return int(result)

def upper(v):
    return str(Fraction(integer(v*10**24, True), 10**24))

def rational_interval(v):
    return [str(Fraction(integer(v*10**24),10**24)),upper(v)]

def kernel(q, u):
    z = q*(-u).exp()
    return arb(1).min(A(KERNEL['R1'])*z).min(A(KERNEL['R2'])*z*z)

def sigma_terms(la, denominator):
    require(denominator >= 32 and denominator % 32 == 0, 'Invalid sigma grid')
    terms, dsum, esum = [], arb(0), arb(0)
    for i in range(denominator//2, 7*denominator//8):
        lo, hi = arb(i)/denominator, arb(i+1)/denominator
        row = i*32//denominator - 16
        require(Fraction(i,denominator) >= Fraction(16+row,32), 'Source row lower')
        require(Fraction(i+1,denominator) <= Fraction(17+row,32), 'Source row upper')
        c,d,e = (arb(v) for v in CS_ROWS[row])
        # Integrate the positive exponential weight exactly; N(s,T)<=N(lo,T).
        weight = ((hi-1)*la).exp() - ((lo-1)*la).exp()
        require(weight > 0, 'Positive sigma weight unresolved')
        p = 3*(1-lo)/(2-lo)
        terms.append((weight*c,p))
        dsum += weight*d
        esum += weight*e
    return terms, dsum, esum

def cumulative_parts(la, u, terms, dsum, esum):
    # Only called for exp(u)>=H, where CS v2 and N(T)<=T log(T) apply.
    main = arb(0)
    v = u + u.log()
    for coefficient,p in terms:
        main += coefficient*(p*v).exp()
    return u*u*main, u*u*dsum+esum*u, (-la/2+u).exp()*u

def cumulative(la, u, terms, dsum, esum):
    return sum(cumulative_parts(la,u,terms,dsum,esum),arb(0))

def height_tail_parts(la, q, U, terms, dsum, esum):
    # Tail of the Stieltjes integral, including residual weight of lower zeros.
    main = arb(0)
    logU = U.log()
    for coefficient,p in terms:
        denominator = 2-p-(p+2)/U
        require(denominator > 0, 'Tail logarithmic-tangent denominator')
        main += coefficient*((p-2)*U+(p+2)*logU).exp()/denominator
    baseline = (-la/2-U).exp()*(U+1)
    lower = (-2*U).exp()*(dsum*(U*U/2+U/2+arb(1)/4)
                                  + esum*(U/2+arb(1)/4))
    factor=4*A(KERNEL['R2'])*q*q
    return factor*main, factor*lower, factor*baseline

def height_tail(la,q,U,terms,dsum,esum):
    return sum(height_tail_parts(la,q,U,terms,dsum,esum),arb(0))

def sensitivity(B1, B23, other):
    """Exact affine dependence of this fixed envelope on CS table constants.

    Increasing only B1 by c gives c*B1+B23+other; increasing all three
    columns gives c*(B1+B23)+other. Critical factors describe this envelope,
    not the largest factor for which the prime theorem or another method holds.
    """
    require(B1>0 and B23>=0 and other>=0,'Sensitivity component signs')
    one=(1-B23-other)/B1
    all_three=(1-other)/(B1+B23)
    scale=A(CERTIFIED_SCALE)
    one_scaled=scale*B1+B23+other
    all_scaled=scale*(B1+B23)+other
    return dict(
        decomposition=dict(B1_ball=B1.str(50),B23_ball=B23.str(50),other_ball=other.str(50)),
        critical_factor_B1_only=rational_interval(one),
        critical_factor_all_three=rational_interval(all_three),
        tested_scale=str(CERTIFIED_SCALE),
        B1_only_scaled_upper=upper(one_scaled),all_three_scaled_upper=upper(all_scaled),
        B1_only_scaled_passed=bool(one_scaled<1),all_three_scaled_passed=bool(all_scaled<1))

def certify_cell(left, right, sigma_denominator=4096, height_denominator=64):
    left,right = Fraction(left),Fraction(right)
    require(167 <= left < right <= 400, 'Cell outside target domain')
    require(height_denominator > 0, 'Invalid height grid')
    la,lb = A(left),A(right)
    q = 1+(lb/6).exp()/6
    logq = q.log()
    H = arb('3000000000000')
    logH = H.log()
    platform_end = logq+A(KERNEL['R1']).log()
    # If H lies on the flat part, use a rational starting point below its end.
    start_index = integer(platform_end*height_denominator)
    candidate = arb(start_index)/height_denominator
    if candidate > logH:
        start = candidate
        require(kernel(q,start) == 1, 'Flat kernel start')
        low = arb(0)
        start_tag = str(Fraction(start_index,height_denominator))
    else:
        start = logH
        # Finite RH: every zero at t<=H has beta=1/2.
        low = 2*(-la/2).exp()*H*logH*(1-kernel(q,logH))
        require(low >= 0, 'Low-height contribution sign')
        start_tag = 'log(3000000000000)'
    require(start_tag == 'log(3000000000000)' or start > logH, 'Density height domain')
    quadratic_start = logq+(A(KERNEL['R2'])/A(KERNEL['R1'])).log()
    end_index = max(integer((quadratic_start+12)*height_denominator,True),
                    integer((logH+12)*height_denominator,True))
    end = arb(end_index)/height_denominator
    require(end >= quadratic_start, 'Quadratic kernel tail domain')
    terms,dsum,esum = sigma_terms(la,sigma_denominator)
    first_index = integer(start*height_denominator)+1
    previous = kernel(q,start)
    finite_parts = [arb(0),arb(0),arb(0)]
    for i in range(first_index,end_index+1):
        u = arb(i)/height_denominator
        current = kernel(q,u)
        mass = previous-current
        require(mass >= 0, 'Kernel positive mass unresolved')
        for j,value in enumerate(cumulative_parts(la,u,terms,dsum,esum)):
            finite_parts[j] += 2*value*mass
        previous = current
    tail_parts=height_tail_parts(la,q,end,terms,dsum,esum)
    finite=sum(finite_parts,arb(0))
    tail=sum(tail_parts,arb(0))
    eps = 6*(-la/6).exp()
    pp = A(KERNEL['maximum'])*(1+eps).sqrt()*(lb+(1+eps).log())**2
    pp *= (-la/3).exp()/(12*arb(2).log())
    trivial = (-3*la).exp()/(1-(-2*la).exp())
    delta = low+finite+tail+pp+trivial
    analysis=sensitivity(finite_parts[0]+tail_parts[0],finite_parts[1]+tail_parts[1],
                         low+finite_parts[2]+tail_parts[2]+pp+trivial)
    require(delta.is_finite(), 'Nonfinite ball')
    return dict(left=str(left),right=str(right),passed=bool(delta<1),
        delta_upper_rational=upper(delta),delta_ball=delta.str(40),
        low_zero_ball=low.str(30),finite_zero_ball=finite.str(35),
        height_tail_ball=tail.str(30),prime_power_ball=pp.str(30),
        trivial_ball=trivial.str(30),height_start=start_tag,
        height_end=str(Fraction(end_index,height_denominator)),
        height_cells=end_index-first_index+1,sigma_cells=len(terms),sensitivity=analysis)

def sensitivity_summary(cells):
    result=dict(tested_scale=str(CERTIFIED_SCALE),
        scope='Uniform changes to CS Table 1 B1 alone or B1/B2/B3 together, with every other input and envelope parameter fixed.')
    for mode,key in [('B1_only','critical_factor_B1_only'),('all_three','critical_factor_all_three')]:
        result[f'{mode}_critical_factor_interval']=[
            str(min(Fraction(c['sensitivity'][key][j]) for c in cells)) for j in (0,1)]
        upper_key=f'{mode}_scaled_upper'
        result[f'{mode}_scaled_maximum_upper']=str(max(Fraction(c['sensitivity'][upper_key]) for c in cells))
        result[f'{mode}_all_passed']=all(c['sensitivity'][f'{mode}_scaled_passed'] for c in cells)
    return result

def verify_certificate(path=OUTPUT):
    saved=json.loads(Path(path).read_text(encoding='utf-8'))
    require(saved['schema']==SCHEMA,'Certificate schema')
    require(saved['status']=='ALL_CELLS_PASSED', 'Saved status')
    require(saved['k']==6 and saved['log_x_interval']==['167','400'], 'Target')
    require(saved['script_sha256']==hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), 'Script hash')
    require(saved['source']==dict(url=SOURCE,constants=[list(r) for r in CS_ROWS],finite_rh=RH_SOURCE,H='3000000000000'), 'Sources')
    require(saved['kernel']==KERNEL, 'Kernel')
    require(saved['target_upper']==str(TARGET_UPPER),'Envelope target')
    require(saved['source_publication_status']=='CS v2 preprint explicitly assumed','CS premise status')
    require(isinstance(saved['precision_bits'],int) and 128<=saved['precision_bits']<=4096,'Precision')
    ctx.prec=saved['precision_bits']
    cells=saved['cells']
    require(len(cells)==saved['number_of_cells'] and cells, 'Cell count')
    require(Fraction(cells[0]['left'])==167 and Fraction(cells[-1]['right'])==400,'Endpoints')
    for old,new in zip(cells,cells[1:]):
        require(Fraction(old['right'])==Fraction(new['left']), 'Coverage gap or overlap')
    for index,cell in enumerate(cells,1):
        replay=certify_cell(cell['left'],cell['right'],saved['sigma_denominator'],saved['height_denominator'])
        bound=Fraction(cell['delta_upper_rational'])
        require(cell['passed'] is True and replay['passed'] and 0<bound<1,'Failed cell')
        require(bound<TARGET_UPPER,'Refined target not attained')
        if Fraction(cell['right'])>176 and Fraction(cell['left'])<182:
            require(Fraction(cell['right'])-Fraction(cell['left'])<=Fraction(1,4),'Critical L mesh too coarse')
        require(Fraction(replay['delta_upper_rational'])<=bound,'Saved bound too small')
        for key in ('height_start','height_end','height_cells','sigma_cells'):
            require(cell[key]==replay[key],f'Metadata mismatch: {key}')
        require(cell['sensitivity']==replay['sensitivity'],'Sensitivity replay mismatch')
        require(replay['sensitivity']['B1_only_scaled_passed'] and replay['sensitivity']['all_three_scaled_passed'],
                'Uniform scaling test failed')
        if index%20==0: print(f'Verified {index}/{len(cells)}',flush=True)
    worst=max(cells,key=lambda c:Fraction(c['delta_upper_rational']))
    require(saved['worst_cell']==worst,'Worst cell metadata')
    require(saved['sensitivity_summary']==sensitivity_summary(cells),'Global sensitivity metadata')
    return dict(status='VERIFIED',k=6,number_of_cells=len(cells),log_x_interval=['167','400'],
        worst_upper_rational=worst['delta_upper_rational'],
        minimum_margin_rational=str(1-Fraction(worst['delta_upper_rational'])),
        sensitivity_summary=saved['sensitivity_summary'],
        script_sha256=saved['script_sha256'],certificate_sha256=hashlib.sha256(Path(path).read_bytes()).hexdigest())

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--single',nargs=2)
    parser.add_argument('--verify',nargs='?',const=str(OUTPUT))
    parser.add_argument('--precision',type=int,default=256)
    parser.add_argument('--sigma-denominator',type=int,default=4096)
    parser.add_argument('--height-denominator',type=int,default=64)
    args=parser.parse_args()
    started=time.monotonic()
    if args.verify:
        print(json.dumps(verify_certificate(args.verify),indent=2));return
    ctx.prec=args.precision
    if args.single:
        print(json.dumps(certify_cell(*args.single,args.sigma_denominator,args.height_denominator),indent=2));return
    initial=[]
    for left,right,width in ((167,176,Fraction(1)),(176,182,Fraction(1,4)),
                             (182,190,Fraction(1)),(190,220,Fraction(2)),(220,400,Fraction(5))):
        v=Fraction(left)
        while v<right:
            next_v=min(v+width,Fraction(right))
            initial.append((v,next_v));v=next_v
    cells,rejected=[],[]
    def visit(left,right):
        cell=certify_cell(left,right,args.sigma_denominator,args.height_denominator)
        if cell['passed'] and Fraction(cell['delta_upper_rational'])<TARGET_UPPER:
            cells.append(cell)
            print(f'PASS [{left},{right}] {cell["delta_ball"]}',flush=True)
        else:
            rejected.append(cell)
            require(right-left>Fraction(1,64),f'No certified margin in {left},{right}')
            middle=(left+right)/2
            visit(left,middle);visit(middle,right)
    for left,right in initial: visit(left,right)
    worst=max(cells,key=lambda c:Fraction(c['delta_upper_rational']))
    saved=dict(schema=SCHEMA,status='ALL_CELLS_PASSED',k=6,log_x_interval=['167','400'],
        created=datetime.now(timezone(timedelta(hours=8))).isoformat(),
        conditional_inputs=['QRH(7/8)','CS v2 Corollary 1 / equation (11)','Platt-Trudgian finite RH'],
        source_publication_status='CS v2 preprint explicitly assumed',
        source=dict(url=SOURCE,constants=[list(r) for r in CS_ROWS],finite_rh=RH_SOURCE,H='3000000000000'),
        kernel=KERNEL,precision_bits=args.precision,sigma_denominator=args.sigma_denominator,
        height_denominator=args.height_denominator,python_flint=flint.__version__,
        number_of_cells=len(cells),cells=cells,worst_cell=worst,rejected_coarse_cells=rejected,
        target_upper=str(TARGET_UPPER),sensitivity_summary=sensitivity_summary(cells),
        script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        elapsed_seconds=time.monotonic()-started,
        scope='Continuous real-x segment only; analytic proof in research/SMOOTH_K6_CERTIFICATE.md')
    OUTPUT.write_text(json.dumps(saved,indent=2)+'\n',encoding='utf-8')
    print(f'Saved {OUTPUT}; {len(cells)} cells; worst {worst["delta_ball"]}')

if __name__=='__main__':main()
