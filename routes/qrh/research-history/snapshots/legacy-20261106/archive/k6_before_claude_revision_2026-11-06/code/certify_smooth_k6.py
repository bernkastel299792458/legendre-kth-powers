"""Arb certificate for QRH(7/8), k=6, 167 <= log(x) <= 400.

Uses a trapezoid weight, CS v2 Corollary 1, and finite RH through 3e12.
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

def cumulative(la, u, terms, dsum, esum):
    # Only called for exp(u)>=H, where CS v2 and N(T)<=T log(T) apply.
    main = arb(0)
    v = u + u.log()
    for coefficient,p in terms:
        main += coefficient*(p*v).exp()
    return (-la/2+u).exp()*u + u*u*(main+dsum) + esum*u

def height_tail(la, q, U, terms, dsum, esum):
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
    return 4*A(KERNEL['R2'])*q*q*(baseline+main+lower)

def certify_cell(left, right, sigma_denominator=2048, height_denominator=32):
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
    finite = arb(0)
    for i in range(first_index,end_index+1):
        u = arb(i)/height_denominator
        current = kernel(q,u)
        mass = previous-current
        require(mass >= 0, 'Kernel positive mass unresolved')
        finite += 2*cumulative(la,u,terms,dsum,esum)*mass
        previous = current
    tail = height_tail(la,q,end,terms,dsum,esum)
    eps = 6*(-la/6).exp()
    pp = A(KERNEL['maximum'])*(1+eps).sqrt()*(lb+(1+eps).log())**2
    pp *= (-la/3).exp()/(12*arb(2).log())
    trivial = (-3*la).exp()/(1-(-2*la).exp())
    delta = low+finite+tail+pp+trivial
    require(delta.is_finite(), 'Nonfinite ball')
    return dict(left=str(left),right=str(right),passed=bool(delta<1),
        delta_upper_rational=upper(delta),delta_ball=delta.str(40),
        low_zero_ball=low.str(30),finite_zero_ball=finite.str(35),
        height_tail_ball=tail.str(30),prime_power_ball=pp.str(30),
        trivial_ball=trivial.str(30),height_start=start_tag,
        height_end=str(Fraction(end_index,height_denominator)),
        height_cells=end_index-first_index+1,sigma_cells=len(terms))

def verify_certificate(path=OUTPUT):
    saved=json.loads(Path(path).read_text(encoding='utf-8'))
    require(saved['status']=='ALL_CELLS_PASSED', 'Saved status')
    require(saved['k']==6 and saved['log_x_interval']==['167','400'], 'Target')
    require(saved['script_sha256']==hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), 'Script hash')
    require(saved['source']==dict(url=SOURCE,constants=[list(r) for r in CS_ROWS],finite_rh=RH_SOURCE,H='3000000000000'), 'Sources')
    require(saved['kernel']==KERNEL, 'Kernel')
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
        require(Fraction(replay['delta_upper_rational'])<=bound,'Saved bound too small')
        for key in ('height_start','height_end','height_cells','sigma_cells'):
            require(cell[key]==replay[key],f'Metadata mismatch: {key}')
        if index%20==0: print(f'Verified {index}/{len(cells)}',flush=True)
    worst=max(cells,key=lambda c:Fraction(c['delta_upper_rational']))
    require(saved['worst_cell']==worst,'Worst cell metadata')
    return dict(status='VERIFIED',k=6,number_of_cells=len(cells),log_x_interval=['167','400'],
        worst_upper_rational=worst['delta_upper_rational'],
        script_sha256=saved['script_sha256'],certificate_sha256=hashlib.sha256(Path(path).read_bytes()).hexdigest())

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--single',nargs=2)
    parser.add_argument('--verify',nargs='?',const=str(OUTPUT))
    parser.add_argument('--precision',type=int,default=160)
    parser.add_argument('--sigma-denominator',type=int,default=2048)
    parser.add_argument('--height-denominator',type=int,default=32)
    args=parser.parse_args()
    started=time.monotonic()
    if args.verify:
        print(json.dumps(verify_certificate(args.verify),indent=2));return
    ctx.prec=args.precision
    if args.single:
        print(json.dumps(certify_cell(*args.single,args.sigma_denominator,args.height_denominator),indent=2));return
    initial=[]
    for left,right,width in ((167,190,1),(190,220,2),(220,400,5)):
        initial.extend((Fraction(v),Fraction(min(v+width,right))) for v in range(left,right,width))
    cells,rejected=[],[]
    def visit(left,right):
        cell=certify_cell(left,right,args.sigma_denominator,args.height_denominator)
        if cell['passed']:
            cells.append(cell)
            print(f'PASS [{left},{right}] {cell["delta_ball"]}',flush=True)
        else:
            rejected.append(cell)
            require(right-left>Fraction(1,64),f'No certified margin in {left},{right}')
            middle=(left+right)/2
            visit(left,middle);visit(middle,right)
    for left,right in initial: visit(left,right)
    worst=max(cells,key=lambda c:Fraction(c['delta_upper_rational']))
    saved=dict(status='ALL_CELLS_PASSED',k=6,log_x_interval=['167','400'],
        created=datetime.now(timezone(timedelta(hours=8))).isoformat(),
        conditional_inputs=['QRH(7/8)','CS v2 Corollary 1 / equation (11)','Platt-Trudgian finite RH'],
        source=dict(url=SOURCE,constants=[list(r) for r in CS_ROWS],finite_rh=RH_SOURCE,H='3000000000000'),
        kernel=KERNEL,precision_bits=args.precision,sigma_denominator=args.sigma_denominator,
        height_denominator=args.height_denominator,python_flint=flint.__version__,
        number_of_cells=len(cells),cells=cells,worst_cell=worst,rejected_coarse_cells=rejected,
        script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        elapsed_seconds=time.monotonic()-started,
        scope='Continuous real-x segment only; analytic proof in research/SMOOTH_K6_CERTIFICATE.md')
    OUTPUT.write_text(json.dumps(saved,indent=2)+'\n',encoding='utf-8')
    print(f'Saved {OUTPUT}; {len(cells)} cells; worst {worst["delta_ball"]}')

if __name__=='__main__':main()
