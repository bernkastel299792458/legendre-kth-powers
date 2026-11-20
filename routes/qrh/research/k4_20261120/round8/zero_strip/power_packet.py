"""Signed Gaussian packet budget with a nonnegative strip-wide rational kernel."""
from functools import partial
from math import comb, factorial
from pathlib import Path
import sys

from flint import arb, arb_series, ctx, fmpz
from paired_packet import check
from strip_boundary import PI,H,T,THETA,S

sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'round4'/'hilbert'))
from periodic_hilbert import integer_hilbert


def removed(eta,R,U,v,h,order,cells=72,prime_phases=False):
    m=order; half=arb(1)/2; bmax=THETA-half
    assert 1<=m<=8 and 1<h+half<6 and 0<m*(bmax/h).asin()<PI/2
    k=lambda a:(-U*a+(a*v)*(a*v)/2).exp()
    abscissa=h+half
    zz=arb_series([abscissa,1],m+1).zeta()
    deriv=-(zz.derivative()/zz)
    mass=arb(0); coeffs=[]
    for j in range(1,m+1):
        coeff=arb(2)**(1-2*m+j)*comb(2*m-j-1,m-j)*h**j
        coeffs.append(coeff)
        gamma=((T+3)/(2*PI)).log()/2+arb('1e-8') if j==1 else 3/H**j+PI/(4*H**(j-1))
        mass+=coeff*(gamma+deriv[j-1]*(-1)**(j-1))
    if prime_phases:
        # Each omitted prime-power deficit w*(1+cos(k theta)) is nonnegative.
        ngrid=128
        cosines=[[1+(k*PI*i/ngrid).cos() for k in range(1,10)] for i in range(ngrid+1)]
        for p in range(2,300):
            if not fmpz(p).is_prime():continue
            lp=arb(p).log()
            weights=[lp*(-abscissa*k*lp).exp()*sum(a*(k*lp)**j/factorial(j) for j,a in enumerate(coeffs))
                     for k in range(1,10)]
            sample=min(sum(t*w for t,w in zip(row,weights)).lower() for row in cosines)
            # The two endpoints are stationary; so is any interior minimum.
            curvature=sum((j+1)**2*w for j,w in enumerate(weights))
            mass-=(sample-curvature*(PI/ngrid)**2/8).max(0)
    own=2*(h*h/(h*h-(S-half)**2))**m
    assert mass>own
    Y=arb(9); decay=v*v/4
    assert R*R<=Y and m/(h*h+Y)<decay
    low=arb(0);far=arb(0);left=arb(0)
    def ratio(bl,br,yl,yr):
        # Uniform bound on the ratio Gaussian ordinate weight / pair mass.
        zlo,zhi=bl**2,br**2
        def numerator(z):
            # Squared modulus is convex in z; at each endpoint the log derivative
            # in y vanishes at the stated positive quadratic root.
            t=(m/decay+((m/decay)**2+16*h*h*z).sqrt())/2-h*h-z
            t=t.max(yl).min(yr)
            A=h*h-z+t
            return (-decay*t).exp()*((A*A+4*z*t).sqrt()/h**2)**m
        numerator_max=numerator(zlo).max(numerator(zhi))
        # For fixed b, 2b sqrt(y)/(h^2-b^2+y) peaks at y=h^2-b^2.
        peak=h*h-zhi
        cut=peak.max(yl).min(yr)
        angle=(2*br*cut.sqrt()/(peak+cut)).atan()
        return numerator_max/(2*(m*angle).cos())
    ymin=R*R
    for beta0,beta1,is_low in ((half,eta,True),(eta,THETA,False)):
        for i in range(cells):
            a=beta0+(beta1-beta0)*i/cells
            b=beta0+(beta1-beta0)*(i+1)/cells
            tail=(-decay*Y).exp()*((h*h+Y+(b-half)**2)/h**2)**m/(2*(m*((b-half)/h).asin()).cos())
            total=farhere=tail
            for yl,yr in ((arb(0),ymin),(ymin,Y)):
                # Uniform grid in y has short cells where both peaks lie.
                n=2*cells
                for j in range(n):
                    tl=yl+(yr-yl)*j/n
                    tr=yl+(yr-yl)*(j+1)/n
                    bnd=ratio(a-half,b-half,tl,tr)
                    total=total.max(bnd)
                    if yl>0:farhere=farhere.max(bnd)
            amp=k(THETA-b)+k(THETA+b-1)
            if is_low:
                low=low.max(amp*total)
            else:
                far=far.max(amp*farhere)
                left=left.max(k(THETA+a-1)*total)
    return (mass-own)*low.max(far).max(left)+k(THETA+S-1)


def run(eta,r,U,v,h,order,lam,goal,cap,cells=72,prime_phases=False):
    use=partial(removed,h=arb(h),order=order,cells=cells,prime_phases=prime_phases)
    # c=1.3 belongs to the basic verifier; the replacement uses c=h+1/2.
    g,n=check(eta,r,U,v,'1.3',lam,restricted=True,subtraction=use)
    assert g>arb(goal) and n<cap
    return g,n


if __name__=='__main__':
    ctx.prec=160
    assert integer_hilbert(210)<arb('.915504')
    for args in [
        ('.8','1.5','33.295','3.616','1.507',5,'.507','.22523',132056),
        ('.815','1.5','33.633','3.917','1.575',6,'.463','.12112',212246),
        ('.82','1.5','33.745','4.020','1.553',6,'.447','.07471',268453),
        ('.825','1.5','33.840','4.110','1.530',6,'.440','.02181',363047),
    ]:
        run(*args,prime_phases=True)
