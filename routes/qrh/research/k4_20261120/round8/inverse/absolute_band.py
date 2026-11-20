"""Mellin absolute costs for the actual J=6 parity detector and true product."""
from pathlib import Path
import sys

from flint import arb, arb_series, ctx, fmpz

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "physical_low"))
from parity_target import H, certificate, majorant


ctx.prec = 160
R = arb
PI = R.pi()
Q = R(10000)
THETA = R(7)/8
SIGMA = R(".8751")


def hole_bound(s,u,beta0,r,shape,c):
    """Pointwise upper bound when all beta>beta0 have |t-gamma|>=r."""
    s,u,beta0,r=map(R,(s,u,beta0,r))
    assert beta0<s<u and u>1 and u+s>2*THETA
    lam=(u-beta0)*((u-beta0)/(s-beta0)).log()
    for j in range(1024):
        b=beta0+(THETA-beta0)*R(2*j+1,1)/2048
        gap=u-b
        test=(gap**2+r*r)/(2*gap)*((gap**2+r*r)/((s-b)**2+r*r)).log()
        lam=lam.max(test)
    zs=arb_series([u,1],2).zeta()
    du=-zs[1]/zs[0]
    h=u-s
    assert lam>h
    log_inv=(u.zeta()/(2*u).zeta()).log()+((lam-h)/2)*(7*H/(2*PI)).log()
    inv=(log_inv+lam*du+R("1e-9")*(lam+h)).exp()
    # A pointwise norm for the actual Selberg lcm polynomial (squarefree d,e).
    cap=(2*(1-s)*38).exp()*(2-s).zeta()/(1-s)**2
    geometry=c*H*shape*((s-1)*c).exp()
    print("good horizontal row",s.str(6),beta0.str(6),"lambda",lam.str(10),
          "reciprocal",inv.str(10),"unit-LCM geometric cap", (geometry*inv).str(10),
          "full majorant", (geometry*inv*cap*(2*s).zeta()).str(10))


def deformed_band(coeff,area,err,c,mass,budget):
    # Select good endpoints inside every frequency cell and tile the entire
    # positive and negative bands by separate Cauchy contours.
    n=8192
    w=R(300)
    beta=2-THETA
    beta_hi=1+THETA
    r=R(".001")
    assert R("1.125")/(R("1.875")**2+4)>R(".14")
    assert 2*r*(17/R(".14"))<1
    zz=arb_series([2,1],2).zeta()
    assert ((7*H+2)/(2*PI)).log()/2-zz[1]/zz[0]+R("1e-9")<17
    assert (beta_hi/2+r**2/(2*beta))*((beta_hi**2+r*r)/r**2).log()<16
    # Endpoint sup for the actual integrand on [.70,2]; zero-free by height.
    assert 30*(R(272)+152).exp()*R("1.4").zeta()<R(430).exp()
    assert (2*R("1.3")*(430+R("1.69")/w**2-900).exp()
            +2*(R(152)-900).exp()*w*R(2).zeta()) < R("1e-100")
    ds=( -w*w*R(2).log()**2/8 ).exp()*(R(2).zeta()-1)
    assert ds<R("1e-100")
    allowance=sum((PI*(abs(coeff[j])+abs(coeff[j+1]))/2 for j in range(1,7)),R(0))
    global_lip=PI*sum(map(abs,coeff),R(0))
    mdl=area-allowance/(2*n)-6*(global_lip/H+err/c)
    factor=(1-(2+60*w)*n/H)*(1-R("1e-90"))*(-R("1.69")/w**2).exp()
    base=H*c*mdl*factor/(2*PI*mass)
    floor=1+(budget/base).log()/c
    assert base>26233271590198
    assert floor<R(".70562")
    print("deformed contour guaranteed base",base.str(20),"minimum necessary abscissa",
          floor.str(14),"absolute cost if real part >= .70562",
          (base*((R(".70562")-1)*c).exp()).str(14))


def prefix_obstruction(c,mass,err):
    p=100000007
    assert fmpz(p).is_prime()
    p=R(p)
    X=R(38).exp()/p
    upper=(p/(p-1))*(X.log()+2+R("2.44")/X.sqrt())/R("39.331")
    assert upper<1
    amp=(1-upper)**2
    w=26*p
    t=( -(w/(4*p))**2 ).exp()
    leakage=16/p*t/(1-t)+2*R(152).exp()*(-w**2*R(2).log()**2/4).exp()
    horizontal=R(3)*(431+R("1.69")/w**2-900).exp()
    outer=4*(R(152)-900).exp()*w
    assert leakage+(horizontal+outer)/(PI.sqrt()*w)<amp/(1000*p**2)
    unit=(R(".52")*c-err)/(4*PI*mass)
    base=2*unit*R(".999")*(-R("1.69")/w**2).exp()*(R(H)/2-2-60*w)*amp
    cost=base*((SIGMA-1)*c-SIGMA*p.log()).exp()
    assert cost>R(".064")
    print("first remaining prime",p.str(12),"squared Selberg amplitude",amp.str(12),
          "right contour actual cost after any prefix below this prime",cost.str(12))


def run():
    _, _, coeff, _, c, a, mass = majorant(6,ctx.prec)
    budget = certificate(6, 38)[-1]
    assert budget > R(".0387663")
    assert R("1.125")*(R("1.125")/(SIGMA-THETA)).log()<11
    # Gaussian mean of the full Dirichlet product.  Bounds below also hold for
    # a time subinterval of width V>=500 after setting w=V/50.
    V = R(H)/2
    w = V/50
    t0 = R("1.35")*H
    assert R(10)*(R(2).log())*10/8 > 6
    # For n>=2 distribute half the exponent in order to save n^-6.
    ds_tail = ((-R(10)**2*R(2).log()**2/8).exp() * (R(2).zeta()-1))
    assert ds_tail < R(".002")
    # The bound exp(220)(2+|t|)^6 on the entire vertical line.
    # For nearby t0 in [1.1H,1.6H] and local w<=H/100.
    gauss_tail = ((R(220)-R(600)).exp()*(2+R("1.6")*H+w)**6)
    assert gauss_tail < R(".001")
    b0 = sum(map(abs,coeff),R(0))
    # K times the Mellin profile differs from c*hatP(t/K) by at most err.
    err = PI*b0/H*(R("2.25")/(4*Q**2)).exp()*((c+3/(4*Q**2))*2*Q/PI.sqrt()+1)
    assert err < R(".00002")
    def prof(j,t):
        return PI/(2*a)*(coeff[j]*((j+1-t)*a).sin()
                            +coeff[j+1]*((t-j)*a).sin())
    cs = list(coeff) + [R(0)]
    coeff = cs
    # On [j,j+1] for 1<=j<=6 only the j and j+1 cosine lobes remain.
    mass_l = R(0)
    for j in range(1,7):
        cuts = [R(0),R(1)]
        if coeff[j]*coeff[j+1] < 0:
            root=(-coeff[j]*a.sin()/(coeff[j+1]-coeff[j]*a.cos())).atan()/a
            assert 0<root<1
            cuts.insert(1,root)
        def primitive(u):
            return PI/(2*a**2)*(coeff[j]*((1-u)*a).cos()-coeff[j+1]*(u*a).cos())
        mass_l += sum((abs(primitive(r)-primitive(l)) for l,r in zip(cuts,cuts[1:])),R(0))
    band = mass_l/(2*PI*mass)
    base = H*c*band
    floor = 1+(budget/base).log()/c
    print("ordinary twist allowance",budget.str(11),"bare ideal vertical threshold",floor.str(9))
    print("double-band geometry",band.str(8),"bare cost at .875",
          (base*((THETA-1)*c).exp()).str(8))
    for n in range(256):
        t=R("1.1") + R(2*n+1,1)/(4*256)
        assert -prof(1,t)>R(".52")
    # One side of the time spectrum suffices.
    unit = ((SIGMA-1)*c).exp()*(R(".52")*c-err)/(4*PI*mass)
    local = unit*R(".99")*PI.sqrt()/50
    assert local*V>R(62000)
    print("certified positive-band absolute cost, minimum line .8751",
          (local*V).str(12),"cost per covered height",local.str(11))
    assert R(".03876635")/local<928000
    # Integrating the short Gaussian centers allows each segment to lose only
    # its two good-height choices and 30w at either end, w=10.
    right_rate=unit*R(".997")*(-R("1.69")/100).exp()
    right_cap=budget/right_rate
    assert right_cap+602<34000
    print("right-excursion allowed aggregate excess width above 602 per component",
          right_cap.str(10),"one-component height ceiling",(right_cap+602).str(10))
    for pars in [(".60","1.185",".50",".25"),(".645","1.18",".55",".25"),
                 (".686","1.166",".60",".25"),(".89","1.40",".865",".25")]:
        hole_bound(*pars,band+6*err/(2*PI*mass*c),c)
    deformed_band(coeff,mass_l,err,c,mass,budget)
    prefix_obstruction(c,mass,err)


if __name__=="__main__":
    run()
