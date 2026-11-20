"""Interval proof for a short high-real-part strip above verified RH height."""
import argparse
from concurrent.futures import ProcessPoolExecutor
from math import prod
from flint import acb, arb, ctx

H = 3000175332800
PREC = 128
DEN = 12
HALF = 24
NODES = tuple(2*j+1 for j in range(-HALF,HALF))


def value(index):
    ctx.prec = PREC
    z = acb(arb(67)/80, H+arb(index)/DEN).zeta()
    # Serialize certified decimals (including the printed radius) across processes.
    return z.real.str(30), z.imag.str(30)


def basis():
    # Integer numerator coefficients at odd integer interpolation nodes.
    all_rows = []
    for a in NODES:
        c = [1]
        for b in NODES:
            if b!=a:
                c = [x-b*y for x,y in zip([0]+c,c+[0],strict=True)]
        denom = prod(a-b for b in NODES if b!=a)
        all_rows.append([arb(v)/denom for v in c])
    return list(zip(*all_rows,strict=True))


def parameters():
    V = arb(H+514)
    M = V/4
    omega = (2*M).log()/2
    sigma = arb(67)/80
    s = arb(4)/5
    q = 128
    hmin = arb(H-3)
    delta = ((2*M)**(1-s)*(4*q/hmin)**4/hmin +
             2*arb(q).zeta()*M**(1-s)*((V+1+3*q)/(2*arb.pi()*M))**q)
    R = arb(15)/4
    r = ((arb(3)/80)**2+(arb(1)/(2*DEN))**2).sqrt()
    mass = 1+((2*M)**(1-sigma)-1)/(1-sigma)
    err = mass*(omega*R).exp()*R/(R-r)
    for i in range(HALF):
        a = arb(2*i+1)/(2*DEN)
        err *= (r**2+a**2)/(R**2-a**2)
    assert err<arb(".00001") and delta<arb("1e-19")
    return omega,r,delta,err


def lower_bound(c, err, conversion, delta):
    # x is normalized time and y is minus the normalized real-part offset.
    stack = [(arb(-1),arb(1),-arb(9)/10,arb(9)/10,0)]
    lower = None
    leaves = 0
    while stack:
        xl,xr,yl,yr,depth = stack.pop()
        xm,ym = (xl+xr)/2,(yl+yr)/2
        z = acb(xm+arb(0,((xr-xl)/2).upper()),ym+arb(0,((yr-yl)/2).upper()))
        p = c[-1]
        for b in reversed(c[:-1]):
            p = p*z+b
        margin = (abs(p)-err)/conversion-delta
        if margin>0:
            lower = margin.lower() if lower is None else lower.min(margin.lower())
            leaves += 1
        elif depth>=18:
            raise ArithmeticError("interpolation cell cannot exclude a zero")
        elif depth%2==0:
            stack.extend(((xl,xm,yl,yr,depth+1),(xm,xr,yl,yr,depth+1)))
        else:
            stack.extend(((xl,xr,yl,ym,depth+1),(xl,xr,ym,yr,depth+1)))
    return lower,leaves


def verify(length,workers):
    if not (1<=length<=510 and workers>=1):
        raise ValueError("certified local height and worker range")
    ctx.prec = PREC
    omega,r,delta,err = parameters()
    table = basis()
    points = range(1-HALF,DEN*length+HALF)
    if workers==1:
        data = list(map(value,points))
    else:
        with ProcessPoolExecutor(max_workers=workers) as pool:
            data = list(pool.map(value,points,chunksize=4))
    eps = arb(0,delta.upper())
    samples = [acb(arb(x),arb(y))+acb(eps,eps) for x,y in data]
    phase = [acb(0,omega*arb(a)/(2*DEN)).exp() for a in NODES]
    conversion = (omega*r).exp()
    worst = None
    total = 0
    for i in range(DEN*length):
        vals = [v*g for v,g in zip(samples[i:i+2*HALF],phase,strict=True)]
        coeff = [sum((v*a for v,a in zip(vals,row,strict=True)),acb(0)) for row in table]
        low,leaves = lower_bound(coeff,err,conversion,delta)
        worst = low if worst is None else worst.min(low)
        total += leaves
    print("closed zero-free rectangle: real part 4/5 through 7/8, height",
          H,"through",H+length,"positive modulus lower bound",worst.str(12),
          "leaves",total,"zeta evaluations",len(samples),"analytic remainder",err.str(10))
    assert worst>0


if __name__=="__main__":
    cli = argparse.ArgumentParser()
    cli.add_argument("--length",type=int,default=32)
    cli.add_argument("--workers",type=int,default=2)
    args = cli.parse_args()
    verify(args.length,args.workers)
