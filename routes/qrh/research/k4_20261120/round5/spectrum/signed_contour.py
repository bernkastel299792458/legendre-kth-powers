"""Signed vertical-integral criterion at the thirty finite rectangle targets."""
from flint import arb, ctx
from reflected_sampling import H, N, D, Q, fraction, reduction, short_second


def mean_square(s, y, width):
    b2 = 2*D**2
    diag = (2*s).zeta()**4
    off = None
    for i in range(4,31):
        eps = arb(i)/100
        alpha = 2-2*s+eps
        term = (alpha**2/(4*b2)).exp()*y**alpha*(1+eps).zeta()**4
        off = term if off is None else off.min(term)
        shrink = 2*s-1-eps
        if shrink>0:
            diag = diag.min(arb(N)**(-shrink)*(1+eps).zeta()**4)
    return (1+5/width)*diag+10*off/width


def row(j, k):
    s = arb(j)/1000
    t = arb(H)*(arb(k)/4).exp()
    width = t/100
    v = t + width
    u = v.log()
    y = 512*v
    p = 3*(1-s)/(3*s-1)
    target = 6*t.log()*t**p
    s2 = short_second(u, Q, N)
    ratio = fraction(u, u, j, 512, s2)*reduction(u, j)
    mean_loss = (ratio*(arb(1)/2-arb("1e-40"))**2 * 7*u*v**p/target).sqrt()
    b2 = 2*D**2
    second = mean_square(s,y,width)
    poisson = (2*t).log()/2+3
    nearby = (arb("2.5")*(width+4)/(arb(".9")*width)*8*
              (arb(4).log()**2+2*arb(4).log()+2)).sqrt()*poisson
    regular = (3+(2*(2-s)+arb("2.5"))*poisson)*second.sqrt()/arb(N).log()
    radius = arb(1)/32
    sup_second = (1+2*radius/width)*mean_square(s-radius,y,width+2*radius)/(
        arb.pi()*radius*arb(N).log())
    horizontal = (regular+nearby*sup_second.sqrt())/(2*arb.pi())
    eta = 1/y.log()
    # gaussian Chernoff majorant, then the harmonic sum for P
    pole = (1+eta**2/(2*b2)).exp()*(1+1/eta)*(1+arb(Q*N).log())/2
    right = 4/(2*arb.pi()*arb(N).log())
    edge = (horizontal+pole+right)/target
    available = 1-arb("1e-28")-mean_loss-edge
    # Any real prime-polynomial coefficients |b_m| <= log m, up to T^3.
    shift = 1-s+eta
    tail_mass = y**shift * (shift**2/(2*b2)).exp()*(1+1/eta)*(1+arb(Q*N).log())
    cutoff = t**3
    # (log n+log m)^2 >= 4 log N log m cancels the coefficient's log m.
    harmonic = 1+(cutoff**(1-s)-1)/(1-s)
    euler_charge = tail_mass*harmonic/(4*arb.pi()*width*arb(N).log()*target)
    return target, mean_loss, edge, available, euler_charge


if __name__ == "__main__":
    ctx.prec = 192
    floor = arb(1)
    maxloss = maxedge = arb(0)
    maxprime = arb(0)
    for k in (1,4,9,17,30,51):
        line = []
        for j in (800,820,837,852,865):
            target, loss, edge, available, prime = row(j,k)
            maxloss = maxloss.max(loss)
            maxedge = maxedge.max(edge)
            floor = floor.min(available)
            maxprime = maxprime.max(prime)
            line.append(available.str(8))
        print("k", k, "available", *line)
    print("worst mean loss",maxloss.str(14),"edge",maxedge.str(14),
          "available",floor.str(14),"prime charge",maxprime.str(14))
    assert floor > arb(".9164648") and maxprime < arb("1e-5")
