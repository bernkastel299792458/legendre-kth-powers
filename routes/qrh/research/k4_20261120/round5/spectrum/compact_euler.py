"""Uniform finite Euler--Maclaurin zero detectors, including the prime-power removal."""
from flint import arb, ctx

H = 3000175332800


def row(s, t, cutoff):
    q = 128
    V = arb("1.01")*t
    M = V/4
    X = M.floor() if cutoff is None else arb(cutoff)
    if not (2<=X and X<=M):
        raise ValueError("mollifier must be inside the plateau")
    ratio = (V+1+3*q)/(2*arb.pi()*M)
    assert ratio<arb(".637")
    quadrature = 2*arb(q).zeta()*M**(1-s)*ratio**q
    pole = (2*M)**(1-s)*(arb(4*q)/H)**4/H
    residual = (pole+quadrature)*(1+(X**(1-s)-1)/(1-s))
    small = X*M**(-2*s)/(1-arb(2)**(-s))**2
    large = X**(1-2*s)/((2*s-1)*(1-X**(-s))**2)
    loss = 2*residual+residual**2+small+large
    return quadrature, residual, loss


if __name__ == "__main__":
    ctx.prec = 192
    for cutoff in (32768, None):
        peak = [arb(0) for _ in range(3)]
        for k in (1,4,9,17,30,51):
            t = arb(H)*(arb(k)/4).exp()
            for j in (800,820,837,852,865):
                for i,z in enumerate(row(arb(j)/1000,t,cutoff)):
                    peak[i] = peak[i].max(z)
        print("X",cutoff or "floor(V/4)","quadrature / single / square losses",
              *[z.str(12) for z in peak])
        assert peak[1] < arb("1e-15") and peak[2] < (
            arb(".00326") if cutoff else arb("5e-7"))
