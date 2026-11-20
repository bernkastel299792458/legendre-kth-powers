"""Complete-residue continuous stationary model and its genuine signed arithmetic."""
from math import prod
from flint import arb,ctx
from quarter_diagonal import primes,zq,signed
from quarter_signed_block import target


def residual(U,q):
    assert q==2310
    a=arb(1)/2;Y=(U-3).exp();S=zq(1+a,q)
    rho=prod(1/(1-1/arb(p)) for p in primes(q))
    best=None
    for j in range(12,19):
        L=arb(j);B=L.exp()
        assert B>=96955
        for i in range(26,49):
            h=arb(i)/100
            b=1+a-h
            small=rho*S**2/(69*L)
            # For p>=13 the extra Euler product costs at most
            # zeta_q(b)*exp(sum_{n>=13} n^(-b-1+h)/(1-13^(-1+h))).
            p0=arb(13)
            correction=p0**(-b-1+h)+p0**(-b+h)/(b-h)
            correction/=1-p0**(-1+h)
            many=zq(b,q)*correction.exp()
            factor=prod(1/(1-arb(p)**(-1+h)) for p in primes(q))
            value=small+S*(B/Y)**h*factor*many
            best=value if best is None else best.min(value)
    return best


if __name__=='__main__':
    ctx.prec=160
    U=arb(37);q=2310;a=arb(1)/2;T=U.exp();eta=arb(480)/q;w=arb('.75')
    s,t=signed(q,a);cut=262144
    lower=s-4*arb(cut)**2/(2**96)-t
    R=residual(U,q)
    print('absolute collapsed linear form, lower Smax, upper Smin-Smax',
          *(x.str(12) for x in (R,lower,2*(R-lower))),flush=True)
    for n in (32,48,64,96):
        alpha=arb(n);K=arb('2.25e12');D=arb('1.01')*T
        area=((D**(1-a/2)-K**(1-a/2))/(1-a/2)*
              (alpha*(q/(2*arb.pi())).sqrt())**(-a)*(a*w).sinh()/(a*w))
        credit=(lower-R)*2*eta/a*area
        room=target(U,alpha,w,(s,t))[-1]
        print('alpha',n,'negative continuous contribution, admissible residual of all signed terms',
              credit.str(12),(room+credit).str(12),flush=True)
