"""Sign and size of the continuum outside all integer ratios, independently of its physical error."""
from math import prod
from flint import arb,ctx
from quarter_diagonal import signed,zq,primes
from quarter_stationary_main import residual


def theorem(cut=2**22):
    q=2310;a=arb(1)/2;u=1+a;Y=arb(34).exp();ps=primes(q)
    W=zq(u,q)/zq(2*u,q)
    best=None
    for j in range(12,19):
        B=arb(j).exp()
        for i in range(26,49):
            h=arb(i)/100
            # Euler prime of g is either absent or present, after summing its h-smooth factors.
            # Sum g^{-u} (g*b)^h/b, with b supported on primes of q*g.
            head=prod(1/(1-1/arb(p)) for p in ps)*W
            # At theta=0, the excess beyond W is product
            # (1+1/((p^u+1)(p-1))).
            def correction(v):
                # log of the excess over zeta_q(u-v) is <= sum n^{-(u+1-2v)}/(1-13^(-1+v)).
                z=u+1-2*v;P=arb(13)
                return ((P**(-z)+P**(1-z)/(z-1))/(1-P**(-1+v))).exp()
            small=head*correction(arb(0))/(69*j)
            upper=prod(1/(1-arb(p)**(-1+h)) for p in ps)*zq(u-h,q)*correction(h)
            val=small+(B/Y)**h*upper
            best=val if best is None else best.min(val)
    # At exponent u the unconstrained factor sums exactly to 1 by gcd inversion.
    # Charge two taper losses only when gr>Y; tau(n) majorizes all squarefree factorizations.
    # For n>Y, sum tau(n)n^{-u} <= Y^{-h} zeta_q(u-h)^2.
    loss=Y**(-arb(25)/100)*zq(u-arb(25)/100,q)**2
    for i in range(26,49):
        h=arb(i)/100
        loss=loss.min(Y**(-h)*zq(u-h,q)**2)
    R=residual(arb(37),q)
    p,t=signed(q,a,cut)
    se=4*arb(cut)**2/2**96
    # Every displayed endpoint uses an outward upper on its allowed error.
    lower=1-best-loss-R-(p+t)
    upper=1+best+loss+R-(p-t-se)
    return best,loss,p,t,lower,upper


if __name__=='__main__':
    ctx.prec=144
    out=theorem()
    print('integer main first reciprocal, absolutely convergent loss, S finite, S tail, other normalized main lower/upper',
          *(v.str(12) for v in out),flush=True)
