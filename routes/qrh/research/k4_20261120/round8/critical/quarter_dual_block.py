"""Positive q-adic decomposition for the complete low dual off-diagonal."""
from flint import arb,ctx
from math import prod
from quarter_diagonal import primes,signed
from quarter_signed_block import periodic,harmonic,target,block
from quarter_far_pairs import separated
from quarter_ordered_cross import cost


def dual_prefix(N,U,alpha,w,q=2310):
    T=U.exp();a=arb(1)/2;K=arb('2.25e12');Dtime=arb('1.01')*T
    eta,C,_=periodic(q,ctx.prec)
    A=eta/a
    yf=w.exp()/alpha*(2*T*q/(2*arb.pi())).sqrt()
    coeff=eta/(1-a)+C*(yf**2/N)**(1-a)
    # For D<=yf bound sum (k*l)^a/[k,l]/D^(2a) uniformly.
    # At a=1/2 the three elementary sums are harmonic, square-root and count.
    # Replace phi(h) by h in nonnegative errors.
    H=harmonic(yf,q,eta)
    upper=A**2*H+2*A*C/(1-a)+C**2
    J=coeff*N**(1-a)*(w.exp()/alpha)**(2*a)*upper
    weights={2:'1.625',3:'3.75',5:'10.5',7:'18'}
    hilbert=arb('117.354')*prod(1/arb(p)+(p-1)/(p*arb(x)) for p,x in weights.items())
    harmonic_gain=prod(arb(4)*(p-1)/p**2 for p in primes(q))
    norm=arb.pi().min(hilbert)+arb('.118')*(1+N.log())*harmonic_gain
    sweep=2+(a+1/(2*w))*((Dtime/K).log()+1/arb(256)+1/arb(2048))
    return J,norm*sweep*J


if __name__=='__main__':
    ctx.prec=160
    U=arb(37);ss=signed(2310,arb(1)/2);w=arb('.75')
    for alpha,zero in ((64,4),(96,8)):
        aa=arb(alpha)
        rest=target(U,aa,w,ss)[-1]-block(zero*U.exp(),aa,w)[-1]-sum(separated(U,aa,w,arb('.03')))-sum(cost(U,aa,w))
        for f in (1,4,16,32,1024,4096):
            j,upper=dual_prefix(f*U.exp(),U,aa,w)
            print('alpha',alpha,'N/T',f,'weighted dual energy, full low dual off, residual',
                  *(v.str(10) for v in (j,upper,rest-upper)),flush=True)
