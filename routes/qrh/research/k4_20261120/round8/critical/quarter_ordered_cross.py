"""Complete stationary interference for one ordering of the two mollifier indices."""
from flint import arb,ctx
from quarter_diagonal import zq,signed
from quarter_far_pairs import positive_prefix,separated
from quarter_signed_block import periodic,target,block


def cost(U,alpha,w,q=2310):
    T=U.exp();sigma=arb(3)/4;a=2*sigma-1
    Y=(U-3).exp();W=arb('9.5');X=Y*W.exp()
    ts=arb('1.5e12');K=arb('2.25e12');P=128;m=2048;D=arb('1.01')*T
    eta,C=positive_prefix(q,'direct',ctx.prec)
    ram,Cr=positive_prefix(q,'dual',ctx.prec)
    yf=alpha*w.exp()*(2*T*q/(2*arb.pi())).sqrt()
    yr=w.exp()/alpha*(2*T*q/(2*arb.pi())).sqrt()
    atoms=(C+eta*yf**(1-sigma)/(1-sigma))*(Cr+ram*yr**sigma/sigma)
    atoms/=arb(q).sqrt()*(q*ts/(2*arb.pi()))**(a/2)
    mass=C+eta*(X**(1-sigma)-Y**(1-sigma))/(W*(1-sigma)**2)
    slope=2*P/K+(m+a/2)/D
    c0=arb(4)/(2*w)
    c1=5*slope/(2*w);c2=16/(2*w*ts)
    end=((ts/K)**(2*P)+(D/(2*T))**m)/(2*w)
    log2=arb(2).log()
    remote=(c1/log2+c2/log2**2)*mass**2
    # Positive integral of the actual squared taper, using its layer derivative.
    _,Cpower,_=periodic(q,ctx.prec)
    b=1-a
    norm=Cpower+eta/b*(2*X**b*(1-(1+b*W)*(-b*W).exp())/(b*W)**2)
    near=(2*c1*(1+X.log())+4*(c0*c2).sqrt())*norm
    equal=c0*zq(2*sigma,q)
    return tuple(2*atoms*v for v in (end*mass**2,remote,near,equal))


if __name__=='__main__':
    ctx.prec=160
    U=arb(37);ss=signed(2310,arb(1)/2);w=arb('.75')
    for alpha,f in ((64,4),(96,8)):
        aa=arb(alpha);fields=cost(U,aa,w)
        print('alpha',alpha,'boundary, separated indices, close indices, equal indices, entire d<=e',
              *(v.str(12) for v in (*fields,sum(fields))),flush=True)
        budget=target(U,aa,w,ss)[-1]-block(f*U.exp(),aa,w)[-1]
        for gap in ('.01','.03'):
            other=separated(U,aa,w,arb(gap))
            print('  log gap',gap,'remainder allowance after the entire half', (budget-sum(other)-sum(fields)).str(12),flush=True)
