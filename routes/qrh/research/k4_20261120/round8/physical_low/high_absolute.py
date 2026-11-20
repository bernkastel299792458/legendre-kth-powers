"""Lower bound for absolute estimation on the unverified first frequency band."""
from flint import arb,ctx
from parity_target import majorant,H


def barrier(J,logz):
    A=arb
    m,tv,b,l,c,a,I=majorant(J,ctx.prec)
    K=A(H);Q=A(10000);pi=A.pi()
    # xi=t/K belongs to [1.2,1.4], with both Fourier coefficients negative.
    assert b[1]<0 and b[2]<0 and a<A.pi()/2
    raw=pi/(2*a)*(-b[1])*(A(".6")*a).sin()
    B0=sum(map(abs,b));sup=pi/a*B0;lip=pi*B0
    # Uniform eta=sigma-1/2 in [3/8,1/2].
    tilt=(1/(16*Q**2)).exp()
    diff=lip*2*Q/(pi.sqrt()*K)+sup*(tilt-1+tilt/(2*Q*pi.sqrt()))
    deriv=tilt*sup*(1/(4*Q**2)+1/(Q*pi.sqrt()))
    kernel=c*(raw-diff)-deriv
    N=2*K
    # Elementary endpoint summation, for sigma>=7/8 and t>=1.2K.
    zeta=1+8*N**(A(1)/8)+N**(A(1)/8)/(A("1.2")*K)
    zeta+=(1+(1+A("1.4")*K)/(A(7)/8))*N**(-A(7)/8)
    den=(1+1/(A(3)/4))*zeta
    interval=K/5-2*576*(A(logz)/4).exp()/A(2).log()
    low=(-c/8).exp()/(4*pi*I)*kernel*interval/den
    return low,kernel,zeta

if __name__=="__main__":
    ctx.prec=160
    for j,z in ((4,40),(6,38),(8,36),(12,34),(24,31),(30,31)):
        v=barrier(j,z)
        print(j,z,*(x.str(15) for x in v))
        assert v[0]>500
