"""A rigorous diagnostic for summation of the individual all-frequency caps over multipliers."""
from flint import arb,ctx,fmpz
from actual_split import constants,H
from odd_sieve import denominator
from physical_l2 import spectrum,units
from wheel_small import osc

def diagnostic(Q=223092870,cut=200):
    z,c,r,I,A,S,u=constants(1732099);X=(c+2*r).exp();xl=(c-2*r).exp()
    ratio=z*z/xl
    # Every k in this interior range has its whole physical support above Y
    # and below X/cut.  The first and last full wheel intervals are discarded.
    L=cut+1;K=int((xl/arb("70.7").exp()).lower().floor().unique_fmpz())
    a=Q*((L+Q-1)//Q);b=Q*(K//Q)
    eta,D,Z,p2=units(Q,ctx.prec);G=denominator(z,Q)
    m,tail,tv=spectrum(arb(".4"),".0002")
    # Monotonicity of log(ratio*t)/t on t>=a, and exact phi(Q) per period.
    # The right Riemann sum is at least the integral started one period later.
    assert b>a+Q and (ratio*a).log()>1
    integral=(((ratio*(b+Q)).log())**2-((ratio*(a+Q)).log())**2)/2
    first=u*tail*(Z*eta)**2/G**2*eta*integral
    # Absolute all-ordinate bound for the high-frequency multiplier of a unit k block.
    d0=arb(osc(Q))/Q if Q<10**9 else arb(D)
    t=arb(".4")*H
    def block(k):
        return tv*H*(2*eta/t**2+d0*(2/t+(1+1/t**2).sqrt()*arb(2).log())/k)
    return a,b,first,[block(arb(j).exp()) for j in (35,38,40,43,45)]

if __name__=="__main__":
    ctx.prec=144;a,b,h,forms=diagnostic()
    print("interior full periods",a,b,"one term of summed outer cap >",h.str(16),
          "grouped high spectrum at log K=35,38,40,43,45",*(v.str(13) for v in forms))
