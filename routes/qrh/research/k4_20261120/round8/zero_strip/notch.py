"""Single high-frequency energy obstruction for one positive notched kernel."""
from flint import arb
from shell_obstruction import T,H,epsilon,prime_bin,kernel


def main():
    L=arb(15);D=arb(40);a=arb(1)/2;delta=arb('.01')
    background=arb(7)
    peak=kernel(delta,arb(0),L)+a*(-delta*D).exp()*(2*(delta*L).cosh()-2)/(L*delta**2)
    peak+=arb('.04')-background
    k=arb('.000146')
    assert (2*(1+3*a)*420070/(background*(T-H))).sqrt()<k
    energy=arb(0)
    for i in range(40*32,54*32):
        l=arb(i)/32;r=arb(i+1)/32
        w=a*(1-(r-D)/L)
        coeff=w*l*(-arb('.875')*r).exp()/(1+(-arb('.75')*l).exp())
        energy+=prime_bin(i,32)*l.exp()*coeff**2
    coeff=(epsilon/(2*k*k)).sqrt()
    gain=coeff*energy.sqrt()
    e=epsilon.sqrt();t=1/arb(2).sqrt()
    fourth=(arb(3)/8).sqrt()*t*(1/k-1/(t*(1+e)))
    assert coeff**2<fourth*e
    w=arb('.05');q=arb(6)/5
    rs=coeff*54*(arb('.125')*54).exp()/energy.sqrt()
    assert rs<1 and rs/(w*arb(20).exp())<arb('.03')
    S=(coeff/w)**2
    assert (1-w)**q+epsilon**(1-q)*w**q*(q*(q-1)*S/arb('.94')).exp()<k**(-2*(q-1))
    print('notched 15 / 40 / .5, weighted energy above log p=40',energy.str(13),
          'minimum budget',gain.str(13),'available peak',peak.str(13))
    assert gain>peak


if __name__=='__main__':
    main()
