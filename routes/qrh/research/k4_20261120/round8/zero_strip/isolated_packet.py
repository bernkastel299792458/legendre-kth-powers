"""Complete-height count of right-hand zeros without a second right-hand zero nearby."""
from flint import arb,arb_series
from strip_boundary import PI,H,T,THETA,S


def prime_energy(j,U,v):
    # Sum (log n) n^(j-2Theta) exp(-(log n-U)^2/v^2) against d psi(n).
    L=arb(16);e=arb('.002');h=1+j-2*THETA
    err=arb('.2')/L**2+arb('1.01624')*((-L/2).exp()+L/arb(2).log()*(-2*L/3).exp())
    assert err<e and L.exp()>3594641
    slope=1/L+j-2*THETA-2*(L-U)/v**2
    small=arb('1.04')*L*(h*L-((L-U)/v)**2).exp()
    m=U+h*v*v/2
    pref=(h*U+(h*v/2)**2).exp()
    assert m>0
    integ=pref*(v*PI.sqrt()*m+v*v/2*(-(m/v)**2).exp())
    if not slope>0:
        # xf increases up to X, hence x(-f')_+ <= f there.
        assert slope+1>0
        early_integral=pref*L*v*PI.sqrt()/2*((m-L)/v).erfc()
        small+=arb('1.04')*early_integral
        integ=pref*(v*PI.sqrt()*m/2*((L-m)/v).erfc()+
                    v*v/2*(-((L-m)/v)**2).exp())
    peak=pref*(m+v)
    return small+(1+e)*integ+3*e*peak


def ratio(a,v,d):
    critical=(2/v**2-a*a).max(0).sqrt()
    t=critical.max(d)
    return (1+(t/a)**2)*(-(v*t)**2/2).exp()


def check(eta,R,U,v,r,c,goal=None,phase=False):
    eta,R,U,v,r,c=map(arb,(eta,R,U,v,r,c))
    assert 0<r and 2*r<=R and arb(1)/2<eta<S and 1<c<2 and U>arb('.75')*v*v
    assert U/v**2>=2 and PI*4/3<arb('4.2')
    k=lambda a:(-a*U+(a*v)**2/2).exp()
    mod=(2*PI).sqrt()*v
    arc=arb_series([c,1],2).zeta()
    P=((T+r+3)/(2*PI)).log()/2-arc[1]/arc[0]+arb('1e-8')
    half=c-arb(1)/2
    low=half/2*ratio(c-eta,v,0)*(k(THETA-eta)+k(THETA+eta-1))
    selfamp=k(THETA-S)-k(THETA+S-1)
    if phase:assert PI/2>v*v*(THETA-eta)*r
    assert low>0 and selfamp>0
    # Bounds for both pole terms, the gamma integral, negative frequencies
    # and the even prime, divided by the Gaussian-transform factor.
    poles=(k(THETA)+k(THETA-1))*(-(v*(H-r))**2/2).exp()
    arch=k(THETA-arb(1)/2)/(2*PI)*((2*PI).sqrt()/v*((T+r+4).log()+6)+2/v**2)
    negative=3*(-U**2/(2*v*v)).exp()
    log2=arb(2).log()
    even=log2*((-U**2/(8*v*v)).exp()+(-THETA*U/2).exp())/(1-(-THETA*log2).exp())
    allowance=poles+arch+(negative+even)/mod
    n=1024
    per=arb(0)
    for i in range(1,n+1):
        y=r*i/n
        own_poisson=2/half/(1+(y/(c-THETA))**2)
        far=half/2*(1+k(2*THETA-1))*ratio(c-THETA,v,R-(r if phase else y))
        left=half/2*k(THETA+eta-1)*ratio(c-THETA,v,0) if phase else arb(0)
        rest=(P-own_poisson)*low.max(far).max(left)
        per+=(selfamp*(-(v*y)**2/2).exp()-rest-allowance).max(0)**2
    per*=2*r*mod**2/n
    norm=((T-H+2*r+arb('4.2'))*prime_energy(0,U,v)
          +arb('4.2')*prime_energy(1,U,v))
    cap=norm/per
    print('phase-isolated' if phase else 'isolated','count',eta.str(5),R.str(5),'packet',U.str(5),v.str(5),
          'arch/extra',allowance.str(6),'zero charge',per.str(9),'cap',cap.str(14))
    if goal is not None:assert cap<goal
    return cap


if __name__=='__main__':
    for row in [
        ('.70',3,'30.2','1.9','1','1.38',150000),
        ('.75',2,'30.9','2.65','.69','1.26',250000),
        ('.76',2,'31','2.66','.63','1.26',320000),
        ('.77',3,'31.3','2.44','.65','1.3',420071),
    ]:
        check(*row)
        check(*row[:-1],phase=True)
