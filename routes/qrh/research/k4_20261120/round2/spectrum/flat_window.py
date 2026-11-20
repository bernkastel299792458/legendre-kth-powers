"""Localize Gabriel's convexity lemma to almost exactly [-T,T]."""
from pathlib import Path
import sys
from flint import arb

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"right"))
from verify_bv import A, check, endpoints as coarse_endpoints


def moments(U,delta,W,logh,fine,signed=False,signed_low=False):
    M=2048
    v=A("1.01")
    ybar=v*M/(M-1)
    T=U.exp()
    H=arb(3*10**12)
    # Uniform for the whole interpolation strip, 1/2 <= Re z <= 3/2.
    e=A(".000001")
    check(T>10**10 and ((1+2/T)/v)**M<e, "inner rational window")
    check(M*4/T<1 and 1/(1-(A(".5")+2/T)**M)<1+e, "outer rational window")
    kap=arb.pi()/(8*ybar**2)
    if fine:
        sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"right"/"fine"))
        from verify_fine import right_endpoint
        k3=right_endpoint(U,delta,kap,W,logh,signed_high=signed,signed_low=signed_low)[0]
    else:
        k3=coarse_endpoints(U,delta,kap,W,logh)[2]
    # The same c1,c2 as in right/PROOF.md, Section 2.
    divisors={1:1}
    for p in (2,3,5,7,11):
        divisors.update({p*d:-sign for d,sign in divisors.copy().items()})
    density=sum(arb(sign)/d**2 for d,sign in divisors.items())
    offset=sum((max(sign,0)-2*sign*arb(d).log())/d**2 for d,sign in divisors.items())
    m0=(1+A("2/3")*A("6/5").sqrt()).sqrt()
    check(T*logh.exp()>2310**2 and density*(W/3+logh)+offset>0,
          "harmonic squarefree estimate")
    c1=density+(density*(W/3+logh)+offset)/U
    taper_integral=2*(W+logh).exp()/W**2*(1-(1+W)*(-W).exp())
    c2=arb.pi()*m0*((density*taper_integral+16/T)/U+c1/(2*T))
    cm=c1*ybar+c2
    # Only rows whose height is already attained are eligible.
    rows=[(10**10,"34.842","1.3897e16"),(10**15,"31.170","4.4328e21"),
          (10**20,"29.364","9.6675e26")]
    log2=arb(2).log()
    check(U>4*log2,"fourth moment correction decreases")
    c4=1/(2*arb.pi()**2)+min(A(b)*(1-log2/U)**3/U+A(c)/(T*U**4)
                                 for start,b,c in rows if T>=start)
    c4*=v**(1+4/U)*M/(M-1-4/U)
    left=(c4**A(".25")*cm.sqrt()+ybar**A(".75")/U**A("1.5"))**A("4/3")
    l0=(1+e)**2/(1-1/H)
    return left,arb(0),k3,l0
