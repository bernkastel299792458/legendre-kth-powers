"""Mixed fourth harmonic on a positive time cell with power-law, paired cutoffs."""
from math import comb
from flint import arb
from periodic_fourth import period,weighted_disc,f


def bound(c,j,q,xscale,yscale,p):
    t,u=c-j,c+j
    root=(c/(2*arb.pi())).sqrt()
    lo=[xscale*root*(t/c)**p,yscale*root*(t/c)**(1-p)]
    hi=[xscale*root*(u/c)**p,yscale*root*(u/c)**(1-p)]
    vals=[list(map(abs,period(q,a))) for a in (False,True)]
    m=[arb(sum(v))/q for v in vals]
    disc=[f(weighted_disc(v)) for v in vals]
    M=[rho+d/n.sqrt() for rho,d,n in zip(m,disc,lo)]
    d=arb(0)
    for rho,ds,n in zip(m,disc,lo):d=d.max(ds/(rho*n))
    h=u.sqrt()
    def integral(k):
        ans=h*d**k
        ans+=k*d**(k-1)*(1+2*h).log()
        for n in range(2,k+1):
            ans+=comb(k,n)*d**(k-n)*(arb(2)**(n-1)-(h+arb(".5"))**(1-n))/(n-1)
        return ans
    common=M[0]**2*M[1]**2/(2*arb.pi())
    top=common*(u**2-t**2)/2*(1/(h+arb(".5"))+d)**4
    vertical=common*(u+t)*integral(4)
    jumps=arb(0)
    for i,exponent in enumerate((p,1-p)):
        if exponent.is_zero():continue
        other=1-i
        num=(m[i]*(hi[i]-lo[i])+disc[i])
        jumps+=2*M[i]*M[other]**2*hi[other]*num/q
    return (top+vertical+jumps*integral(3))/2
