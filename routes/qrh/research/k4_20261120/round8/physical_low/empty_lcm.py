"""All complete dyadic/gcd rectangles whose lcm exceeds the physical location."""
from functools import lru_cache
from flint import arb,ctx,fmpz
from row_inputs import norm,PERRON,MEAN


@lru_cache(None)
def primes(n):
    return tuple(int(p) for p,_ in fmpz(n).factor())


@lru_cache(None)
def local(n,s100,prec):
    s=arb(s100)/100
    v=arb(1)
    for p in primes(n):
        x=arb(p);w=x**(-s)
        v/=1-w+w/(x-1)
    return v


@lru_cache(None)
def inner(i,g,s100,prec):
    assert ctx.prec==prec
    B=2**(i+1)
    return local(g,s100,prec)*sum((local(b,s100,prec)/int(fmpz(b).euler_phi())
                          for b in range(1,B) if fmpz(b).moebius_mu() and fmpz(b).gcd(g)==1),arb(0))


def conditional_rows(table,z):
    v0=16*arb(10).log()
    rows=[(v0,arb(".006688")/v0)]
    for j in range(37,67):
        v=arb(".006688")/j
        for start,val in table:
            if j>=start:v=v.min(arb(val))
        rows.append((arb(j),v))
    return rows


def region(L,C,table=(),partial=False,whole_cut=None,threshold=None,sieve_mod=1,uniform=False):
    h=arb(3000175332800);x=arb(L).exp();z=arb(C)*(x/h).sqrt()
    r=arb("1e-6");d=(4*(-arb(L)/4).exp()).log1p()/2;c=arb(L)+d
    a=(1-arb("1e-12"))*h*d
    assert r>d and z.log()<66 and arb("1.33258")-arb("2.44")/z.sqrt()>arb("1.331")
    X=(c+r).exp() if threshold is None else threshold
    cut=(z*z/((1 if partial else 4)*X)).floor().unique_fmpz(); assert cut is not None
    cut=int(cut) if whole_cut is None else int(whole_cut)
    assert sieve_mod>=1 and fmpz(sieve_mod).moebius_mu()
    density=arb(int(fmpz(sieve_mod).euler_phi()))/sieve_mod
    G=(z.log()+arb("1.331"))*density
    rows=conditional_rows(table,z)
    params=(0,10,20,25,30,33,35,37,39,41,43,45,47)
    @lru_cache(None)
    def single(i,g):
        conductor=sieve_mod*g
        scale=2**(i+1)*g/z
        ns=[norm(100-t,200-2*t,ctx.prec)*inner(i,conductor,100-t,ctx.prec)
            for t in params]
        val=rows[-1][1]*ns[0]
        for k in range(1,len(rows)):
            level,eps=rows[k]
            change=(rows[k-1][1]-eps).max(arb(0))
            if change.is_zero():continue
            base=scale*level.exp();v=ns[0]
            for t,norm0 in zip(params[1:],ns[1:]):
                v=v.min(base**(arb(t)/100)*norm0)
            val+=change*v
        hurst=None
        for t in (5,8,10,12,15,20):
            v=(scale*z**(arb(t)/100)).sqrt()*norm(50,100+t,ctx.prec)
            hurst=v if hurst is None else hurst.min(v)
        return val+inner(i,conductor,50,ctx.prec)*hurst
    total=arb(0);boxes=0
    if partial:
        # Ramaré Theorem 3.1 gives this for real D>=32; verify all smaller cells.
        assert arb(2).log()+arb("2.44")*(1+arb(2).sqrt())/arb(32).sqrt()<2
        for k in range(1,32):
            assert sum(arb(int(fmpz(n).moebius_mu())**2)/int(fmpz(n).euler_phi())
                       for n in range(k//2+1,k+1))<2
        Q=2000
        rho_norm=arb(1)
        for p in range(2,Q+1):
            if fmpz(p).is_prime():rho_norm*=1+arb(1)/(p-1)**2
        rho_norm=(rho_norm*(arb(1)/(Q-1)).exp()).sqrt()
    for g in range(1,cut+1):
        if not fmpz(g).moebius_mu() or fmpz(g).gcd(sieve_mod)>1:continue
        imax=(cut//g).bit_length()-1
        rho=arb(g)/int(fmpz(g).euler_phi())
        for i in range(imax+1):
            for j in range(imax+1-i):
                ray=z*z/(g*2**(i+j))
                if whole_cut is not None or (ray/4>=X and not uniform):
                    total+=rho**2/g*single(i,g)*single(j,g)
                else:
                    assert partial
                    wx=sum((arb(int(fmpz(b).moebius_mu())**2)/int(fmpz(b).euler_phi())
                        for b in range(1,2**(i+1)) if fmpz(b).gcd(sieve_mod*g)==1),arb(0))
                    wy=sum((arb(int(fmpz(b).moebius_mu())**2)/int(fmpz(b).euler_phi())
                        for b in range(1,2**(j+1)) if fmpz(b).gcd(sieve_mod*g)==1),arb(0))
                    mix=(wx*single(j,g)).min(wy*single(i,g))
                    total+=rho**2/g*(2*rho_norm/(2+arb(2).log()))*mix
                boxes+=1
    Q=(2+arb(2).log())**2/G**2*total*density
    full=(c+r)*(3*r/2).exp()*(1-a/arb.pi())*Q
    return boxes,Q,full


if __name__=="__main__":
    import argparse
    ctx.prec=160
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--ratio",type=int,default=10000000)
    ap.add_argument("--perron",action="store_true");ap.add_argument("--upper")
    ap.add_argument("--mean",action="store_true")
    ap.add_argument("--partial",action="store_true")
    a=ap.parse_args()
    assert not (a.mean and a.perron)
    b,q,c=region("116",a.ratio,MEAN if a.mean else PERRON if a.perron else (),a.partial)
    print("dyadic/gcd blocks",b,"signed inverse moment",q.str(15),"all near-lobe cost",c.str(15))
    if a.upper:assert c<arb(a.upper)
