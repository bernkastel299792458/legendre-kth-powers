"""Credit the single-vector spectral slope on the actual prime coefficients."""
from pathlib import Path
import sys
from flint import arb
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/"round5"/"mean"))
from local_energy import gram_bounds


def saving(U,V,d,W,lh,cutoff,q=2310):
    assert q==2310 and (V is U or V>=U) and U>=30
    v=arb("1.01");a=arb("1.03")
    eps=(v*U.exp())**(-arb(1)/5)
    corr=((1+eps)*eps*(2*eps**3).exp()).exp()/(1-4*eps/arb.pi())
    scale=q*v*a*(1+eps)*(eps**3).exp()/arb.pi()
    j=int((scale/cutoff).upper().floor().unique_fmpz())+1
    _,outer=gram_bounds(q,max(32,j))
    e=2*d/U
    good=1-2*a**(-2048)
    res=arb(0)
    # On p >= z_i T the orientation-independent Fourier count is <= i.
    last=arb(outer[j])/10**6
    for i in range(j-1,0,-1):
        nxt=last.min(arb(outer[i])/10**6)
        gain=last-nxt
        z=(scale/i+arb(".01")).max(arb(cutoff))
        logp=V+z.log()
        # For p>X the coefficient is one. Between Y and X it is log(p/Y)/W.
        coeff=((z.log()-lh)/W).min(arb(1)).max(arb(0))
        tail=-(1+e)*(-e*logp).ei()-arb("1.25506")*(-e*logp).exp()/logp
        assert tail>0 and scale/z<i
        res+=gain*tail*coeff**2
        last=nxt
    return good*corr*arb.pi()*res/(q*V)


if __name__=="__main__":
    from flint import ctx
    ctx.prec=160
    val=saving(arb(37),arb("37.125"),arb("1.16"),arb("9.5"),arb(-3),160)
    print("absolute deduction from right mean",val.str(15),flush=True)
