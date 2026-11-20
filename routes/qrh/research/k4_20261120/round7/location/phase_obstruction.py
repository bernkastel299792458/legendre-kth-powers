"""A finite arithmetic phase condition at the midpoint of each potential prime gap."""
import argparse
import sys
from flint import arb,arb_mat,ctx
from location_moments import research
sys.path.insert(0,str(research/"round6"/"reduction"))
from irregular import call_rows,validate_slabs
from tables import H,get_data
from grid_target import weights,dot


def test(cut=814,quarter=37,width_text="1.7",sub=2,tight=False):
    h0=arb(3*10**12)
    hh=arb(H)
    width=arb(width_text)
    beta=arb(cut)/1000
    nodes=8
    assert 1<=width<=2 and 650<cut<875 and 1<=quarter<100 and 2<=sub<=32
    validate_slabs(phased=True)
    logs,counts,real,raw,remote,remote_cap=get_data(nodes,phased=True)
    rows=call_rows([],logs,raw,real,nodes)
    Ls=[arb(j)/sub for j in range(115*sub,(736*sub)//5+1)]
    full=[weights([real],L) for L in Ls]
    partial=[weights([real[:cut-650+1]],L) for L in Ls]
    complete=arb_mat([v[1:] for v in full])*arb_mat(rows).transpose()
    truncated=arb_mat([v[1:] for v in partial])*arb_mat([r[:cut-650] for r in rows]).transpose()
    top=hh*(arb(quarter)/4).exp()
    t=[u.exp() for u in logs]
    # Select the first node provably above the requested ordinate.
    index=next(i for i,z in enumerate(t[1:]) if z>top)
    thresholds=[arb(0),arb(".01"),arb(".02"),arb(".05"),arb(".10"),arb(".2"),arb(".4")]
    best=[None]*len(thresholds)
    minsignal=maxerror=None
    for j,L in enumerate(Ls):
        span=(arb(1)/sub+arb("1e-10")) if tight else arb(1)
        # 4 log(1+1/n) <= 4 exp(-L/4) for every candidate in this cell.
        assert 4*(-L/4).exp()<arb("1e-10")
        M=((L+span)/4).exp()
        d=width/M
        tc=2/d
        envelope=[arb(1).min((tc/z)**2) for z in t]
        above=[arb(1).min((tc/z.max(top))**2) for z in t]
        fringe=2*(tc**2)*((beta-1)*L).exp()*(1+logs[-1])/t[-1]
        part=hh*hh.log()*(-L/2).exp()+fringe
        rem=(tc/t[-1])**2*dot(weights(remote,L),remote_cap)
        height_tail=rem
        absolute=rem
        for i in range(len(counts)):
            full_mass=full[j][0]*counts[i]+complete[j,i]
            smaller=(partial[j][0]*counts[i]+truncated[j,i]).min(((beta-1)*L).exp()*counts[i])
            part+=(envelope[i]-envelope[i+1]).max(arb(0))*smaller
            absolute+=(envelope[i]-envelope[i+1]).max(arb(0))*full_mass
            height_tail+=(above[i]-above[i+1]).max(arb(0))*full_mass
        critical=2*h0*h0.log()*(d-L/2).exp()
        powers=(L+span+d)**2*(3*d/2-L/2).exp()/(2*d*arb(2).log())
        trivial=(-3*(L-d)).exp()/(1-(-2*(L-d)).exp())
        effect=d*d.exp()*(full[j][0]*counts[index]+complete[j,index])
        # K(i gamma) is exactly sinc^2(d gamma/2), nonnegative.
        signal=(1-critical-powers-trivial)/2-d.exp()*(part+height_tail)-effect
        assert signal>0
        minsignal=signal if minsignal is None else minsignal.min(signal)
        maxerror=effect if maxerror is None else maxerror.max(effect)
        for i,q in enumerate(thresholds):
            # beta<=7/8, so one positive summand is at most exp(-L/8).
            number=((signal-q*absolute)/(1-q))*(L/8).exp()
            best[i]=number if best[i] is None else best[i].min(number)
    print("arithmetic midpoint phase, real part >",cut,"height quarter",quarter,
          "absolute phase approximation error",maxerror.str(14),"signal",minsignal.str(14))
    for q,v in zip(thresholds,best,strict=True):
        print("cosine threshold",q.str(5),"resonating zero count lower",v.str(13),flush=True)
    if (cut,quarter,width_text,sub,tight)==(814,37,"2",8,True):
        assert best[0]>596115 and best[3]>429637 and best[4]>244661
        assert minsignal>arb(".34068033") and maxerror<arb("4.46e-11")
    return best


if __name__=="__main__":
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--width",default="1.7")
    cli.add_argument("--sub",type=int,default=2)
    cli.add_argument("--tight",action="store_true")
    a=cli.parse_args()
    ctx.prec=160
    test(width_text=a.width,sub=a.sub,tight=a.tight)
