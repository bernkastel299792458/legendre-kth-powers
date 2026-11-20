"""Location moments of a putative empty fourth-power interval, with finite ordinates."""
import argparse
from math import factorial
from pathlib import Path
import sys

from flint import arb,ctx

research=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(research/"round2"/"local"))
from check_exceptional import bounds


def frequency_factor(k,cut=None):
    """Taylor expand only the differences of the tuple decay rates."""
    lowest=arb(k)/8
    highest=k*(1-arb(cut)/1000) if cut is not None else 7*arb(k)/8
    s=(lowest+highest)/2
    r=(highest-lowest)/2
    norm=arb(1)
    for j in range(1,33):
        t=arb(1).min(j/s)
        norm+=(-s*t).exp()*(r*t)**j/factorial(j)
    # j! >= (j/e)^j; maximizing over all nonnegative times gives (r/s)^j.
    norm+=(r/s)**33/(1-r/s)
    return arb.pi()*norm**2/(2*arb(1).sin()**2)


def slab_energies(blocks,nheight,cut,top_quarters,width):
    """Bound the coefficient square sum by integrating the zero hinges in height."""
    sys.path.insert(0,str(research/"round6"/"reduction"))
    from irregular import call_rows,validate_slabs
    from tables import H,get_data
    from grid_target import weights,dot
    from flint import arb_mat
    # The certified slab constants were generated with the 160-bit mesh choices.
    with ctx.workprec(160):
        validate_slabs(folded=True,phased=True)
    logs,base,real,raw,remote,remote_cap=get_data(nheight,folded=True,phased=True)
    rows=call_rows([],logs,raw,real,nheight)
    w=[weights([real],2*L) for L in blocks]
    hinge=arb_mat([v[1:] for v in w])*arb_mat(rows).transpose()
    if top_quarters is not None:
        short_w=[weights([real],L) for L in blocks]
        short_hinge=arb_mat([v[1:] for v in short_w])*arb_mat(rows).transpose()
        assert 0<top_quarters<100
        top=arb(H)*(arb(top_quarters)/4).exp()
    if cut is not None:
        assert 650<cut<875
        stop=cut-650
        capw=[weights([real[:stop+1]],L) for L in blocks]
        lowhinge=arb_mat([v[1:] for v in capw])*arb_mat([r[:stop] for r in rows]).transpose()
        beta=arb(cut)/1000
    t=[u.exp() for u in logs]
    hh=arb(H)
    out=[]
    removed=[]
    far=[]
    for j,L in enumerate(blocks):
        m=((L+1)/4).exp()/width
        assert hh<2*m and 2*m<t[-1] and logs[-1]==55
        envelope=[arb(1).min((2*m/z)**4) for z in t]
        q=hh*hh.log()*(-L).exp()
        q+=4*(2*m)**4*(-3*logs[-1]-L/4).exp()*(logs[-1]/3+arb(1)/9)
        for i,(lo,hi) in enumerate(zip(envelope,envelope[1:])):
            q+=(lo-hi).max(arb(0))*(w[j][0]*base[i]+hinge[j,i])
        out.append((2/m).exp()*q)
        low=arb(0)
        if cut is not None:
            cap=((beta-1)*L).exp()
            low=hh*hh.log()*(-L/2).exp()
            low+=2*(2*m)**2*cap*(1+logs[-1])/t[-1]
            linear=[arb(1).min((2*m/z)**2) for z in t]
            for i,(lo,hi) in enumerate(zip(linear,linear[1:])):
                mass=(capw[j][0]*base[i]+lowhinge[j,i]).min(cap*base[i])
                low+=(lo-hi).max(arb(0))*mass
            low*=(1/m).exp()
        removed.append(low)
        residual=arb(0)
        if top_quarters is not None:
            assert top<t[-1]
            residual=(2*m/t[-1])**2*dot(weights(remote,L),remote_cap)
            capped=[arb(1).min((2*m/z.max(top))**2) for z in t]
            for i,(lo,hi) in enumerate(zip(capped,capped[1:])):
                mass=short_w[j][0]*base[i]+short_hinge[j,i]
                residual+=(lo-hi).max(arb(0))*mass
            residual*=(1/m).exp()
        far.append(residual)
    return out,removed,far


def calculate(nheight=None,cut=None,top_quarters=None,width_text="1",through=297):
    H=arb(3*10**12)
    width=arb(width_text)
    assert width>=1 and width<2
    degrees=range(2,16)
    signed={k:arb(0) for k in degrees}
    unsigned=signed.copy()
    factors={k:frequency_factor(k,cut) for k in degrees}
    max_energy=max_tail=arb(0)
    lowest=arb(1)/2
    witness_counts=None
    assert 294<=through<=297
    blocks=[arb(half)/2 for half in range(230,through+1)]
    assert (cut is None and top_quarters is None) or nheight
    slab=slab_energies(blocks,nheight,cut,top_quarters,width) if nheight else None
    for j,L in enumerate(blocks):
        energy,deficit,M,d=bounds(L,L,coefficient_energy=True)
        if width_text!="1":
            energy*=(2*(width-1)*d).exp()
            d=width/M
            critical=2*H*H.log()*(d-L/2).exp()
            powers=(L+1+d)**2*(3*d/2-L/2).exp()/(2*d*arb(2).log())
            trivial=(-3*(L-d)).exp()/(1-(-2*(L-d)).exp())
            deficit=1-critical-powers-trivial
        if slab is not None: energy=energy.min(slab[0][j])
        assert M>8 and 4*(-L/4).exp()<arb(1)/2
        Y=(3*L/8+15).exp()
        assert Y>2/d and 2/d>H
        tail=2*(d-L/8).exp()*(2/d)**2*(1+Y.log())/Y
        if top_quarters is not None: tail=slab[2][j]
        signal=deficit/2-tail
        if cut is not None: signal-=slab[1][j]
        if not signal>0:
            raise ArithmeticError(f"cut {cut}/1000 exhausts the signal at L={L}: {signal}")
        assert signal>0
        max_energy=max_energy.max(energy)
        max_tail=max_tail.max(tail)
        lowest=lowest.min(signal)
        for k in degrees:
            threshold=2*(2-width)*signal**(2*k)/M
            diag=factorial(k)*energy**k
            signed[k]=signed[k].max(diag/threshold)
            unsigned[k]=unsigned[k].max(factors[k]*diag/threshold)
            if k==3 and cut is not None and top_quarters is not None:
                # Delete all common labels. For three tuples the matching coefficients
                # for zero, one and two matched labels are respectively 1, 9 and 18.
                room=threshold/factors[k]-diag
                if room>0:
                    single=(d-L/8).exp()
                    limits=[room/(3*c*energy**(3-i)*single**(2*i))
                            for i,c in ((1,18),(2,9),(3,1))]
                    witness_counts=limits if witness_counts is None else [
                        x.min(y) for x,y in zip(witness_counts,limits,strict=True)]
                else:
                    witness_counts=[arb(0)]*3
    print(len(blocks),"blocks, positive coefficient square sum",max_energy.str(14),
          "discarded positive-height tail",max_tail.str(14),"signal lower",lowest.str(14),flush=True)
    if cut is not None:
        print("removed beta up through",cut,"maximum absolute cost",max(slab[1]).str(14))
    if witness_counts is not None:
        print("necessary alternatives, ordered near pairs at multiplicities 1,2,3:",
              *(v.lower().floor().unique_fmpz() for v in witness_counts),flush=True)
        if (nheight,through,cut,top_quarters,width_text)==(8,294,814,37,"1.7"):
            assert unsigned[3]<arb(".111763") and lowest>arb(".23026741")
            assert all(v>n for v,n in zip(witness_counts,(
                2655276,15968322816888,432136936418540421553),strict=True))
    for k in degrees:
        print("moment",2*k,"signed diagonal fraction",signed[k].str(12),
              "positive near-sum diagonal fraction",unsigned[k].str(12),flush=True)
    if cut is None and top_quarters is None and width_text=="1":
        assert signed[7]<arb(".019440") and unsigned[7]<arb(".115327")
        if nheight==8: assert signed[3]<arb(".001221") and unsigned[3]<arb(".006008")
    return signed,unsigned


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--slabs",type=int,help="certified log-height subdivisions per unit")
    parser.add_argument("--cut",type=int,help="discard ordinates with real part at most cut/1000")
    parser.add_argument("--top-quarters",type=int,help="truncate all blocks at H exp(q/4)")
    parser.add_argument("--width",default="1",help="tent half-width times exp((L+1)/4)")
    parser.add_argument("--through",type=int,default=297,help="twice the last block origin")
    args=parser.parse_args()
    ctx.prec=192
    calculate(args.slabs,args.cut,args.top_quarters,args.width,args.through)
