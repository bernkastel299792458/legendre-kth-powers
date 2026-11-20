"""Grouped Fourier charges for the exact low-modulus complement at L=116."""
import argparse
from math import sqrt,log
import numpy as np
from numba import njit
from flint import arb,ctx
from actual_split import H,C0,constants,direct,costs
from bilinear import upper,lower
from extras.weight_energy import squarefree_groups,factors,paley,zero_frequency

@njit
def columns(gs,en,ep,zlo,zhi,root,rs):
    # Keep the edge classes distinguished for each requested exact product cutoff.
    rows=[]
    for a in range(len(gs)):
        ga,gb,gw=gs[a]
        for b in range(len(gs)):
            ha,hb,hw=gs[b]
            for i in range(en.shape[2]):
                if en[a,b,i]==0. or zhi/(ga*ha*2.**i)<1:continue
                for j in range(i+1):
                    if en[a,b,j]==0 or zhi/(ga*ha*2.**j)<1:continue
                    f=2.**(i+j);s=ga*f
                    lo=zlo/(gb*hb*2.**j);small=zlo/(gb*hb*2.**i)
                    di=min(1.,.5+1/lo);ei=min(1.,.5+1/small)
                    w=gw*hw/f*(1 if i==j else 2)
                    v=w*sqrt(en[a,b,i]*en[a,b,j]);p=w*sqrt(ep[a,b,i]*ep[a,b,j])
                    # bins of reciprocal modulus relative to x; interval lower representative only
                    bidx=0
                    while bidx<11 and s>=root*4.**bidx:bidx+=1
                    rows.append((s,gb*f,1/lo,1/small,di,ei,v,p,float(bidx)))
    return np.asarray(rows)

@njit
def block(data,n,last,wmain,wfej,zlo,zhi,tlo,thi,lg,phase,cc,rr,clip,exact):
    out=np.zeros((len(rr),12))
    for s,sup,id_,ie,di,ei,v,p,ib in data:
        kinv=zhi*zhi/(n*tlo*s);ktop=last*thi*sup/(zlo*zlo)
        # old formula's second term equals 32 Ktop/D/E
        old=di*(ie+32*ktop*id_*ie*ei)+4*lg*(kinv+32*ei*id_)
        spec=paley(ktop,kinv,1/id_,1/ie)
        rev=paley(ktop,kinv,1/ie,1/id_)
        trivial=sqrt(di*ei)
        raw=sqrt(min(di*ei,old,spec,rev))
        coeff=wfej*v+wmain*min(v,p*phase*last*sup)
        for ir in range(len(rr)):
            threshold=cc*rr[ir]
            if (exact and 4*sup<threshold) or (not exact and s<threshold):continue
            # If the group intersects q=x/R, its v-prefix depends on u.
            local=raw if not exact or s>threshold else min(trivial,clip*raw)
            out[ir,int(ib)]+=local*coeff
    return out


def run(C,rs,blocks,trunc_exp,near,Jexp,exact):
    z,c,r,I,mass,peaks,u=constants(C);G=z.log()+arb("1.331")
    assert blocks<=76 and trunc_exp<=52 and Jexp<=52
    tru=2**trunc_exp;order=2**Jexp;rr=np.array(rs,np.float64)
    gs=squarefree_groups(tru);en,ep=factors(gs,blocks,G,z,z)[:2]
    cc=C*C/H
    # Integer vs non-integer ray positions are separated, up to the largest
    # threshold, by at least 1/H. Check floating point comparisons exactly.
    for R in rs:
        assert int(cc*R)==C*C*R//H and cc*R-int(cc*R)>1e-10 and 1+int(cc*R)-cc*R>1e-10
    if not exact:assert max(C*C*v//H for v in rs)<32
    zmin,zmax=lower(z),upper(z)
    zmax0=int(z.upper().ceil().unique_fmpz())
    clip=upper(2+arb(2**(zmax0.bit_length())).log())
    zfr=zero_frequency(z,z)
    # A restricted Fejer zero term is positive and bounded by the unrestricted one.
    pref=u*arb(H)*(-c).exp()*peaks*z*z
    zer=pref*(zfr/G)**2/(order+1)
    tail=(1+arb(2).zeta())/tru+2*arb(2).zeta()**2/2**blocks
    data=columns(gs,en,ep,zmin,zmax,cc,rr)
    phase=upper(arb.pi()*(c+2*r).exp()/H/z**2*mass/peaks)
    matrix=np.zeros((len(rs),12));freq=np.zeros((len(rs),7))
    totalcoeff=arb(0);n=1
    print("rows",len(data),"clip",clip,"J",order,flush=True)
    while n<=order:
        last=min(2*n-1,order)
        wmain=2*(arb(last+1).digamma()-arb(n).digamma())/arb.pi()
        wfej=2*arb(last-n+1)/(order+1)
        value=block(data,n,last,upper(wmain),upper(wfej),zmin,zmax,lower((c-2*r).exp()),upper((c+2*r).exp()),upper(1+z.log()),phase,cc,rr,clip,exact)
        matrix+=value
        freq[:,min(6,(n.bit_length()-1)//8)]+=np.sum(value,axis=1)
        totalcoeff+=wmain+wfej;n=last+1
    # Nonnegative standard operations: at most len(data) + O(100)
    # roundings per addend. This margin covers 67 million double additions.
    assert len(data)<2**26
    scale=float((pref*(1+arb("1e-7"))).upper())*(1+2**-45)
    mat=matrix*scale;fr=freq*scale
    # Direct absolute tails need no curved-boundary separation penalty.
    extra=zer+pref*totalcoeff*tail
    print("zero, omitted h/g/i/j Fourier bound",zer.str(12),(extra-zer).str(12),flush=True)
    main=sum(costs(C));print("main included in final",main.str(15))
    for ir,R in enumerate(rs):
        d=sum(direct(C,R,near,exact)[2:])
        print("R",R,"product bands",*(format(v,".6g") for v in mat[ir]))
        print("R",R,"frequency bands",*(format(v,".6g") for v in fr[ir]))
        total=main+d+extra+arb(float(np.sum(mat[ir])))*(1+arb("1e-12"))
        print("R",R,"genuine large-q",(d).str(12),"full test cost",total.str(12),flush=True)
if __name__=="__main__":
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--C",type=int,default=C0);ap.add_argument("--R",type=int,nargs="+",default=[1,2,4,8])
    ap.add_argument("--blocks",type=int,default=64);ap.add_argument("--tail",type=int,default=50)
    ap.add_argument("--order",type=int,default=48);ap.add_argument("--mean",action="store_true")
    ap.add_argument("--rectangles",action="store_true");args=ap.parse_args();ctx.prec=144
    run(args.C,args.R,args.blocks,args.tail,args.mean,args.order,not args.rectangles)
