"""Disjoint positive four-prime families with the same true physical gap criterion."""
from flint import arb,ctx
from actual_split import constants
from prime_gap_block import bound

def total(grid=72,asymmetric=False):
    z=constants(1732099)[0]
    edges=[100,300,1000,3000,10000,30000,100000,300000,1000000,10000000,100000000,1000000000,10000000000,30000000000]
    ranges=list(zip(edges,edges[1:]));cost=arb(0);cells=boxes=0
    for i,(al,ah) in enumerate(ranges):
        for j in range(i,len(ranges)):
            bl,bh=ranges[j]
            cap=int((z/bh**2).lower().floor().unique_fmpz())-1
            paircap=int((z/(ah*bh)).lower().floor().unique_fmpz())-1
            if (paircap if asymmetric and i!=j else cap)<=2500:continue
            top=min(al-1,cap,500000)
            if top<=50:continue
            if asymmetric and i!=j:top=(min(bl-1,paircap,500000),top)
            n,val=bound(grid=grid,top=top,spatial=True,refined=True,small_range=(al,bh),
                        specific=((al,ah),(bl,bh)) if i!=j else None)
            cost+=val;cells+=n;boxes+=1
    return boxes,cells,cost

if __name__=="__main__":
    import argparse
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument("--grid",type=int,default=72)
    ap.add_argument("--lower");ap.add_argument("--asymmetric",action="store_true");a=ap.parse_args();ctx.prec=144
    b,n,v=total(a.grid,a.asymmetric);print("small-prime boxes, prime-product cells, negative margin",b,n,v.str(15))
    if a.lower:assert v>arb(a.lower)
