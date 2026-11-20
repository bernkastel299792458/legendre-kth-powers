"""Checked logarithmic height slabs for the cumulative positive-part moments."""
from pathlib import Path
import sys
from flint import arb,ctx

here=Path(__file__).resolve().parent
research=here.parents[1]
sys.path.insert(0,str(research/"round5"/"kernel"))
from finite_anchor import row_constants,A
from grid_target import curves
from radial_detectors import bound as radial

TRIPLE=(".92","9.5","-3.5")
H=3000175332800
LOW="115.035950"
LAST="162.3"
SCALE=10**12
SLABS=list(zip([28]+list(range(30,55,2)),range(30,57,2)))

def checked_constants():
    """Integer upper bounds for K1,K3,Ec on each finite height slab."""
    for low,high in SLABS:
        U=arb("28.7") if low==28 else arb(low)
        d,l,r,ec=row_constants(U,arb(high),*map(A,TRIPLE),32768,True,True,16)
        print(low,high,*[int((x*SCALE).upper().ceil().unique_fmpz()) for x in (l,r,ec)],flush=True)

def extra_constants(phased=False):
    sys.path.insert(0,str(research/"round6"/"folds"))
    from fold_mean import joint,source
    from short_block import normalized_row
    if phased:
        from shifted_harmonic import disjoint_fourth
    _,w,lh=map(A,TRIPLE)
    for lo,hi in SLABS:
        U=A("28.7") if lo==28 else arb(lo)
        V=arb(hi)
        pieces=int((2*(V-U)).upper().ceil().unique_fmpz())
        left=arb(0)
        for j in range(pieces):
            l,h=U+(V-U)*j/pieces,U+(V-U)*(j+1)/pieces
            val=joint(l,h,w,lh,ncore=2097152,base=30)[0]
            if phased:
                for base in (30,210):
                    def cm(u,ww,hh,q):
                        return source(u,ww,hh,q,base,12)
                    def m4(u):
                        return disjoint_fourth(u,base,A("1.25"),A(".06"),384)
                    val=val.min(normalized_row(l,h,210,2097152,w,lh,cm,fourth_fn=m4,
                                               sieve_base=base,small_factor=arb(1)/12)[0])
            left=left.max(val)
        yield lo,hi,int((left*SCALE).upper().ceil().unique_fmpz())

if __name__=="__main__":
    ctx.prec=160
    if sys.argv[1:] in (["--extra"],["--phased"]):
        for row in extra_constants(sys.argv[1:]==["--phased"]): print(*row,flush=True)
    else: checked_constants()
