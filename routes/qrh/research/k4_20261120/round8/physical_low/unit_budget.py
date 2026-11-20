"""Budget at L=116 after removing the entire empty range of presieved lcms."""
from pathlib import Path
import sys
from flint import arb,ctx,fmpz
from actual_split import constants,costs
from presieved_empty import run
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/"round7"/"physical"))
from odd_sieve import denominator


def budget(P,C=1732099):
    z,c,r,I,mass,peaks,u=constants(C)
    _,upstream,remote=costs(C)
    eta=arb(int(fmpz(P).euler_phi()))/P
    G=denominator(z,P)
    main=u*(2*r).exp()*mass*eta/G
    k,_,_,empty=run("116",C,P,True)
    return k,main,upstream+remote,empty,1-main-upstream-remote-empty


if __name__=="__main__":
    ctx.prec=160
    for p in (2,6,30,210):
        k,*values=budget(p)
        print(p,k,*(v.str(15) for v in values),flush=True)
