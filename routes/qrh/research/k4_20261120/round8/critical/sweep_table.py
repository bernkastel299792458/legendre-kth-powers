"""Amortize complete fourth-moment half-lines over many log-height queries."""
from functools import lru_cache

from flint import arb,ctx

from rational_fourth import fourth as rational
from sweep_boundary import finite


@lru_cache(maxsize=4096)
def _piece(i,j,den,q,alpha,width,Z,limit,prec):
    assert prec==ctx.prec and i<j
    return finite(arb(i)/den,q,arb(alpha),arb(width),Z,arb(j-i)/den,limit)


def index(u,den=8):
    """Round the entire input enclosure down to a safe left endpoint."""
    if den<1:
        raise ValueError("positive grid denominator needed")
    return int((arb(u)*den).lower().floor().unique_fmpz())


def table(heights,den=8,q=210,alpha=".82",width=".34",Z=384,limit=65536,tail_length=10):
    """Return {index(u,den): rigorous bound on every height from u onward}."""
    requested={index(u,den) for u in heights}
    if not requested or tail_length<1:
        raise ValueError("supply heights and a positive integer tail length")
    upper=(max(requested)//den+1)*den
    end=upper+tail_length*den
    suffix=rational(arb(end)/den,q,arb(1),arb(".04"),Z)
    options=den,q,alpha,width,Z,limit,ctx.prec
    for i in range(end-den,upper-1,-den):
        suffix=suffix.max(_piece(i,i+den,*options))
    results={}
    for i in range(upper-1,min(requested)-1,-1):
        suffix=suffix.max(_piece(i,i+1,*options))
        if i in requested:
            results[i]=suffix
    return results


if __name__=="__main__":
    ctx.prec=160
    rows=table([arb(37),arb(37)+arb(1)/4],den=4)
    for i,value in sorted(rows.items()):
        assert value<arb(".000755")
        print("log-height >=",arb(i)/4,"uniform fourth bound",value.str(15))
