"""Recompute the dilated sieve caps and apply them to the physical exterior lobes."""
import argparse
from flint import arb,ctx
from dilation import denominator
from cover import full

LOCATION="115.4"
TABLE=(("3",1024,"3.0827"),("4",2048,"3.8794"),("6",4096,"4.4783"),
       ("5",4096,"4.8033"),("5",4096,"4.8602"),("5",4096,"4.6736"))
WEIGHTED=(("5",1024,"3.9465"),("6",2048,"4.6404"),("7",2048,"4.9876"),
          ("7",4096,"5.0939"),("5",4096,"5.0089"),("5",4096,"4.8274"))


def check_table(weighted=False):
    for i,(c,order,limit) in enumerate(WEIGHTED if weighted else TABLE,83):
        pieces=4 if weighted and i!=87 else 1
        for j in range(pieces):
            eta=denominator(i+j/pieces,i+(j+1)/pieces,c,order,reciprocal=True,
                            location_hi=LOCATION,weighted=weighted)
            assert eta>arb(limit)


def physical(left,right,qrh,weighted=False):
    settings=tuple(row[2] for row in (WEIGHTED if weighted else TABLE))
    high=".005937108818" if qrh else None
    value,saving=full(left,right,16000000000 if qrh else -206000,"auto",high,
                      cell_bounds=settings,location_hi=LOCATION)
    print(left,right,"QRH" if qrh else "unrestricted","cost",value.str(18),
          "sieve saving",saving.str(12),flush=True)
    return value


if __name__=="__main__":
    arg=argparse.ArgumentParser(description=__doc__)
    arg.add_argument("--table",action="store_true")
    arg.add_argument("--weighted",action="store_true")
    arg.add_argument("--lo")
    arg.add_argument("--hi")
    arg.add_argument("--qrh",action="store_true")
    arg.add_argument("--diagnose",action="store_true")
    a=arg.parse_args()
    ctx.prec=192
    if a.table:check_table(a.weighted)
    if a.lo is not None:
        value=physical(a.lo,a.hi,a.qrh,a.weighted)
        if not a.diagnose:assert value<1
