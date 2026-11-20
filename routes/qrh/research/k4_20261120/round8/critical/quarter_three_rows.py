"""Replay all mollifier multiples on the primitive denominators 1, 13, 17."""
import argparse
from flint import arb,ctx
from quarter_long_row import result
from quarter_rational_rows import price
from quarter_local_mertens import local

def run(verify=False,denominators=(1,13,17)):
    ctx.prec=144
    if verify:
        from quarter_mertens_finite import run as scan
        from quarter_weighted_mertens import NANOS
        got=scan()
        assert [i for i,_ in got]==list(range(18,30))
        assert [n for _,n in got]==list(NANOS)
    d0=100000;base=result(d0);out=arb(0)
    for s in denominators:
        parts=price(s,d0,base,ctx.prec)
        beta=arb('.008191074') if s==1 else arb('.008191074')*(1+1/arb(s))+arb('1.16')/(s*(s-1))
        u,j=local(s,d0,beta)[-2:]
        row=sum(parts[1:4])+u+j
        print('s',s,'head, time, arithmetic, u and j short, total before common nonstationary',
              *(x.str(14) for x in (*parts[1:4],u,j,row)),flush=True)
        out+=row
    print('selected complete denominators, with common nonstationary and cost to beat from remaining pieces',
          (out+20522030).str(15),(arb('9446212020')-out).str(15))
    if list(denominators)==[1,13,17]:assert out+20522030 < -arb('27478716220')

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--verify-table',action='store_true')
    ap.add_argument('--denominators',type=int,nargs='+',default=[1,13,17]);args=ap.parse_args()
    assert len(set(args.denominators))==len(args.denominators)
    run(args.verify_table,args.denominators)
