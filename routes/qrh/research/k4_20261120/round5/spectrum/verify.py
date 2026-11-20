"""Full fourth-power budget with a sparse critical polynomial and localized right norm."""
import argparse
from pathlib import Path
import sys

from flint import arb, ctx

research = Path(__file__).resolve().parents[2]
for folder in ("round4/euler","round4/density","round5/left","round5/mean","round5/kernel"):
    sys.path.insert(0,str(research/folder))
from verify_euler import A, check, verify as previous
from direct_high import direct_high
from mellin_low import mellin_low_rows
from local_energy import local_right_rows
from six_energy import fourth
from critical_mean import critical_mean


def moments(U, delta, W, logh, q, frequency_cut, short=None, mix=None,tight=False):
    order, v = 2048, A("1.01")
    ybar = v*order/(order-1)
    cm = critical_mean(U,W,logh,q=q,mix=mix)
    c4 = fourth(U)*v**(1+4/U)*order/(order-1-4/U)
    left = (c4**A("1/4")*cm.sqrt()+ybar**A("3/4")/U**A("3/2"))**A("4/3")
    if short is not None:
        left = left.min(short(U,W,logh,q))
    outer = {} if q==210 else dict(spacing=210,outer_spacing=q,frequency_cut=frequency_cut)
    effective=W
    if mix is not None:
        from mixed_low import mixed_low_rows
        last_width,theta=mix
        # The local certificates require all complementary divisors to lie
        # below exp(W). Check that domain using the smaller width first.
        cap=arb(210)*A("1.01")*A("1.03")*(1+(A("1.01")*U.exp())**(-A("1/5")))
        cap*=((A("1.01")*U.exp())**(-A("3/5"))).exp()/arb.pi()
        if q!=210:
            cap=A(frequency_cut)
        check(1+cap/logh.exp() < W.exp(),"local cells below the shorter transition")
        effective=1/((1-theta)/W+theta/last_width)
        low=mixed_low_rows(U,delta,W,last_width,theta,logh,q,cells=16,tight=tight)
    elif tight:
        from mixed_low import mixed_low_rows
        low=mixed_low_rows(U,delta,W,W,arb(0),logh,q,cells=16,tight=True)
    else:
        low=mellin_low_rows(U,delta,W,logh,q,cells=16)
    hilbert,local,tail = local_right_rows(U,delta,effective,logh,q,cells=16,**outer)
    high = direct_high(U,delta,W,logh,q)
    if mix is not None:
        high=(1-theta)*high+theta*direct_high(U,delta,last_width,logh,q)
    emax = 2*delta/U
    right = arb(0)
    for i,(low_cell,local_cell) in enumerate(zip(low,local,strict=True)):
        upper = emax*(i+1)/len(local)
        discount = (-2*delta-upper*logh).exp()
        right = right.max(discount*(hilbert*low_cell+
                          (local_cell+tail*high)*upper/(2*delta)))
    return left,right


def verify(anchor, shift, transition, cutoff, q=210, frequency_cut="100"):
    L, delta, W, logh = map(A,(anchor,shift,transition,cutoff))
    U = L/4-A("1.02")
    fixed,old_left,old_right,terms = previous(
        anchor,q,210,shift,transition,cutoff,split_left=True,fold="density",breakdown=True)
    left,right = moments(U,delta,W,logh,q,frequency_cut)
    ratio = left/right
    for s_int in range(650,869):
        s = arb(s_int)/1000
        c = 3*delta/(2-s)
        check(c+1+c/U < (U*ratio).log(),"height correction at the new moments")
    total = fixed
    for contribution,exponent in terms:
        total += contribution*(left/old_left)**(1-exponent)*(right/old_right)**exponent
    print("improved L",anchor,"K1",left.str(14),"K3",right.str(14),"total",total.str(20),flush=True)
    return total


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--anchor",default="170")
    cli.add_argument("--shift",default=".92")
    cli.add_argument("--transition",default="9.5")
    cli.add_argument("--cutoff",default="-3.5")
    cli.add_argument("--diagnose",action="store_true")
    cli.add_argument("--modulus",type=int,choices=(210,2310),default=210)
    cli.add_argument("--frequency-cut",default="100")
    args = cli.parse_args()
    ctx.prec = 192
    result = verify(args.anchor,args.shift,args.transition,args.cutoff,args.modulus,args.frequency_cut)
    if not args.diagnose:
        check(result<1,"strict full half-line budget")
