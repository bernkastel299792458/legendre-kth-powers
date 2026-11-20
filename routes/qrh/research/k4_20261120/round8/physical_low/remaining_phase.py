"""Direct composition of the Q=210 first band, signed low phase and smooth tails."""
from fractions import Fraction
from flint import arb,ctx
from unit_budget import budget
from presieved_prefix import run as physical
from compact_spline import run as spline
from phase_window import run as low
if __name__=="__main__":
    ctx.prec=144;Q=210;C=1732099;cut=23;J=4*10**18
    _,main,other,_,_=budget(Q,C)
    _,_,prefix=physical(C,Q,37,cut,True,False)
    _,increase,ordinary,wedge,tiny=spline(C,Q,cut,".0002",J,64,"70.7")
    first=low(C,Q,cut,Fraction(1))
    rem=1-main-other-ordinary-(prefix+first)*(1+increase)-wedge-tiny
    print("remaining signed normalized allowance",rem.str(18),"phase in (1,",str(Fraction(J*cut,Q)),"]")
    assert rem>arb(".00236860")
