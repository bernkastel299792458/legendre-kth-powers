"""Whole new prime-interval slab using the frozen fourth-moment detector."""
from flint import arb, ctx
from moving_window import A, scalar


def verify():
    ctx.prec=192
    lo,hi="115.033675","115.034000"
    total,zeros,_=scalar(lo,hi,1100000000,8,frozen=True)
    end=(A(hi)/4).exp().floor().unique_fmpz()
    assert total<arb(".999994") and 4*arb(end).log()<A(hi)<4*arb(end+1).log()
    print(lo,hi,"upper normalized cost",total.str(18),"high zeros",zeros.str(17),
          "last integer",end,flush=True)


if __name__=="__main__":
    verify()
