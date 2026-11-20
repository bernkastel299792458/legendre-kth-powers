"""Join the published-input low endpoint to the stronger squarefree sieve."""
from flint import arb, ctx
from physical_tail import refine
from squarefree_farey import added_denominator


def verify():
    ctx.prec = 192
    eta = "1.16613"
    assert arb("1.1328")+added_denominator()>arb(eta)
    for lo,hi,parts,res in (("115.033660","115.034610",512,256),
                            ("115.034610","115.034625",1024,512)):
        total = refine(lo,hi,-206000,parts=parts,res=res,addition=eta)[0]
        assert total<1
        print(lo,hi,total.str(18),flush=True)
    end = (arb(hi)/4).exp().floor().unique_fmpz()
    assert end==3088344337091 and 4*arb(end).log()<arb(hi)<4*arb(end+1).log()
    print("last integer",end)


if __name__=="__main__":
    verify()
