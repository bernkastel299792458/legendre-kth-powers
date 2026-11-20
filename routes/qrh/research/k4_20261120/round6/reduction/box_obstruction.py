"""Check feasible reflected test populations for the finite certified hinge constraints."""
from flint import arb,ctx
from coupled import H,SIX,height_data,conditions
from tables import validate_slabs

def run(nheight=16,sharp=True):
    hs,D,real,hinges,_,_=height_data(nheight,True,True,sharp,ctx.prec)
    ceilings=[conditions(hs[0]+arb(k)/4,arb(m)/1000) for k,m in SIX]
    fractions=list(map(arb,("16.94","16.96","15.03","18.43","22.78","32.18")))
    for index,(k,m) in enumerate(SIX):
        j=2+k*(nheight//4)
        beta=arb(m)/1000+arb(1)/10**6
        assert beta<arb(7)/8 and 1-beta<real[0]
        T=arb(H)*(arb(k)/4).exp()
        assert hs[j].exp()+10**9<T
        required=int(ceilings[index].floor().unique_fmpz())+1
        possible=D[j]/2
        future=D[j]/2
        at_target=D[j]
        threshold=arb(m)/1000
        for a,v in zip(real,hinges[j],strict=True):
            if a<threshold:at_target=at_target.min(v/(threshold-a))
        for i in range(j,len(D)):
            current=D[i]/2
            for a,v in zip(real,hinges[i],strict=True):
                if a<beta:current=current.min(v/(beta-a))
                if a<threshold:future=future.min(v/(threshold-a))
            possible=possible.min(current)
        analytic=possible/required
        for l,(kk,s) in enumerate(SIX):
            if l!=index and kk>=k and arb(s)/1000<beta:
                possible=possible.min(ceilings[l])
        multiplier=1
        while (multiplier+1)*required<possible:multiplier+=1
        assert multiplier>=1 and multiplier*required<possible
        assert multiplier==[3,2,15,18,4,32][index]
        assert analytic>fractions[index]
        assert at_target<[18473370,7196025,157825660,66932550,26385740,163220660][index]
        print(k,m,"first failing integer",required,"hinge and total caps / first failing",
              analytic.str(9),"direct rigorous count upper bound",at_target.str(11),
              "including later true height nodes",future.str(11),
              "certified multiplier also honoring the other five",multiplier,flush=True)
    simultaneous=3*sum((1/f for f in fractions),arb(0))
    assert simultaneous<arb(".941282")
    print("three times all six first-failing populations / every analytic allowance",
          simultaneous.str(14),flush=True)
    # Among the optional 1,2,4-step windows after these six heights (and H),
    # the only one meeting a population is (T_6,T_7], containing population 2.
    assert nheight==16
    ends=[k*(nheight//4) for k,_ in SIX]
    hits=[(start,start+w,j) for start in [0]+ends for w in (1,2,4)
          for j,e in enumerate(ends) if start<e<=start+w]
    assert hits==[(24,28,1)]
    from local_calls import hinges as local_hinges
    nodes=[arb(k)/1000 for k in range(650,876)]
    z=local_hinges(24,28,16,nodes,shrink=True)
    b=arb(865001)/10**6
    local=arb(0)
    for s,a in zip(nodes,z,strict=True):
        if s<b:local=local.max(3*420071*(b-s)/a)
    assert local<arb(".175149")
    print("simultaneous witness / every optional increment allowance",local.str(14),flush=True)

if __name__=="__main__":
    ctx.prec=160
    validate_slabs(phased=True)
    run()
