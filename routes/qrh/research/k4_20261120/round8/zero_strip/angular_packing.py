"""Insert separately certified three/four-frequency source groups into a hinge allocation."""
from flint import arb
from angular_certificate import certify


def geometry(nodes,frequency,frozen,step):
    assert 6%step==0 and 450%step==0
    count=14;stride=6//step;gap=arb(3)/1000
    groups=[]
    for offset in range(stride):
        last=len(nodes)-2-offset
        ids=tuple(last-(count-1-j)*stride for j in range(count))
        assert ids[0]>0 and 1300+ids[0]*step+count*6>=1750
        groups.append(ids)
    info={}
    for positive,degree in ((True,3),(False,4)):
        k,wt,c,M,modes=certify(gap*frequency,count,positive,degree,weight_step=frozen*gap,details=True)
        assert k>0 and M>0
        # For each interpolation line both Poisson multipliers at 140 are checked
        # below 10^-7. The same is then true at each actual mode frequency.
        co=[k*w+arb('1e-7')*sum(map(abs,cs),arb(0)) for w,cs in zip(wt,c,strict=True)]
        info[positive]=(wt,co,M)
    return groups,info


def candidates(geo,positive,sources,src_groups,caps,weights,scalar):
    groups,info=geo
    for mode in ((True,False) if positive else (False,)):
        wt,co,M=info[mode]
        for ids in groups:
            price=None
            for fam,jlist in src_groups.items():
                edge=M*sources[jlist[0]][3]
                totals=None
                for ix,coeff in zip(ids,co,strict=True):
                    rows=caps(ix,fam,1)
                    if totals is None:totals=[edge+coeff*v for v in rows]
                    else:totals=[z+coeff*v for z,v in zip(totals,rows,strict=True)]
                for z in totals:price=z if price is None else price.min(z)
            # All these interior knots are on the uniform 1/2000 integer lattice.
            # Their physical coefficients differ exactly by exp(frozen*j*.003).
            original=sum((w*scalar[i] for i,w in zip(ids,wt,strict=True)),arb(0))
            yield tuple((ix,10**6) for ix in ids),weights[ids[0]]*(original-price)
