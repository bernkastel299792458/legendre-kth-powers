"""A universal lower bound for the monotone spectrum moment of every positive window."""

import numpy as np
from flint import arb, ctx
from scipy.optimize import linprog
from scipy.sparse import bmat, csr_matrix, diags, eye


def candidate(frequency):
    # This floating calculation proposes a rational witness. Its solver status
    # and primal objective play no part in the verified lower bound.
    y=np.array(frequency)/16
    t=np.linspace(0,.5,513)
    F=csr_matrix(np.cos(y[:,None]*t))
    m,n=F.shape
    chain=diags([-np.ones(m-1),np.ones(m-1)],[0,1],shape=(m-1,m))
    inequalities=bmat([[F,-eye(m)],[-F,-eye(m)],[None,chain]],format="csr")
    objective=np.r_[np.zeros(n),np.diff(np.r_[1.45**.4,y**.4])]
    solution=linprog(objective,A_ub=inequalities,b_ub=np.zeros(inequalities.shape[0]),
                     A_eq=csr_matrix(np.r_[np.ones(n),np.zeros(m)][None,:]),b_eq=[1],
                     method="highs")
    if not solution.success:
        raise ArithmeticError("failed to propose signed coefficients")
    multipliers=solution.ineqlin.marginals
    return [int(10**6*c) for c in -multipliers[:m]+multipliers[m:2*m]]


def lower_bound():
    frequency=list(range(24,192))+list(range(192,960,2))+list(range(960,3840,8))
    raw=candidate(frequency)
    p=arb(2)/5
    floor=arb(29)/20
    floor_power=floor**p
    prefix=0
    rows=[]
    for a,c in zip(frequency,raw,strict=True):
        prefix+=abs(c)
        y=arb(a)/16
        if not arb(prefix)/10**6 <= y**p-floor_power:
            raise ArithmeticError("failed rational prefix check")
        if c:
            rows.append((y,arb(c)/10**6))
    second=sum(abs(c)*y*y for y,c in rows)
    steps=4096
    values=[arb(0) for _ in range(steps+1)]
    for y,c in rows:
        theta=y/(2*steps)
        cs,sn=theta.cos(),theta.sin()
        for start in range(0,steps+1,64):
            co,si=(theta*start).cos(),(theta*start).sin()
            for index in range(start,min(start+64,steps+1)):
                values[index]+=c*co
                co,si=cs*co-sn*si,sn*co+cs*si
    minimum=values[0]
    for val in values[1:]:
        minimum=minimum.min(val)
    bound=floor_power+minimum-second/(8*(2*steps)**2)
    if not bound>arb("1.893"):
        raise ArithmeticError("lower bound is too weak")
    return bound


if __name__=="__main__":
    ctx.prec=160
    print("All positive windows, p=2/5 and floor 1.45:",lower_bound().str(16))
