"""Certified radial bounds for a family of integer-degree zero detectors."""
from flint import arb


def radial_bound(q, nu):
    t=nu/2
    # v=log(1+r^2/q). Its positive maximizing critical point solves
    # 1-exp(-v)-t*v=0, and lies above -log(t).
    lo=-t.log()
    hi=arb(2)/t
    for _ in range(45):
        mid=(lo+hi)/2
        sign=-(-mid).expm1()-t*mid
        if sign>0:
            lo=mid
        elif sign<0:
            hi=mid
        else:
            break
    return (q+1)*hi/(2*(q*lo.expm1())**t)


def coefficient(lo,hi):
    # Supremum on the exponent interval occurs at one of the endpoints.
    return min(radial_bound(q,lo).max(radial_bound(q,hi))
               for q in range(3,9))
