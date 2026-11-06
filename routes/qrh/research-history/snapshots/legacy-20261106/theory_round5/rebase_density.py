"""Rebase CS v2 Theorem 1 at a higher T0; no old file is modified.

The only non-elementary scalar is Gamma in an analytic upper bound for K1.
This remains conditional on CS v2 Theorem 1 / Corollary 5 and finite RH.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import runpy
from fractions import Fraction
from pathlib import Path

from flint import arb, ctx

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
HELPER = ROOT / "code" / "certify_k4_round3.py"
HELPER_HASH = "665413028150b9eafa96d51071e2864da5408086393b91d6ea8e956798e7ea16"
OUTPUT = HERE / "rebased_density_certificate.json"
PROOF = HERE / "PROOF.md"
SOURCE = "https://arxiv.org/html/2507.15184v2"


def require(test, message):
    if not test:
        raise ValueError(message)


def A(value):
    q = Fraction(value)
    return arb(q.numerator) / q.denominator


def power(x, y):
    require(x > 0, "Power base")
    return (y * x.log()).exp()


def ceil_decimal(x, digits=12):
    scale = 10 ** digits
    n = (x * scale).ceil().unique_fmpz()
    require(n is not None, "Rounding unresolved")
    n = int(n)
    return f"{n // scale}.{n % scale:0{digits}d}"


def constants(log_t0=80, log_a0=75):
    U, V = arb(log_t0), arb(log_a0)
    T, AA, H = U.exp(), V.exp(), arb(3) * 10**12
    d, kap, delta = A("3/10"), A("3/20"), A("1/5")
    pi, eg = arb.pi(), arb.const_euler()
    m0 = (1 + A("2/3") * A("6/5").sqrt()).sqrt()
    require(T >= H and H >= 1002 and U >= 2*d and U >= arb(1).exp(), "Theorem 1 T domains")
    require(T >= 3*10**10 and 0 < delta <= U/20 and AA >= 10**10, "Theorem 1 / Corollary 5 domains")
    require(A("17/32") > A("1/2") + d/U, "First rebased sigma endpoint")
    C1 = 6/pi**2 + A("1.048")/U
    C2 = pi*m0*A("0.62")/U + 6*m0/(pi*T) + pi*m0*A("1.048")/(T*U)
    C3 = pi*m0*A("0.54")/(2*delta) * (2*delta*eg/U).exp()
    C4 = A("0.54")/(5*delta*delta.exp()) + A("0.605")*(-2*delta).exp()/U
    z = 9*(1+(2+eg+7/(36*T))/U)**2*U**2/T
    require(0 < z < 1, "Logarithm in C5/C6")
    C5 = -(-z).log1p()*(3+8*pi*m0)*(1+A("3.31")/U)/(9*(1+(2+eg+7/(36*T))/U)**2)*U
    C6 = 220 + pi/arb(2).log()*(T**(-A("3/2"))).log1p()
    C6 += 4/arb(2).log()*(((5/(2*H))**2+(1+2/H)**2).sqrt()/(2*pi)).log()
    C6 -= 2*pi/arb(2).log()*(-z).log1p()
    a1 = AA*(V-arb(2).log())**4/(2*pi**2) + A("34.842")*AA*(V-arb(2).log())**3 + A("1.3897e16")
    a2 = (1-arb(2).log()/V)**4/(2*pi**2) + A("34.842")/V*(1-arb(2).log()/V)**3 + A("9.5079e15")/(AA*V**4)
    L0 = (kap*(1+((1+2*delta/U)/(4*T))**2)).exp()/(1-1/H)
    K3 = C3 + C4*((pi.sqrt()/2)/(2*kap).sqrt()+pi*m0/T)
    K2 = power(arb(2), A("1/3"))*(3/(4*kap)).sqrt()*pi.sqrt()/2
    K2 += power(arb(2), A("1/3"))*4*kap/3*(AA/T)**3

    # (1 + log(1+a*u)/(2U))^(4/3) <= D exp(c*u).
    # Concavity/subadditivity splits (C1*sqrt(a*u)+C2)^(2/3).
    a, v = 3/(4*kap), 2/(3*U)
    c = v*a/(1+a)
    D = (v*((1+a).log()-a/(1+a))).exp()
    require(0 < c < 1, "Gamma integral decay")
    integ = D*(power(C1*a.sqrt(), A("2/3"))*A("3/2").gamma()/power(1-c,A("3/2"))
               + power(C2,A("2/3"))*A("7/6").gamma()/power(1-c,A("7/6")))
    K1_upper = power(2*a2*a.sqrt(),A("1/3"))*integ
    K1_upper += power(2*a1,A("1/3"))*power(C2+AA*C1/T,A("2/3"))/(power(T,A("1/3"))*power(U,A("4/3")))
    require(K3 > 1 and L0 > 1, "Negative exponent maxima become one")
    # The full A1 expression is increasing in K1, so an upper bound suffices.
    L1_upper = power(K1_upper,3*delta/U).max(arb(1))*(3*delta+4*delta*U.log()/U).exp()
    L2 = power(K2,3*delta/U).max(arb(1))*(3*delta).exp()
    rows = [("5.069", "9.461", "167.8")]
    raw = []
    for i in range(17, 28):
        s, t = arb(i)/32, arb(i+1)/32
        fixed = power(L0,2/(2-s)).max(power(L0,2/(2-t)))
        fixed *= power(K3,(2*s-1)/(2-s)).max(power(K3,(2*t-1)/(2-t)))
        AA1 = L1_upper*(d*(3+4*U.log()/U)).exp()*power(K1_upper,3*d/U).max(arb(1))*fixed
        AA1 *= power(K1_upper,3*(1-s)/(2-s)).max(power(K1_upper,3*(1-t)/(2-t)))
        AA2 = L2*(3*d).exp()*power(K2,3*d/U).max(arb(1))*fixed
        AA2 *= power(K2,3*(1-s)/(2-s)).max(power(K2,3*(1-t)/(2-t)))
        bracket = (3-2*s)/(2*d)+1/U
        AA3 = bracket/(pi*arb(2).log())
        AA4 = 3*bracket/(2*arb(2).log())
        AA5 = C6/(2*pi)*bracket+C5/(2*pi*d)
        B1 = (AA1+AA2*power(U,-6*(1-t)/(2-t)))/(2*pi*d)
        B2, B3 = AA3+AA4, AA3*H.log()+AA5
        rows.append(tuple(ceil_decimal(b) for b in (B1,B2,B3)))
        raw.append(dict(sigma=[str(Fraction(i,32)),str(Fraction(i+1,32))], B1=B1.str(45), B2=B2.str(45), B3=B3.str(45)))
    return rows, dict(log_T0=log_t0,log_A0=log_a0,H="3000000000000",h="1",d="3/10",kappa="3/20",delta="1/5",
        scalars={k:x.str(45) for k,x in dict(C1=C1,C2=C2,C3=C3,C4=C4,C5=C5,C6=C6,a1=a1,a2=a2,L0=L0,K1_upper=K1_upper,K2=K2,K3=K3,L1_upper=L1_upper,L2=L2,gamma_decay=1-c).items()},rows=raw)


def calculate(L0=362, denominator=65536):
    ctx.prec = 256
    require(hashlib.sha256(HELPER.read_bytes()).hexdigest() == HELPER_HASH, "Frozen helper changed")
    rows, details = constants()
    helper = runpy.run_path(str(HELPER))
    # Mutate only this isolated in-memory global dictionary, never source files.
    helper['certify_point'].__globals__['CS_ROWS'] = tuple(rows)
    point = helper['certify_point'](L0, denominator)
    U = (A("16/7")*(1+(arb(L0)/4).exp()/4)).log()
    require(U > 80, "Every nonflat kernel height >= T0=e^80")
    rates = dict(main=arb(1)/24-3/(4*U)-1/arb(L0),baseline=arb(1)/4-1/(4*U),
                 second=arb(1)/8-2/(4*U)-1/arb(L0),third=arb(1)/8-1/(4*U)-1/arb(L0),prime_powers=arb(1)/4-2/arb(L0))
    require(all(x>0 for x in rates.values()), "Positive rates for continuous budget")
    return dict(schema="k4-rebased-cs-round5-v1",status="POINT_AND_ANALYTIC_RATES_CHECKED" if point['passed'] else "BOUND_NOT_BELOW_ONE",
        full_k4_proved=False,L0=str(L0),n_lower_log=str(Fraction(L0,4)),source=SOURCE,
        inputs=["QRH(7/8)","CS v2 Theorem 1, Corollary 5, and original first Table 1 row", "Finite RH to 3e12", "Rosser total count and integrated explicit formula"],
        rows=[list(row) for row in rows],derivation=details,point=point,u0=U.str(45),decay_rates={k:x.str(45) for k,x in rates.items()},
        helper_sha256=HELPER_HASH,script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        proof_sha256=hashlib.sha256(PROOF.read_bytes()).hexdigest(),
        scope="Numerical scalar bounds supporting a separate written proof, not end-to-end formalization.")


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--point',type=int,default=362)
    parser.add_argument('--denominator',type=int,default=65536)
    parser.add_argument('--save',action='store_true')
    parser.add_argument('--verify',action='store_true')
    args=parser.parse_args()
    fresh=calculate(args.point,args.denominator)
    if args.verify:
        require(json.loads(OUTPUT.read_text(encoding='utf-8'))==fresh,"Replay differs")
        print('VERIFIED '+fresh['point']['delta_ball'])
    elif args.save:
        require(fresh['point']['passed'], "Cannot save failed candidate as certificate")
        OUTPUT.write_text(json.dumps(fresh,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
        print('SAVED '+str(OUTPUT))
    else:
        print(json.dumps(fresh,ensure_ascii=False,indent=2))


if __name__ == '__main__':
    main()
