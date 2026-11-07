# -*- coding: utf-8 -*-
"""
Recompute the recursion of the proof of Corollary 2 (l.379-422 of arXiv:2507.15184v2):
  C2(T)       = (2/pi^2) T log^4 T + 2*C1*T log^{7/2} T + M2(3e3,6e3)_upper
  M2(1e4,2e4) <= C2(1e4),   M2(1e4) <= C2(1e4/2) + M2(3e3)_upper
  for n=5..10, A_n={1..n-4}:
  M2(10^n,2.10^n) <= min{ C2(10^n), min_i [10^n/pi^2 log^4 10^n + 2.10^n M1(10^{n-i}) log^3 10^n + M2(10^{n-i},2.10^{n-i})] }
  M2(10^n)        <= min{ C2(10^n/2)+M2(3e3)_up, min_i [10^n/(2pi^2) log^4(10^n/2) + M1(10^{n-i}) 10^n log^3(10^n/2) + frakM2(10^{n-i})] }
  frakM2(10^n) >= M2(10^n) + M2(10^n,2.10^n).
Then Corollary 4: a1(A0), a2(A0) at log10 A0 = 11.46.
Arb throughout.  Run: python -I recursion.py [C1] [M2_3e3_up] [M2_3e3_6e3_up] [M1 overrides as n=val,...]
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cs4_formulas import Q, PI, arb, ctx

ctx.prec = 128

TABLE2 = {  # n: (M1, frakM2, M2(T0)<=, M2(T0,2T0)<=)
    4: ("59.300", "1.3796e9", "3.8095e8", "9.9857e8"),
    5: ("48.801", "2.8051e10", "8.7748e9", "1.9276e10"),
    6: ("43.230", "4.1722e11", "1.3688e11", "2.8034e11"),
    7: ("39.720", "5.8170e12", "1.8478e12", "3.9692e12"),
    8: ("37.550", "7.9793e13", "2.5002e13", "5.4791e13"),
    9: ("36.211", "1.0629e15", "3.3317e14", "7.2965e14"),
    10: ("34.842", "1.3897e16", "4.3883e15", "9.5079e15"),
}


def QE(s):
    """'1.3796e9' -> exact arb"""
    if "e" in s:
        m, e = s.split("e")
        return Q(m) * arb(10) ** int(e)
    return Q(s)


def up(x):
    return x.mid() + x.rad()


def run(C1, M2a, M2b, M1, use_table_downstream=True, verbose=True):
    """C1, M2a=M2(3e3) upper, M2b=M2(3e3,6e3) upper, M1: dict n->arb"""
    def C2(T):
        return 2 / PI ** 2 * T * T.log() ** 4 + 2 * C1 * T * T.log() ** Q("3.5") + M2b

    res = {}
    U = {}   # M2(10^n,2 10^n) bound used downstream
    V = {}   # M2(10^n) bound
    F = {}   # frak M2 used downstream
    T = arb(10) ** 4
    U[4] = C2(T)
    V[4] = C2(T / 2) + M2a
    F[4] = U[4] + V[4]
    res[4] = (V[4], U[4], F[4], None, None)
    for n in range(5, 11):
        T = arb(10) ** n
        cand_U = [("C2", C2(T))]
        cand_V = [("C2", C2(T / 2) + M2a)]
        for i in range(1, n - 3):
            k = n - i
            Uk = QE(TABLE2[k][3]) if use_table_downstream else U[k]
            Fk = QE(TABLE2[k][1]) if use_table_downstream else F[k]
            cand_U.append(("i=%d" % i, T / PI ** 2 * T.log() ** 4 + 2 * T * M1[k] * T.log() ** 3 + Uk))
            cand_V.append(("i=%d" % i, T / (2 * PI ** 2) * (T / 2).log() ** 4 + M1[k] * T * (T / 2).log() ** 3 + Fk))
        bu = min(cand_U, key=lambda p: float(up(p[1])))
        bv = min(cand_V, key=lambda p: float(up(p[1])))
        U[n], V[n] = bu[1], bv[1]
        F[n] = U[n] + V[n]
        res[n] = (V[n], U[n], F[n], bu[0], bv[0])
    if verbose:
        print("  n | M2(10^n) <=        (paper)    | M2(10^n,2.10^n) <=   (paper)   | frakM2 = sum   (paper)   | argmin U,V | all <= paper")
        for n in range(4, 11):
            v, u, f, iu, iv = res[n]
            p = TABLE2[n]
            ok = (v <= QE(p[2])) and (u <= QE(p[3])) and (f <= QE(p[1]))
            print("  %2d | %.6e (%s) | %.6e (%s) | %.6e (%s) | %s,%s | %s"
                  % (n, float(up(v)), p[2], float(up(u)), p[3], float(up(f)), p[1], iu, iv, ok))
    return res


def a12(A0, M1_10, frakM2_10, U10):
    LA = A0.log()
    l2 = arb(2).log()
    a1 = 1 / (2 * PI ** 2) * A0 * (A0 / 2).log() ** 4 + M1_10 * A0 * (A0 / 2).log() ** 3 + frakM2_10
    a2 = (1 / (2 * PI ** 2) * (1 - l2 / LA) ** 4 + M1_10 / LA * (1 - l2 / LA) ** 3 + U10 / (A0 * LA ** 4))
    return a1, a2


if __name__ == "__main__":
    args = sys.argv[1:]
    C1 = Q(args[0]) if len(args) > 0 else Q("20.7225")
    M2a = QE(args[1]) if len(args) > 1 else QE("7.032e5")
    M2b = QE(args[2]) if len(args) > 2 else QE("1.25e6")
    M1 = {n: Q(TABLE2[n][0]) for n in TABLE2}
    if len(args) > 3:
        for kv in args[3].split(","):
            k, v = kv.split("=")
            M1[int(k)] = Q(v)
    print("Inputs: C1=%s  M2(3e3)<=%s  M2(3e3,6e3)<=%s" % (C1.str(8), M2a.str(8), M2b.str(8)))
    print("M1:", {k: M1[k].str(8) for k in sorted(M1)})
    print("--- (a) downstream uses the TABLE values (verifies each table entry given the earlier ones)")
    ra = run(C1, M2a, M2b, M1, True)
    print("--- (b) pure chain (downstream uses the recomputed values)")
    rb = run(C1, M2a, M2b, M1, False)
    A0 = arb(10) ** Q("11.46")
    for lab, F10, U10 in (("paper constants", QE("1.3897e16"), QE("9.5079e15")),
                          ("pure chain", rb[10][2], rb[10][1])):
        a1, a2 = a12(A0, M1[10], F10, U10)
        print("Cor.4 at log10 A0=11.46 with %s: a1 = %s, a2 = %s" % (lab, a1.str(10), a2.str(10)))
    # paper-constant a2 at A0=1e10 (sanity) and asymptote
    a1p, a2p = a12(A0, Q("34.842"), QE("1.3897e16"), QE("9.5079e15"))
    print("   main term share of a2: 1/(2pi^2)(1-log2/logA0)^4 = %s" %
          (1 / (2 * PI ** 2) * (1 - arb(2).log() / A0.log()) ** 4).str(8))
