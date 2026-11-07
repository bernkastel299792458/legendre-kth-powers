"""Float sanity check (not a proof) that Phase-0's per-representative bound Hn dominates the exact per-r sum
  delta * sum_s w(|g_r - g_s|),  w(D) = min(K/(2 delta), 1/D) for D < 1,  S(D) for D >= 1,
for adversarial representative configurations in boxes of height lam*delta (one rep per box, every box non-empty).
The sup over theta of the configuration is approached by putting r at position theta in its box and every other
rep at the end of its box nearest to r (the extremal configuration in the referee's derivation), scanning theta."""
import math, sys

def S(y, a0):
    return math.sqrt(2 * math.pi) * math.exp((1.5 - 2 * a0) * math.log(y) - math.pi * y / 2 + 1 / (6 * y))

def IS(a0, n=200000, Y=40.0):
    h = (Y - 1) / n
    return sum(S(1 + h * (i + 0.5), a0) for i in range(n)) * h

def Hn_phase0(lam, K, J1, dmax, a0):
    half = 0.5
    m = lambda d: K / 2 if d == 0 else min(K / 2, 1 / (lam * d))
    dstar = 2 / (K * lam)
    tot = K / 2; j = 1
    if J1 >= 1 and dstar <= 0.5:
        tot += K / 2 + 1 / (lam * (1 - dstar)); j = 2
    while j <= J1 and not (j - 1 >= dstar):
        tot += m(j - 1) + m(j - 0.5); j += 1
    for i in range(j, J1 + 1):
        tot += (1 / (i - 1) + 1 / i) / lam
    return tot + 2 * dmax * S(1, a0) + 2 / lam * IS(a0)

def exact(lam, delta, K, a0, theta, nside):
    h = lam * delta
    tot = K / 2 * 1.0                      # s = r (units: delta * weight)
    for side in (+1, -1):
        for j in range(1, nside + 1):
            D = ((j - theta) if side > 0 else (j - 1 + theta)) * h
            D = max(D, 1e-15)
            if D < 1:
                tot += delta * min(K / (2 * delta), 1 / D)
            else:
                tot += delta * S(D, a0)
    return tot

if __name__ == '__main__':
    worst_ratio = 0
    for a0 in (0.9927, 0.985, 0.98):
        for Zc in (5.558691, 4.896):
            for L in (28.8, 50.0, 80.0, 100.0):
                nu = 1 / (Zc * L)
                for lam in (1.0, 4.0, 9.7, 11.0, 13.3):
                    K = 1.0
                    J1 = int(math.floor(1 / (lam * nu))) + 2
                    for delta in (nu, (nu + (1 - a0)) / 2, 1 - a0):
                        if delta < nu: continue
                        Hb = Hn_phase0(lam, K, J1, 1 - a0, a0)
                        nside = int(60 / (lam * delta)) + 5
                        ex = max(exact(lam, delta, K, a0, th / 200, nside) for th in range(0, 201))
                        rat = ex / Hb
                        worst_ratio = max(worst_ratio, rat)
                        if rat > 0.995:
                            print(f"a0={a0} Z={Zc} L={L} lam={lam} delta={delta:.5f}: exact={ex:.5f} Hn={Hb:.5f} ratio={rat:.5f}")
    print("max exact/Hn over grid:", round(worst_ratio, 6))
