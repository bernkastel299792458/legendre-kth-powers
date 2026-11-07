"""Independent float check of T_N and H2' (repair Lemma 3.1' / R2'), N = 1e10. Sanity only."""
import mpmath as mp
mp.mp.dps = 30
N = mp.mpf(10) ** 10
LN = mp.log(N)
g = lambda u: u * mp.exp(-u) * (mp.li(mp.exp(u)) - mp.li(N))
umax = max((LN * (1 + i / 2000.0) for i in range(4001)), key=g)
print("T_N: argmax u=%s (y=%s), max=%s" % (mp.nstr(umax, 8), mp.nstr(mp.exp(umax), 6), mp.nstr(g(umax), 12)))
print("     g at u = LN*[1.2,1.5,2,3,5]:", [mp.nstr(g(LN * t), 8) for t in (1.2, 1.5, 2, 3, 5)])
# H2' = sup_{t>=N} log t * sum_k 2^-k |m(t/2^k)| bound, as in repair: k-th term 0.0144/log(t/2^k) if t/2^k >= 96955
x0 = mp.mpf(96955)
def H2(t):
    s = mp.mpf(0); k = 0
    while t / 2 ** k >= 1:
        u = t / 2 ** k
        s += 2 ** (-k) * (mp.mpf("0.0144") / mp.log(u) if u >= x0 else mp.sqrt(2 / u))
        k += 1
    return s * mp.log(t)
for t in (N, 2 * N, 10 * N, 1e12, 1e15):
    print("  t=%s: log t * sum 2^-k bound(t/2^k) = %s" % (mp.nstr(t, 3), mp.nstr(H2(mp.mpf(t)), 10)))
