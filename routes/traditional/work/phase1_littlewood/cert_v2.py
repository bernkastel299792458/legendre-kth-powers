"""Version 2 of the profile (REPORT.md §11).
Extends v1 below log t = 30 (down to 28.73) and above 300 with geometric bands up to V1, where the profile meets the
refereed Vinogradov-Korobov region 1/(54.004 v^(2/3) (log v)^(1/3)) (Bellotti, JMAA 536 (2024)).
v1 (zfr_local_v1.csv) is not touched.

  python -I cert_v2.py design      -> profile_v2.json   (float search; not part of the proof)
  python -I cert_v2.py certify     -> zfr_local_v2.csv, cert_v2_summary.json, cert_v2_log.txt
"""
import os, sys; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import json, math, time
from zl_core import *
import cert_profile as CP

HERE = os.path.dirname(os.path.abspath(__file__))
V0 = 28.73                       # > log(3e12) = 28.7297...; below V0: MTY (and RH up to 3e12)
Z3_VK = arb('54.004')


def z_eff_vk(v):
    """VK width 1/(Z3 v^(2/3)(log v)^(1/3)) = l(t)/Z_eff with Z_eff = Z3 (log v)^(4/3)/v^(1/3); decreasing for log v > 4."""
    v = arb(v)
    return Z3_VK * v.log() ** (arb(4) / 3) / v ** (arb(1) / 3)


def make_zw(V1):
    """Window function for v2: above V1 the region counts as Z_above = min(21.233, Z_eff_VK(V1)) + 1e-20 (an upper
    bound for the effective constant of the better of the two published regions at every height > V1)."""
    zv = z_eff_vk(V1)
    z21 = arb(CP.Z2_ABOVE)
    above = (zv if zv.upper() < z21.lower() else z21) + arb('1e-20')
    above_up = arb(above.upper())

    def zw_window(profile, va, vb, V0_, V1_):
        lo = va + math.log1p(-1e10 * math.exp(-va)) - 1e-9 * max(1.0, va / 100)
        hi = vb + math.log(16 + 1e10 * math.exp(-va)) + 1e-9 * max(1.0, vb / 100)
        ups = []
        if lo < V0_:
            ups.append((CP.Z1_BELOW * arb(V0_).log()).upper())
        if hi > V1_:
            ups.append(above_up.upper())
        for (a, b, Zs) in profile:
            if b >= lo and a <= hi:
                ups.append(arb(Zs).upper())
        if not ups:
            return arb(0)
        m = ups[0]
        for u in ups[1:]:
            if u > m:
                m = u
        return arb(m)
    return zw_window, above_up


def best_lines(v, Z):
    """Up to 3 zeta lines n, best first, for a tiny cell at v with constant Z (float ranking)."""
    res = []
    for n in range(3, 19):
        r = cell_terms(arb(v), arb(v) + arb('1e-7'), arb(Z), arb(Z), n)
        if r is None:
            continue
        mu, PE = r
        G = CP.GT.lower(mu)
        res.append((float((PE / G).upper()), n))
    res.sort()
    return [n for _, n in res[:3]]


def z_local(v, Zw_extra=None, lines=None):
    if lines is None:
        lines = best_lines(v, 19.0 if v < 1000 else 13.0) or [3, 4, 5]
    lo, hi = 8.0, 24.0
    for _ in range(26):
        Z = (lo + hi) / 2
        Zw = Z if Zw_extra is None else max(Z, float(Zw_extra))
        n, _r = CP.cell_ok(v, v + 1e-7, Z, Zw, tuple(lines))
        if n is not None:
            hi = Z
        else:
            lo = Z
    return hi, list(lines)


def design(passes=3):
    CP.GT.check_increasing()
    v1 = json.load(open(os.path.join(HERE, 'profile_design.json')))
    edges = [V0, 29.0] + [float(a) for a, b, Z in v1['bands']] + [300.0]
    v = 300.0
    while True:
        nv = float(round(v * 1.05))
        zl, _ = z_local(nv)
        edges.append(nv)
        if zl >= float(z_eff_vk(nv).mid()):       # crossover with VK reached
            V1 = nv
            break
        v = nv
        if nv > 3e7:
            raise RuntimeError("no crossover")
    zw, above = make_zw(V1)
    CP.zw_window = zw
    prof = []
    for j in range(len(edges) - 1):
        a, b = edges[j], edges[j + 1]
        mid = (a + b) / 2
        prof.append([a, b, 0.0, best_lines(mid, 19.0 if mid < 1000 else 13.0) or [3, 4, 5]])
    for p in range(passes):
        new = []
        for (a, b, Zold, ln) in prof:
            pts = [a + (b - a) * q / 8 for q in range(9)] + [a + 1e-9 * max(1, a / 100), b - 1e-9 * max(1, b / 100)]
            pts += [x for x in (b - 2.8, b - 2.0, b - 1.0, b - 0.5) if x > a]
            zl = 0.0
            for x in pts:
                extra = None if p == 0 else zw([(q[0], q[1], f"{q[2]:.3f}") for q in prof if q[0] != a], x, x + 1e-7, V0, V1)
                z, l = z_local(x, extra, ln)
                zl = max(zl, z)
            new.append([a, b, math.ceil((zl * (1 + 2e-4)) * 1000) / 1000, ln])
        prof = new
        print("design pass", p, "done; V1 =", V1, flush=True)
    json.dump(dict(V0=V0, V1=V1, above_Z=above.str(20), bands=[[a, b, f"{Z:.3f}", ln] for a, b, Z, ln in prof]),
              open(os.path.join(HERE, 'profile_v2.json'), 'w'), indent=1)
    for a, b, Z, ln in prof:
        print(f"{a:10.2f} {b:10.2f} {Z:.3f} {ln}")


def run_certify(hmin_rel=2.5e-7):
    CP.GT.check_increasing()
    d = json.load(open(os.path.join(HERE, 'profile_v2.json')))
    V0_, V1 = float(d['V0']), float(d['V1'])
    zw, above = make_zw(V1)
    CP.zw_window = zw
    prof = [[float(a), float(b), str(Z)] for a, b, Z, ln in d['bands']]
    lines = [tuple(ln) + tuple(n for n in (3, 4, 5) if n not in ln) for a, b, Z, ln in d['bands']]
    orig_cell_ok = CP.cell_ok
    log = open(os.path.join(HERE, 'cert_v2_log.txt'), 'w')
    t0 = time.time()
    results = []
    for i in range(len(prof)):
        a, b = prof[i][0], prof[i][1]
        CP.cell_ok = (lambda va, vb, Z, Zw, lines_=(), _l=lines[i]: orig_cell_ok(va, vb, Z, Zw, _l))
        h0 = 0.004 * max(1.0, a / 100) * (0.5 if a >= 300 else 1.0)
        r = CP.certify_band(prof, i, V0_, V1, h0, hmin_rel * max(1.0, a))
        r['Z'] = prof[i][2]
        results.append(r)
        msg = (f"band ({a:.3f}, {b:.3f}] Z={prof[i][2]}: {'OK' if r['ok'] else 'FAIL'} cells={r['cells']} "
               f"minrel={r['minrel']:.2e} lines={r['lines']} {'fails=' + str(r['fails']) if not r['ok'] else ''} "
               f"t={time.time() - t0:.0f}s")
        print(msg, flush=True)
        log.write(msg + chr(10))
        log.flush()
    CP.cell_ok = orig_cell_ok
    allok = all(r['ok'] for r in results)
    with open(os.path.join(HERE, 'zfr_local_v2.csv'), 'w', newline='') as f:
        f.write("logt_lo,logt_hi,Z2,status,notes\n")
        for (a, b, Zs), r in zip(prof, results):
            f.write(f"{a:.10g},{b:.10g},{Zs},{'proved' if r['ok'] else 'FAILED'},own proof (thesis method; refereed inputs only); "
                    f"zeta line(s) n={'/'.join(map(str, r['lines']))}; cells={r['cells']}; min rel. margin={r['minrel']:.1e}\n")
    json.dump(dict(V0=V0_, V1=V1, above_Z=d['above_Z'], all_ok=allok, seconds=round(time.time() - t0),
                   bands=[dict(lo=a, hi=b, Z2=Zs, **{k: v for k, v in r.items() if k != 'Z'})
                          for (a, b, Zs), r in zip(prof, results)]),
              open(os.path.join(HERE, 'cert_v2_summary.json'), 'w'), indent=1)
    msg = f"ALL BANDS CERTIFIED: {allok} ({len(prof)} bands, {round(time.time() - t0)} s)"
    print(msg)
    log.write(msg + chr(10))
    log.close()


if __name__ == '__main__':
    if sys.argv[1:] == ['design']:
        design()
    elif sys.argv[1:] == ['certify']:
        run_certify()
    else:
        print(__doc__)
