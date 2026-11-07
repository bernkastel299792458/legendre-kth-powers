"""Local classical zero-free region (BTY method, our proof; REPORT.md §12).

  python -I cert_classical.py design    -> profile_classical.json  (float search; not part of the proof)
  python -I cert_classical.py certify   -> zfr_classical_local.csv, cert_classical_summary.json, cert_classical_log.txt

Needs cl_constants.json from check_cl.py (same Z_MIN, U_CUT).
"""
import os, sys; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import json, math, time
from flint import arb
import cl_core as C

HERE = C.HERE
V_LO = 28.7296                  # < log H = 28.72966 (zeros below H lie on the critical line)
V1 = 60.0                       # profile top; above it MTY (1/(5.558691 log t)) is used in the window


def edges():
    e = [V_LO] + [round(28.8 + 0.1 * i, 4) for i in range(32)]          # 28.8 .. 31.9
    e += [round(32 + 0.25 * i, 4) for i in range(16)]                     # 32 .. 35.75
    e += [round(36 + 0.5 * i, 4) for i in range(16)]                      # 36 .. 43.5
    e += [float(x) for x in range(44, 61)]                                # 44 .. 60
    return e


def margin_at(prof, x, Zs, h=1e-7):
    y, _ = C.window_y(prof, x + h, V1)
    r = C.cell_margin(x, x + h, Zs, y)
    return None if r is None else r


def z_local(prof, i, x, lo=4.58, hi=5.55):
    """Smallest Z (float search) for band i at height x, with band i itself set to the trial Z in the window."""
    for _ in range(24):
        Z = (lo + hi) / 2
        trial = [list(q) for q in prof]
        trial[i][2] = f"{Z:.12f}"
        m = margin_at(trial, x, f"{Z:.12f}")
        if m is not None and m > 0:
            hi = Z
        else:
            lo = Z
    return hi


def design(passes=4):
    C.GT.check_increasing()
    e = edges()
    prof = [[e[j], e[j + 1], "4.700"] for j in range(len(e) - 1)]
    for p in range(passes):
        new = []
        for i, (a, b, Zs) in enumerate(prof):
            pts = [a + (b - a) * q / 8 for q in range(9)]
            pts[0] = a + 1e-9
            pts[-1] = b - 1e-9
            zl = max(z_local(prof, i, x) for x in pts)
            Z = math.ceil(zl * (1 + 4e-5) * 1000) / 1000
            if Z < float(C.Z_MIN.upper()):
                print(f"band ({a}, {b}]: local Z {zl:.5f} below Z_MIN; clamped", flush=True)
                Z = math.ceil(float(C.Z_MIN.upper()) * 1000) / 1000
            new.append([a, b, f"{Z:.3f}"])
        prof = new
        print("design pass", p, "done:", " ".join(z for _, _, z in prof[:6]), "...", prof[-1][2], flush=True)
    json.dump(dict(V_LO=V_LO, V1=V1, Z_MIN=C.Z_MIN.str(10), bands=prof), open(os.path.join(HERE, 'profile_classical.json'), 'w'), indent=1)
    for a, b, Z in prof:
        print(f"{a:9.4f} {b:9.4f} {Z}")


def certify_band(prof, i, h0, hmin):
    a, b, Zs = prof[i]
    assert arb(Zs) >= C.Z_MIN and arb(Zs) <= C.Z_MTY
    stack = []
    n = max(1, math.ceil((b - a) / h0))
    for j in range(n):
        stack.append((a + (b - a) * j / n, a + (b - a) * (j + 1) / n))
    # cover the DECIMAL band [a, b] of the CSV: the float edges may lie on either side of the decimal ones
    stack[0] = (math.nextafter(a, -math.inf), stack[0][1])
    stack[-1] = (stack[-1][0], math.nextafter(b, math.inf))
    stack.reverse()
    cells, fails, minrel = 0, [], None
    A = 1 / arb(Zs)
    while stack:
        va, vb = stack.pop()
        y, _ = C.window_y(prof, vb, V1)
        r = C.cell_margin(va, vb, Zs, y)
        if r is not None and r > 0:
            cells += 1
            rel = float((r / (C.KC * A)).lower())
            minrel = rel if minrel is None else min(minrel, rel)
            continue
        if vb - va < hmin:
            fails.append((va, vb))
            continue
        mid = (va + vb) / 2
        stack.append((mid, vb))
        stack.append((va, mid))
    return dict(ok=not fails, cells=cells, fails=fails[:5], minrel=minrel)


def run_certify():
    C.GT.check_increasing()
    d = json.load(open(os.path.join(HERE, 'profile_classical.json')))
    assert d['V1'] == V1 and d['V_LO'] == V_LO and V_LO < float(C.LOGH.lower())
    prof = [[float(a), float(b), str(Z)] for a, b, Z in d['bands']]
    for j in range(len(prof) - 1):
        assert prof[j][1] == prof[j + 1][0]
    log = open(os.path.join(HERE, 'cert_classical_log.txt'), 'w')
    t0 = time.time()
    res = []
    for i in range(len(prof)):
        r = certify_band(prof, i, 0.002, 1e-6)
        res.append(r)
        msg = (f"band ({prof[i][0]:.4f}, {prof[i][1]:.4f}] Z1={prof[i][2]}: {'OK' if r['ok'] else 'FAIL'} cells={r['cells']} "
               f"minrel={r['minrel'] if r['minrel'] is None else format(r['minrel'], '.2e')} "
               f"{'fails=' + str(r['fails']) if not r['ok'] else ''} t={time.time() - t0:.0f}s")
        print(msg, flush=True)
        log.write(msg + "\n")
    allok = all(r['ok'] for r in res)
    with open(os.path.join(HERE, 'zfr_classical_local.csv'), 'w', newline='') as f:
        f.write("logt_lo,logt_hi,Z1,status,notes\n")
        for (a, b, Zs), r in zip(prof, res):
            f.write(f"{a:.10g},{b:.10g},{Zs},{'proved' if r['ok'] else 'FAILED'},our proof using the BTY method "
                    f"(arXiv:2603.21490 preprint; corrected constants); zeta != 0 for sigma >= 1 - 1/(Z1 log t); "
                    f"cells={r['cells']}; min rel. margin={r['minrel']:.1e}\n")
    json.dump(dict(V_LO=V_LO, V1=V1, all_ok=allok, seconds=round(time.time() - t0),
                   constants=json.load(open(os.path.join(HERE, 'cl_constants.json'))),
                   bands=[dict(lo=a, hi=b, Z1=Zs, **r) for (a, b, Zs), r in zip(prof, res)]),
              open(os.path.join(HERE, 'cert_classical_summary.json'), 'w'), indent=1)
    msg = f"ALL BANDS CERTIFIED: {allok} ({len(prof)} bands, {round(time.time() - t0)} s)"
    print(msg)
    log.write(msg + "\n")
    log.close()


if __name__ == '__main__':
    if sys.argv[1:] == ['design']:
        design()
    elif sys.argv[1:] == ['certify']:
        run_certify()
    else:
        print(__doc__)
