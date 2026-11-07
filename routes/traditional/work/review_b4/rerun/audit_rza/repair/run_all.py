"""
run_all.py -- re-run the repaired-b4 certificate (REPORT.md).

  python -I run_all.py          # uses cached long computations (m-certificate to 1e10, sign table,
                                # xi_N Euler products/scans); ~2 min
  python -I run_all.py --full   # recomputes everything (~30 min on 16 cores)

Tags: OK / FAIL (exit 1 on FAIL).
"""
import os, sys, subprocess, json, time

HERE = os.path.dirname(os.path.abspath(__file__))
PARENT = os.path.dirname(HERE)
OUT = os.path.join(HERE, "out")
OUT_HF = os.path.join(HERE, "out_hf")
PY = [sys.executable, "-I"]
bad = 0
HF_ENV = dict(RZA_LOG10N="10", RZA_H1="0.0144", RZA_H2="0.029762", RZA_OUTDIR=OUT_HF)


def run(script, args=(), env=None, cwd=HERE, out=None):
    t = time.time()
    e = dict(os.environ)
    for k in list(e):
        if k.startswith("RZA_"):
            del e[k]
    if env:
        e.update(env)
    r = subprocess.run(PY + [script] + list(args), capture_output=True, text=True, cwd=cwd, env=e)
    if out:
        open(out, "w").write(r.stdout + r.stderr)
    print("  ran %-60s %6.1f s (exit %d)" % (os.path.basename(script) + " " + " ".join(args), time.time() - t, r.returncode), flush=True)
    return r.stdout + r.stderr


def tag(ok, msg):
    global bad
    print(("OK    " if ok else "FAIL  ") + msg)
    bad += 0 if ok else 1


def main():
    full = "--full" in sys.argv
    os.makedirs(OUT, exist_ok=True); os.makedirs(OUT_HF, exist_ok=True)
    for e0 in ("0", "0.0227", "0.04"):
        s = run(os.path.join(HERE, "repair_hweights.py"), [e0, "90"], out=os.path.join(OUT, "repair_hweights_%s.txt" % e0))
    tag("[0.332879289369" in open(os.path.join(OUT, "repair_hweights_0.txt")).read(),
        "h-weights with eps0=0 reproduce S11(68) (consistency of the weighted code)")
    if full:
        run(os.path.join(HERE, "repair_mcert.py"), ["10"], out=os.path.join(OUT, "repair_mcert_1e10.txt"))
        run(os.path.join(PARENT, "lemma31", "sign_table_arb.py"), ["a,c,c_tight,d0"], out=os.path.join(OUT, "sign_table_acd_rerun.txt"))
        run(os.path.join(PARENT, "lemma31", "sign_table_arb.py"), ["b1,b2"], out=os.path.join(OUT, "sign_table_b_rerun.txt"))
        run(os.path.join(PARENT, "rza_euler.py"), env=HF_ENV, cwd=PARENT, out=os.path.join(OUT_HF, "rza_euler_out.txt"))
        run(os.path.join(PARENT, "rza_scans.py"), ["--only", "B,C"], env=HF_ENV, cwd=PARENT, out=os.path.join(OUT_HF, "scans_BC_out.txt"))
        run(os.path.join(PARENT, "rza_scans.py"), ["--only", "E,F"], env=HF_ENV, cwd=PARENT, out=os.path.join(OUT_HF, "scans_EF_out.txt"))
    mc = json.load(open(os.path.join(OUT, "mcert_1e10.json")))
    tag(mc["ok"] and mc["N"] == 10 ** 10, "own certificate |m(t)|<=sqrt(2/t), |m_2(t)|<=sqrt(3/t), t<=1e10")
    for f in ("sign_table_acd_rerun.txt", "sign_table_b_rerun.txt"):
        t = open(os.path.join(OUT, f)).read()
        tag("FAIL" not in t and len(t) > 0, "sign table re-run (%s) has no failing cell" % f)
    s = run(os.path.join(PARENT, "rza_mpatterns.py"), out=os.path.join(OUT, "rza_mpatterns_out.txt"))
    tag("class  1: max 19/210" in s and "(c) min over other classes" in s and "OK" in s, "m_l(t) pattern constants (exact)")
    s = run(os.path.join(HERE, "repair_hf_inputs.py"), ["10"], out=os.path.join(OUT, "repair_hf_inputs_1e10.txt"))
    hf = json.load(open(os.path.join(OUT, "hf_inputs_1e10.json")))
    from flint import arb
    tag(arb(hf["H2p"]) <= arb("0.029762"), "derived H2' = %s <= 0.029762 (used)" % hf["H2p"][:12])
    res = {}
    for name, args, env in [("rza_3e12", ["3e12", "0.0227"], None), ("rza_1e12", ["1e12", "0.04"], None),
                            ("hf_3e12", ["3e12", "0.0227"], HF_ENV), ("hf_1e12", ["1e12", "0.04"], HF_ENV)]:
        s = run(os.path.join(HERE, "repair_bound.py"), args, env=env, out=os.path.join(OUT, "repair_bound_%s.txt" % name))
        line = [l for l in s.splitlines() if l.startswith("b4 (rounded")]
        res[name] = line[0].split("=")[1].strip() if line else None
        tag(bool(line) and "CERTIFIED" in s, "certificate %s: b4 = %s" % (name, res[name]))
    json.dump(res, open(os.path.join(OUT, "b4_results.json"), "w"), indent=1)
    print("DONE, %d FAIL" % bad)
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
