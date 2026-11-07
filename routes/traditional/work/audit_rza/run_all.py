"""
run_all.py -- one-shot re-run of the RZA (arXiv:2603.25961v3, Theorem 1.2) audit.

  python -I run_all.py            # everything except the 4e9 sigma-scan (uses its cached JSON) ~3 min
  python -I run_all.py --full     # also re-runs scan A to 4e9 (~8 min extra)

Each step's stdout goes to out/<step>_out.txt.  Tags in this script's output:
  OK    = the check passed
  ISSUE = a statement of the paper that is false as written (downstream effect assessed in REPORT.md)
  FAIL  = an unexpected result (exit code 1)
"""
import os, sys, subprocess, json, hashlib, time

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "out")
PY = [sys.executable, "-I"]
bad = 0


def run(name, args=(), timeout=3600):
    t = time.time()
    r = subprocess.run(PY + [os.path.join(HERE, name)] + list(args), capture_output=True, text=True, cwd=HERE, timeout=timeout)
    tag = os.path.splitext(name)[0] + ("_" + "".join(a.strip("-").replace(",", "") for a in args) if args else "")
    open(os.path.join(OUT, tag + "_out.txt"), "w").write(r.stdout + r.stderr)
    print("  ran %-28s %6.1f s  (exit %d)" % (name + " " + " ".join(args), time.time() - t, r.returncode), flush=True)
    return r.stdout


def tag(ok, msg, issue=False):
    global bad
    if ok:
        print(("ISSUE " if issue else "OK    ") + msg)
    else:
        print("FAIL  " + msg)
        bad += 1


def main():
    os.makedirs(OUT, exist_ok=True)
    full = "--full" in sys.argv
    src = os.path.join(HERE, "src_dl", "v3", "x", "OnADoubleMobiusSum-20.tex")
    print("source v3 sha256:", hashlib.sha256(open(src, "rb").read()).hexdigest())
    for v in ("v1", "v2", "v3"):
        p = os.path.join(HERE, "src_dl", v, "eprint.tar.gz")
        print("  %s eprint sha256: %s" % (v, hashlib.sha256(open(p, "rb").read()).hexdigest()))

    s = run("rza_assembly.py")
    tag("ALL ROWS REPRODUCED" in s, "paper replay: all nine printed Theorem 1.2 values reproduced from the paper's own inputs")

    s = run("rza_euler.py")
    E = json.load(open(os.path.join(OUT, "euler_products.json")))
    from flint import arb
    b = lambda k: arb(E[k][0], E[k][1])
    tag("mismatches: none" in s, "Euler factors: every printed closed form equals the generic Thm 4.1/4.2 factor (except P0_LX)")
    tag(abs(b("P0_LX_paperformula") - arb("0.694045937")) < arb("1e-9"), "P0_LX: paper's 0.694045937 = product of the PRINTED factor ...", True)
    tag(abs(b("P0_LX_true") - arb("0.82106529778")) < arb("1e-10"), "... but the correct factor (1+f)(1-1/p) gives 0.8210653 (c1 = 0.71336, not 0.60300)", True)
    tag(abs(b("APROD_all") - arb("0.428249506119")) < arb("1e-11"), "W = prod(1-2/p^2+1/p^3) = 0.4282495 (paper APROD = 0.40282372 is WRONG; = (6/pi^2) prod(1-1/(p(p+1))))", True)
    tag(abs(b("ASUM_all") + arb("0.5772156649") - arb("2.046752376")) < arb("1e-8"), "ASUM: paper's 2.046752376 already contains gamma (double counted; unused downstream)", True)

    s = run("rza_thm11.py")
    tag("[0.333415398792099" in s and "[41346.2541122163" in s, "S11(80), S12(80) reproduced exactly (paper 0.333415398793, 41346.25411)")
    s = run("rza_thm11_ext.py", ["160"])
    tag("S11(inf)" in s, "S11(J) to J=160 + consistency with Helfgott's lim S_0 (needs the true W)")

    if full:
        run("rza_scans.py", ["--only", "A"])
    run("rza_scans.py", ["--only", "B,C,D"])
    run("rza_scans.py", ["--only", "E,F"])
    run("rza_scans.py", ["--only", "G,H,I"])
    A = json.load(open(os.path.join(OUT, "scans_A.json")))["A"]
    tag(all(d["argmax"] == 42 and d["N"] == 4 * 10 ** 9 for d in A), "Lemma 4.5: sup over X <= 4e9 of sigma1,sigma2,Sigma1 / X at X=42 (scan A, cached unless --full)")
    BCD = json.load(open(os.path.join(OUT, "scans_BCD.json")))
    tag(BCD["B"][0]["claimed_ok"] and BCD["C"][0]["claimed_ok"], "Lemma 4.6 (max at 6) and Lemma 4.8 (max at 2) constants hold")
    tag(not BCD["D"][0]["claimed_ok"], "Lemma 4.10: claimed maxima (at 978118, 478671) are not the maxima (2.25327 > 2.25265); harmless", True)
    EF = json.load(open(os.path.join(OUT, "scans_EF.json")))
    tag(arb(EF["E"]["true"]["sup_K_minus_clog"]) < arb("1.29424331261228"), "Lemma 4.11: logmx = 1.29424 holds with the TRUE c1 = 0.71336")
    tag(arb(EF["F"]["true"]["sup_K_minus_clog"]) > arb("2.15"), "Lemma 4.13: log2mx, log2mm are K_1's numbers; true 2.15300, -0.13571", True)
    GHI = json.load(open(os.path.join(OUT, "scans_GHI.json")))
    tag(GHI["G"]["ok"], "G(1e8; 1.1) = %.6f >= 9.1" % GHI["G"]["G_1e8_1p1"])
    H = GHI["H"]
    tag(H["max"][0] <= 1.048 and H["min"][0] >= 1.040 and H["all_X_ge1"]["max"][0] <= 1.166 and H["all_X_ge1"]["min"][0] >= 0.578,
        "Lemma 4.3 (Ramare) constants hold on X <= 1e8 (partial check)")
    I = GHI["I"]
    tag(all(I[k][0] <= 1.0 + 1e-12 for k in ("sqrt2", "sqrt3_odd", "log_m", "log_m2")), "Lemmas 2.2/2.3 hold for X <= 1e8 (partial check)")

    s = run("rza_mpatterns.py")
    tag("(c) min over other classes" in s and s.count("FAILS") == 2,
        "Lemma 6.2 proof: max m_l(t) <= 57731/570570 FALSE for classes 11, 13 (69/455, 53/385); repairable via Delta<=0 (lemma31 4d)", True)
    s = run("rza_counterexample.py")
    tag(s.count("FALSE (certified") >= 4, "INEQUALITY (6.6) OF THE PROOF OF THM 1.2 IS FALSE (rigorous Arb counterexamples X=1000, 3000)", True)

    s = run("rza_audited.py")
    tag("[1e12,1e16) eps<=1/25  printed 0.5936" in s, "corrected-input replay written (rza_audited_out.txt)")
    s = run("rza_effects.py")
    tag("W (APROD) true" in s, "one-at-a-time effects on the 0.5936 row written (rza_effects_out.txt)")
    run("explore_repair.py")
    run("explore_exxp.py")
    print("DONE, %d FAIL" % bad)
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
