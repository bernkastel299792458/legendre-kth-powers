"""Run every check of the phase1_cs audit; outputs go to *_out.txt; exit 1 on any FAIL.
   python -I run_all.py      (about 10 minutes)"""
import hashlib, os, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
SCRIPTS = ["zeta_half_max.py", "cs_thm1.py", "run_thm1_tables.py", "run_kln_tables.py",
           "check_misc.py", "run_b4_05161.py", "run_low_sigma.py", "cs_bounds.py"]   # cs_bounds reads the CSV written by run_b4_05161
OUT = {"zeta_half_max.py": "zeta_half_max_out.txt", "cs_thm1.py": "cs_thm1_out.txt",
       "run_thm1_tables.py": "run_thm1_tables_out.txt", "run_kln_tables.py": "run_kln_tables_out.txt",
       "check_misc.py": "check_misc_out.txt", "run_b4_05161.py": "run_b4_05161_out.txt",
       "run_low_sigma.py": "run_low_sigma_out.txt",
       "cs_bounds.py": "cs_bounds_selftest_out.txt"}
SOURCES = ["../audit_rza/repair/REPORT.md", "src/v2/InghamPostArXiv.tex", "src/v1/Main.tex", "src/2101.12263/KLN.tex",
           "src/2204.01980/x/main.tex", "src/2603.25961/x/OnADoubleMobiusSum-20.tex",
           "src/2603.25961/x/OnADoubleMobiusSum-20.sagetex.sout"]
bad = []
for s in SOURCES:
    p = os.path.join(HERE, s)
    h = hashlib.sha256(open(p, "rb").read()).hexdigest()
    print("sha256 %s  %s" % (h[:16], s))
for sc in SCRIPTS:
    r = subprocess.run([sys.executable, "-I", os.path.join(HERE, sc)], capture_output=True, text=True, cwd=HERE)
    open(os.path.join(HERE, OUT[sc]), "w", encoding="utf8").write(r.stdout + r.stderr)
    status = "ok" if r.returncode == 0 else "FAIL (exit %d)" % r.returncode
    print("%-22s -> %-28s %s" % (sc, OUT[sc], status))
    if r.returncode != 0:
        bad.append(sc)
print("ALL OK" if not bad else "FAILURES: %s" % bad)
sys.exit(1 if bad else 0)
