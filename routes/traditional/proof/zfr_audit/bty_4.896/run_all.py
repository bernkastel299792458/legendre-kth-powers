"""Run all BTY checks in order and save their outputs.
Run:  python -I run_all.py        (about 5 minutes)"""
import hashlib
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
PARTS = ["check_part1_sec3_lemma5.py", "check_part2_lemmas6_8_9_12_13.py",
         "check_part3_lemmas10_11.py", "check_part4_lemma14.py", "check_part5_lemma15_final.py"]
OUTS = ["part1_output.txt", "part2_output.txt", "part3_output.txt", "part4_output.txt", "part5_output.txt"]
src = os.path.join(HERE, "source", "Bellotti_Trudgian_Yang_v1.tex")
print("source sha256:", hashlib.sha256(open(src, "rb").read()).hexdigest())
bad = 0
for p, o in zip(PARTS, OUTS):
    r = subprocess.run([sys.executable, "-I", os.path.join(HERE, p)], capture_output=True, text=True, cwd=HERE)
    open(os.path.join(HERE, o), "w", encoding="utf-8").write(r.stdout + r.stderr)
    summ = [ln for ln in r.stdout.splitlines() if ln.startswith("SUMMARY")]
    print(f"{p}: exit {r.returncode}; {summ[0] if summ else 'no summary'}")
    bad += r.returncode != 0
print("ALL BTY CHECKS PASSED (ISSUE items are paper misstatements handled downstream)" if bad == 0 else f"{bad} PART(S) FAILED")
sys.exit(bad)
