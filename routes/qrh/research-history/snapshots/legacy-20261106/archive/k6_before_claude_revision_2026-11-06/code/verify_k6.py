"""Replay every module used by the documented conditional all-n k=6 proof."""
from __future__ import annotations
import hashlib
import json
import subprocess
import sys
from datetime import datetime, timezone, timedelta
from fractions import Fraction
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
MODULES=(
    ('certify_lower_range_k6.py','lower_range_k6_certificate.json'),
    ('certify_smooth_k6.py','smooth_k6_certificate.json'),
    ('certify_smooth_segment.py','smooth_segment_certificate.json'),
    ('certify_tail_cs.py','tail_cs_certificate.json'),
)

def require(condition,message):
    if not condition:raise ValueError(message)

def main():
    runs=[]
    documents=[]
    for script,name in MODULES:
        path=ROOT/'code'/script
        run=subprocess.run([sys.executable,'-X','utf8',str(path),'--verify'],
            cwd=ROOT,capture_output=True,text=True,encoding='utf-8',check=True)
        certificate=ROOT/'results'/name
        documents.append(json.loads(certificate.read_text(encoding='utf-8')))
        runs.append(dict(script=script,certificate=name,passed=True,output=run.stdout.strip(),
            script_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
            certificate_sha256=hashlib.sha256(certificate.read_bytes()).hexdigest()))
        print(f'PASS {script}',flush=True)
    lower,middle,old_middle,tail=documents
    require(lower['k']==6 and middle['k']==6 and old_middle['k']==4,'Exponents')
    Lsmall=Fraction(lower['coverage']['target_L_numerator'],lower['coverage']['target_L_denominator'])
    require(lower['coverage']['all_n_with_6_log_n_le_target_L_covered'],'Lower range not verified')
    m0,m1=map(Fraction,middle['log_x_interval'])
    o0,o1=map(Fraction,old_middle['log_x_interval'])
    t0=Fraction(tail['parameters_exact']['L0'])
    require(Lsmall>=m0 and m1>=o0 and o1>=t0,'Uncovered log(x) interval')
    # For x>=1, 4*x^(3/4) <= 6*x^(5/6), since 4<=6 and 3/4<=5/6.
    require(o0>=0 and 4<=6 and Fraction(3,4)<=Fraction(5,6),'Tail inclusion')
    result=dict(status='ALL_K6_MODULES_VERIFIED',k=6,conditional_all_positive_integers_covered=True,
        theorem='Assuming QRH(7/8) and the stated published inputs, every integer n>=1 has a prime n^6<p<(n+1)^6.',
        created=datetime.now(timezone(timedelta(hours=8))).isoformat(),
        proof_document='research/K6_PROOF.md',
        scope='Numerical module replay and exact coverage checks for the written analytic proof; not a formal proof checker or external peer review.',
        lower_n_max=lower['coverage']['n_max_inclusive'],
        new_real_x_log_interval=[str(m0),str(m1)],
        inherited_real_x_log_interval=[str(o0),'infinity'],
        uncovered_log_x_intervals=[],runs=runs,
        script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    out=ROOT/'results'/'k6_verification_summary.json'
    out.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print(result['status'])
    print('Conditional all-n coverage: true; uncovered intervals: []')

if __name__=='__main__':main()
