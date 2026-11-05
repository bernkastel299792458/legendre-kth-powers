"""一键复核阶段性成果（v4；在 proof/code 目录下运行：python verify_all.py）的全部计算部分。
需要：Python 3.10+，python-flint 0.9.0（arb）。

两条证书链：
  k0 = 70，常数组 'bty_pub' = (4.896 [BTY, arXiv, 已独立核实], 21.233 [Yang JMAA 2024], 54.004 [Bellotti JMAA 2024])
  k0 = 74，常数组 'pub'     = (5.558691 [MTY RNT 2024], 21.233, 54.004)，全部已发表
每条链：
  [log 4e18, L1]   CHL 两对 (Δ, x0) → numeric_facts.py；CHL 的上游输入 (I10)(b) → kln_lemma32_check.py
  [L1, L2]         命题 S → check_smooth_chain.py --pure-arb --expect-range
  [L2, 1e8]        命题 H → check_certificate.py --expect-range
  [1e8, ∞)         Lemma T → tail.py
"""
import subprocess
import sys
import hashlib
import os

HERE = os.path.dirname(os.path.abspath(__file__))
CERT = os.path.join(HERE, '..', 'certificates')
c = lambda f: os.path.join(CERT, f)
CHAINS = [  # (k0, 常数组, L1, L2)
    ('70', 'bty_pub', '2186309/1024', '9521'),
    ('74', 'pub', '578863/256', '7343'),
]
L3 = '100000000'
jobs = [['kln_lemma32_check.py']]
for k, z, L1, L2 in CHAINS:
    tag = f'k{k}_{z}'
    jobs += [
        ['numeric_facts.py', k, L1],
        ['tail.py', L3, k],
        ['check_certificate.py', '--zfr', z, '--expect-range', L2, L3, c(f'cert_hyb_v3_{tag}.csv')],
        ['check_smooth_chain.py', '--pure-arb', '--zfr', z, '--expect-range', L1, L2, c(f'cert_smooth_v3_{tag}.csv')],
    ]
print('SHA256 of certificates:')
for f in sorted(os.listdir(CERT)):
    if f.endswith('.csv'):
        h = hashlib.sha256(open(c(f), 'rb').read()).hexdigest()
        print(f'  {h}  {f}')
print('SHA256 of code:')
for f in sorted(os.listdir(HERE)):
    if f.endswith('.py'):
        h = hashlib.sha256(open(os.path.join(HERE, f), 'rb').read()).hexdigest()
        print(f'  {h}  {f}')
ok = True
for j in jobs:
    print('\n$ python', ' '.join(os.path.basename(a) if a.endswith('.csv') else a for a in j), flush=True)
    r = subprocess.run([sys.executable, '-B'] + j, cwd=HERE)
    ok &= (r.returncode == 0)
print('\nALL CHECKS PASSED' if ok else '\nSOME CHECK FAILED')
sys.exit(0 if ok else 1)
