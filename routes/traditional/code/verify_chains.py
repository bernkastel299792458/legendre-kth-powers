"""对 make_chain.py 生成的证书链做纯 Arb 复核（含端点断言）。用法：python verify_chains.py K ZSET L1 L2"""
import sys, subprocess
k, z, L1, L2 = sys.argv[1:5]
tag = f'k{k}_{z}'
jobs = [
    ['tail.py', '100000000', k],
    ['check_certificate.py', '--zfr', z, '--expect-range', L2, '100000000', f'../results/cert_hyb_v3_{tag}.csv'],
    ['check_smooth_chain.py', '--pure-arb', '--zfr', z, '--expect-range', L1, L2, f'../results/cert_smooth_v3_{tag}.csv'],
]
ok = True
for j in jobs:
    print('$ python', ' '.join(j), flush=True)
    r = subprocess.run([sys.executable, '-B'] + j)
    ok &= r.returncode == 0
print(f'[{tag}] ' + ('ALL CHECKS PASSED' if ok else 'SOME CHECK FAILED'))
sys.exit(0 if ok else 1)
