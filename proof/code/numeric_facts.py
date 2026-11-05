"""Lean 结构 `Hypotheses` 中数值事实 num1、num2 的 arb 验证（下段：Cully-Hugill–Lee 的两对 (Δ, x0)）。
用法：python numeric_facts.py K L1    （例：70 2186309/1024；74 578863/256）
  num1: exp(600/K) <= K (Δ1 - 1),  Δ1 = 39097000（x0 = 4e18）
  num2: exp(L1/K)  <= K (Δ2 - 1),  Δ2 = 251949000000（x0 = e^600）"""
import sys
from fractions import Fraction
from flint import arb, ctx
ctx.prec = 200
k = int(sys.argv[1]); L1f = Fraction(sys.argv[2])
K = arb(k); L1 = arb(L1f.numerator) / L1f.denominator
facts = {
    f'num1: exp(600/{k}) <= {k}*(39097000-1)': K * (arb(39097000) - 1) - (arb(600) / K).exp(),
    f'num2: exp(L1/{k}) <= {k}*(251949000000-1), L1={L1f}': K * (arb(251949000000) - 1) - (L1 / K).exp(),
}
ok = True
for name, v in facts.items():
    good = v.lower() > 0
    ok &= good
    print(f"{name}: margin = {v}  {'OK' if good else 'FAIL'}")
print('NUMERIC FACTS VERIFIED' if ok else 'FAILED')
sys.exit(0 if ok else 1)
