"""Lean 结构 `Hypotheses` 中 num1、num2 两个数值事实的 arb 验证。"""
from flint import arb, ctx
ctx.prec = 200
L1 = arb(2089605) / 1024
facts = {
    'num1: exp(600/67) <= 67*(39097000-1)': 67 * (arb(39097000) - 1) - (arb(600) / 67).exp(),
    'num2: exp(L1/67) <= 67*(251949000000-1), L1=2089605/1024': 67 * (arb(251949000000) - 1) - (L1 / 67).exp(),
}
ok = True
for k, v in facts.items():
    good = v.lower() > 0
    ok &= good
    print(f"{k}: margin = {v}  {'OK' if good else 'FAIL'}")
print('NUMERIC FACTS VERIFIED' if ok else 'FAILED')
import sys
sys.exit(0 if ok else 1)
