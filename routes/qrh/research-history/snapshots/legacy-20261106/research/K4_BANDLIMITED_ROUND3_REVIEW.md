# 第三轮带限分支独立审阅

2026-11-06。审阅者：Codex 子代理 `qrh_status`。实现及正文作者为另一子代理 `prior_progress`。本审阅没有修改被审正文、代码或证书；只新增本文件。这是 AI 交叉审阅，不是人类专家同行评审。

## 1. 结论与冻结版本

**在所列文献输入下，未发现阻断该局部书面计算辅助论证的数学或数值缺陷。** 论证覆盖每个实数 x 的范围

\[
109.46\le\log x\le112.5,
\qquad (x,x+4x^{3/4})\text{ 含有素数}.
\]

对应整数 `x=n^4` 的本段范围为 `766422943599 <= n <= 1638823955138`。本结论不扩展至 `log(x)>112.5`，不表示整个 k=4 猜想已经解决。

审阅的最终 SHA256：

| 文件 | SHA256 |
|---|---|
| `research/K4_BANDLIMITED_ROUND3.md` | `0f52d2524623af5b6103768f38d4d6ecce2a568e91004f1ee9bed2d098850453` |
| `code/k4_bandlimited_round3.py` | `924c95379de0cafd32a086372e6ef53f319680952ac0ffd19e8b995b4ecc7f62` |
| `results/k4_bandlimited_round3.json` | `061fb3598c66c6df6dfdac325d519db2b287d904eda92ed6ba32b2dd5f4b37d8` |

## 2. 独立数学检查

已通读冻结正文和脚本，并独立核对下列连接。

- **显式公式归一化。** 对 `h(z)=cos(cz)G(z)`，周期 Fourier 变换在 `log(n)/(2pi)` 处等于 `pi Q(log n)`；源公式的两项对称素数和恰好给出正文的 S，没有遗漏 2 或 2π。直接检查了 [Carneiro–Milinovich–Soundararajan v2，Lemma 6，第 17 页](https://arxiv.org/pdf/1708.04122v2) 的原文及条带条件。
- **负权与开区间提取。** 对 u≥0，反射项 F(u+c)≤0；目标区间外和端点上 Q(u)≤0，目标内 Q(u)≤1。因此在无内部素数时 S 至多为正素数幂预算。没有把区间外负贡献改作正项，也没有用正性假设替换有符号核。
- **频谱、质量及正则化。** 独立重算了 sinc 四次方的三次 B 样条，确认 `G0=B+B''/d²`、`||B''||1=4pi/(3a²)`、质量与绝对质量界。B 为 C²，B'' 不含漏掉的端点原子。Gaussian 卷积使 G 整解析，并在固定水平条带中快速衰减；未将实轴硬截断误用在复零点处。
- **pole 主项方向。** `exp(-v²)cosh(v/2)<=1`；在 f≤0 的外部，乘这个因子提高积分。正内部的损失至多 2d³，所以 `G(i/2)>=C_m d-2d³` 正确。主项使用有符号质量，没有以 L¹ 质量代替。
- **零点复移及全尾。** 保留了 `exp(delta²/4)` 和 `cosh(c delta)` 两项，安全片段只使用 `|delta|<1/2`。有限 RH 处的零点确实在实轴；检查了 [Platt–Trudgian v1，Theorem 1](https://arxiv.org/pdf/2004.09765v1) 的高度 `3000175332800>H`。高尾的 Stieltjes 下边界为负，丢弃方向正确；`N(t)<=t log t<=t²` 仅用于 t≥H。代换后积分正好给出 `H²(1+4/D²)exp(-D²/4)`，从而可以取 D≥64 的统一上界。
- **无穷位与素数幂。** 文中 digamma 级数的非负增量及首项/积分估计足以推出 `|Omega(t)|<=7+log(1+|t|)`；Gaussian 的绝对一阶矩为 `2/sqrt(pi)`。正素数幂预算中的 `exp(d)` 来自 `sqrt(y/x)`，没有漏掉 n^(-1/2) 权重。
- **连续参数范围。** d 递减、c 与 K 递增；主项与四项费用使用的端点方向均保守。覆盖结论来自对整个实 L 区间的一致界，不是从有限采样推断连续覆盖。
- **L=120 的附加模型诊断。** 独立核对 G0 的全局 Lipschitz 常数、Gaussian 复平移的常数抵消及共振四元组的因子 4。这里仅推出该具体核在所列模型上的绝对值预算大于 12；没有声称模型是真实 ζ，也没有声称所有非紧支撑核都失败。

总零点计数采纳正文明确列明的 Rosser 重述及其源域；本审阅没有重新证明上述文献定理或重做有限 RH 的原始大规模计算。安全片段不需要额外 QRH 假设、CS 密度假设或实际低零点的逐个高度。

## 3. 数值证据与检查等级

对冻结代码执行了只读命令：

```powershell
python -B Legendre_k8/code/k4_bandlimited_round3.py --verify
```

结果为 **19/19 严格标量检查通过**，完整重算与保存 JSON 一致，包括正文及脚本散列。它们的用途必须分开：

| 检查组 | 数量 | 证明用途 |
|---|---:|---|
| 安全片段的连续参数、谱隙、主项及费用前提 | 12 | 配合解析论证证明实区间 `[109.46,112.5]` |
| 整数端点及相邻整数的严格 log 比较 | 4 | 给出上述实区间对应的精确整数范围 |
| L=120 模型诊断 | 3 | 验证该候选核在明确模型中的预算障碍；不是额外素数覆盖 |

因此前 **16 项**服务于安全片段及其整数解释，后 **3 项**属于不同性质的模型诊断。标量检查本身没有形式化显式公式等解析推导。

另以 **Arb 512 位**、不导入作者模块的独立公式代码复算了：

1. 八个主预算量：pole 下界、低零点、高零点、无穷位、正素数幂、总费用、正余量、相对费用。全部独立结果落在 JSON 保存的相应球内。
2. 四个整数端点严格不等式，全部为正；独立复算使用明确整数值，再与 JSON 核对，不只复用生成器的 floor 结果。

没有把上述范围称为“独立 512 位复算全部 19 项”。三项模型诊断经过独立公式审阅与作者脚本的 256 位只读重放，未另行声明独立 512 位重算。

主要数值（仅显示近似，判断使用完整 Arb 球）：

| 项目 | 数值 |
|---|---:|
| H−K_max | 50116880746.4616… > 64 |
| pole 下界 | 123571131220.835926… |
| 低零点上界 | 2016.037085442558… |
| 高零点上界 | 1.5947674… × 10^-395 |
| 无穷位上界 | 67.163113018830… |
| 正素数幂上界 | 9129.554555650142… |
| 全部费用上界 | 11212.754754111530… |
| 相对费用 | 9.073927416002236… × 10^-8 |

四个整数端点余量依次为：

\[
\begin{aligned}
4\log(766422943599)-109.46&>5.03147\cdot10^{-12},\\
109.46-4\log(766422943598)&>1.87577\cdot10^{-13},\\
112.5-4\log(1638823955138)&>2.08604\cdot10^{-12},\\
4\log(1638823955139)-112.5&>3.54725\cdot10^{-13}.
\end{aligned}
\]

## 4. 独立复算片段

在工作区根目录以 `python -B` 执行。只读取专属 JSON，不导入作者代码，不写文件。

```python
import json
from pathlib import Path
from flint import arb, ctx

ctx.prec = 512
saved = json.loads(Path('Legendre_k8/results/k4_bandlimited_round3.json')
                   .read_text(encoding='utf-8'))
r, H, pi = arb(9)/10, arb(3)*10**12, arb.pi()
lo, hi = arb(5473)/50, arb(225)/2
d0 = (4*(-lo/4).exp()).log1p()/2
d1 = (4*(-hi/4).exp()).log1p()/2
c0, c1, K = lo+d0, hi+d1, 4*r/d1
J = pi*(2/(3*r)-1/(2*r**3))
Ja = pi*(2/(3*r)+1/(2*r**3))
C = 2*pi+4*pi/(3*r**2)
v = {}
v['pole_lower'] = 2*(c0/2).cosh()*(J*d1-2*d0**3)
v['low_zeros_upper'] = 2*H*H.log()*Ja*d0
v['high_zeros_upper'] = (2*(c1/2).cosh()*C/(2*pi.sqrt())
    *(arb(1)/16).exp()*H**2*(1+arb(4)/4096)*arb(-1024).exp())
v['archimedean_absolute_upper'] = C/(2*pi)*(7+(1+K).log()+2/pi.sqrt())
v['positive_prime_powers_upper'] = d0.exp()*(hi+2*d0)**2/(2*arb(2).log())
v['all_costs_upper'] = sum(v[k] for k in ('low_zeros_upper',
    'high_zeros_upper', 'archimedean_absolute_upper', 'positive_prime_powers_upper'))
v['positive_margin_lower'] = v['pole_lower']-v['all_costs_upper']
v['relative_cost_upper'] = v['all_costs_upper']/v['pole_lower']
for key, value in v.items():
    assert arb(saved['uniform_budget_balls'][key]).contains(value), key
assert H-K > 64
assert v['positive_margin_lower'] > 0
assert v['relative_cost_upper'] < arb(1)/10**6
n0, n1 = 766422943599, 1638823955138
for value in (4*arb(n0).log()-lo, lo-4*arb(n0-1).log(),
              hi-4*arb(n1).log(), 4*arb(n1+1).log()-hi):
    assert value > 0
assert saved['exact_parameters']['n_min_inclusive'] == str(n0)
assert saved['exact_parameters']['n_max_inclusive'] == str(n1)
print('Independent 512-bit checks: 8 budget enclosures + 4 integer endpoints PASS')
```

## 5. 未完成或未覆盖的事项

本审阅支持的是列明输入下的局部书面计算辅助证明。没有完成 Lean 或其他证明助理的端到端形式化；Arb 标量验证没有自动认证全部复分析、Fourier 与显式公式连接。没有新增核心中段的相位定理，没有消除 `log(x)>112.5` 的剩余问题，也没有重新审计 k=6 或旧 k=4 证书。

截至上述冻结版本，本次已检查范围内没有遗留的阻断缺陷。
