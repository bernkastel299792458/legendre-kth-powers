# QRH 与 CS 密度界给出的四次幂无限尾部

日期：2026-11-06（Asia/Shanghai）。状态：接受 \(\beta\le7/8\) 的 QRH 研究前提，以及本文明确列出的 CS、CHJII 文献输入；本地代数推导及 256 位 Arb 数值前提已核验。这不是完整的所有 \(n\) 四次幂证明，也不是 Lean 形式化。

## 结论

对每个实数

\[
x\ge e^{700},
\]

开区间 \((x,x+4x^{3/4})\) 含有素数。因此对所有整数 \(n\ge e^{175}\)，存在素数

\[
n^4<p<(n+1)^4.
\]

阈值 700 采用较大余量，未主张其最优性。与 [小范围证书](LOWER_RANGE.md) 的 \(L\le109.46\) 拼接后，仍有 \(109.46<L<700\) 的中间范围需要处理。

本模块的直接密度与总零点数输入均来自 CS，**不使用 FKS 的密度定理或表格**。原 FKS 尾部仍保留为独立历史产物，未被覆盖。

## 1. 固定输入及安全放大

**QRH。** 每个非平凡零点 \(\rho=\beta+i\gamma\) 满足 \(\beta\le7/8\)。不假定完整 RH。

**CS 密度界。** Shashi Chourasiya、Aleksander Simonič，*An explicit form of Ingham’s zero density estimate*，固定 [arXiv:2507.15184v2（2025-09-30）](https://arxiv.org/html/2507.15184v2)，Corollary 1、Table 1 及推论后的统一展示界给出：对 \(U\ge H_{\mathrm{RH}}=3\cdot10^{12}\)、\(5/8\le\sigma\le7/8\)，

\[
N(\sigma,U)\le21.77\,U^{p(\sigma)}(\log U)^{q(\sigma)}
+8.29(\log U)^2+147\log U,
\]

其中

\[
p(\sigma)=\frac{3(1-\sigma)}{2-\sigma},
\qquad q(\sigma)=\frac{7-5\sigma}{2-\sigma}.
\]

CS 的 \(N(\sigma,U)\) 按重数计 \(\beta\ge\sigma\)、\(0<\gamma\le U\) 的零点，包含边界。这里明确采用 **v2** 的陈述。为保持首轮计算简单，将 \(21.77\) 保守增大为 \(22.44=561/25\)，并使用

\[
p(\sigma)\le\frac83(1-\sigma),\qquad q(\sigma)\le3.
\]

第一式等价于 \(\sigma\le7/8\)，第二式由 \(\sigma\ge1/2\) 得出。由于 \(\log U>1\)，得到本模块实际使用的界

\[
N(\sigma,U)\le\frac{561}{25}U^{\frac83(1-\sigma)}(\log U)^3
+\frac{829}{100}(\log U)^2+147\log U.
\tag{CS}
\]

以上放大逐点有效，不需要插值或将离散表格值推广到未认证区间。

**总零点数。** 同一 CS v2 的式 (11) 第一不等式适用于 \(U\ge H_{\mathrm{RH}}\)：

\[
N(U)\le\frac{U}{2\pi}\log\frac{U}{2\pi e}+0.43\log U.
\]

因此在该高度域内，利用 \(\pi>1\)、\(U>20\) 可进一步放大为

\[
N(U)\le(U/2+0.43)\log U<U\log U.
\tag{N}
\]

此处未将 CS 式 (11) 的来源域错误延伸到所有 \(U\ge20\)；我们始终同时要求 \(U\ge H_{\mathrm{RH}}\)。[CS v2，Corollary 1 的证明及式 (11)](https://arxiv.org/html/2507.15184v2#S2.SS1)

**共同高度的短区间公式。** Cully-Hugill–Johnston，[arXiv:2402.04272v3，Theorem 1.3 和 Table 1](https://arxiv.org/html/2402.04272v3)。取 \(\alpha=1/2\)、\(\omega=0\)、\(M=2.894=1447/500\)。对于 \(\log x\ge40\)、任意非负 \(h(x)\)，只要

\[
\max\{51,(\log x)^2\}<T<\frac{\sqrt{x}-2}{4},
\]

则有两端共用的 \(T^*\in[T,2T]\)，使

\[
\psi(x+h)-\psi(x)=h-
\sum_{|\gamma|\le T^*}\frac{(x+h)^\rho-x^\rho}{\rho}+E,
\]

\[
|E|\le\frac M T\big((x+h)\log(x+h)+x\log x\big).
\tag{CHJ}
\]

本文件已核对上述定理陈述、常数和域；未重跑上游表格优化或重证其分析定理。

## 2. 固定参数及适用条件

设

\[
L=\log x\ge700,\quad h=4x^{3/4},\quad y=x+h,
\quad\mu=\frac9{32},\quad T=x^\mu,\quad U=2T,
\]

\[
u=\log U=\mu L+\log2,
\qquad
\lambda_0=L-\frac83u=\frac L4-\frac83\log2.
\]

阈值处的 Arb 检查与下列单调性保证全部条件对 \(L\ge700\) 保持：

- \(T>51\)、\(U>3\cdot10^{12}\)、\(u>1\)，因为相应对数随 \(L\) 递增。
- \(\mu L-2\log(L+1)>0\)，且导数 \(\mu-2/(L+1)>0\)，故 \(T>(L+1)^2>L^2\)。
- \(4e^{-(1/2-\mu)L}+2e^{-L/2}<1\)，且左侧递减，这等价于 CHJ 的严格高度上界。
- \(h/x=4e^{-L/4}<1\)，所以 \(y<2x\)、\(\log y<L+1\)。
- \(\lambda_0>0\)，且 \(\lambda_0'=1/4>0\)。

## 3. 零点和的统一上界

逐零点有

\[
\left|\frac{(x+h)^\rho-x^\rho}{\rho}\right|
\le\int_x^{x+h}t^{\beta-1}\,dt\le h x^{\beta-1}.
\]

将共同高度放大到 \(U=2T\)，在 \(\sigma_0=5/8\) 分层，并使用 QRH 截断右端，得到

\[
\sum_{|\gamma|\le T^*}x^{\beta-1}
\le2x^{-3/8}N(U)
+2L\int_{5/8}^{7/8}x^{\sigma-1}N(\sigma,U)\,d\sigma.
\]

第一项覆盖全部低实部零点。\(\beta=7/8\) 的零点仍被保留；CS 的高度边界约定与这里一致。

代入 (CS)、(N)，并使用

\[
x^{\sigma-1}U^{\frac83(1-\sigma)}
=e^{-\lambda_0(1-\sigma)},
\]

可精确积分；丢弃积分结果中的负项后得到

\[
Z_0(L)=4u e^{-3L/32},
\]

\[
Z_1(L)=\frac{1122}{25}\,u^3\frac L{\lambda_0}e^{-\lambda_0/8},
\]

\[
Z_2(L)=2\left(\frac{829}{100}u^2+147u\right)e^{-L/8}.
\]

这里 \(1122/25=2\cdot22.44\)。与旧 FKS 版本不同，\(\lambda_0\) 不含 \(-2\log u\)：CS 主项已经以统一的 \(u^3\) 放大，不能再重复引入旧的对数因子。

## 4. 其余误差、素数幂与开端点

(CHJ) 除以 \(h\)，并利用 \(y\le2x\)、\(\log y\le L+1\)，给出

\[
|E|/h\le R(L)=\frac{1447}{2000}(3L+2)e^{-L/32}.
\]

对 \(y\ge2\)，元素计数给出

\[
Q(y):=\psi(y)-\theta(y)
\le\frac{\sqrt y(\log y)^2}{2\log2}.
\]

理由是高次幂指数不超过 \(\log y/\log2\)，每层至多 \(\sqrt y\) 项，每项的 \(\log p\le(\log y)/2\)。由于 \(\sqrt y\le2\sqrt x\)、\(\log2>1/2\)，

\[
Q(y)/h\le P(L)=\frac12(L+1)^2e^{-L/4}.
\]

为保证所有实数 \(x\) 的开区间结论，再预留右端点可能为素数的权重：

\[
\log y/h\le B(L)=\frac14(L+1)e^{-3L/4}.
\]

令

\[
F_{\mathrm{CS}}(L)=Z_0+Z_1+Z_2+R+P+B.
\]

若 \(F_{\mathrm{CS}}(L)<1\)，则 \(\theta(y)-\theta(x)>\log y\)。若 \((x,y)\) 内没有素数，差分至多来自右端点并不超过 \(\log y\)，矛盾。左端点由差分自动排除。

## 5. 全部无限尾部的单调论证

以下均在 \(L\ge700\) 上成立；\(u\) 严格递增。

1. \(Z_0\) 的对数导数为 \(\mu/u-3/32<0\)。
2. \(L/\lambda_0\) 为正，且
   \[
   \frac d{dL}\frac L{\lambda_0}
   =-\frac{(8/3)\log2}{\lambda_0^2}<0.
   \]
   另一正因子满足
   \[
   \frac d{dL}\log(u^3e^{-\lambda_0/8})
   =\frac{3\mu}{u}-\frac1{32}<0.
   \]
   因此 \(Z_1\) 严格递减。
3. 设 \(a=829/100,b=147\)。有
   \[
   \frac d{dL}\log Z_2
   =\mu\frac{2au+b}{au^2+bu}-\frac18
   \le\frac{2\mu}{u}-\frac18<0.
   \]
4. \(R\) 的对数导数为 \(3/(3L+2)-1/32<0\)。
5. \(P\) 的对数导数为 \(2/(L+1)-1/4<0\)。
6. \(B\) 的对数导数为 \(1/(L+1)-3/4<0\)。

各负号判断中的正倒数项均随 \(L\) 递减，故在阈值处认证后永久成立。由此 \(F_{\mathrm{CS}}\) 在 \([700,\infty)\) 上严格递减。

## 6. Arb 证书与可复算边界

脚本 [certify_tail_cs.py](../code/certify_tail_cs.py) 使用精确整数比构造所有有限常数，256 位 Arb 检查 21 项数值条件。它们依次覆盖适用域、两个高度界及其保持条件、\(\lambda_0\) 正性、对数指数放大条件、各项减性，以及最终的两个严格总和界。

本次已实际获得

\[
F_{\mathrm{CS}}(700)
=0.557220462408670948864420999882333777436735925799936356303329\ldots
<\frac{14}{25}=0.56<1.
\]

余量超过 0.442。全部球区间、21 项条件、固定来源、精确参数、库版本及脚本 SHA256 存于 [tail_cs_certificate.json](../results/tail_cs_certificate.json)。生成后另行执行只读 `--verify`，现有 JSON 与重算结果完全一致。另以独立的 384 位 Arb 表达式重算六项，结果被原证书的总和球包含；保留积分负项及精确截断余项时，上界进一步减小，方向一致。

```powershell
python D:\UGit\AI4Math\Legendre_k8\code\certify_tail_cs.py
python D:\UGit\AI4Math\Legendre_k8\code\certify_tail_cs.py --verify
```

第一条生成本模块的证书；第二条只读重算并比较，不改任何证书。还可通过 `--output` 指定独立输出路径。运行环境为 Python 3.12.10、python-flint 0.9.0。

该证书认证本地数值前提；无限性依赖第 5 节的解析证明。它不重证 QRH、CS 或 CHJII，不宣称已经填补中间缺口，也不宣称改进了全领域已知指标。
