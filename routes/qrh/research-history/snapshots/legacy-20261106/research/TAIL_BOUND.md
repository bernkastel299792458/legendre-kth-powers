# k=4 的一个显式无限尾部

日期：2026-11-06。状态：**在接受 QRH 的 7/8 零点界和下列明确文献输入后，本文件给出可复算的尾部证明。它不覆盖全部正整数 n，也不是 Lean 形式化或对上游论文的独立审核。**

## 结论和复算

在上述输入下，对每个实数

\[
x\ge e^{800},
\]

开区间 \((x,x+4x^{3/4})\) 含有素数。因此，所有整数 \(n\ge e^{200}\) 满足

\[
\exists p\text{ prime}:\qquad n^4<p<(n+1)^4.
\]

这里使用 \(n^4+4n^3<(n+1)^4\)。本结果留下的范围是 \(1\le n<e^{200}\)；本文件不声称该范围已经覆盖。阈值 800 是保守的首个认证目标，不是本方法的最优阈值。

复算命令（Python 需安装 `python-flint`）：

```powershell
python D:\UGit\AI4Math\Legendre_k8\code\certify_tail.py
```

结果写入 `results/tail_certificate.json`。脚本以 256-bit Arb 区间算术核查阈值处的不等式；整个无限区间由第 6 节的解析单调性覆盖，不以采样替代证明。

## 1. 输入与适用域

1. **QRH 输入**：每个非平凡 zeta 零点 \(\rho=\beta+i\gamma\) 满足 \(\beta\le7/8\)。这是本项目接受的研究前提。
2. **FKS 密度界**：在 \(\sigma\in[5/8,7/8]\)、\(U\ge H_0=3\cdot10^{12}\) 时，
   \[
   N(\sigma,U)\le c_1 U^{\frac83(1-\sigma)}(\log U)^{5-2\sigma}
                 +c_2(\log U)^2,
   \]
   其中 \(c_1=17.4194=87097/5000\)、\(c_2=5.2954=26477/5000\)。这由 Fiori–Kadiri–Swidinsky 的 Theorem 2.7、Corollary 2.9 与 Table 8 中采用 \(a_1=0.77\) 的第一组分段常数，取覆盖区间内的统一上界得到。[固定 v3 原文](https://arxiv.org/html/2204.02588v3)
3. **CHJII 短区间公式**：Cully-Hugill–Johnston 的 Theorem 1.3 和 Table 1，取 \(\alpha=1/2\)、\(\omega=0\)、\(M=2.894=1447/500\)，在 \(\log x\ge40\) 且
   \[
   \max\{51,(\log x)^2\}<T<\frac{\sqrt{x}-2}{4}
   \]
   时提供**共同的** \(T^*\in[T,2T]\)，满足
   \[
   \psi(x+h)-\psi(x)=h-
   \sum_{|\gamma|\le T^*}\frac{(x+h)^\rho-x^\rho}{\rho}
   +E,
   \quad
   |E|\le\frac{M}{T}\big((x+h)\log(x+h)+x\log x\big).
   \]
   直接使用该短区间定理；没有分别在两端选取不同截断高度后将其混合。[固定 v3 原文，Theorem 1.3](https://arxiv.org/html/2402.04272v3#S1)
4. **总零点数**：采用 FKS Lemma 2.1、Remark 2.2 所列 Rosser 界（\(U\ge2\)）：
   \[
   N(U)\le\frac{U}{2\pi}\log\frac{U}{2\pi e}
   +\frac78+0.137\log U+0.443\log\log U+1.588.
   \]
   对 \(U\ge20\)，利用 \(\pi>1\)、\(\log\log U\le\log U\)、\(1\le\log U\)，右侧不超过
   \[
   \left(\frac U2+\frac{3043}{1000}\right)\log U<U\log U.
   \]
   因而本文件只需较弱的 \(N(U)\le U\log U\)。[固定 v3 原文，§2.1](https://arxiv.org/html/2204.02588v3#S2.SS1)

\(N(U)\) 只计正虚部，零点按重数计。涉及 \(\gamma<U\) 与 \(\gamma\le U\) 的源文献约定差异，可通过从右侧取极限和上界连续性统一；不会漏掉恰位于截断高度的零点。\(\beta\le7/8\) 的端点也保留。

这些来源的定理陈述、表格常数及适用域已阅读核对；本次没有重跑其作者的全部数值计算或重证其分析输入。

## 2. 固定参数与共同高度条件

写

\[
L=\log x\ge800,\qquad h=4x^{3/4},\qquad
\mu=\frac9{32},\quad T=x^\mu,\quad U=2T,
\]
\[
u=\log U=\mu L+\log2,\qquad
\lambda=L-\frac83u-2\log u
=\frac L4-\frac83\log2-2\log u.
\]

此处 \(\lambda\) 是本文件密度积分的变量，不是 CHJII Table 1 的权重参数。

以下条件均在 \(L=800\) 由 Arb 核查，并保持于其后：

- \(L>40\)，\(T>51\)。
- \(\mu L-2\log(L+1)>0\)，其导数 \(\mu-2/(L+1)>0\)。故 \(T>(L+1)^2>L^2\)，甚至覆盖 \(\log(x+h)\le L+1\) 的附加端点检查。
- \(4e^{-(1/2-\mu)L}+2e^{-L/2}<1\)，等价于 CHJII 的严格高度上界；左侧递减。
- \(U>3\cdot10^{12}\)，故使用 FKS 时不需要延拓到未列明的低高度。
- \(h/x=4e^{-L/4}<1\)。因此 \(y=x+h\le2x\)、\(\log y\le L+1\)。
- \(\lambda>0\)；其导数 \(\lambda'=1/4-9/(16u)>0\)。

## 3. 零点和

因为 \(\beta<1\)，

\[
\left|\frac{(x+h)^\rho-x^\rho}{\rho}\right|
=\left|\int_x^{x+h}t^{\rho-1}\,dt\right|
\le h x^{\beta-1}.
\]

将 \(T^*\) 放大至 \(U=2T\)，并在 \(\sigma_0=5/8\) 分层，得到

\[
S:=\sum_{|\gamma|\le T^*}x^{\beta-1}
\le 2x^{-3/8}N(U)
+2L\int_{5/8}^{7/8}x^{\sigma-1}N(\sigma,U)\,d\sigma.
\]

该式可以逐零点验证：对于 \(\beta>5/8\)，写
\(x^{\beta-1}=x^{-3/8}+L\int_{5/8}^{\beta}x^{\sigma-1}d\sigma\)；对于其余零点使用基底上界。因而没有将 \(\sigma<3/4\) 的贡献遗漏。

FKS 主项满足

\[
x^{\sigma-1}U^{\frac83(1-\sigma)}u^{5-2\sigma}
=u^3e^{-\lambda(1-\sigma)}.
\]

精确积分给出

\[
\begin{aligned}
S\le{}&2x^{-3/8}N(U)\\
&+\frac{87097}{2500}u^3\frac L\lambda
  (e^{-\lambda/8}-e^{-3\lambda/8})\\
&+\frac{26477}{2500}u^2
  (e^{-L/8}-e^{-3L/8}).
\end{aligned}
\]

使用 \(N(U)\le Uu\) 并丢弃负项，得到三个正上界：

\[
Z_0(L)=4u e^{-3L/32},\qquad
Z_1(L)=\frac{87097}{2500}u^3\frac L\lambda e^{-\lambda/8},\qquad
Z_2(L)=\frac{26477}{2500}u^2e^{-L/8}.
\]

## 4. 截断误差与素数幂

令 \(r=h/x\le1\)。CHJII 余项除以 \(h\) 后满足

\[
\frac{|E|}{h}
\le\frac M4 e^{-L/32}\big((1+r)\log(x+h)+L\big)
\le R(L):=\frac{1447}{2000}(3L+2)e^{-L/32}.
\]

下面的素数幂界不依赖额外数论输入。对所有 \(y\ge2\)，

\[
Q(y):=\psi(y)-\theta(y)
=\sum_{m=2}^{\lfloor\log y/\log2\rfloor}
  \sum_{p\le y^{1/m}}\log p
\le\frac{\sqrt y(\log y)^2}{2\log2}.
\]

理由是外层项数不超过 \(\log y/\log2\)，每个内层最多 \(\sqrt y\) 项，且每项不超过 \((\log y)/2\)。空和情形亦成立。

从 \(\sqrt y\le2\sqrt x\)、\(\log y\le L+1\)、\(\log2>1/2\) 可得

\[
\frac{Q(y)}h\le P(L):=\frac12(L+1)^2e^{-L/4}.
\]

又因为
\(\theta(y)-\theta(x)\ge\psi(y)-\psi(x)-Q(y)\)，这足以排除“只有高次素数幂”的假阳性。

## 5. 开区间端点与合并不等式

为证明对所有实数 \(x\) 的**开区间**结论，额外扣除可能位于 \(y\) 的一个素数权重：

\[
\frac{\log y}h\le B(L):=\frac14(L+1)e^{-3L/4}.
\]

定义

\[
F(L)=Z_0(L)+Z_1(L)+Z_2(L)+R(L)+P(L)+B(L).
\]

只要 \(F(L)<1\)，便有 \(\theta(y)-\theta(x)>\log y\)，所以 \((x,y)\) 中必有素数：若没有内点素数，\((x,y]\) 至多贡献右端点的 \(\log y\)。左端点已由差分自动排除。

## 6. 覆盖整个无限尾部的单调证明

以下均对 \(L\ge800\) 成立；\(u\) 严格递增。

1. \(Z_0\) 的对数导数为 \(\mu/u-3/32<0\)。
2. 对 \(Z_1\)，先观察
   \[
   \lambda'L-\lambda
   =\frac83\log2+2\log u-\frac{2\mu L}{u}>0,
   \]
   因为 \(\log u>1\) 且 \(\mu L/u<1\)。所以正函数 \(L/\lambda\) 递减。另有
   \[
   \frac d{dL}\log(u^3e^{-\lambda/8})
   =\frac{117}{128u}-\frac1{32}<0
   \quad(u>117/4).
   \]
   两个正递减因子的乘积 \(Z_1\) 递减。
3. \(Z_2\) 的对数导数为 \(2\mu/u-1/8<0\)。
4. \(R\) 的对数导数为 \(3/(3L+2)-1/32<0\)。
5. \(P\) 的对数导数为 \(2/(L+1)-1/4<0\)。
6. \(B\) 的对数导数为 \(1/(L+1)-3/4<0\)。

上述各导数中控制符号的倒数项随 \(L\) 递减。脚本在阈值处认证它们为严格负，同时认证 \(\lambda>0\) 以及使其永久保持正的条件。因此 \(F\) 在 \([800,\infty)\) 上递减。

## 7. Arb 认证与结果边界

`certify_tail.py` 中所有有限小数常数由整数比构造；没有将二进制浮点近似作为严格常数输入。Arb 的严格区间比较核查：

\[
F(800)<\frac{117}{1000}<1.
\]

其中主密度项约为 \(0.11601139774569547\)，最终准确球区间、其余各项、正余量、全部适用域检查、库版本及脚本 SHA256 保存在 `results/tail_certificate.json`。结合单调性，结论覆盖每个 \(L\ge800\)，不是只覆盖计算过的离散点。

这个认证没有证明 QRH，没有重证 FKS/CHJII 或其表格计算，没有处理 \(n<e^{200}\)，也没有声称本阈值具有新颖性。它提供一个明确、独立可复算的尾部模块，可供后续降低阈值与有限范围拼接使用。
