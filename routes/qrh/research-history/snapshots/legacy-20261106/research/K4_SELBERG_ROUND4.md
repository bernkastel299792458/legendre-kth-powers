# 第四轮：Selberg minorant 将有限 RH 下端覆盖延伸至 L=113.1

2026-11-06。Codex 理论分支。只新增本文、`code/k4_selberg_round4.py` 与
`results/k4_selberg_round4.json`；不修改 round3、k=6、主证书或独立算法分支。

**结果。** 对每个实数 x，若

\[
\frac{225}{2}\le L:=\log x\le\frac{1131}{10},
\]

则开区间 `(x,x+4x^(3/4))` 含有素数。这里使用经典 Selberg minorant、
Guinand–Weil 公式、Platt–Trudgian 已验证的有限 RH 和经典总零点计数；
**不使用额外 QRH 或 CS 密度假设。** 这是以明确文献输入为基础的书面计算辅助论证，
并非端到端 Lean 形式化，也不宣称整个 k=4 已闭合。

本轮换用 Selberg 的精确质量缺损 `2pi/K`，不是微调上一轮的 sinc 参数。
一个一般 L¹ 引理使显式频谱计算不再必要。整个闭区间的认证相对预算小于
`5.916641e-7 < 10^(-6)`，并与上一轮的右端点 `L=225/2` 精确衔接。

## 1. 记号和固定输入

置

\[
y=x+4x^{3/4},\quad\varepsilon=4e^{-L/4},\quad
d=\tfrac12\log(1+\varepsilon),\quad c=L+d,
\]

故目标的对数区间为 `(c-d,c+d)`。采用角频率 Fourier 变换
`G0(t)=integral_R f(v) exp(itv) dv`，逆变换系数为 `1/(2pi)`。

固定

\[
H=3000000000000,\qquad K=H-128=2999999999872.
\tag{1}
\]

文献输入分别是：

- [Lê–Vaaler，Sums of products of fractional parts，arXiv:1309.1506v1，式 (3.1)–(3.7)、Lemma 3.1，第 6–7 页](https://arxiv.org/pdf/1309.1506v1)：
  下节使用的 Selberg minorant。也实际核对了[作者保存的出版后稿](https://home.olemiss.edu/~leth/papers/fractional_parts.pdf)
  中同号引理；文章发表于 [Proc. London Math. Soc. 111 (2015), 561–590](https://doi.org/10.1112/plms/pdv038)。
- [Carneiro–Milinovich–Soundararajan，arXiv:1708.04122v2，Lemma 6](https://arxiv.org/pdf/1708.04122v2)：
  Guinand–Weil 公式，使用第 4 节写明的归一化。
- [Platt–Trudgian，arXiv:2004.09765v1，Theorem 1](https://arxiv.org/pdf/2004.09765v1)：
  RH 已验证至 `3000175332800>H`，因此所有 `0<gamma<=H` 的零点满足 `beta=1/2`。
- [FKS v3，Lemma 2.1、Remark 2.2](https://arxiv.org/html/2204.02588v3)
  对 Rosser 总数界的重述，仅使用 `0.137,0.443,1.588` 三个经典常数，不使用该文的密度估计。
  如 N(T) 按正高度、重数及右端点计数，则对 `T>=H` 有

\[
N(T)<(T/2+3.043)\log T<T\log T.
\tag{2}
\]

这里 `3.043=7/8+0.137+0.443+1.588`；使用 `loglog T<=log T`、`log T>=1` 即可从源界推出。
源计数若采用平均端点，可取右极限。没有把式 (2) 应用到 H 以下的高度。
全部零点仍只需经典条带 `0<beta<1` 和共轭对称性。

## 2. 实际使用的 Selberg 函数

为避免与高度 H 和频宽 K 混淆，记 Beurling 的函数为

\[
H_B(z)=\left(\frac{\sin\pi z}{\pi}\right)^2
\left(\sum_{j\ne0}\frac{\operatorname{sgn}(j)}{(z-j)^2}+\frac2z\right),
\qquad K_B(z)=\left(\frac{\sin\pi z}{\pi z}\right)^2,
\]

可去奇点取整函数延拓。取 `tau=K/(2pi)>0`，定义

\[
f(z)=\tfrac12\big[H_B(\tau(z+d))-H_B(\tau(z-d))
-K_B(\tau(z+d))-K_B(\tau(z-d))\big].
\tag{3}
\]

上述源引理给出 f 实整、属于 `L1(R)`，且在实轴上不超过目标区间的规范化指示函数。
H_B 为奇函数、K_B 为偶函数，故 f 是偶函数。
源 Fourier 采用 `exp(-2pi iuv)`；转换到本文角频后，得到

\[
\operatorname{supp}G_0\subset[-K,K],\qquad
m:=\int_{\mathbb R}f=2d-\frac{2\pi}{K}.
\tag{4}
\]

规范化指示函数在端点取 1/2，不影响积分。更关键的是，由 f 连续且在 `|v|>d` 非正，
可取外侧极限得到 `f(±d)<=0`，因此端点不会误抽取素数。

Lemma 3.1 对任意正 tau 与任意区间长度成立，不要求 `tau*2d` 为整数。
本轮只使用其质量、符号、L¹ 性和频谱支撑，不声称当前非整数参数下 f 是所有 minorant 中的最优者。
[Bober 等人的 Definition 4.2、Lemma 4.3](https://arxiv.org/pdf/1211.5996v2) 提供了另一个实际核对的写法；
不使用该文关于 L 函数零点的 GRH 主定理。

## 3. 一般 L¹ 引理与 Gaussian 正则化

以下推导适用于任意实偶连续 `f in L1(R)`，只要 `f(v)<=1` 于 `|v|<d`、
`f(v)<=0` 于 `|v|>=d`、`integral f=m>0`，且角频谱支持在 `[-K,K]`。
不要求 f 在目标区间内部非负。

由于 `f_+<=1_{(-d,d)}`，

\[
\|f\|_1=2\int f_+-m\le4d-m=:U.
\]

再由 `|G0(t)|<=||f||1` 与有限频谱支撑，

\[
\|G_0\|_1\le2K U=:V.
\tag{5}
\]

Selberg 情形特别给出 `U=2d+2pi/K`。这就是本轮代替显式谱求积的界。
因为 f 与 G0 都可积，Fourier 逆变换还给出点态界 `|f(v)|<=V/(2pi)`。

令

\[
F(v)=f(v)e^{-v^2},\qquad
G(z)=\int_{\mathbb R}F(v)e^{izv}dv.
\]

高斯尾与 f 的点态界保证该积分定义整函数；卷积公式给出

\[
G(z)=\frac1{2\sqrt\pi}\int_{-K}^K G_0(t)e^{-(z-t)^2/4}dt.
\tag{6}
\]

等式先在实轴证明，再延拓至整个复平面。对实 gamma>K 和 delta，

\[
|G(\gamma-i\delta)|
\le\frac{V}{2\sqrt\pi}e^{\delta^2/4}e^{-(\gamma-K)^2/4}.
\tag{7}
\]

正则化后的 F 并不严格带限；式 (7) 正是必须保留的频谱泄漏。
它同时证明 G 在每个固定水平条带上实方向快速衰减。

**pole 质量。** 偶性给出 `G(i/2)=integral f(v) w(v)dv`，
其中 `w(v)=exp(-v²)cosh(v/2)` 满足 `0<w<=1` 和 `w>=1-v²`。
f 的负部分乘 w 只会提高积分；正部分局限在 `(-d,d)` 并不超过 1。
因此

\[
G(i/2)\ge m-2d^3.
\tag{8}
\]

事实上可将损失改为 `2d³/3`，本轮保留较粗的 `2d³`。
没有假定 f 在内部处处为正，也没有漏掉外部负尾。

## 4. 显式公式和开区间素数抽取

设

\[
h(z)=\cos(cz)G(z),\quad Q(u)=F(u-c)+F(u+c),\quad
S=\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}Q(\log n).
\]

式 (6) 保证 h 在 `|Im z|<=1/2+epsilon` 上解析且随 `|Re z|` 快速衰减。
`|F(v)|<=V exp(-v²)/(2pi)` 保证素数侧绝对收敛；式 (7) 与经典总数增长保证零点侧绝对收敛。
所以可使用 CMS Lemma 6。

具体地，`h(t)=integral Q(u)exp(itu)du/2`，故源文周期频率变换满足
`hat h(log n/(2pi))=pi Q(log n)`。源文的对称两项于是合并为 S，得到

\[
S=M-\sum_\rho h\big(\gamma-i(\beta-1/2)\big)+\mathcal A,
\quad M=2\cosh(c/2)G(i/2),
\tag{9}
\]
\[
\mathcal A=\frac1{2\pi}\int_{\mathbb R}h(t)\Omega(t)dt,\qquad
\Omega(t)=\Re\frac{\Gamma'}{\Gamma}(1/4+it/2)-\log\pi.
\]

由于 `c>d`，对 `u>=0` 总有 `F(u+c)<=0`。因此 Q 在目标开对数区间外非正，
在目标内至多为 1，两个端点也非正。正素数幂贡献不超过

\[
P:=\frac{\psi(y)-\theta(y)}{\sqrt x}
\le\frac{e^d(L+2d)^2}{2\log2}.
\tag{10}
\]

最后一式是初等 `psi(y)-theta(y)<=sqrt(y)(log y)²/(2log2)`。
故只要由式 (9) 得到 `S>P`，就必有某个内部素数的正权贡献，推出严格的 `x<p<y`。
外部负素数权无需删除；它只使这个充分条件更强。

## 5. 四项完整误差预算

低于 H 的零点均在临界线上，因此

\[
Z_{\rm low}\le2N(H)\|F\|_1\le2H\log H\,U.
\tag{11}
\]

对于高零点，写 `delta=beta-1/2`。本轮使用完整临界条带的 `|delta|<1/2`，
并保留平移中心外因子

\[
|\cos(c(\gamma-i\delta))|\le\cosh(c\delta)\le\cosh(c/2).
\]

若 `D=H-K>=64`，式 (2)、(7) 和 Stieltjes 分部积分给出

\[
Z_{\rm high}\le2\cosh(c/2)\frac{V}{2\sqrt\pi}e^{1/16}
H^2(1+4/64^2)e^{-1024}.
\tag{12}
\]

为明确完整尾部：取 `w(t)=exp(-(t-K)²/4)`，
`integral_(H,infty) w dN=-N(H)w(H)+integral_H^infty N(t)(-w'(t))dt`。
丢弃负下端项，在 `t>=H` 用 `N(t)<=t log t<=t²`。
换元 `v=t-K>=D`，用 `K+v<=(H/D)v`，积分恰不超过
`H²(1+4/D²)exp(-D²/4)`，再放大至式 (12)。
这包含所有高于 H 的零点；没有把实轴的原始谱支撑错误延伸成复零点处的硬截断。

无穷位可用

\[
|\Omega(t)|\le7+\log(1+|t|).
\]

一个直接证明由 [DLMF 5.7.6](https://dlmf.nist.gov/5.7.E6) 开始：
`Re psi_Gamma(1/4+ib)-psi_Gamma(1/4)` 是正项和
`sum_(j>=0) b²/[(j+1/4)((j+1/4)²+b²)]`。
第 0 项不超过 4，其余由首项加积分不超过 `1+log(1+b²)/2`。
结合 `-5<psi_Gamma(1/4)=-EulerGamma-pi/2-3log2<0`、`b=|t|/2` 即得。
对式 (6) 的高斯卷积取模，用其一阶绝对矩 `2/sqrt(pi)`，得到

\[
|\mathcal A|\le\frac{V}{2\pi}
\left[7+\log(1+K)+\frac2{\sqrt\pi}\right].
\tag{13}
\]

此项已包含无穷位/平凡零点信息。素数幂由式 (10) 单独支付。
联合式 (8)–(13)，一般充分条件是

\[
2\cosh(c/2)(m-2d^3)>Z_{\rm low}+Z_{\rm high}+|\mathcal A|+P.
\tag{14}
\]

## 6. 全实参数区间的统一认证

取 `L_-=225/2`、`L_+=1131/10`，记 `d_-=d(L_-)`、`d_+=d(L_+)`，c 同理。
因为
`d'(L)=-epsilon/[8(1+epsilon)]<0`、`c'(L)>7/8`，
可对每个 L 一致使用

\[
m_{\min}=2d_+-2\pi/K,\quad
U_{\max}=2d_-+2\pi/K,\quad V_{\max}=2K U_{\max},
\]
\[
M_-=2\cosh(c_-/2)(m_{\min}-2d_-^3).
\tag{15}
\]

式 (11)、(13) 使用上述 U、V；式 (12) 中 c 用 `c_+`；
素数幂取 `exp(d_-)(L_++2d_-)²/(2log2)`。
对每个 L 都选取式 (3) 的 Selberg 函数。证明不需要该选择依 L 解析，
更没有以有限点采样替代整个闭区间。

256 位 Arb 的结果是：

| 项目 | 统一界或精确参数 |
|---|---:|
| K | 2999999999872 |
| H−K | 128 > 64 |
| Selberg 最小质量 | 6.3991255374446… × 10^(-15) |
| 空间 L¹ 上界 U_max | 4.5351697735217… × 10^(-12) |
| 频谱 L¹ 上界 V_max | 27.211018639969… |
| 主项下界 M_- | 17186412735.484212… |
| 低零点上界 | 781.762590125318… |
| 高零点上界 | 5.113911… × 10^(-395) |
| 无穷位绝对上界 | 159.623505926740… |
| 正素数幂上界 | 9227.196156004496… |
| 全部扣除上界 | 10168.582252056553… |
| 扣除/主项下界 | 5.916640318466… × 10^(-7) < 10^(-6) |

所有比较使用完整 Arb 球，表中小数只供阅读。19 个严格检查中，15 个是上述标量前提，
另 4 个独立检查整数端点：

\[
1638823955139\le n\le1904041788883.
\tag{16}
\]

整数先由 `floor(exp(L/4)).unique_fmpz()` 唯一隔离，再用相邻整数的四个严格 log 不等式复核。
上一轮至 `n=1638823955138`，因此整数链无缝；实参数链在 `L=225/2` 共享端点。
因为 `n^4+4n^3<(n+1)^4`，本段当然也给出相邻四次幂间的素数。

## 7. 改进的含义与边界

本轮没有对同一个 sinc 核调参，而是将上一轮的“特定核质量/频谱常数”替换为一个一般引理，
再利用 Selberg 的经典缺损 `2pi/K`。保守的频谱 L¹ 界虽然不精细，但现有主项余量足以吸收它。
不需要数值评价 Beurling 的无穷级数、复 Fourier 求积或新的零点相消假设。

固定频宽 K 时，Selberg 正质量条件为 `K*log(1+4exp(-L/4))>2pi`。
频宽不能超过有限 RH 截点而完全避免未知高频时，其尺度约为旧轮记录的 `L=113.1122…`。
本轮在 113.1 停止，不进行末位优化；不由此推断所有正则化权的最优上限。
它没有解决更大的核心中段，也没有排除此前在 L=120 的计数模型障碍。

本轮下一步是把这个一般引理作为理论组件审阅、接入已存在的下端链。
若要显著越过有限 RH 的频宽尺度，仍须处理未知高零点的频谱贡献或引入新的算术/相位输入，
不能把 Gaussian 泄漏当作零。

## 8. 可复算产物和证据等级

```powershell
python -B code/k4_selberg_round4.py
python -B code/k4_selberg_round4.py --verify
```

第一条只写专属 JSON。第二条只读重算并比较全部字段，包含本文和脚本的 SHA256。
脚本独立使用 python-flint Arb，未导入旧项目代码或算法分支代码。
JSON 检查的是连续论证中的有限标量不等式；式 (3)–(14) 的解析连接与文献前提仍必须审阅。
已有发表输入未在此独立重证；本文件没有把 Arb 成功、AI 复核或不存在 `sorry` 等同于端到端形式化。
