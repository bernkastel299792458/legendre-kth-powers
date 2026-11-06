# Round 5 下端：Selberg 频宽越过有限 RH 高度的严格窄带控制

2026-11-06，Codex 子任务。只新增本目录文件；没有修改 round4、主日志、
计算分支、k=6 或 publication。**候选：待独立解析复审与第二实现；本轮不改变正式覆盖。**

## 结论及意义

沿用 round4 的 Selberg minorant 和 Gaussian 正则化，在 **QRH(7/8)**
假定下，本候选推导将同一显式公式的充分条件验证到每个实数

\[
113.1\le L=\log x\le113.1124367.
\]

从而这些 x 的开区间 `(x,x+4x^(3/4))` 含素数。这里没有使用 CS 密度估计。
本轮不是 k=4 全范围证明。主要增加仍来自使用有限 RH 已公布的实际高度并逼近
正质量阈值；真正越过该阈值的部分仅约 `1.3254e-7`。
其理论新内容是：**QRH 可支付一小段未知零点频带的代价，严格带限阈值并非
加入 QRH 后的绝对障碍。** 下面给出完整可核对的边缘频谱与泄漏引理。

经典输入、Fourier 归一化、素数抽取沿用
[round4](../../research/K4_SELBERG_ROUND4.md) 第 2–4、6 节。
对应主来源是 [Lê–Vaaler, Lemma 3.1](https://arxiv.org/pdf/1309.1506v1)、
[CMS, Lemma 6](https://arxiv.org/pdf/1708.04122v2)、
[Platt–Trudgian, arXiv:2004.09765v1, Theorem 1, PDF 第 2 页](https://arxiv.org/pdf/2004.09765v1)。
这里只把最后来源的验证高度使用到内部整数

\[
H=3000175332799<3000175332800,
\quad w=320000,\quad K=H+w,\quad T=K+64.
\tag{1}
\]

因此所有 `0<gamma<=H` 的零点都在临界线上。高于 H 的零点只用 QRH
及函数方程所给出的 `|beta-1/2|<=3/8`；未把它们当作临界线零点。

## 1. 显式边缘频谱引理（本文推导）

仍令 `d=log(1+4exp(-L/4))/2`、`c=L+d`，f 为 round4 式 (3) 的实偶
Selberg minorant，`G0(t)=integral f(v)exp(itv)dv`。若 `0<t<K`、`u=t/K`，则

\[
G_0(t)=\frac{2\sin(td)}t W(u)
-\frac{2\pi}{K}(1-u)\cos(td),
\quad
W(u)=\pi u(1-u)\cot(\pi u)+u.
\tag{2}
\]

简要独立推导：写 `K_B(x)=(sin(pi*x)/(pi*x))^2`，则
`H_B(x)=sum_{j!=0}sgn(j)K_B(x-j)+2sin^2(pi*x)/(pi^2*x)`。
在 tempered distributions 意义下采用 `exp(2*pi*i*u*x)` 变换。
第一项的变换为 `(1-|u|)_+ i cot(pi*u)`（cot 取主值，可由 Abel 和
`sum_{j>=1}r^j(exp(2*pi*i*j*u)-exp(-2*pi*i*j*u))` 的极限得到）；
第二项为 `i sgn(u)/pi` 于 `|u|<1`，外部为零。这两个表达式相加给出
`i W(|u|)/(pi*u)`。代入 f 的两次平移及缩放，主值奇点由 `sin(td)`
消去，得到 (2)。在 t=0 连续延拓给出 `2d-2pi/K`，在 t=K 连续为零。
这也核对了角频归一化和符号。

取 `r=1-u`。对于 `0<=r<=1/2`，cot 的部分分式展开给出

\[
0\le1-\pi r\cot(\pi r)
=2r^2\sum_{j\ge1}\frac1{j^2-r^2}
\le\frac{\pi^2r^2}{3(1-r^2)}\le\frac{4\pi^2}9r^2.
\]

故 **对任意 d>0**、`K/2<=t<=K`，

\[
|G_0(t)|\le A(K-t)+B(K-t)^2,
\quad A=\frac{2\pi}{K^2},\quad B=\frac{8\pi^2}{9K^3}.
\tag{3}
\]

这是新窄带估计的关键。仅使用 round4 的粗界 `|G0|<=U` 会丢失此线性边缘消失。

## 2. Gaussian 泄漏与复零点引理

置 `F(v)=f(v)exp(-v^2)`，并记 `U=2d+2pi/K`、`V=2KU`。
round4 的卷积公式仍在整个复平面成立。令

\[
I_j(q)=\frac1{2\sqrt\pi}\int_{-q}^{\infty}(q+s)^j e^{-s^2/4}\,ds.
\]

对于 `gamma>=H>K/2` 以及实数 delta，由 (3) 和卷积的绝对值有

\[
|G(\gamma-i\delta)|\le e^{\delta^2/4}
\left[A I_1(K-\gamma)+B I_2(K-\gamma)
+\frac V{2\sqrt\pi}e^{-(\gamma-K/2)^2/4}\right].
\tag{4}
\]

证明：把卷积拆为 `K/2<=t<=K` 与 `-K<=t<K/2`。前一段用 (3)，
令 `s=gamma-t` 后把非负积分延长至无穷；后一段用 `||G0||1<=V`。
因此式 (4) 明确包括了 `H<gamma<K` 内部的未知频带和复位移；
没有误用仅适用于 `gamma>K` 的 Gaussian 带外尾界。

`I1,I2` 是 q 的非负递增函数，且 `I2'=2I1`、`I3'=3I2`。
对 w>=0，初等 Gaussian 积分给出如下方便的严格上界：

\[
I_1(w)\le J_1:=w+1/\sqrt\pi,
\quad I_2(w)\le J_2:=w^2+2+w/\sqrt\pi,
\]
\[
I_3(w)\le J_3:=w^3+6w+(w^2+4)/\sqrt\pi.
\tag{5}
\]

尤其 `integral_H^infinity I1(K-t)dt=I2(w)/2`，
`integral_H^infinity I2(K-t)dt=I3(w)/3`。

## 3. 计数的 Stieltjes 窄带预算

用 Rosser 的总零点数界，按 [FKS Lemma 2.1 / Remark 2.2](https://arxiv.org/html/2204.02588v3)
记 `P(t)=t/(2pi)log(t/(2pi*e))+7/8`、
`R(t)=.137log(t)+.443loglog(t)+1.588`，则 `|N(t)-P(t)|<=R(t)`。
计数若采用不同端点约定，取右极限；以下上界不受影响。
具体使用 `N(t)<=P(t)+R(t)` 和 **下界** `N(H)>=P(H)-R(H)`，
没有相减两项上界。于是对 H<=t<=T，

\[
N(t)-N(H)\le a(t-H)+b,
\quad a=\frac1{2\pi}\log\frac T{2\pi},\quad b=R(T)+R(H).
\tag{6}
\]

对任何非负递减 C1 函数 E，分部积分严格推出

\[
\int_{(H,T]}E(t)\,dN(t)\le a\int_H^T E(t)dt+bE(H).
\tag{7}
\]

将 E 取为 (4) 中的前两项，利用 (5) 即得正高度未知窄带的谱预算

\[
D_{\rm edge}=a(AJ_2/2+BJ_3/3)+b(AJ_1+BJ_2).
\tag{8}
\]

`H-K/2>64`，故 (4) 最后一项在 H..T 的总和至多
`V T^2 exp(-1024)/(2sqrt(pi))`，这里仅用 `N(T)<T logT<T^2`。
高于 T 的带外 Gaussian 尾用 round4 同一 Stieltjes 推导，给出
`V T^2(1+4/64^2)exp(-1024)/(2sqrt(pi))`。
因此合计可用

\[
D_{\rm rem}=\frac V{2\sqrt\pi}T^2(2+4/64^2)e^{-1024}.
\tag{9}
\]

QRH 与共轭对称性保证整个高零点贡献至多

\[
Z_{\rm high}\le 2\cosh(3c/8)e^{9/256}
(D_{\rm edge}+D_{\rm rem}).
\tag{10}
\]

这是一个适用于所有满足 (1) 型窄带参数的明确引理，而非特定零点分布的启发式。

## 4. 整个实区间的可复算充分条件

脚本 [selberg_overshoot.py](selberg_overshoot.py) 使用 256-bit Arb。
令 `Llo=113.1, Lhi=113.1124367`，固定 H,K,T，取

\[
d_{\max}=d(L_{lo}),\ d_{\min}=d(L_{hi}),\quad
U_{\max}=2d_{\max}+2\pi/K,\quad V_{\max}=2K U_{\max}.
\]

`c(L)` 递增而 d 递减，故下列量分别是一致下界/上界：

\[
M_{\min}=2\cosh(c(L_{lo})/2)
\left(2d_{\min}-2\pi/K-2d_{\max}^3\right),
\]
\[
Z_{\rm low}\le2H\log H\,U_{\max},\quad
|\mathcal A|\le\frac{V_{\max}}{2\pi}
\left(7+\log(1+K)+2/\sqrt\pi\right),
\]
\[
P_{\rm pp}\le\frac{e^{d_{\max}}(L_{hi}+2d_{\max})^2}{2\log2}.
\]

式 (10) 用 `c(Lhi),Vmax`。检验
`Mmin>Zlow+Zhigh+|A|+Ppp` 后，round4 的严格开区间素数抽取直接适用。
脚本还检查整段在已验证高度内/外的分界、正质量、真正跨过 H 的正质量阈值，
以及整数 n 的端点。结果文件为 [selberg_overshoot.json](selberg_overshoot.json)。
运行 `python -B -X utf8 Legendre_k8/theory_round5/lower/selberg_overshoot.py --verify`
只读复算。该脚本只认证列出的标量条件，未形式化文献定理或分布 Fourier 计算。

首次 Arb 结果如下（表中数字为显示近似值，严格区间在 JSON 内）：

| 量 | 数值 |
|---|---:|
| pole 一致下界 | 558241.1894559247 |
| 高零点一致上界 | 418229.5714936816 |
| 全部代价一致上界 | 428329.6389919614 |
| 正余量下界 | 129911.5504639633 |
| 相对代价上界 | 0.767284190207143 < 4/5 |
| 候选新增整数区间 | 1904041788884 <= n <= 1909971000714 |

额外自检在内存中以 70 位 mpmath 重算上述代价与余量，显示值吻合；
另在 K=2pi、d=.37、v=.11,.73,1.62，数值反 Fourier 积分 (2) 与
由 trigamma 表达的原始 Selberg f 相比，误差均低于 1e-60。
这些检查只用于抓取归一化或代码错误，**不是独立解析复审或第二个严格实现**。

## 5. 不能把微小跨越理解为密度突破

令 `Lcrit(H)=-4log((exp(2pi/H)-1)/4)`，写 `L=Lcrit+s`。
在 `w/H`、s 很小时，忽略较小误差的主预算为

\[
M\sim \frac{2\pi e^{L/2}}{H^2}(w-Hs/4),\qquad
Z_{high}\lesssim e^{9/256}\frac{\pi a e^{3L/8}}{H^2}w^2.
\tag{11}
\]

这个二次预算自身允许的 s 只有约 `2exp(L/8)/(aH)`，此处约 `2e-7`。
式 (11) 是该具体绝对值估计的尺度诊断，并非对其他方法的不可能性定理。
当所需增量变为 0.01、0.1 时，不能继续把未知窄带当作如此微薄的 Gaussian 尾。

CS 的 [Theorem 1 及证明](https://arxiv.org/html/2507.15184v2) 左边虽写
`N(sigma,T)-N(sigma,H)`，右边主要仍随 T 的幂增长；它没有给出只依赖 T-H 的主项。
两项密度上界不能相减来取得局部计数上界。本文没有这样使用它。
其 Littlewood 矩形从 H 积到 T，但 dominant mollifier moment 由以零为中心、
尺度为 T 的 Gaussian 插值估计控制；恢复 Lemma 7 中舍弃的一个 T-H 项
并不能自动使主项局部化。

后续真正可检验的接口是：建立 explicit anchored density `D_sigma(v)`，满足
`N(sigma,H+v)-N(sigma,H)<=D_sigma(v)`、`D_sigma(0)=0`，并在
第 3 节同样的 Stieltjes 权重下使用。必须对全部 beta 层积分或离散分层，
不能只控制 beta≈7/8 一层。新界应首先在 `v≈1e9..1e11` 的实际尺度代入预算，
若预算仍大于 pole 则停止推广该具体路线，转向零点相位取消或其他显式公式结构。
这个接口尚未证明，不能作为当前结论的一部分。

## 6. 可直接接入将来局部密度定理的分层引理

这里给出接口的精确形式，避免把第 5 节的建议误解为只需一个端点计数。
记 `vmax=T-H`、`E(t)=A I1(K-t)+B I2(K-t)`，并设对每个
`1/2<sigma<7/8` 已经有真实零点的局部上界

\[
N(\sigma,H+v)-N(\sigma,H)\le D_\sigma(v),\qquad 0\le v\le v_{max}.
\]

定义

\[
\mathcal B_\sigma=E(T)D_\sigma(v_{max})+
\int_0^{v_{max}}D_\sigma(v)(-E'(H+v))\,dv.
\tag{12}
\]

由 Stieltjes 分部积分，带 E 权的该层零点计数不超过 `B_sigma`。
函数方程使同一正高度的 beta 与 1-beta 配对。对固定高度带作层析积分可得

\[
\sum_{H<\gamma\le T}\cosh(c(\beta-1/2))E(\gamma)
\le \mathcal B_{\rm all}
+2c\int_{1/2}^{7/8}\sinh(c(\sigma-1/2))\mathcal B_\sigma\,d\sigma,
\tag{13}
\]

其中 `B_all` 是 (8) 的总零点数预算。证明只需对每个零点使用
`cosh(c|delta|)=1+integral_0^|delta| c sinh(cu)du`，再用配对与 Tonelli；
故临界线零点和所有中间 beta 层都已计入。最终乘 `2exp(9/256)`，
加上 (9) 经 `2cosh(3c/8)exp(9/256)` 放大的余项，得到新的高零点上界。
当前的 (10) 相当于直接用 QRH 的最坏 cosh；(12)–(13) 不要求采用该粗化。

因此，新的局部密度定理是否足够，可由这个明确的一维/二维积分预算判定。
在边缘线性近似下，所需控制的是 `A integral_0^w D_sigma(v)dv`。
一个全局常数包络给出约 `A D_global w`，真正线性局部包络才给出约
`A density_sigma w^2/2`；这两种量不能混淆。式 (12)–(13) 本身已由上述
初等分部积分和层析推导，缺少的是足够强、常数明确的 `D_sigma(v)`。
