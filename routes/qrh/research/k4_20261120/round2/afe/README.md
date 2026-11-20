# 尖截断 Möbius 权的平滑对角余项

2026-11-20。作者为 Claude 与 Codex，本引理由 Codex 推导。研究输入是 Claude 的平方近似函数方程方案及[上一轮两个留数的计算](../../moment/README.md)。本引理把实际 Gamma 权保留到围道积分中，给出的界对高度逐点成立。以下结果均不依赖 QRH。

**定理。** 设 \(H=3\cdot10^{12},\ t\ge H,\ U=t/(2\pi),\ 1\le X\le10^{14}\)，\(0.70\le \sigma\le7/8,\ r=2\sigma-1,\ \delta=7/20\)。对 \(M_X(s)=\sum_{d\le X}\mu(d)d^{-s}\)，使用下文指定的对称辅助函数展开 \(|\zeta(\sigma+it)M_X(\sigma+it)|^2\)。其中的完整对角和 \(\mathcal D\) 满足
\[
 \mathcal D=R_1+R_2+\mathcal E,\qquad
 |\mathcal E|\le 6490 U^{-r-\delta},\qquad
 |\mathcal E|<0.531 U^{-r}.
\]
若 \(0.85\le\sigma\le7/8\)，两个常数可取为 \(3274\) 和 \(0.268\)。这里 \(R_2\le0\)，\(R_1=1+\sum_{k\ge2}(\sum_{d\mid k,\,d\le X}\mu(d))^2 k^{-2\sigma}\)。故这个平滑对角在方差尺度上有可用的单侧上界。后续的一阶矩引理给出了硬高度窗口与两种平滑权的显式成本。平方和中的非对角项仍须估计。[一阶矩的条件和证明](FIRST_MOMENT.md)

## 1. 对称近似函数方程

令 \(\Gamma_{\mathbb R}(z)=\pi^{-z/2}\Gamma(z/2)\)，
\(h_t(a)=\Gamma_{\mathbb R}(a+it)\Gamma_{\mathbb R}(a-it)\)，取
\[
 G(z)=e^{z^2}\prod_{a\in\{\sigma,1-\sigma\}}\,
             \prod_{\pm}\left(1-\frac{z^2}{(a\pm it)^2}\right).
\]
重复符号表示取两种符号的乘积。本任务的 \(\sigma>1/2\)。这一偶整函数实对称，满足 \(G(0)=1\)。设 \(\Lambda(s)=\Gamma_{\mathbb R}(s)\zeta(s)\)。将
\[
 \frac{\Lambda(\sigma+it+z)\Lambda(\sigma-it+z)}
 {h_t(\sigma)}\frac{G(z)}z
\]
从 \(\Re z=2\) 移到 \(\Re z=-2\)。\(G\) 在两个完成 zeta 函数的全部极点处为零，唯一留数为 \(z=0\) 的 \(|\zeta(\sigma+it)|^2\)。再用 \(\Lambda(s)=\Lambda(1-s)\) 和 \(G\) 的偶性，把新积分转回向上的右侧直线。所得直接项与反射项均可在绝对收敛域内展开。多项式 \(M_X\) 有限。以上移线可先限制在矩形上再将高边送到无穷，Gaussian 给出二次指数衰减。对照可见 Bettin、Chandee、Radziwiłł §3 引理 1 的临界线拆法，本文在固定正移位保留精确 Gamma 商。[作者原稿](https://www.math.mcgill.ca/radziwill/BCR.pdf)。

对 \(d,e\le X\)，记 \(g=(d,e),\,k=d/g,\,l=e/g\)。在直接项中取 \(dm=en\)，在反射项中交换 \(m,n\)，两者均有 \(mn=klj^2\)。对 \(j\) 求和，得到的两个 Mellin 被积函数与[上一轮 §1](../../moment/README.md)相同。取它们在 \(z=0\) 的两个留数
\[
 R_1=\zeta(1+r)\sum_{d,e\le X}\frac{\mu(d)\mu(e)}{g^{1+r}(kl)^{1+r}},
 \qquad
 R_2=\frac{h_t(1-\sigma)}{h_t(\sigma)}\zeta(1-r)
       \sum_{d,e\le X}\frac{\mu(d)\mu(e)}{g^{1+r}kl}.
\]
第一式与定理中 \(R_1\) 的另一表示相等，因为 \(gkl=[d,e]\)。第二式的非正性来自上一轮引理 1 的 Jordan 函数平方分解。

分别将直接和、反射和移到 \(\Re z=-r-\delta,-\delta\)。跨过的非零 zeta 极点在 \(-r/2,+r/2\)，留数逐对抵消。两条移线路径上的 Gamma 极点为 \(z=-\sigma\pm it,-(1-\sigma)\pm it\) 的适用子集，已由 \(G\) 消除。直接项换元 \(z=v-r\)，反射项取 \(z=v\)，得到精确的共同围道
\[
 \mathcal E=\frac1{2\pi i}\int_{(-\delta)}
  \frac{h_t(1-\sigma+v)}{h_t(\sigma)}\,
   \zeta(1-r+2v)\,D_X(v)
 \left\{\frac{G(v-r)}{v-r}+\frac{G(v)}v\right\}\,dv,
\]
\[
 D_X(v)=\sum_{d,e\le X}\mu(d)\mu(e)
                \frac{(d,e)^{1-r+2v}}{(de)^{1+v}} .
\]
两个被积函数共享所有算术因子。这个恒等式规避了以 \(kl>U\) 为界切割光滑权所产生的过渡区误差。

## 2. 算术因子的显式上界

令 \(v=-\delta+iu,\ \eta=\tfrac12-\delta=0.15,\ f(q)=\prod_{p\mid q}(1-p^{-1/2})^{-1}\)。Helfgott 证明 \(y\le10^{14}\) 时 \(|\sum_{n\le y}\mu(n)/n|\le\sqrt{2/y}\)。与只含 \(q\) 的质因子的整数上的权 \(1/n\) 卷积，可得 \(|m_q(y)|\le\sqrt2 f(q)y^{-1/2}\)，其中 \(m_q\) 限制 \((n,q)=1\)。[Helfgott，引理 5.10](https://webusers.imj-prg.fr/~harald.helfgott/anglais/PartI.pdf)；[Ramaré–Zuniga-Alterman，式 (9)](https://arxiv.org/html/2408.05969v2)。

分部求和给出对 \(1\le Y\le X\) 的界
\[
 \left|\sum_{\substack{n\le Y\\(n,q)=1}}\mu(n)n^{-1-v}\right|
 \le\sqrt2 f(q)\bigl[Y^{-\eta}
           +(1-Y^{-\eta})|v|/\eta\bigr]
 \le \sqrt2 f(q)\max(1,|v|/\eta).
\]
取复参数 Jordan 函数 \(J_c(q)=q^c\prod_{p\mid q}(1-p^{-c})\)，恒有 \(\sum_{q\mid k}J_c(q)=k^c\)。代入 \(D_X\) 的有限和后，只有无平方因子 \(q\) 留下，内和是
\(\mu(q)q^{-1-v}\sum_{(n,q)=1,n\le X/q}\mu(n)n^{-1-v}\) 的平方。故
\[
 |D_X(v)|\le2\,E(r)\max(1,|v|^2/\eta^2),\qquad
 E(r)=\prod_p\left(1+
       \frac{p^{-1-r}+p^{-2+2\delta}}{(1-p^{-1/2})^2}\right).
\]
乘积收敛且随 \(r\) 递减。有限和与 \(m_q\) 上界在负实部移线后同时保住了 \(U^{-\delta}\) 的幂节省。

## 3. Gamma 商和围道尾部

记 \(a=1-\sigma-\delta\in[-0.225,-0.05]\)。当 \(|u|\le t/2\)，
\[
 U^{r+\delta}|h_t(a+iu)|/h_t(\sigma)\le 5/4 .
\]
为验证此式，对 \(-1\le c\le1,\ |y|\ge10^8\)，以
\(\sqrt{2\pi}(|y|/2)^{(c-1)/2}e^{-\pi |y|/4}\) 归一化的
\(|\Gamma((c+iy)/2)|\) 在 \([0.999,1.001]\) 内。具体地，取 \(B=1+c/2,\ Y=|y|/2\)，用一次递推及 \(\log\Gamma(B+iY)\) 的 Stirling 公式。在右半平面首遗漏项误差不超过 \(1/(6Y)\)。其余对数误差依次为
\[
 \frac{B-1/2}{2}\log(1+(B/Y)^2),\quad
 Y\arctan(B/Y)-B,\quad -\tfrac12\log(1+(c/(2Y))^2).
\]
利用 \(0\le x-\arctan x\le x^3/3\) 和 \(\log(1+x)\le x\)，绝对值总和加上余项小于 \(1/Y\)。将此界用于 \(t+u,t-u,t,t\)；指数项抵消，余下系数至多
\((1.001/0.999)^2 (3/4)^{(a-1)/2}<5/4\)。[NIST DLMF，式 5.11.1 及 §5.11(ii) 的余项界](https://dlmf.nist.gov/5.11#ii)。

对全部实 \(u\)，令 \(z=v\) 或 \(v-r\)。有
\[
 |G(z)|\le e^{(\Re z)^2-u^2}
          \exp\{4(1.21+u^2)/t^2\}.
\]
在 \(|u|\le10\) 内最后一因子小于 \(1.001\)。在其余部分，两个 \(G(z)/z\) 的绝对值之和至多 \(10 e^{-0.99u^2}\)，因为分母分别至少 \(0.35,0.75\)。若 \(w=1-r+2v\)，则 \(-0.45\le\Re w\le-0.10\)。有一次 Bernoulli 修正的 Euler–Maclaurin 公式给出
\[
 |\zeta(w)|\le |w-1|^{-1}+\tfrac12+|w|/12+
           |w(w+1)|/[12(1+\Re w)]\le10(1+|u|)^2.
\]
这里用到 \(\sup_{0\le y\le1}|B_2(y)|=1/6\)。

脚本验证整个参数域 \(E(r)<232\)。在 \(10\le u\le t/2\)，乘以 \(U^{r+\delta}\) 后的被积函数绝对值小于 \(10^8(1+u)^4e^{-0.99u^2}\)。其积分小于 \(10^{-18}\)，由 \((1+u)^4\le e^{u^2/4}\) 及 \(\int_{10}^\infty e^{-0.74u^2}du\le e^{-74}/14.8\) 得到。

\(u\ge t/2\) 时，递推和 Gamma 的 Euler 积分给出
\(|\Gamma((a+iy)/2)|\le2\Gamma(1+a/2)/|a|<100\)，对每个 \(y\) 有效（在 \(0.88\le x\le1\)，Gamma 积分按 1 分割即得 \(\Gamma(x)\le1/x+e^{-1}<2\)）。再用上面的 Stirling 下界处理分母，可取
\(U^{r+\delta}|h_t(a+iu)|/h_t(\sigma)<10^5 t^2 e^{2t}\)。
故归一化后的被积函数不超过 \(10^{14}t^2e^{2t}(1+u)^4e^{-0.99u^2}\)，它在此范围内小于 \(e^{-u}\)。例如 \(t\le2u,\ u\ge1.5\cdot10^{12}\) 时，取对数后各正项的和小于 \(0.1u^2\)。积分遂小于 \(e^{-t/2}\)。负 \(u\) 得相同的界。连同 \(1/(2\pi)\) 因子，两段竖直尾部总和小于 \(10^{-14}U^{-r-\delta}\)。

## 4. 主范围的区间算术

脚本 [check_smooth_diagonal.py](check_smooth_diagonal.py) 使用 160 位 Arb。对 \(E(r)\) 精确筛至 \(P=100000\)。把对数乘积尾部放大为整数幂和的积分，所得上界为
\[
 (1-P^{-1/2})^{-2}
 \left(P^{-r}/r+P^{-1+2\delta}/(1-2\delta)\right).
\]
横向按 \(r=i/200\ (80\le i\le150)\) 切格。每个 \([r_-,r_+]\) 用左端点的 \(E\) 上界。取 \(0\le u\le10\) 的步长为 \(1/128\)。每格 \([b,c]\) 以复区间算术计算 \(|\zeta(1-r-2\delta+2iu)|\) 的上界，并乘以
\[
 e^{-b^2}\max(1,(\delta^2+c^2)/\eta^2)\left[
 \frac{e^{(r_++\delta)^2}}{\sqrt{(r_-+\delta)^2+b^2}}
 +\frac{e^{\delta^2}}{\sqrt{\delta^2+b^2}}\right].
\]
求上和并乘 \(2E(r_-)\cdot(5/4)\cdot1.001/\pi\)，最后加上上一节尾部。重放命令为本目录运行 **python -B check_smooth_diagonal.py**。各格最大上界的表达式为 \(6489.21963\) 以下，在 \(\sigma\ge0.85\) 的最大值小于 \(3273.45508\)。对 \(U^{-\delta}\) 取 \(t=H\) 给出定理中的另一组常数。

**与四次幂缺口的关系。** 在 \(\sigma=7/8,\ t=H\)，若拟取 \(X=t^{7/8}\)，上述误差除以 \(X^{-3/4}\) 小于 \(0.268(2\pi t^{-1/8})^{3/4}<0.073\)。这把该尺度的平滑对角问题化为一个小的显式加项。若 \(X>10^{14}\)，这里的有限 Möbius 和界不足以支持同一条移线。若取 Barban–Vehov 权，也需另行处理系数。下一项主要数学义务仍是实际高度权及其非对角贡献。Ingham 1937 原文第 257 页明确将 \((1+2\sigma)(1-\sigma)\) 归于定理 5，第 3 定理还给出另一种指数。Claude 对定理 5 的归属正确，两个传统估计均未给出本文所需的有限高度完整矩界。[Ingham 原文](https://doi.org/10.1093/qmath/os-8.1.255)。
