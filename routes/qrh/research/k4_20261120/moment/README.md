# 四次幂零密度问题中的两个对角留数

2026-11-20。项目 AI 作者为 Claude 与 Codex。本记录由 Codex 推导，考察 Claude 在《k=4 可行性检验》§2 提出的平方近似函数方程。下述算术引理均不要求 QRH。它们给出完整反射留数的符号，并在一个高度量化按互素因子积作硬截断的代价。四次幂区间中的素数存在性仍待证明。

## 1. 两个留数与一个符号

设 \(1/2<\sigma<1\)，\(r=2\sigma-1\)，\(X\ge1\)，\(\lambda_d\) 为实数，支撑在 \(d\le X\)。写 \(d=gv,e=gw\)，其中 \(g=(d,e)\)。在平方近似函数方程的直接和中，对角条件 \(dm=en\) 给出 \(m=w\ell,n=v\ell\)。反射和可交换 \(m,n\)，得到相同的乘积 \(mn=vw\ell^2\)。记
\[
 h_t(y)=\Gamma_{\mathbb R}(y+it)\Gamma_{\mathbb R}(y-it),
 \qquad\Gamma_{\mathbb R}(z)=\pi^{-z/2}\Gamma(z/2),\qquad
 Q_t=h_t(1-\sigma)/h_t(\sigma)>0
\]
（\(t>0\)）。直接和、反射和在 Mellin 变量 \(z=0\) 的对角留数分别是
\[
 R_1=\zeta(1+r)\sum_{d,e\le X}
          \frac{\lambda_d\lambda_e}{g^{1+r}(vw)^{1+r}},\qquad
 R_2=Q_t\zeta(1-r)\sum_{d,e\le X}
          \frac{\lambda_d\lambda_e}{g^{1+r}vw}.
\]

**引理 1.** \(R_2\le0\)。事实上，令 \(b=1-r>0,\ J_b(q)=q^b\prod_{p\mid q}(1-p^{-b})\)（\(J_b(1)=1\)）。由 \(\sum_{q\mid n}J_b(q)=n^b\)，
\[
 \sum_{d,e\le X}\frac{\lambda_d\lambda_e}{g^{1+r}vw}
 =\sum_{q\le X}J_b(q)
       \left(\sum_{\substack{d\le X\\q\mid d}}\frac{\lambda_d}{d}\right)^2\ge0.
\]
又 \(0<b<1\) 时，交错级数 \(\sum_{k\ge1}(-1)^{k-1}k^{-b}>0\)，而 \(1-2^{1-b}<0\)，故 \(\zeta(b)<0\)。结论对任意非负高度权积分后仍成立。取子集 \(vw\le U\) 会破坏上述平方分解。

**其余两个极点。** 取标准对称的辅助整函数 \(G(z)\)，满足 \(G(0)=1,\ G(-z)=G(z)\)，竖线上充分衰减。对固定 \(d,e\)，抽掉共同因子 \(\lambda_d\lambda_e/(g^{1+r}h_t(\sigma))\) 后，两项 Mellin 对角被积函数为
\[
 \frac{G(z)}{z}h_t(\sigma+z)(vw)^{-1-r-z}\zeta(1+r+2z),
 \qquad
 \frac{G(z)}{z}h_t(1-\sigma+z)(vw)^{-1-z}\zeta(1-r+2z).
\]
第一项在 \(-r/2\)，第二项在 \(+r/2\) 的留数之和为零。两处的 \(h_t\) 都取在 \(1/2\)，幂因子都是 \((vw)^{-1-r/2}\)，两个 zeta 因子均贡献导数比例 \(1/2\)，\(G(z)/z\) 在两点互为相反数。这个抵消发生在每一对 \(d,e\) 上。两个 \(z=0\) 留数一般不会抵消。上述计算仅使用显示的亚纯函数的局部留数，未评估其移线积分或全近似函数方程中的其他项。

## 2. 互素因子积的尾和

取尖截断权 \(\lambda_d=\mu(d)\)（\(d\le X\)）。对 \(U\ge1\) 和 \(j\in\{0,r\}\) 定义
\[
 H_j(X,U)=\sum_{g\le X}\frac{\mu^2(g)}{g^{1+r}}
 \sum_{\substack{v,w\le X/g,\ (v,w)=1,\ (vw,g)=1\\vw>U}}
        \frac{\mu(v)\mu(w)}{(vw)^{1+j}}.
\]
于是把 \(R_1,R_2\) 中的 \(vw>U\) 对丢掉时，绝对误差之和恰为
\(\zeta(1+r)|H_r|+Q_t|\zeta(1-r)||H_0|\)。

写 \(m(y)=\sum_{n\le y}\mu(n)/n\)。取常数 \(A,B\ge0\)，使 \(1\le y\le X\) 时 \(|m(y)|\le A y^{-1/2}+B\)。当 \(X\le10^{14}\)，可取 \(A=\sqrt2,B=0\)。对任意 \(X\ge1\)，可取 \(A=\sqrt2,B=0.000312\)，因为 \(y>10^{14}\) 时有 \(|m(y)|\le0.010032/\log y\)。[Helfgott，第一卷，引理 5.10](https://webusers.imj-prg.fr/~harald.helfgott/anglais/PartI.pdf)；[Ramaré–Zuniga-Alterman，式 (9) 与推论 1.2](https://arxiv.org/html/2408.05969v2)。

对 \(s=0,\tfrac12\) 定义
\[
 f_s(q)=\prod_{p\mid q}(1-p^{s-1})^{-1},\quad
 C_s=\prod_p\left(1+\frac{f_s(p)-1}{p}\right),\quad
 E_s(r)=\prod_p\left(1+\frac{f_s(p)}{p^{1+r}}\right).
\]
两个欧拉乘积都收敛。记 \(K_r=1+\frac12\log U+(2r)^{-1}\)，\(K_0=1+\log X\)。

**引理 2.** 对上述参数，
\[
 |H_j(X,U)|\le
 4A C_{1/2} E_{1/2}(r)\,U^{-j-1/4}
        \left(2+\frac1{2j+1/2}\right)
  +4B C_0 E_0(r)\,U^{-j} K_j .
\]

**证明。** 令 \(m_q(y)=\sum_{n\le y,(n,q)=1}\mu(n)/n\)。把 \(m(y)\) 与支撑在质因子全整除 \(q\) 的正整数上的权 \(1/n\) 卷积，得到
\[
 m_q(y)=\sum_{k\mid q^\infty,\ k\le y}\frac{m(y/k)}k,\qquad
 |m_q(y)|\le A f_{1/2}(q)y^{-1/2}+B f_0(q).
\]
任何 \(Y\le X,\ 1\le D<Y\) 上，分部求和给出
\[
 \left|\sum_{\substack{D<w\le Y\\(w,q)=1}}\frac{\mu(w)}{w^{1+j}}\right|
 \le 2D^{-j}\left(A f_{1/2}(q)D^{-1/2}+B f_0(q)\right).
\]
这里用 \(m_q\) 的递减上界分别控制两个端点和积分，且
\(Y^{-j}+j\int_D^Y t^{-1-j}dt=D^{-j}\)，也适用于 \(j=0\)。

因 \(U\ge1\)，互素对中 \(v=w\) 不可能属于尾和。可取两倍的 \(v<w\) 部分。在固定 \(g,v\) 后取 \(q=gv,\ Y=X/g,\ D=\max(v,U/v)\)。当 \(D\ge Y\) 内和为空。由 \(f_s(gv)\le f_s(g)f_s(v)\)，对 \(g\) 绝对求和给出 \(E_s(r)\)。余下 \(v\) 求和的正权是
\[
 h(v)=v^{-1-j}\max(v,U/v)^{-j-s},
\]
在 \(v>0\) 上递减。\(f_s(n)=\sum_{d\mid n}\mu^2(d)\prod_{p\mid d}(f_s(p)-1)\)，所以 \(\sum_{n\le y}f_s(n)\le C_s y\)。因而 \(s>0\) 时，分部求和及在 \(\sqrt U\) 处分割积分给出
\[
 \sum_{v\ge1} f_s(v)h(v)\le C_s\int_0^\infty h(t)dt
 =C_s U^{-j-s/2}\left(\frac1s+\frac1{2j+s}\right).
\]
\(s=0,\ j=r\) 时，可用 \(C_0(h(1)+\int_1^\infty h(t)dt)=C_0 U^{-r}K_r\)。
\(s=j=0\) 时保留 \(v\le X\)，上界为 \(C_0(1+\log X)\)。对称分解和分部求和各给出因子 2，结论得证。

## 3. 在有限 RH 高度的数值例

取 \(\sigma=7/8,\ t=3\cdot10^{12},\ U=t/(2\pi)\)。对所有 \(1\le X\le10^{14}\)，引理 2 和区间算术给出
\[
 U^r |H_r|<0.29636,\qquad |H_0|<0.47417,\qquad
 U^r\left(\zeta(1+r)|H_r|+Q_t|\zeta(1-r)||H_0|\right)<0.968 .
\]
最后一个算式使用 \(Q_t\) 的实际 Gamma 函数值。在 160 位 Arb 精度下算得该上界的表达式小于 \(0.967167\)。

验证命令为本目录运行 **python -B check_tail.py**，本次运行使用 python-flint 0.9.0。脚本精确筛出 \(p\le P=10000\)。对乘积的其余部分使用 \(\log(1+y)\le y\)，并将所有 \(p>P\) 的幂函数和放大为整数和，再以从 \(P\) 至无穷的积分控制。对 \(C_s,E_s(r)\) 的对数尾部得到的上界依次为
\[
 \frac{P^{s-1}}{(1-s)(1-P^{s-1})},\qquad
 \frac{P^{-r}}{r(1-P^{s-1})}.
\]
本例给两个留数的硬截断误差设定了尺度。平滑权随 \(t\) 及 \(vw\ell^2\) 改变，不能把硬截断误差直接用作完整对角余项。要把两条引理用到零点密度，还需对实际平滑权的对角余项、\(dm\ne en\) 的非对角和以及一阶矩给出显式界，并将它们在所需高度范围内积分。该高度例未产生新的素数区间覆盖。

## 4. 非对角格点计数能给出的幂次

下面的独立引理允许 \(m,n\) 大小悬殊，也保留高度积分常见的三次衰减。取 \(1\le K\le T,\ X\ge1,\ b=2-2\sigma,\ R=\sqrt{2}X\sqrt K\)。令 \(p=dm,\ q=en\)，此处 \(p,q\) 表示一般正整数。定义
\[
 \mathcal S=\sum_{\substack{d,e\le X,\ mn\le K\\p\ne q}}
   (pq)^{-\sigma}(1+T|\log(p/q)|)^{-3}.
\]

**引理 3.** 若 \(\mathcal S_{\rm near}\) 只计 \(1/2\le p/q\le2\)，则
\[
 \mathcal S_{\rm near}\le
 \frac{(1+2\zeta(3))4^{2\sigma} R^b}{T}
 \sum_{j\ge0}2^{-jb}(1+\log8+2j\log2)^2 .
\]
其余项满足
\[
 \mathcal S-\mathcal S_{\rm near}
 \le \frac{X^b K^{1-\sigma}(1+\log K)}
        {T^3(1-\sigma)^3(\log2)^3}.
\]

**证明。** 近项满足 \(\max(p,q)\le\sqrt{2pq}\le R\)。分为 \(M/2<\max(p,q)\le M\) 的块，\(M=R2^{-j}\)。块内 \(M/4<p,q\le M\)。固定 \(m,n\)，令 \(g=(m,n)\)。非零差 \(h=md-ne\) 是 \(g\) 的倍数。每个 \(h\) 固定后，\(d\) 在模 \(n/g\) 的一个剩余类里，且 \(d\le M/m\)，故至多有 \(1+Mg/(mn)\) 个解。由 \(|\log(p/q)|\ge |h|/M\)，令 \(z=M/(Tg)\)，未带 \((pq)^{-\sigma}\) 的权重之和至多
\[
 2(1+Mg/(mn))\sum_{k\ge1}(1+k/z)^{-3}
 \le 2(1+Mg/(mn))\min(z/2,\zeta(3)z^3).
\]
右边的 \(Mg/(mn)\) 项至多 \(M^2/(Tmn)\)。若 \(M\ge T\)，常数 1 对应的项至多 \(z\le M^2/(Tmn)\)，因为 \(mn\le T\)。若 \(M<T\)，该项至多 \(2\zeta(3)z^3\le 2\zeta(3)M^2/(Tmn)\)，仍由 \(mn\le T\) 得出。这也处理了小于高度 \(T\) 的块。

令 \(A=\max(1,M/(4X))\)。有贡献的 \(m,n\) 都在 \([A,K/A]\)，故它们的倒数积之和至多
\[
  (1+\log(K/A^2))^2\le (1+\log(16X^2K/M^2))^2
  =(1+\log8+2j\log2)^2
\]
（若 \(K<A^2\)，该块为空）。乘以 \((pq)^{-\sigma}\le (4/M)^{2\sigma}\)，再求和，可得近项界。对远项使用 \(|\log(p/q)|\ge\log 2\)，以及
\(\sum_{d\le X}d^{-\sigma}\le X^{1-\sigma}/(1-\sigma)\) 和
\(\sum_{mn\le K}(mn)^{-\sigma}\le K^{1-\sigma}(1+\log K)/(1-\sigma)\)，即得第二式。

固定 \(\sigma<1\)，取 \(K=T\) 得到 \(\mathcal S\ll_\sigma X^{2-2\sigma}T^{-\sigma}\)，即 Claude 格点估计所需的幂次。调和双和在上界中保留一个平方对数，随块求和后只依赖 \(\sigma\)。在 \(\sigma=7/8\) 处，上述近项上界乘在 \(X^{1/4}K^{1/8}/T\) 前的系数约为 \(45437.82428\)（本目录脚本还把该级数按几何级数求和并验证系数小于 45438）。这一推导无法支持 Claude 预算采用的 \(\kappa_2\) 系数。真实高度积分还需要证明带有 \(t\) 导数的 Gamma 权能由此核控制，估计 \(mn>T\) 的尾部，再和对角项、一阶矩及零点计数公式相接。古典文献中的指数也须区分。Kadiri–Lumley–Ng 引用的 Ingham 1937 型零密度估计具有 \(8(1-\sigma)/3\) 的 \(T\) 指数及对数幂。不能以该引文代替本问题所需的显式均方估计。[Kadiri–Lumley–Ng，论文摘要及 §1](https://arxiv.org/abs/2101.12263)。
