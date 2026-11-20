# 完整剥离小欧拉因子的零点检测

设 \(L=\log x\)，目标为 \(x<p<x+4x^{3/4}\)。本段沿用[频谱证明](../../round3/spectrum/PROOF.md)的 QRH(7/8)、有限高度 RH、Gabriel 插值、显式公式、Möbius 和界及检测多项式常数。新增输入是[小素数欧拉因子的四阶矩推导](../density/SIEVED.md)。这里的结论为条件解析研究稿，标量采用 192 位 Arb 检查。

## 同一个检测函数的两个边界

取平方自由 \(Q\)，其素因子选自 \(2,3,5,7,11\)。在每个固定高度 \(T\) 冻结 \(V=\log T,\ e=2\delta/V,\ Y=hT,\ X=e^WY\) 和[对数梯形权](../../round2/right/PROOF.md) \(\omega\)。定义
\[
 E_Q(z)=\prod_{p\mid Q}(1-p^{-z}),\qquad C_Q(z)=\sum_{(d,Q)=1}\mu(d)\omega(d)d^{-z},
 \qquad f_Q(z)=\zeta(z)E_Q(z)C_Q(z)-1 .
\]
在 \(\Re z>1\)，\(\zeta E_Q\) 就是对与 \(Q\) 互素的正整数求和。因此 \(f_Q\) 在 \((n,Q)=1\) 上的系数恰等于原检测函数 \(f=\zeta M-1\) 的系数，在其他整数处为零。其常数系数及所有 \(n\le Y\) 的系数为零。若 \(\zeta(\rho)=0\)，则 \(1+f_Q(\rho)=0\)，保留零点重数。原来两个正的系数平方和 \(S(1+e),S(2+e)\) 都是新范数的上界。[原范数逐格估计](../../round2/spectrum/POLE_BOUND.md)

**右边界。** 取 \(m\mid Q\)，将级数依模 \(m\) 的 \(\varphi(m)\) 个单位类分组。每类在局部区间 \(b<\log n\le b+w\) 的最小间距至少为 \(m e^{-b-w}\)。沿用局部 Montgomery–Vaughan 不等式，再以 Cauchy 合并各类，加权二阶矩的两个系数成为
\[
 C_D\varphi(m)T,\qquad C_H\,\varphi(m)/m,\quad
 C_D=(\bar y+B/T_0)/(1-\eta),\quad C_H=\pi e^w/(1-\eta).
\]
它们依次乘与 \(Q\) 互素时的 \(S_Q(2+e)\)、\(S_Q(1+e)\)。这里 \(w=.001,\ B=10^9,\ \eta=4/(\pi wB),\ T_0=e^{U_0}\)，权为 \(G(t)=\min(1,(vT/t)^M),\ M=2048,\ v=1.01,\ \bar y=vM/(M-1)\)。对新系数按原公式调用 \(\texttt{sharp_right}\) 给出对全体 \(T\ge T_0\) 的统一常数。它多计的 \(C_H\varphi(m)/(2mT_0)\) 对角系数为正。

可另外用一个连续时间权处理相同的两项。取 \(0<\alpha<\pi\)，对 \(V'>0\) 用 \(\operatorname{sinc}^2(\alpha t/(2V'))/\operatorname{sinc}^2(\alpha/2)\) 盖住 \([-V',V']\)，其中 \(\operatorname{sinc}(u)=\sin(u)/u\)。变换为三角权。写 \(\rho_m=\varphi(m)/m\)，\(D_m\) 为任意区间单位整数个数减去 \(\rho_m\) 乘区间长度的上界。删去整周期后，剩余区间可紧缩到首末单位整数，故程序枚举一个周期内所有首末位置，允许跨周期。若 \(w'=\alpha/V'\)，三角权在固定 \(n\) 的行和满足
\[
 \int_0^1\#\{j:(j,m)=1,\ ne^{-w'u}<j<ne^{w'u}\}\,du
 \le D_m+\rho_m n w'e^{w'} .
\]
由 \(2|a_na_j|\le |a_n|^2+|a_j|^2\)，时间反射对称，以及 \(-dG(V')\) 支撑于 \(V'\ge vT\)，得到另一个全高度可选的系数对
\[
 \pi D_m\bar y T/(\alpha\operatorname{sinc}^2(\alpha/2)),\qquad
 \pi\rho_m e^{\alpha/(vT_0)}/\operatorname{sinc}^2(\alpha/2).
\]
下述模 6 的基本证书使用前一种估计。

**临界线。** 取 \(A=6\) 若 \(6\mid Q\)，否则在 \(2\mid Q\) 时取 \(A=2\)。将 \(E_A\) 并入 \(\zeta\) 使用相应的四阶矩。剩余多项式 \(E_{Q/A}C_Q\) 的每个索引都唯一写成 \(rd,\ r\mid Q/A,\ (d,Q)=1\)，且为奇数。其调和平方和与无权平方和分别是 \(C_Q\) 的同类和的 \(\prod_{p\mid Q/A}(1+1/p)\) 倍及 \(2^{\omega_0(Q/A)}\) 倍，\(\omega_0(u)\) 表示不同素因子的个数。应用上述单个奇剩余类的均方，Hilbert 项的系数为 \(C_H/2\)。

为界定 \(C_Q\) 的两项，对 \(p\le11\) 的五个素数，若 \(p\mid Q\) 则排除 \(p\mid d\)，否则排除 \(p^2\mid d\)。五个除数的所有子集乘积 \(j\) 有符号 \(\epsilon_j=(-1)^{|S|}\)。令 \(b=\sum\epsilon_j/j,\ c=\sum(\max(\epsilon_j,0)-\epsilon_j\log j)/j\)。容斥、\(\log t\le H_{\lfloor t\rfloor}\le1+\log t\) 及对 \(-d\omega^2\) 分部求和给出调和和除以 \(V\) 的上界
\[
 b+\max(0,b(\log h+W/3)+c)/U_0 .
\]
这里 \(Y_0=hT_0>\max j\)。所有 \(t\ge0\) 的无权累计数至多 \(bt+\#\{j:\epsilon_j<0\}\)。因此无权和除以 \(T\) 的上界为
\[
 2b h e^W[1-(1+W)e^{-W}]/W^2+\#\{j:\epsilon_j<0\}/T_0 .
\]
将两项代回原来的 Hölder 及平顶时间权估计，给出新 \(K_1\)。

**方差扣项。** 还可用[方差计算](../density/variance.py)加强右边界。记 \(b_v(j)=\sum_n\mu(n)n^{-v}(1-\omega(jn))\)，\(Z=\prod_{p\mid Q}(1-p^{-v})^{-1}\)，\(\zeta_Q=\zeta/Z\)。在与 \(Q\) 互素的整数中应用原 Selberg 分解，再将 \(\mu 1_{(\cdot,Q)=1}\) 写成 \(\mu\) 与仅含 \(Q\) 素因子的整数指标的卷积，得到
\[
 S_Q(v)\le\zeta_Q(v)\sum_{(j,Q)=1}j^{-v}
       \left(\sum_{k\mid Q^\infty} k^{-v}b_v(jk)\right)^2 .
\]
由加权方差恒等式，原来的 Selberg 上界至少比这一上界多出
\[
 \zeta_Q(v)\sum_{(j,Q)=1}j^{-v}\!
 \sum_{\substack{k<l\\k,l\mid Q^\infty}}(kl)^{-v}
                [b_v(jk)-b_v(jl)]^2 .
\]
对 \(v=2+e\) 限制 \(k,l\le96,\ r=\log(jk/Y)\in[0,4],\ r+\log(l/k)\le W\)。沿用[余项界](../../round2/right/fine/PROOF.md) \(|R_v(t)|\le1.2 e^{-(v-1)t}\)。两个过渡段的差乘 \(W\) 后，绝对值至少为
\[
 [\,\log(l/k)/\zeta(2)-1.2(1+l/k)e^{r-W}\,]_+ .
\]
在宽 \(1/16\) 的 \(r\) 格上对 \((j,Q)=1\) 作容斥下计，两端取整损失合计每格至多 \(2^{\omega_0(Q)}\)。将 \(T\) 乘入并提出 \(Y^{-e}\)，剩余量至少为程序的 \(\Delta_Q=\texttt{high_saving}\)。若原有无折扣高范数界为 \(A_2\)，其格内实际使用值为 \(\{\zeta(2+l_0)/\zeta(2)\}A_2\)，其中 \(l_0\) 为 \(e\) 格的左端。括号内系数至多 1，因此以 \(1-\Delta_Q/A_2\) 缩小对角项的系数有效。这样可以直接复用原标量程序。

## 从边界到相邻四次幂

在 \(\Re z=2\)，系数消失至 \(Y\) 且其余系数绝对值至多 \(d(n)\)，故 \(|f_Q|\le9/\sqrt Y\)。在 Jensen 外圆上，\(E_Q C_Q\) 的各项系数模至多 1，长度至多 \(QX\)，故其模至多 \(2\sqrt{QX}\)。这样只需将外圆的 \(11\sqrt{he^W}\) 换成 \(11\sqrt{Qhe^W}\)。右竖边费用仍为 \(162/h\)。零点检测多项式、冻结高度后取矩形极限、实部弦系数及显式公式均沿用[原证明](../../round2/spectrum/PROOF.md)。

取 \(a=1/4,\ U_0=L_*/4-1.02\)，最低无量纲频率 \(1.45\)，网格 \(1/256\)，连续尾自 192 起。每个实部节点检查全部高度的矩常数和衰减条件。锚点 \(L_*\) 过线后，随 \(L\) 增大冻结该锚点的全部频谱阶梯及常数，控制到无穷远。素数在开支撑内部；对正整数 \(n\)，\(n^4+4n^3<(n+1)^4\)。

在低范数 \(S_Q(1+e)/V\) 上，另取 \(jk\le X\le jl\) 的正方差项。随 \(r=\log(X/(jk))\) 分格后，\(W(b_v(jl)-b_v(jk))=G_e(r)\)；对 \(k,l\le512\) 的指定格，有限 Möbius 和给出 \(G_0(r)\ge\min(r,.65)\)，再用 \(G_e(r)\ge e^{-er}G_0(r)\)。因此整个未折扣 Hilbert 项可至少扣除 \(\texttt{low_saving}\)。由于 \(h<1\) 及 \(Y^{-e}\ge e^{-2\delta}\)，程序在取旧总上界之后扣去 \(C_H\varphi(m)e^{-2\delta}\texttt{low_saving}/m\)（连续时间权选项使用其相应 Hilbert 系数）。[两条方差扣项证明](../density/VARIANCE.md)

在 \(Q=m=6,\ \delta=.9,\ W=9.6,\ \log h=-2.8,\ L_*=184.5\) 时，得到 \(K_1<.191933702,\ K_3<.010754941\)，总预算 **小于 \(0.998076370\)**。由此对每个 \(x\ge e^{184.5}\) 有上述开区间内的素数。下列命令重放完整半直线证书。

~~~sh
python -B verify_euler.py --anchor 184.5 --modulus 6 --spacing 6 --shift .9 --transition 9.6 --cutoff -2.8 --split-left
~~~

## 模 30 的周期均方

若使用 \(\texttt{--periodic}\)，对每个局部对数频率窗同时处理全部单位类。整数 Hilbert 矩阵在模 \(m\) 单位类上的算子范数，由有限 Hermitian 矩阵给出。模 30 中，局部换回对数频率后，无权项的系数小于 \(.984448337\)，对角项只乘 \(C_D\)。临界线多项式支撑于与 6 互素的整数，在同一证明中用模 6 的系数。同时，在 \(S_Q(2+e)\) 的八个指数格中，对与 \(Q\) 互素的 Möbius 和直接求至 768，给其余尾项加上显式界。这个直接上界和前节方差改进的上界逐点取小，低范数的方差扣项另行保留。[周期矩阵与误差](../hilbert/PROOF.md) · [高范数直接估计](../density/DIRECT_HIGH.md)

在 \(Q=m=30,\ \delta=.84,\ W=10.2,\ \log h=-3.8,\ L_*=181.5\) 时，\(K_1<.182715299,\ K_3<.011266561\)，总预算小于 **\(0.993818730\)**。因此这个锚点也覆盖整条右半直线。

~~~sh
python -B verify_euler.py --direct --periodic --anchor 181.5 --modulus 30 --spacing 30 --shift .84 --transition 10.2 --cutoff -3.8
~~~

## 模 210 的折叠均方与 Mellin 估计

在随取均方高度 \(V'\) 变化的短窗内，把对数频率近似成等距频率，并显式上界相位余项。在等距频率上，时间区间分成完整周期和一个余段。余段的二次型由模 210 的 Ramanujan 和矩阵控制。矩阵上界用实数 Schur 补逐个核验。右边界用模 210 的 density 参数，左边界在与 6 互素的索引上用 unit 参数。它们分别用于同一个 \(f_{210}\) 的两个插值边界。[折叠均方引理及适用域](../hilbert/FOLDED.md)

在 \(Q=m=210,\ \delta=.89,\ W=9.7,\ \log h=-3.8,\ L_*=178.2\) 时，仅用方差低范数、直接高范数和折叠均方，得到 \(K_1<.192429640,\ K_3<.007982473\)，总预算小于 **\(0.995625300\)**。这给出独立的 \(L\ge178.2\) 证书。

在右边界还可以把低范数中的连续能量写成 Mellin–Plancherel 积分。使用 Ramaré–Zuniga Alterman 定理 1.3 的互素 Möbius 和估计处理小索引，另用 Leong 推论 4 表 5 控制积分高度 100 以上的尾部。其余积分、离散取样与极点邻域均有显式界。对 \(e\) 的 16 个闭格分别计算低范数，和同一格中高范数的上界相加，再对所有格取最大；这次直接计算低范数时不重复扣除低方差。对可同时成立的两套整条右边界上界取小。[Mellin 推导及版本](../density/MELLIN_LOW.md) · [Ramaré–Zuniga Alterman，定理 1.3](https://arxiv.org/html/2312.05138v2#S1) · [Leong，推论 4](https://arxiv.org/abs/2405.04869)

令 \(Q=m=210,\ \delta=.92,\ W=9.5,\ \log h=-3.5,\ L_*=176\)。所有有效高度满足统一门槛 \(U_0=42.98\)。半直线程序给出 \(K_1<.201865697,\ K_3<.006281473\)，固定误差小于 \(.001148412\)，总预算 **小于 \(0.991507758\)**。冻结阶梯后的衰减检验逐实部节点通过，从而覆盖每个实数 \(x\ge e^{176}\)。

~~~sh
python -B verify_euler.py --direct --fold density --anchor 178.2 --modulus 210 --spacing 210 --shift .89 --transition 9.7 --cutoff -3.8
python -B verify_euler.py --direct --fold density --mellin --anchor 176 --modulus 210 --spacing 210 --shift .92 --transition 9.5 --cutoff -3.5
~~~

2026-11-20。项目共同 AI 作者为 Claude、Codex。本轮 QRH 欧拉因子构造、方差界、频谱核验由 Codex 完成。
