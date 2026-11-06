# k=6：用梯形权改善临界中段

日期：2026-11-06。状态：解析候选引理及浮点筛选，**不是全范围证书**。

现有CSv2、beta型M=2权在L=175给出约1.153的归一化扣除。本次保留相同零点输入，仅将权换成两个均匀密度的卷积。固定a=1/32的梯形权在L∈[167,200]的加密采样及平台接触点上，将候选最大值降至约0.91。代码与数据分别为`code/k6_kernel_explore.py`和`results/k6_kernel_trapezoid.{csv,json}`。

## 1. 权函数及精确常数

取0<a≤1/2，b=1−a，定义

\[
\phi=\frac{\mathbf1_{[0,a]}}a*\frac{\mathbf1_{[0,b]}}b.
\]

于是phi在[0,1]之外为零，在三个内部区间上为

\[
\phi(v)=
\begin{cases}
v/(ab),&0\le v\le a,\\
1/b,&a\le v\le b,\\
(1-v)/(ab),&b\le v\le1.
\end{cases}
\]

它是非负连续函数、绝对连续、质量I=1，且max(phi)=1/b。导数为分段常数，故

\[
\|\phi'\|_1=\frac2b,\qquad
d\phi'=\frac{\delta_0-\delta_a-\delta_b+\delta_1}{ab},\qquad
\operatorname{TV}(d\phi')=\frac4{ab}.
\]

a=b时两个中间原子重合，变差仍为4/(ab)。端点0、1处的跳跃均已计入。

对于x>1、h=kx^(1−1/k)、Y=x+h、F(t)=phi((t−x)/h)，记q=Y/h，则逐零点Mellin界为

\[
\frac1h\left|\int_x^Y F(t)t^{\rho-1}\,dt\right|
\le x^{\beta-1}
g_q(|\gamma|),\quad
g_q(T)=\min\left\{1,\frac2b\frac qT,
\frac4{ab}\left(\frac qT\right)^2\right\}.\tag{1}
\]

零次界用非负性及质量；一次分部积分用F端点为零、F'可积；二次用有界变差测度dF'。分母模长分别至少为|gamma|及|gamma|²，在支撑上t^(beta+j−1)≤x^(beta−1)Y^j。因而(1)不需要把phi假装成C1函数。

固定a=1/32、b=31/32时，全部常数为精确有理数：

\[
R_0=1,\quad R_1=\frac{64}{31},\quad
R_2=\frac{4096}{31},\quad\frac{\max\phi}{I}=\frac{32}{31}.
\]

g的三个活跃区间由T/q=R1及T/q=R2/R1=64划分。

## 2. 非光滑权的显式公式：四个点即可推出

无需以不光滑函数直接测试分布。设

\[
\Psi_1(t)=\sum_{m\ge1}\Lambda(m)(t-m)_+.
\]

逐个整数m核对梯形分段表达式，即得精确有限差分恒等式

\[
\sum_m\Lambda(m)F(m)=
\frac{\Psi_1(x)-\Psi_1(x+ah)-\Psi_1(x+bh)+\Psi_1(Y)}{ab h}.\tag{2}
\]

每个Psi1值的求和本身有限。(2)也就是对测度

\[
dF'=\frac{\delta_x-\delta_{x+ah}-\delta_{x+bh}+\delta_Y}{ab h}
\]

积分Psi1。将项目已有的积分显式公式代入这四个点：

\[
\Psi_1(t)=\frac{t^2}{2}
-\sum_\rho\frac{t^{\rho+1}}{\rho(\rho+1)}
-t\log(2\pi)+C
-\sum_{j\ge1}\frac{t^{1-2j}}{2j(2j-1)}.
\]

在固定紧区间[x,Y]上，非平凡零点级数由sum|gamma|^(−2)<∞绝对一致收敛，平凡零点级数也绝对一致收敛。因此与四点线性组合交换求和合法。仿射项消失；主项给出h；对每个光滑单项两次Stieltjes分部积分，得到

\[
\sum_m\Lambda(m)F(m)
=h-\sum_\rho\int_x^YF(t)t^{\rho-1}\,dt
-\int_x^Y\frac{F(t)}{t(t^2-1)}\,dt.\tag{3}
\]

(1)的二次衰减也保证(3)中的变换后零点和绝对收敛。因此有限差分推导没有使用对条件收敛未平滑级数的微分，也没有遗漏端点原子。

## 3. 密度积分和后续认证要求

将(1)代入已有正高度累计零点和及Stieltjes分部积分，原CSv2平滑模型继续适用。有限高度RH输入使T≤H=3·10^12的非临界线密度为零；T>H使用[CSv2 Corollary 1、Table 1](https://arxiv.org/html/2507.15184v2)。探索脚本复用`smooth_scan.cumulative_terms`，并未改变其上游输入。

主要贡献由线性衰减段产生。与beta型M2权的R1=15/4相比，新R1=64/31明显更小，核更早开始衰减；付出的二次尾部变差常数仍可控制。这次改善不依赖新增零点猜想或相消假设。

固定闭单元L∈[u,v]时，先对每个零点使用

\[
e^{(\beta-1)L}g_{q(L)}(T)
\le e^{(\beta-1)u}g_{q(v)}(T),\qquad
q(L)=1+e^{L/6}/6,
\]

再进行正Stieltjes积分，即可沿用现有连续单元认证逻辑。需要重新处理核平台起点位于H以下的情况，不能沿用四次幂证书中“全部高度大于H”的断言。

认证可在H处分段：T≤H处用有限RH给出A_u(T)=e^(−u/2)N(T)≤e^(−u/2)N(H)；T≥H处用密度上和。H以下整体基底也可用N(H)≤H log H保守覆盖，避免另依赖低高度简化计数界。

若高度尾部从log T=U进入二次段，并使用N(T)≤T log T及QRH，则

\[
2\int_U^\infty A_u(e^w)(-dg_{q(v)}(e^w))
\le4R_2q(v)^2e^{-u/8-U}(U+1).\tag{4}
\]

这是Stieltjes积分尾部，含低零点的剩余核权重。探索程序使用其较紧的N(T)≤T log T/(2pi)版本；严格认证如用(4)应重新设定高度终点。

素数幂扣除的系数由15/8改为32/31：

\[
P\le\frac{32}{31}\frac{\sqrt Y\log^2Y}{2h\log2}.
\]

平凡零点扣除仍≤1/(x³−x)。若严格总扣除小于1，(3)保证某个素数F(p)>0。由于phi端点为零，得到开区间x<p<x+h。

## 4. 探索结果的边界

脚本扫描a∈{1/200,1/100,1/50,3/100,1/32,1/20,3/40,1/10,3/20}，并在固定a=1/32时扫描L=167至200的四分之一步长、核平台接触H的点，以及225、250、275、300、350、400。全部计算仍为普通浮点。

候选峰出现在平台边缘接触H附近，其精确关系为

\[
L_H=6\log\left(6(H/R_1-1)\right).
\]

对a=1/32，此值约178.779；实际值与最坏候选delta见保存JSON。对a=1/10，稀疏采样会漏掉约0.922918的峰，因此不能只引用L=178处的0.90875。a约0.03略优于0.1，选择1/32是为了认证常数简单，不是宣称全局最优。

用48阶高度、36阶实部、半步高度积分复算接触点是数值稳定性检查，不等于Arb证书。完整覆盖必须由独立的连续区间上界、端点衔接及无限尾部共同证明。

复算命令：

```powershell
python -X utf8 code/k6_kernel_explore.py
```
