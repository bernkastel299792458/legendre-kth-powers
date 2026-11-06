# 六次幂中段的条件性连续区间证书

日期：2026-11-06。主程序为[certify_smooth_k6.py](../code/certify_smooth_k6.py)，数据为[smooth_k6_certificate.json](../results/smooth_k6_certificate.json)。

**结论。** 假定所有非平凡zeta零点满足Re(rho)≤7/8，并接受下列公开文献输入，则对所有实数

\[
e^{167}\le x\le e^{400}
\]

均存在素数

\[
x<p<x+6x^{5/6}.
\]

本模块是解析推导加Arb区间运算证书，不是Lean形式化或上游定理的独立重证。它覆盖连续中段；与整数小范围、已有无限尾部的总装另见项目的六次幂总证明。

76个闭单元无缝覆盖[167,400]。所有总扣除上界严格小于1；最坏单元为[179,180]，其保存的精确有理上界为

\[
\Delta\le
\frac{495563626579399060177723}{500000000000000000000000}
=0.991127253158798120355446<1.\tag{0}
\]

对应Arb球为`[0.9911272531587981203554453286352079656183 +/- 4.80e-41]`。本结论依赖这些向上包围的界，不能用探索脚本约0.90945的峰值替代它们。

## 1. 固定输入

1. 工作假设QRH(7/8)：每个非平凡零点rho=beta+i gamma都有beta≤7/8。
2. [Platt–Trudgian有限高度RH计算](https://arxiv.org/abs/2004.09765)：0<gamma≤H=3·10^12的零点均满足beta=1/2。
3. [Chourasiya–Simonič固定v2](https://arxiv.org/html/2507.15184v2)，Corollary 1、Table 1：对于T≥H、表中每个闭实部条带，

\[
N(\sigma,T)\le cT^{p(\sigma)}(\log T)^{p(\sigma)+2}
+d(\log T)^2+e\log T,
\quad p(\sigma)=\frac{3(1-\sigma)}{2-\sigma}.\tag{1}
\]

这里N(sigma,T)计beta≥sigma、0<gamma≤T的零点，含重数。所用条带为[i/32,(i+1)/32]，16≤i≤27：

| i | c | d | e |
|---:|---:|---:|---:|
|16|5.069|9.461|167.8|
|17|6.046|9.168|162.6|
|18|7.077|8.875|157.4|
|19|8.185|8.582|152.2|
|20|9.387|8.290|147.0|
|21|10.70|7.997|141.9|
|22|12.11|7.704|136.7|
|23|13.66|7.411|131.5|
|24|15.35|7.118|126.3|
|25|17.21|6.826|121.1|
|26|19.31|6.533|115.9|
|27|21.77|6.240|110.7|

同文式(11)在T≥H给出总正高度零点数的界

\[
N(T)\le\frac{T}{2\pi}\log\frac{T}{2\pi e}+0.43\log T
<T\log T.\tag{2}
\]

程序只使用最后的保守界，且不将其源适用域延伸到H以下。源文献的十进制常数直接进入Arb，不经二进制浮点解析。另使用经典积分显式公式，下面说明在本权函数上的交换与归约。

## 2. 梯形权与四点显式公式

固定alpha=1/32、b=31/32，令

\[
\phi=\frac{\mathbf1_{[0,\alpha]}}{\alpha}
*\frac{\mathbf1_{[0,b]}}b.
\]

这是一条非负、连续、绝对连续的梯形函数，支持在[0,1]，质量为1，在端点为零。其分段值依次为v/(alpha b)、1/b、(1−v)/(alpha b)，分界点为alpha、b。故

\[
\max\phi=\frac{32}{31},\qquad
\|\phi'\|_1=\frac{64}{31},\qquad
d\phi'=\frac{\delta_0-\delta_\alpha-\delta_b+\delta_1}{\alpha b},\qquad
\operatorname{TV}(d\phi')=\frac{4096}{31}.\tag{3}
\]

两个支撑端点的导数跳跃均已计入(3)。phi不属于C1；下面不假定它有这种正则性。

取L=log x、h=6x^(5/6)、Y=x+h、F(t)=phi((t−x)/h)。由

\[
\Psi_1(t)=\sum_{m\ge1}\Lambda(m)(t-m)_+
\]

的定义，对每个整数m直接核对梯形的三个分段，即得

\[
\sum_m\Lambda(m)F(m)
=\frac{\Psi_1(x)-\Psi_1(x+\alpha h)-\Psi_1(x+bh)+\Psi_1(Y)}{\alpha b h}.\tag{4}
\]

右侧仅是四个函数值的线性组合。将积分显式公式

\[
\Psi_1(t)=\frac{t^2}{2}
-\sum_\rho\frac{t^{\rho+1}}{\rho(\rho+1)}
-t\log(2\pi)+C
-\sum_{j\ge1}\frac{t^{1-2j}}{2j(2j-1)}
\]

代入(4)。在固定紧区间[x,Y]上，零点级数由sum|gamma|^(−2)<∞绝对一致收敛，平凡零点级数也绝对一致收敛。因此与四点线性组合交换级数合法。仿射项消失，二次主项给出h。对每个单项两次Stieltjes分部积分，或者直接计算四点差分，得到

\[
\sum_m\Lambda(m)F(m)
=h-\sum_\rho\int_x^YF(t)t^{\rho-1}\,dt
-\int_x^Y\frac{F(t)}{t(t^2-1)}\,dt.\tag{5}
\]

这里dF'=(delta_x−delta_(x+alpha h)−delta_(x+bh)+delta_Y)/(alpha b h)。该推导不对未平滑的条件收敛零点级数微分，也不需要用不光滑函数直接测试一般分布。

## 3. Mellin核包络与整个L单元的统一性

记q=Y/h=1+e^(L/6)/6、R1=64/31、R2=4096/31。分别用非负质量、一次普通分部积分、二次有界变差分部积分，有

\[
\frac1h\left|\int_x^YF(t)t^{\rho-1}\,dt\right|
\le e^{(\beta-1)L}g_q(|\gamma|),
\qquad
g_q(T)=\min\{1,R_1q/T,R_2(q/T)^2\}.\tag{6}
\]

分母模长至少为|gamma|^j，而支撑上t^(beta+j−1)≤x^(beta−1)Y^j。这也解释(3)中的导数与测度总变差怎样进入(6)。二次衰减保证(5)变换后零点和绝对收敛。

g连续非增，T≤R1 q时等于1，T≥64q时等于R2(q/T)²。固定闭单元[L_-,L_+]，令q_+=1+e^(L_+/6)/6。由于beta<1且g关于q非减，对单元内每个L、每个零点都有

\[
e^{(\beta-1)L}g_{q(L)}(|\gamma|)
\le e^{(\beta-1)L_-}g_{q_+}(|\gamma|).\tag{7}
\]

先建立逐零点共同包络，再进行Stieltjes积分。这不是对随参数变化的导数测度作未经证明的比较。

定义

\[
A(T)=\sum_{0<\gamma\le T}e^{(\beta-1)L_-}.
\]

由共轭成对及Stieltjes分部积分，全部归一化零点贡献满足

\[
Z\le2\int_0^\infty A(T)(-dg_{q_+}(T)).\tag{8}
\]

无穷边界由A(T)≤e^(−L_-/8)N(T)和二次核衰减消失；零高度之前累计数为零。平台上的测度质量为零，但较低零点仍由随后每个累计A(T)计入。

## 4. 实部积分：精确积分权重，正向包围密度

QRH和逐零点层积分给出

\[
A(T)\le e^{-L_-/2}N(T)
+L_-\int_{1/2}^{7/8}e^{(\sigma-1)L_-}N(\sigma,T)\,d\sigma.\tag{9}
\]

beta<1/2的零点由基底放大计入；beta=7/8也没有丢弃。这里不用对称扣回，避免引入额外负项。

实部网格为精确的1/2048，共768格。每一小格[s0,s1]完全落在某条源表闭区间内。由N(sigma,T)关于sigma非增，

\[
L_-\int_{s_0}^{s_1}e^{(\sigma-1)L_-}N(\sigma,T)d\sigma
\le w\,N(s_0,T),\qquad
w=e^{(s_1-1)L_-}-e^{(s_0-1)L_-}>0.\tag{10}
\]

程序对指数权重作精确的Arb表达式积分，而不是把正权也取右端矩形值。将(1)在s0代入(10)，令p_j=p(s0)、C_j=w_j c_j，并记D=sum w_j d_j、E=sum w_j e_j，则对u=log T≥log H有

\[
A(e^u)\le\Phi(u)
=e^{-L_-/2+u}u
+\sum_j C_j e^{p_j u}u^{p_j+2}+Du^2+Eu.\tag{11}
\]

所有C_j、D、E均非负。`cumulative`中以u² exp(p_j(u+log u))计算同一个主项。全程没有在表行之间猜测常数插值。

## 5. H以下与有限高度正上和

程序将平台结束点的对数向下取到1/32网格。只有这个候选网格点本身严格高于log H时，才采用它作为高段起点，并认证g=1。因此此前没有遗漏任何下降测度。

否则从log H开始作高段积分。有限RH给出T≤H时A(T)=e^(−L_-/2)N(T)≤e^(−L_-/2)H log H。于是低高度整体贡献被

\[
Z_{\rm low}\le
2e^{-L_-/2}H\log H\,[1-g_{q_+}(H)]\tag{12}
\]

包住。这里仅在T=H使用(2)，没有把其源适用域延伸到低高度。

高度网格步长为1/32。log H与第一个有理网格点之间单独构成第一格；其后均为精确有理端点。对每一格[u_i,u_(i+1)]，实际累计A(e^u)非减，故

\[
2\int_{u_i}^{u_{i+1}}A(e^u)(-dg_{q_+}(e^u))
\le2\Phi(u_{i+1})
\big[g_{q_+}(e^{u_i})-g_{q_+}(e^{u_{i+1}})\big].\tag{13}
\]

程序以Arb检查每个核质量差非负。即使某格跨过核活跃段分界，连续核端点差仍给出准确测度质量；不需要数值求积余项估计。

## 6. CS密度控制的解析无限高度尾部

令U是最后网格点，程序保证U≥log(64q_+)且U≥log H。因而在u≥U上

\[
-dg_{q_+}(e^u)=2R_2q_+^2e^{-2u}du.
\]

对(11)逐项积分。基底以及两个低次对数项的积分精确为

\[
\int_U^\infty e^{-u}u\,du=e^{-U}(U+1),
\]
\[
\int_U^\infty e^{-2u}u^2du
=e^{-2U}\left(\frac{U^2}{2}+\frac U2+\frac14\right),
\qquad
\int_U^\infty e^{-2u}u\,du
=e^{-2U}\left(\frac U2+\frac14\right).
\]

对每个主密度项，利用log(u/U)≤(u−U)/U，得到

\[
\int_U^\infty e^{-(2-p_j)u}u^{p_j+2}du
\le
\frac{e^{-(2-p_j)U}U^{p_j+2}}
{2-p_j-(p_j+2)/U},\tag{14}
\]

其中每个分母严格为正，由程序认证。于是(8)的剩余高度积分至多为

\[
\begin{aligned}
Z_{\rm tail}\le4R_2q_+^2\Bigg[&e^{-L_-/2-U}(U+1)
+\sum_j C_j\frac{e^{-(2-p_j)U}U^{p_j+2}}
{2-p_j-(p_j+2)/U}\\
&+e^{-2U}\left\{D\left(\frac{U^2}{2}+\frac U2+\frac14\right)
+E\left(\frac U2+\frac14\right)\right\}\Bigg].
\end{aligned}\tag{15}
\]

这是本次实际代码的高度尾界，使用CS密度而不是探索说明中的粗总计数尾界。(15)是Stieltjes积分的尾部，包含所有较低零点在U之后剩余的核权重；没有遗漏边界校正。高度终点由二次活跃起点与log H各加12后向上取1/32网格点确定，有限与无限高度无缝相接。

## 7. 素数幂、平凡零点及正性

初等界

\[
\psi(Y)-\theta(Y)\le\frac{\sqrt Y\log^2Y}{2\log2}
\]

可由sum_(r≥2) theta(Y^(1/r))逐项放大得到。乘max(phi)=32/31并除以h，控制(5)中所有高次素数幂的归一化贡献。单元内令epsilon=6e^(−L_-/6)，有

\[
P\le\frac{32}{31}
\frac{\sqrt{1+\epsilon}\,[L_++\log(1+\epsilon)]^2}{12\log2}
e^{-L_-/3}.\tag{16}
\]

平凡零点积分归一化后至多为

\[
V\le\frac{e^{-3L_-}}{1-e^{-2L_-}}.\tag{17}
\]

程序逐格认证

\[
\Delta=Z_{\rm low}+Z_{\rm finite}+Z_{\rm tail}+P+V<1.\tag{18}
\]

由(5)，总Lambda加权和超过全部高次素数幂能够提供的质量，因此某个素数p满足F(p)>0。权仅在开区间(x,Y)中为正，所以得到x<p<Y。取x=n^6时，Y=n^6+6n^5<(n+1)^6，得到所述整数幂应用。

## 8. 连续覆盖、复算及版本

保存运行使用160-bit Arb、实部步长1/2048、高度步长1/32。初始L网格在[167,190]用宽1、[190,220]用宽2、[220,400]用宽5。两个粗单元[177,178]、[178,179]的包围超过1，随后各自二分；所有被拒绝的粗单元也保存在JSON中。最终76个闭单元的端点以有理数存储，逐一精确衔接到167和400。

每格结果的Arb球向上取到分母10^24的有理上界。证明比较使用Arb及精确有理数，不使用浮点显示值。76格中最大上界为(0)。

从Legendre_k8目录重建或只读复核：

```powershell
python -X utf8 code/certify_smooth_k6.py
python -X utf8 code/certify_smooth_k6.py --verify
```

只读接口`verify_certificate(path=OUTPUT)`检查代码散列、源常数、核参数、精度、精确覆盖端点及相邻衔接，然后重新计算每格，要求保存上界包围复算结果且小于1。它不只读取成功标志。

本说明对应的冻结文件散列：

| 文件 | SHA256 |
|---|---|
| `code/certify_smooth_k6.py` | `9555c1ad6dfb713b84b2d9c3b28938fb353f551d8e517be200a4f8ea4e563ede` |
| `results/smooth_k6_certificate.json` | `165988b5642582864ba39bf6415c43776f45a94501a280da8692fe3ae48d69d0` |

JSON包含代码散列；重建会改变时间元数据及JSON散列。独立审阅另行记录，不以本文自身的推导替代独立复核。
