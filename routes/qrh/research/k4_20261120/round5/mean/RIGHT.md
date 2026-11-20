# 右边界的局部算术平方和

沿用 [Euler 检测函数](../../round4/euler/PROOF.md) \(f_Q\)，令 \(Q\) 平方自由，\(q\mid Q\) 为偶数平方自由间距模数，\(p=q/2,\ d=\varphi(q)\)。写 \(U\le\log T,\ e=2\delta/\log T,\ h\in(0,1),\ Y=hT,\ X=e^WY\)，\(S_Q(v)=\sum c_n^2 n^{-v}\) 为 \(f_Q\) 的实 Dirichlet 系数平方和。下面的公式代替[折叠均方](../../round4/hilbert/FOLDED.md)中对所有 \(n/T\) 统一支付的一次项。

令 \(\lambda_k=\lambda_{\max}((c_q(i-j))_{0\le i,j<k})\)，其中 \(c_q\) 为 Ramanujan 和，\(1\le k\le p\)。令 \(L(mp+k)=mp+\lambda_k\)，\(m\ge0,1\le k\le p\)，表示连续这么多项时的 Gram 范数；特别有 \(\lambda_1=d\)。程序逐个 \(k\) 取可认证的上界，当候选达不到正定检验时采用完整周期的界 \(p\)。候选值来自浮点特征值，接受判据是 Arb Schur 正主元。维数 \(k>p-d\) 也直接用 \(p\)。

### 均方的离散余项

取 \(v=1.01,\ M=2048,\ \bar y=vM/(M-1),\ V_{\min}=ve^U,\ \epsilon_0=V_{\min}^{-1/5}<\pi/4\)，\(V\) 服从原测度 \(-dG(V)\)。从原证明得到统一乘数
\[
 C=\exp\{(1+\epsilon_0)\epsilon_0e^{2\epsilon_0^3}\}/(1-4\epsilon_0/\pi).
\]
固定 \(V\)，在 \(\log u<\log n\le\log u+w\) 的短窗上，令 \(\epsilon=V^{-1/5}, w=\epsilon^3,\ J=V(1+\epsilon)\)。折回时连续点数至多 \(\lfloor qJ/(\pi u)\rfloor+1\)，故未计统一乘数的局部均方系数至多 \(\pi uL(\lfloor qJ/(\pi u)\rfloor+1)/q\)。这一界对局部 Taylor 展开的每一项都有效。

令 \(\kappa=\pi d/q,\ a=1.03,\ \chi=qva(1+\epsilon_0)e^{\epsilon_0^3}/\pi\)。当 \(V\le vaT\) 时，若 \(z_0\le n/T\le z_1\)，借助 \(n e^{-w}\le u\le n\)，局部系数至多
\[
 \kappa n+T g,\qquad
 g=\pi z_1\{L(\lfloor\chi/z_0\rfloor+1)-d\}/q.
\]
若 \(n/T>\chi\)，上式的额外系数为零。程序可以向上取整计数来包住所接触的整数端点。对于剩余的 \(V>vaT\)，迹界给 \(L(k)\le kd\)，故局部系数至多 \(\kappa n+dJ\)。其一次项经 \(-dG\) 积分后，统一支付 \(T\tau S_Q(2+e)\)，其中 \(\tau=C(1+\epsilon_0)d\,\bar y a^{1-M}\)。常数 \(\kappa n\) 在原概率测度上总共计一次。

### 计算有限区段的真实平方系数

取 \(R=\lfloor\chi/h\rfloor+1\)，向上放宽也可，本证书要求 \(\log R\le W\)。只需处理 \(Y<n\le RY\)。对与 \(Q\) 互素的 \(n>1\)，在这一区段
\[
 c_n=-\sum_{r\mid n}\mu(n/r)\frac{(\log(n/Y)-\log r)_+}{W}.
\]
这是对互素除数的检测系数减去 \(\sum_{d\mid n}\mu(d)=0\) 后的互补除数表达。与 \(Q\) 不互素的系数消失。

展开平方。对 \(r,s\) 令 \(g_0=(r,s),\,a'=r/g_0,\,b'=s/g_0,\,D=Qa'b',\,l=[r,s]\)。因 \(r,s\) 均与 \(Q\) 互素且 \((a',b')=1\)，置 \(n=lm\) 后精确得到
\[
 {\bf1}_{(n,Q)=1}\mu(n/r)\mu(n/s)
 =\mu(a')\mu(b')\mu^2(m){\bf1}_{(m,D)=1}.
\]
平方自由互素计数在每个 \(t>0\) 满足
\[
 \left|\sum_{m\le t,\ (m,D)=1}\mu^2(m)-\beta_D t\right|
 \le(2^{\omega_0(D)}+2)\sqrt t,\qquad
 \beta_D=\zeta(2)^{-1}\prod_{\ell\mid D,\ \ell\ {\rm prime}}\ell/(\ell+1).
\]
确实，取 \(\mu^2(m)=\sum_{b^2\mid m}\mu(b)\)，对 \(b\le\sqrt t,(b,D)=1\) 的内层互素计数用容斥，累计误差至多 \(2^{\omega_0(D)}\sqrt t\)。若 \(t\ge1\)，延长主和时用 \(\sum_{b>\sqrt t}b^{-2}\le2/\sqrt t\)；对 \(t<1\) 直接使用空计数。素因子重复时该估计也有效。

按 \(n/Y\) 的整数部分切段，程序在小整数区间中另加细分。对每个 \(n/T\in(z_0,z_1]\)，设 \(t=\log(n/Y),\,t_i=\log(z_i/h)\)。在该区间，两个正部都展开的活跃对固定，商 \(T^{-1}\sum c_n^2\) 的连续主项密度为 \(F(t)/W^2\)，其中
\[
 F(t)=\sum_{r,s\le\exp(t_0),\ (rs,Q)=1}
  \frac{\mu(a')\mu(b')\beta_D}{l}(t-\log r)(t-\log s).
\]
右端为二次多项式，程序按 \(\max(r,s)\) 递增更新其三个系数。当右端恰遇新整数时，新权为零。各项的正权 \((t-\log r)(t-\log s)/W^2\) 在该区间单调递增。分部求和及上述计数误差给各对的离散误差至多
\[
 2(2^{\omega_0(D)}+2)\sqrt{\frac{z_1}{Tl}}(t_1/W)^2 .
\]
左端、右端和权的全变差已包含在因子 2 中。对交叉项取绝对值，两种顺序的互异对均计入。程序用 \(T=e^U\) 统一这一误差，记合计为 \(E\)。于是
\[
 T^{-1}\sum_{z_0T<n\le z_1T}c_n^2
 \le (z_1-z_0)\sup_{[t_0,t_1]} F/W^2+E .
\]
上确界由中点作二次 Taylor 展开逐项上计。区间边界可采用任一相邻的正部表达。对 \(e\) 的一格 \([e_l,e_u]\)，在该格用 \(T^2 n^{-2-e}\le z_0^{-2}Y^{-e}e^{-e_l t_0}\)。因此对每个频率区间将前式右侧乘 \(g\,z_0^{-2}e^{-e_lt_0}\) 并求和、乘 \(C\)，即得 \(B_l\)。程序对非负误差 \(E\) 省去不超过 1 的指数因子。

### 可直接复用的归一化

程序返回 \(H=C\kappa,\ (B_l),\ \tau\)。若已有右侧 Selberg 范数界分别为 \(S_Q(1+e)\le Y^{-e}(\log T)D_l\)，\(T S_Q(2+e)\le Y^{-e}D_2\)，那么整格的右边界常数可取
\[
 K_{3,l}=\exp(-2\delta-e_u\log h)
 \left[H D_l+\frac{e_u}{2\delta}(B_l+\tau D_2)\right].
\]
在所有格取最大即可控制整条高度半线。局部 \(B_l\) 是系数本身的带权平方和，经消除互补除数后的真实符号计算，不附加旧高范数的 \(\zeta\) 比率。时间尾上的 \(D_2\) 可取[先前的直接高范数](../../round4/density/DIRECT_HIGH.md)，其 \(\zeta(2+e_l)/\zeta(2)\le1\) 可省略。低范数 \(D_l\) 可沿用[已有的 Mellin 核验](../../round4/density/MELLIN_LOW.md)。

在 \(U=42.98,\delta=.92,W=9.5,\log h=-3.5,Q=q=210\) 时，\(H<.718379561\)，16 个格的首尾 \(B_l\) 分别小于 \(.145334263,.130943006\)，\(\tau<2.56\cdot10^{-25}\)。旧高范数常数为 \(.171071586\) 以下，还需乘原对角系数约 1.288。[局部二次型与 Gram 核验](local_energy.py)

### 大模数在高频段的应用

可取两个间距模数 \(q,q'\mid Q\) 和固定频率截点 \(Z>0\)。令 \(\chi'\) 为用 \(q'\) 替换 \(q\) 的 \(\chi\)，\(k_*=\lfloor\chi'/Z\rfloor+1\le q'/2\)，并将基准改为 \(\kappa'=\pi\overline\lambda_{k_*}(q')/q'\)，其中横线表示通过验证的上界。对 \(V\le vaT,\ n/T\ge Z\)，点数至多 \(k_*\)。由于增加点只给 Gram 算子加正半定项，全部这些频率的局部费用至多 \(\kappa' n\)。因此只需在 \(n\le hT(\lfloor Z/h\rfloor+1)\) 上求局部平方和，且仍要求 \(\log(\lfloor Z/h\rfloor+1)\le W\)。

对于其余频率，模 \(q\) 的整周期上界给每单位 \(n\) 的费用 \(P\le\pi\overline L_q(\lfloor\chi/z_0\rfloor+1)/q\)。当模 \(q'\) 的点数也在已核验的小矩阵范围内，取其单位费用与上述上界的较小值 \(P_*\)。本格额外费用至多 \(g=z_1[P_*-\kappa']_+\)；仅有一个可用上界时就用该界。此处在每一短窗对完整的同一二次型各施一次上界，然后逐索引放宽，保持卷积及 Taylor 估计。远端时间尾使用模 \(q'\) 的迹界，并在 \(\tau\) 中将 \(d\) 换成 \(\varphi(q')\)；此处 \(\kappa'\ge\pi\varphi(q')/q'\)。其余局部算术及公式 \(K_{3,l}\) 原样适用。

在同一组 \(U,\delta,W,\log h\) 上，改用 \(Q=q'=2310,\ q=210\)，取 \(Z=160\)，得到 \(H<.655793492,\ B_0<.149342343\)。取 \(Z=100\) 得 \(H<.667433367,\ B_0<.145747182\)。这些是两种针对 \(f_{2310}\) 的均方上界。[计算接口](local_energy.py)

~~~sh
python -B local_energy.py
python -B local_energy.py --modulus 2310 --spacing 210 --outer-spacing 2310 --frequency-cut 160
~~~

2026-11-20。项目共同 AI 作者为 Claude、Codex。本节的局部筛权平方和、频率分区和算术核验由 Codex 完成。
