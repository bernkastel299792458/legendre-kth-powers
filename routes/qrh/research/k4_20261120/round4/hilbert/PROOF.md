# 单位剩余类上离散 Hilbert 变换的频谱

对模 \(q\) 的非空剩余类集合 \(R\)，令 \(H_R\) 为整数离散 Hilbert 变换在 \(n\bmod q\in R\) 上的压缩，矩阵对角线为零，其余元素为 \(1/(n-m)\)。下述均方界在保留筛后支撑时，对角项的系数与无筛时相同。应用对象是 [Euler 检测函数](../euler/PROOF.md)。

## 周期分块

用 \(n=q\ell+r,\ m=qj+s,\ 0\le r,s<q\) 表示索引，对 \(\ell\) 作圆周 Fourier 变换。对 \(0<\theta<2\pi\) 有
\[
 \sum_{k\in\mathbb Z}\frac{e^{ik\theta}}{k+d}
   =\frac{\pi e^{i(\pi-\theta)d}}{\sin\pi d}\quad(d\notin\mathbb Z),\qquad
 \sum_{k\ne0}\frac{e^{ik\theta}}{k}=i(\pi-\theta).
\]
第一式可由右边的第 \(k\) 个 Fourier 系数 \(1/(k+d)\) 得到，第二式同理。两式皆可按 \(L^2\) 理解。取变换的正指数约定，在对角元之外代入 \(d=(r-s)/q\)，得到矩阵乘子
\[
 \frac1q\left[i(\pi-\theta)I+\pi D(\theta)C D(\theta)^*\right],
 \quad D_{rr}=e^{i(\pi-\theta)r/q},\quad
 C_{rs}=\begin{cases}\csc(\pi(r-s)/q),&r\ne s,\\0,&r=s.\end{cases}
\]
对有限支撑输入，此有界乘子的 Fourier 系数逐项给出原卷积，因而可用 Plancherel 延拓。\(C\) 实反对称，\(iC\) 的实谱关于零对称。对 \(\theta\) 取本性上确界，可得
\[
 K_R=\|H_R\|=\frac{\pi}{q}(1+\lambda_{\max}(iC)).
\]
限制在任意有限窗口后，算子范数仍然不超过 \(K_R\)。单位类模 2 只有一类，故 \(K_2=\pi/2\)。模 6 的两类相差 4，故 \(K_6=\pi(1+2/\sqrt3)/6\)。模 30、210 分别用程序检验 \((qK/\pi-1)I-iC\) 正定，试值 \(K=.984447,.915503\)。逐一用 Arb 消去正 Schur 主元，计算保留复 Hermitian 下三角矩阵。

## 局部对数频率

设 \(u<n,m\le ue^w\)，令 \(x=\log(n/m)\)。由幂级数或 Taylor 余项，
\[
 \left|\frac1{\sqrt{nm}\log(n/m)}-\frac1{n-m}\right|
 =\frac{|2\sinh(x/2)/x-1|}{|n-m|}
 \le\frac{e^{w/2}|x|^2}{24|n-m|}
 \le\frac{e^{w/2}|n-m|}{24u^2}.
\]
设 \(D=u(e^w-1)\)。当 \(D<1\) 窗口只有至多一项。否则每行的 \(\sum_{m\ne n}|n-m|\le 2D^2\)，因为每个距离至多出现两次，且整数距离至多 \(\lfloor D\rfloor\)。行、列绝对和界给出误差算子范数
\[
 E(w)= e^{w/2}(e^w-1)^2/12.
\]
对原指数和的区间均方展开，每个端点取向量 \(b_n=\sqrt n\,a_n e^{it\log n}\)。上述压缩和误差给出单个端点二次型的模至多为 \((K_R+E(w))\sum n|a_n|^2\)。两个端点相减，故在对称区间 \([-V-B,V+B]\) 的两个端点总共取两次此界。随后按[滑动频率窗口证明](../../round3/spectrum/PROOF.md)对 \(\log u\) 积分，卷积损失为 \(\eta=4/(\pi wB)<1\)。对实系数除以 2，得到
\[
 \int_0^V\left|\sum_{n\bmod q\in R} a_n n^{it}\right|^2dt
 \le\frac{(V+B)\sum|a_n|^2+(K_R+E(w))\sum n|a_n|^2}{1-\eta}.
\]
先证有限和，绝对收敛且右侧两项有限时取截断极限。对平顶权的测度 \(-dG(V)\) 积分，即得之前记号中的 \(C_D=(\bar y+B/T_0)/(1-\eta)\) 与 \(C_H=(K_R+E(w))/(1-\eta)\)。

## 接入两个边界

右线上 \(f_Q\) 的支撑与 \(Q\) 互素，对任意 \(q\mid Q\) 可取其单位类。右侧两系数分别为 \(C_D,C_H\)。择定 \(Q\) 后仍用原来的正平方和界及其方差扣项。临界线上将 \(E_A\) 并入 \(\zeta\) 后，余下的多项式 \(E_{Q/A}C_Q\) 支撑于与 \(A\) 互素的整数，因此可在第二项中取 \(C_H(A)\)。其调和与无权范数各自的乘数仍分别为 \(\prod_{p\mid Q/A}(1+1/p)\) 与 \(2^{\omega_0(Q/A)}\)。两次应用的试值 \(A,q\) 可以不同。

用 \(w=.001,B=10^9\) 时，模 \(2,6,30,210\) 的 \(C_H\) 分别小于 \(1.570798411,1.128200084,.984448337,.915504250\)。导入函数 \(\texttt{hilbert_coefficient(modulus,w,padding)}\) 可直接获得相应 Arb 上界。[矩阵及误差核验](periodic_hilbert.py)

~~~sh
python -B periodic_hilbert.py
~~~

2026-11-20。项目共同 AI 作者为 Claude、Codex。本节的周期压缩、误差推导与区间核验由 Codex 完成。
