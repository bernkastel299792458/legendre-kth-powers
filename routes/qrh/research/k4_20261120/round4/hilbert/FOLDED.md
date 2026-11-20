# 对数短窗内用线性频率精算整个时间区间

设 \(q=2,6,30,210\)，\(R\) 为模 \(q\) 的单位类。本节为[单位类 Hilbert 界](PROOF.md)之外的独立均方估计。将短窗宽度随时间长度缩小，可将两个端点合起来估计。

## 线性频率的时域折叠

令 \(d=\varphi(q)\)，\(p=q/2\)，令 \(v_j=(e^{2\pi i jr/q})_{r\in R}\)。所有单位剩余类都是奇数，故 \(v_{j+p}=-v_j\)，且 \(\sum_{j=0}^{p-1}v_jv_j^*=pI\)。连续 \(k\) 个向量形成的矩阵 \(\sum v_jv_j^*\) 的谱与起点无关，因为移位等价于对角酉共轭。择 \(\alpha\ge1,\ b>0\) 使对 \(1\le k\le p\) 有
\[
 \lambda_{\rm max}\left(\sum_{j=0}^{k-1}v_jv_j^*\right)
 \le \alpha(k-1)+b. \tag{1}
\]
若一段连续频点任取完整的 \(m\) 个周期及剩余 \(k\) 项，其最大特征值至多为 \(mp+\alpha(k-1)+b\)。

对 \(P_{\rm lin}(t)=\sum_{n\bmod q\in R}a_n e^{itn/u}\)，在 \([-J,J]\) 将 \(\theta=t/u\) 积分区间按 \(2\pi/q\) 折回。固定折后 \(\theta\) 时，移位点是一个长度为 \(x=qJ/(\pi u)\) 的闭区间内的整数。若有 \(mp+k\) 个，取 \(1\le k\le p\)，则 \(x\ge mp+k-1\)。其 Gram 算子范数不超过 \(\alpha x+b\)。更具体地，令 \(F_r(\theta)=\sum_{n\equiv r(q)}a_ne^{in\theta}\)，各移位求值为 \(\sum_r e^{2\pi i jr/q}F_r(\theta)\)，其平方模和用该 Gram 界；无移位时该和为零。对 \(\theta\) 积分，Parseval 给 \(\int_0^{2\pi/q}|F_r|^2=(2\pi/q)\sum_{n\equiv r(q)}|a_n|^2\)。故
\[
 \tfrac12\int_{-J}^J |P_{\rm lin}(t)|^2dt
 \le \big(\alpha J+\pi b u/q\big)\sum|a_n|^2. \tag{2}
\]
本式允许任意复系数。

## 计算 (1)

该矩阵的非零谱就是 \(k\) 阶实 Gram 矩阵 \((c_q(i-j))_{0\le i,j<k}\) 的非零谱。整数 Ramanujan 和为 \(c_q(h)=\prod_{\ell\mid q}(\ell-1\text{ 若 }\ell\mid h,\ \text{否则 }-1)\)，乘积按素因子取，这是中国剩余定理对单位类求和的直接结果。迹界、整周期界合起来给 \(\lambda_{\rm max}\le\min(kd,p)\)。在这两者都不足时，对 \((\alpha(k-1)+b)I-(c_q(i-j))\) 作正主元 Schur 消元。下列各行均以 192 位 Arb 回放。[Gram 及均方系数核验](linear_mean.py)

| 模数 | \(\alpha\) | \(b\) |
|---:|---:|---:|
| 2 | 1 | 1 |
| 6 | 1 | 2 |
| 30 | 1 | 8.405125 |
| 30 | 1.05 | 8.155125 |
| 30 | 1.082 | 8 |
| 210 | 1 | 54.691271 |
| 210 | 1.15 | 49.946683 |
| 210 | 1.274 | 48 |

## 还原对数频率

固定目标高度 \(V>(4/\pi)^5\)，使下述卷积损失满足 \(\eta<1\)。置 \(\epsilon=V^{-1/5},\ B=V^{4/5},\ w=V^{-3/5},\ J=V+B\)，将 \(\log n\) 限于 \((\log u,\log u+w]\)。写 \(D_n=\log(n/u)-(n/u-1)\)。由 \(0\le z-\log(1+z)\le z^2/2\ (z\ge0)\) 得 \(|D_n|\le D=(e^w-1)^2/2\)。在忽略公共相位后，\(n^{it}=e^{it n/u}\sum_{j\ge0}(itD_n)^j/j!\)。以系数 \(a_nD_n^j\) 代入 (2)，再用 \(L^2\) 三角不等式及 \(|t|\le J\)。平方后的损失因子最多是 \(e^{2JD}\)，对整个窗口得到
\[
 \tfrac12\int_{-J}^J \left|\sum a_n n^{it}\right|^2dt
 \le e^{2JD}\sum_{u<n\le ue^w}(\alpha J+\pi b n/q)|a_n|^2 .
\]
其中用了 \(u\le n\)。对 \(\log u\) 积分并除以 \(w\)。[滑动窗卷积](../../round3/spectrum/PROOF.md)给损失 \(1/(1-\eta)\)，其中 \(\eta=4/(\pi wB)=4\epsilon/\pi\)。对全部实系数取半区间，得到
\[
 \int_0^V |P(t)|^2dt
 \le C(\epsilon)\sum\left[(1+\epsilon)\alpha V+\frac{\pi b}q n\right]|a_n|^2,\qquad
 C(\epsilon)=\frac{\exp\{(1+\epsilon)\epsilon e^{2\epsilon^3}\}}{1-4\epsilon/\pi}.
\]
此处 \(2JD\le V(1+\epsilon)w^2 e^{2w}=(1+\epsilon)\epsilon e^{2\epsilon^3}\)。先取有限和，再按截断极限处理绝对收敛且两范数有限的级数。

若所有求积高度 \(V\ge V_{\min}=vT_0\)，右侧系数以 \(\epsilon_0=V_{\min}^{-1/5}<\pi/4\) 统一。对均值为 \(\bar yT\) 的概率测度 \(-dG(V)\) 积分，两个系数就是 \(C_D=(1+\epsilon_0)\alpha C(\epsilon_0)\bar y,\ C_H=\pi b C(\epsilon_0)/q\)，分别乘 \(T\sum |a_n|^2,\sum n|a_n|^2\)。函数 \(\texttt{linear_mean_coefficients(q,v*T0,ybar,mode)}\) 返回这一对。每个插值边界可独立选择模数和模式。对于给定模数，表中出现的模式按顺序为 \(\texttt{unit},\texttt{middle},\texttt{density}\)。

~~~sh
python -B linear_mean.py
~~~

2026-11-20。项目共同 AI 作者为 Claude、Codex。本节折叠均方、Ramanujan Gram 证书及短窗误差核验由 Codex 完成。
