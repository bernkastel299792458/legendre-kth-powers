# The signed continuous stationary term on the complete mollifier

Use the genuine cutoffs, real coefficients $w_d=\mu(d)\Omega(d)\mathbf1_{(d,q)=1}$ and the saddle transform of [the finite negative triangle](QUARTER_NEGATIVE.md). For the **complete** remaining family of pairs the continuous model consists of using the principal Fresnel term followed by the zero Fourier mode in the periodic raw-index lattice. This defines an explicit quantity whether or not the total error is small. The true stationary replacement error and the nonconstant lattice modes have only been controlled on the finite families specified in the preceding note.

With the notation $S_{\max}=\sum_{d,e}w_dw_e/([d,e]\max(d,e)^a)$ and $S_{\min}$ defined using the minimum, the model equals
\[
 \frac{\eta}{a}(S_{\min}-S_{\max})
 \int_{t_s}^{2T} V(t)\,\mathbb E_\alpha[y^{-a}]\,dt .
\]
This follows by summing the ordered-pair formula already proved and exchanging the indices in the other triangle. The model is supported on $d>e$; the corresponding continuous difference vanishes on $d=e$. The signed arithmetic simplifies further:
\[
 S_{\min}-S_{\max}=2R-2S_{\max},
 \qquad R=\sum_d w_d d^{-a}\sum_e w_e/[d,e] .
\]
Therefore adding the two matching arithmetic $S_{\max}$ terms of [the deleted direct and reflected diagonals](QUARTER_DIAGONAL.md) leaves only $2R$ as the principal coefficient.

## A bound on the collapsed signed form

For $m\ge1$ write $M_m(x)=\sum_{n\le x,(n,m)=1}\mu(n)/n$ and $M=M_1$. As an identity of finite sums $M_m(x)=\sum_{h\mid m^\infty}M(x/h)/h$. We use $|M(x)|\le1$ at all $x>0$. For $x\ge1$, multiplying by $x$ and using $\sum_{n\le x}\mu(n)\lfloor x/n\rfloor=1$ proves the bound since the fractional parts with $n=1$ and $n\ge2$ sum to at most $\{x\}+\lfloor x\rfloor-1$. Also $|M(x)|\le1/(69\log x)$ for $x\ge96955$. [Ramaré, *Explicit estimates on several summatory functions involving the Moebius function*](https://ramare-olivier.github.io/Maths/mcom2914.pdf).

Expand $(d,e)=\sum_{k\mid(d,e)}\varphi(k)$ in the inner sum. For squarefree $k\mid d$, the remaining reciprocal Möbius sum is $\mu(k)/k$ times the log-taper average of $M_{qk}(v/k)$ on $Y\le v\le X$. Fix $B\ge96955$ and $0<\theta<a$. For $h\le Y/(Bk)$ bound $M(v/(kh))$ by $1/(69\log B)$ and for larger $h$ use the unit bound and $(Bkh/Y)^\theta$. Dropping absolute weights on $d=kl$ gives the explicit upper
\[
 |R|\le\frac{q}{\varphi(q)}\frac{\zeta_q(1+a)^2}{69\log B}
 +\zeta_q(1+a)(B/Y)^\theta
 \prod_{p\mid q}(1-p^{-1+\theta})^{-1}
 \prod_{p\nmid q}\left(1+\frac{(1-1/p)p^{-1-a+\theta}}{1-p^{-1+\theta}}\right).
\]
For the first term $\varphi(k)/k$ cancels the extra $k/\varphi(k)$ from the smooth Euler sum. In the last product set $b=1+a-\theta$. The logarithmic excess over $\zeta_q(b)$ is at most $\sum_{n\ge13}n^{-b-1+\theta}/(1-13^{-1+\theta})$, by bounding the excess in each positive Euler factor. A decreasing integral bounds this last series. Try $\log B=12,\ldots,18$ and $\theta=.26,\ldots,.48$.

At $T=e^{37}$ this gives $|R|<.018143300$. The signed finite submatrix and absolute tail in the previous note give $S_{\max}>.8883871546$; for a lower bound subtract $4(262144)^2/2^{96}$ from the upward rounded finite result before subtracting the tail. In particular $S_{\min}-S_{\max}<-1.7404877$. Taking the true positive time integral only over $K\le t\le1.01T$ proves that this continuous contribution at $\alpha_0=64,w=.75$ is below $-3.192726149\,10^{10}$. At $\alpha_0=32$ it is below $-4.515196621\,10^{10}$. The independently defined signed target for the actual non-diagonal minus this explicitly computed reference quantity is accordingly larger. This does not bound that remaining difference.

~~~powershell
python -B round8/critical/quarter_stationary_main.py
~~~

2026-11-20. Joint Claude and Codex research workspace.
