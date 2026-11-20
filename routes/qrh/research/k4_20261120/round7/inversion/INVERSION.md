# Recovering the signed lcm phase on the full sieve range

Let \(q=[d,e]\), put \(a_q=\sum_{[d,e]=q}\lambda_d\lambda_e\) and \(D(s)=\sum_q a_q q^{-s}\), with the [finite Selberg coefficients](../physical/BILINEAR.md). For \(\Re s>1\),
\[
 \zeta(s)D(s)=\sum_{m\ge1}m^{-s}\Big(\sum_{d\mid m}\lambda_d\Big)^2 .
\]
For all complex \(s\), the finite identity
\[
 D(s)=\sum_{g\le z}J_s(g)\Big(\sum_{g\mid d}\lambda_d d^{-s}\Big)^2,
 \qquad J_s(g)=\sum_{k\mid g}\mu(k)(g/k)^s
\]
follows from \(\sum_{g\mid(d,e)}J_s(g)=(d,e)^s\). These are genuine signed squares without conjugation. In particular \(D(1)=1/G(z)\) and \(D(0)=(\sum_d\lambda_d)^2\). Directly \(\sum_q|a_q|\le z^2\), and \(|a_q|\le \mu^2(q)3^{\omega(q)}\le\tau_3(q)\) because a prime of a squarefree lcm can occur on either side or both.

## Compact inversion for all large lcms

For a physical Fourier harmonic set \(A=2\pi nM>0\). Fix \(T>0,\ 0<\eta<1,\ h>0\), an integer \(m\ge2\), and put \(Q=A/(\eta T),\ U=\log Q,\ Z=2\log z\). The transition strip has width \(h\) in \(\log q\). Assume \(U+h<Z\). Convolve the indicator of \([U+h/2,Z+h/2]\) with \(m\) independent uniform densities of width \(h/m\), centered at zero, and denote the result by \(w\). Thus \(0\le w\le1,\ w=1\) on \([U+h,Z]\) and \(w=0\) outside \([U,Z+h]\). Each derivative of one uniform density is a signed measure of variation \(2m/h\), so \(\|w^{(j)}\|_\infty\le(2m/h)^j\) for \(0\le j\le m\) in the weak sense.

Set \(f(u)=w(u)\exp(iAe^{-u})\), with \(\widehat f(t)=\int f(u)e^{-itu}du\). Then
\[
 \sum_q a_qe^{iA/q}
 =\sum_{q<e^hQ}a_q(1-w(\log q))e^{iA/q}
   +\frac1{2\pi}\int_{-T}^T \widehat f(t)D(-it)\,dt+R ,
\]
\[
 |R|\le \frac{(Z+h-U)T}{\pi(m-1)}
 \left(\eta+\frac{m(1+2/h)}{T}\right)^m\sum_q|a_q|.             \tag{1}
\]
If \(Z\le U+h\) one can instead keep the entire finite sum on the small-lcm side. Thus the split applies at every \(z\). To prove (1), the modulus of the \(j\)-th derivative of \(\exp(iAe^{-u})\) is at most \(\sum_{r=0}^j {j\brace r}x^r\) with \(x=Ae^{-u}\). The coefficients follow by induction with the chain rule. The recurrence for Stirling numbers of the second kind is bounded termwise by the recurrence for the unsigned first kind since \(r\le j\) at step \(j\to j+1\). Consequently the sum is at most \(x(x+1)\cdots(x+j-1)\le (x+j)^j\). On the support \(x\le\eta T\). Leibniz's rule gives \(\|f^{(m)}\|_1\le (Z+h-U)(\eta T+m+2m/h)^m\). Integrating \(|\widehat f(t)|\le\|f^{(m)}\|_1|t|^{-m}\) proves (1), with both signs included. The same formula holds for \(|\lambda|\) in place of \(\lambda\) when a nonnegative approximation to the fractional-part error needs this second set of coefficients.

At \(L=116,\ K=H=3000175332800,\ d=\frac12\log(1+4e^{-L/4}),\ M=e^{L+d},\ y=M/K\), take \(T=H/2,\ \eta=1/2,\ h=1/10,\ m=384\). For every \(58\le\log z\le116\) and \(1\le n\le128\), (1) divided by \(y\) is \(<3.211\cdot10^{-42}\), including all large lcms. Indeed its majorant increases with \(Z\) and decreases with \(n\); \(U+h<116\) even for \(n=128\). At \(\log z=58,\ n=1\) the corresponding error is \(<2.431\cdot10^{-93}\). The finite integral still needs a signed bound for \(D(-it)\), and the complementary lcms can reach \(e^{1/10}8\pi n\,y\). The approximation estimate alone does not bound these two contributions. For example an entirely explicit universal fallback replaces the complement by \(X(1+\log X)^2\) with \(X=\min(z^2,e^h Q)\ge1\), by summing \(\tau_3(q)\). If \(X<1\) it is empty. These fallbacks do not suffice at \(L=116\).

## An unpartitioned Mellin formula

For \(1/2<a<1\), the complete unweighted signed oscillatory sum also has the absolutely convergent representation
\[
 S(A)=D(0)+\frac1{2\pi}\int_{\mathbb R}
 \Gamma(-a+it)e^{i\pi(-a+it)/2} A^{a-it}D(a-it)\,dt.             \tag{2}
\]
Apply Mellin inversion to \(\exp(-(\epsilon-i)A/q)\), move left across zero, and let \(\epsilon\downarrow0\). For \(\epsilon>0\) the vertical gamma decay dominates the complex argument. The bound below dominates uniformly for \(0<\epsilon\le1\), with an extra factor \(2^{a/2}\), justifying the limit. [Mellin inversion](https://dlmf.nist.gov/2.5)

Let \(\sigma=2-a\) and \(C_a=\sqrt{2\pi}\exp(1/(12\sigma))(1+\sigma^2)^{(\sigma-1/2)/2}\). For \(|t|\ge1\), \(|\Gamma(-a+it)|e^{\pi|t|/2}\le C_a|t|^{-a-1/2}\). In Binet's first formula the remainder for \(\log\Gamma(\sigma+it)\) has modulus at most \(1/(12\sigma)\), since the kernel \((1/(e^v-1)-1/v+1/2)/v\) lies between zero and \(1/12\). The latter also follows from the positive partial fractions for \(\coth(v/2)\). Now use \(|t|\arctan(\sigma/|t|)\le\sigma\), \(|\sigma+it|\le|t|\sqrt{1+\sigma^2}\), and lower bound each of the two recurrence denominators by \(|t|\). [Binet's formula](https://dlmf.nist.gov/5.9.E10_2)

At a cutoff \(T\ge1\), the absolute tail in (2) is at most
\[
 \frac{C_a(1+e^{-\pi T}) A^a\,T^{1/2-a}}{2\pi(a-1/2)}
 \sum_q |a_q|q^{-a}.
\]
The final mass is at most \(e\,z^{2(1-a)}(1+2\log z)^3\) for \(z>1\), by Rankin's inequality at \(1+1/(2\log z)\) and the elementary integral upper bound on \(\zeta\). For \(a=.99,\ T=H/2,\ n=1,\ \log z=58\), this resulting *upper estimate* is over \(9.2\cdot10^{13}y\). The compact formula (1) removes this loss from the large-lcm portion.

## A necessary physical bandwidth

For the current [exterior prime weight](../physical/MAIN_OBSTRUCTION.md) put \(c=L+d,\ M=e^c,\ u=K(\log p-c),\ a=(1-10^{-12})Kd,\ I=\pi\sin a/a,\ Q_0=10000\), and \(g(u)=(\cos a-\cos u)/(u^2-a^2)\). In the **linear** physical coordinate \(x=K(p/M-1)\) the prime weight, after taking out \(c/\sqrt M\), is
\[
 (1+v/c)e^{-v/2-(Q_0v)^2}g(Kv),\qquad v=\log(p/M).
\]
Consider a nonnegative continuous integrable majorant \(F(x)\) of its exterior positive part with angular Fourier support in \([-B,B]\). At \(x_\pm=K(e^{\pm d}-1)\) continuity requires \(F(x_\pm)\ge b\), where \(b=(1-d/c)e^{-d/2-(Q_0d)^2}g(Kd)>0\). This uses the continuous exterior and takes limits from outside. The zero-harmonic charge, when the entire physical integral is used in the Selberg upper bound, is exactly \(c\int F/(I G(z))\) in the normalization \(I\sqrt M/K\). Indeed the lattice spacing for multiples of \(q\) in \(x\) is \(Kq/M\); Poisson summation samples \(\widehat F\) at \(\xi=2\pi n M/(Kq)\). The signed coefficient is \(a_q/q\) times a phase, so the zero harmonic involves \(D(1)=1/G(z)\). In this setting all retained nonzero Poisson harmonics have stationary Mellin scale \(2\pi |n|M/q=K|\xi|\le KB\). This statement concerns the scale of the reciprocal phase, without asserting sharp support for its Mellin transform.

For every such nonnegative \(F\),
\[
 \int_{\mathbb R} F(x)\,dx\ \ge\
 \frac{4\pi b}{B+|\sin(BK\sinh d)|/(K\sinh d)}.                 \tag{3}
\]
Here is a proof requiring only elementary polynomial factorization. Periodize \(F\) with period \(2R\). Its Fourier coefficients vanish for \(|j|>N=\lfloor BR/\pi\rfloor\), so it agrees almost everywhere with a nonnegative trigonometric polynomial of degree at most \(N\). The polynomial dominates \(F\) everywhere since it dominates \(F\) almost everywhere and both are continuous. A nonnegative trigonometric polynomial \(P\) factors as \(|\sum_{j=0}^N b_je^{i\pi jx/R}|^2\): multiply by a monomial, pair reciprocal conjugate roots, and take half of each even-multiplicity unit-circle root, adjusting the positive constant. Its integral over one period is \(\int_{\mathbb R}F=2R\sum|b_j|^2\). The largest eigenvalue of the Gram matrix of the two evaluation vectors at \(x_\pm\) is
\[
 (N+1)+\left|\frac{\sin((N+1)\pi(x_+-x_-)/(2R))}
                         {\sin(\pi(x_+-x_-)/(2R))}\right|.
\]
The sum of their squared evaluations is at least \(2b\). Divide by that eigenvalue and let \(R\to\infty\), using \(x_+-x_-=2K\sinh d\), to obtain (3). This also covers a sum of positive majorants sharing the stated bandwidth. The denominator in (3) is nondecreasing in \(B\) by the Lipschitz bound on the sine.

At \(L=116,\ K=H\), the main charge and required bandwidth for the main charge to fall below one satisfy the following strict bounds. The final column also holds at \(K=H+16000000000\). The upper estimate \(G(z)\le\log Z_0+2+2.44/\sqrt{Z_0}\) when \(z\le Z_0\) uses monotonicity followed by the [published sieve estimate](../physical/BILINEAR.md).

| Ceiling \(\log Z_0\) | Main charge for \(KB\le H\) exceeds | Required \(KB/H\) exceeds |
|---:|---:|---:|
|58|2.3370|3.2260|
|60|2.2616|3.0867|
|65|2.0928|2.8500|
|70|1.9475|2.6861|
|116|1.1883|1.4294|

This tests continuous positive majorants charging the full zero harmonic and treating residual losses as nonnegative. Signed nonzero harmonics could reduce the charge, and methods treating frequencies above \(H\) separately are also possible. The verified lower and upper \(k=4\) endpoints are unchanged by these tests.

## A lattice diagnostic for arbitrary bandwidth

Write \(D_*=K\sinh d\). Let \(j\ge1\) be an integer, \(h_j=2D_*/j\), set \(x_i=x_-+ih_j\), and put \(\omega_j=2\pi/h_j\). Then \(x_j=x_+\). Let \(b_i\) be any lower bound for \(F(x_i)\), choosing zero for all \(0<i<j\). Suppose \(F\) is nonnegative, continuous and integrable and its zero harmonic costs at most one. For any finite index set \(S\),
\[
 \sum_{n\ge1}|\widehat F(n\omega_j)|
 \ \ge\ \frac12\left(h_j\sum_{i\in S}b_i-\frac{I G(z)}c\right).       \tag{4}
\]
To see this, periodize \(F\) with period \(h_j\). Its Fourier coefficients are \(\widehat F(n\omega_j)/h_j\). If the series in (4) is infinite the claim follows immediately. Otherwise the Fourier series is absolutely convergent and its continuous sum agrees with the periodization almost everywhere. It dominates every finite sum of translates of \(F\) at every point by continuity. Evaluate at \(x_-\) and use \(\widehat F(0)=\int F\le I G(z)/c\). This covers majorants of arbitrary bandwidth. It constrains Fourier samples of the **physical test**, without presuming that these samples occur at exactly the rational frequencies of squarefree lcms or fixing the signs in their true sum.

For \(i<0\) or \(i>j\), the code uses the positive part of the actual exterior prime weight at \(v_i=\log(1+x_i/K)\), including its Gaussian and prefactors. At \(i=0,j\) it uses \(b\) from (3). The following finite sums take \(-200j\le i\le201j\), \(L=116,\ K=H\), and the same conservative \(G\) upper as the preceding table.

| Ceiling \(\log z\) | \(j\) | First scale \(K\omega_j/H\) exceeds | Positive Fourier sample mass exceeds |
|---:|---:|---:|---:|
|58|134|275.815|\(.00001347\)|
|60|23|47.341|\(.00045297\)|
|65|7|14.408|\(.0076268\)|
|70|4|8.233|\(.020021\)|
|116|1|2.058|\(.016473\)|

For example, the mass column is the sum on the left of (4), and every sample has stationary scale at least the one displayed. These conclusions are necessary for a positive continuous majorant whose entire zero harmonic fits the target budget.

The published two-sided estimate gives \(G(z)\le\log z+1.332583+2.44/\sqrt z\) for \(z>1\). Here \(1.332583\) rounds the published value of \(c_0\) upwards. Applying it to a ceiling for \(z\) uses the monotonicity of \(G\). This is the same sieve estimate already used in the project. The present application is to the positive exterior main charge and to (4). [Ramaré, Theorems 1.3 and 3.1](https://www.impan.pl/shop/en/publication/transaction/download/product/113104)

Using this sharper constant in the existing [positive-area lower bound](../physical/MAIN_OBSTRUCTION.md) gives the following at \(L=116\). When \(K=H,\ z\le e^{58}\), the main charge alone exceeds \(1.005136\), irrespective of bandwidth. With \(z\le C\sqrt{e^{116}/K}\) it exceeds \(1.000355\) for \(K=H,\ C=2300000\), and \(1.000431\) for \(K=H+16000000000,\ C=1700000\). At the [tested larger level](../../round8/physical_low/TOP_SIGNED.md) \(K=H,\ C=3000000,\ \log z=58.549276923\ldots\), (4) with \(j=210,\ -500j\le i\le501j\) forces
\[
 \sum_{n\ge1}|\widehat F(n\omega_{210})|>.00004379,\qquad
 K\omega_{210}>432.24H .
\]
The lattice restriction and the area restriction are independent of the explicit finite-height inverse-zeta inputs in the [complete moment estimate](HARD_MOMENT.md).

~~~powershell
python -B round7/inversion/budget.py
~~~

2026-11-20. Joint project attribution to Claude and Codex. The full-range lcm inversion and two-point physical calculation are by Codex.
