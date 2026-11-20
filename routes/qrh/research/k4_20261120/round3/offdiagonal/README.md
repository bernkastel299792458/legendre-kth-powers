# Explicit elementary weights for the complete signed non-diagonal sum

Let \(H=3\cdot10^{12}\), \(\sigma\in[0.70,7/8]\), \(r=2\sigma-1\), \(T\ge H\) and \(X\le\min(T^{7/8},10^{14})\). Write \(I=\{|t|\ge H\}\), \(U=|t|/(2\pi)\). Use the normalized Gaussian \(W_T\) centered at \(2T\) with width \(T/10\) and the sharp Möbius mollifier from the [common-window inequality](../../round2/afe/GAUSSIAN_WINDOW.md). Define
\[
 \Phi(s)=\tfrac12\operatorname{erfc}(s/2),\qquad
 F_r(s)=(1+e^{rs})\Phi(s).
\]

**Weight replacement theorem.** In the entire non-diagonal contribution \(X^r\int_I W_T\mathcal O_X\), the sum may be replaced by the integral of
\[
 X^r \sum_{k\ne l}\frac{\cos(t\log(k/l))}{(kl)^\sigma}
   \sum_{\substack{d\mid k,\ e\mid l\\d,e\le X}}
   \mu(d)\mu(e)\,
   F_r\left(\log\frac{kl}{deU}\right).
 \tag{1}
\]
The absolute error of the replacement is less than **0.002204** over the stated range and **0.000157** for \(\sigma\ge0.85\). At \(T=H,\ \sigma=7/8,\ X=10^{10}\) it is less than **0.00001388**. The same bounds hold for any subset of terms and any choice of signs of the arithmetic coefficients, including the true ones. This reduction still requires a bound on the full signed elementary sum (1) to prove a variance estimate. The scalar checks use [Arb](check_gamma.py).

## 1. Symmetric Gamma ratios

With \(z=c+iu,\ 0\le c\le2,\ a\in[1/8,7/8]\), use the notation \(h_t\) and \(G_t\) of the [square AFE](../../round2/afe/README.md). It suffices to prove for \(t\ge H\), since the weights are even in \(t\). For \(|u|\le t/2\) and \(w_\pm=(a+z\pm it)/2\), logarithmic differentiation gives
\[
 \frac{d}{dz}\log h_t(a+z)
 =\tfrac12[\psi(w_+)+\psi(w_-)]-\log\pi .
\]
For \(\Re w>0,\ y=|\Im w|>0\), Euler–Maclaurin on the defining digamma sum through the \(B_2\) term gives
\[
 \left|\psi(w)-\log w+\frac1{2w}\right|
 \le\frac1{12y^2}+\frac16\int_0^\infty \frac{dx}{(x^2+y^2)^{3/2}}
 =\frac1{4y^2}.
\]
The first bound is the \(1/(12w^2)\) term. The remainder uses \(\sup|B_2|=1/6\) and the second derivative of \(1/(x+w)\). [Digamma expansion](https://dlmf.nist.gov/5.7#E6) · [Euler–Maclaurin formula](https://dlmf.nist.gov/2.10#E1)

The logarithm part of the symmetric pair minus \(\log U\) equals \(\tfrac12\log(1+(a+z)^2/t^2)\), on the branch continued from \(z=0\). The reciprocal parts sum to \(-(a+z)/((a+z)^2+t^2)\). Each \(|\Im w_\pm|\ge t/4\), and \(|a+z|^2/t^2\le 1/4+9/t^2<0.26\). Hence the derivative minus \(\log U\) has modulus at most
\[
 t^{-2}(|a+z|^2+2|a+z|+4)\le t^{-2}(3+|z|)^2 .
\]
Integrating along the straight segment to \(z\), and bounding the logarithm of the four factors \(1-z^2/(b\pm it)^2\) in \(G_t\) by \(6|z|^2/t^2\) in total, gives
\[
 \left|\log\left[\frac{h_t(a+z)G_t(z)}
             {h_t(a)U^ze^{z^2}}\right]\right|
 \le B,\qquad B=\frac{|z|^3+12|z|^2+9|z|}{t^2}.
\]
The logarithm is continued along that segment. The same derivative estimate for real \(a\in[1-\sigma,\sigma]\) gives \(|\log(q_t/U^{-r})|\le9r/t^2\), and in particular \(|q_t/U^{-r}-1|\le10/t^2\).

## 2. The two Mellin lines

For \(n\ge1\), Mellin inversion of \(e^{z^2}(U/n)^z/z\) on \(\Re z=2\) gives \(\Phi(\log(n/U))\). This follows by differentiating the Gaussian transform in \(\log(n/U)\) and taking the boundary value at positive infinity. In the difference with the exact \(V_{a,t}(n)\), the residue at zero cancels. Thus either \(c=0\) or \(c=2\) can be used. On the strip there are no Gamma poles, since \(a+c>0\). The Gaussian handles the horizontal limits.

In \(|u|\le t/2\), \(B\le0.01+u^2/2\). For example its numerator is at most \(|u|^3+18u^2+69|u|+74\), from \(|z|\le|u|+2\); use \(|u|^3\le tu^2/2\). By \(|e^\xi-1|\le|\xi|e^{|\xi|}\), the error integral divided by \((U/n)^c t^{-2}\) is bounded by
\[
 \frac{e^{4.01}}{2\pi}\int_{\mathbb R}e^{-u^2/2}
       (u^2+16|u|+37)\,du<1117 .
\]
At \(|u|\ge t/2\), the Gamma integral gives \(|\Gamma((a+c+iy)/2)|\le\Gamma((a+c)/2)<18\). For the last bound, on \((0,1)\) integrate \(x^{(a+c)/2-1}\) crudely and on \([1,\infty)\) use \(x^{(a+c)/2-1}\le x\). The Stirling lower bound of §3 of the square AFE, valid for all these \(a\), gives \(|h_t(a+c+iu)/(h_t(a)U^c)|<10^5t e^{2t}\). Each auxiliary polynomial has total product at most \(\exp(4(c^2+u^2)/t^2)\). After multiplication by \(e^{c^2-u^2}\) and division by \(|z|\ge|u|\), both exact and approximate tails together are bounded by \(e^{-|u|}\) pointwise. Indeed \(t\le2|u|\), \(|u|\ge1.5\cdot10^{12}\), and the Gaussian supplies at least \(0.99u^2\) in the exponent. Their integral including \(1/(2\pi)\) is \(<t^{-2}\).

Combining the two lines yields the pointwise estimate for both branches
\[
 |V_{a,t}(n)-\Phi(\log(n/U))|
 \le \frac{1300}{t^2}\min(1,(U/n)^2). \tag{2}
\]
Also \(\Phi(\log y)\le\min(1,e^4y^{-2})\), from the Gaussian exponential moment. Combining (2) with the ratio \(q_t\) gives an error for the reflected weight \(q_tV_{1-\sigma,t}(n)\) of at most \(1850\,U^{-r}t^{-2}\min(1,(U/n)^2)\). This comparison retains the coefficients of the two actual branches.

## 3. Absolute summation of all replacement errors

Write \(k=dm,\ l=en\). After extracting \((kl)^{-\sigma}\), the reflected main coefficient relative to the direct one is \((mn/U)^r\), giving precisely \(F_r\) in (1). To sum the Gamma replacement errors let
\[
 S_a(U)=\sum_{n\ge1}\tau(n)n^{-a}\min(1,(U/n)^2).
\]
For \(a=\sigma\) or \(1-\sigma\), the power \(b=1-a+1/\log U\) lies in \([0,2]\). Using \(\min(1,(U/n)^2)\le(U/n)^b\) and the integral test for \(\zeta(1+1/\log U)\) gives \(S_a(U)\le e U^{1-a}(1+\log U)^2\). The sums over \(d,e\) cost at most \(X^{2-2\sigma}/(1-\sigma)^2\). Thus the full scaled error at height \(|t|\ge H\) is bounded by
\[
 A(t,\sigma,X)=\frac{3200eX U^{1-\sigma}(1+\log U)^2}
 {(1-\sigma)^2t^2}.
\]
These summable bounds also justify termwise integration. For the elementary main terms use the same \(\min(1,(U/n)^2)\) estimate before integrating the Gaussian in height.

For \(|t|\ge T\), bound \(X\le |t|^{7/8}\). The ensuing majorant decreases in \(|t|\) because \(2/(1+\log U)<1+\sigma-7/8\). Its logarithmic derivative in \(\sigma\) is \(-\log U+2/(1-\sigma)<0\). For \(H\le |t|<T\) bound \(A\le A(H,0.70,10^{14})\), multiplied by total Gaussian mass at most \(20e^{-100}/\sqrt\pi\). At the sample one may keep \(X=10^{10}\) throughout. This proves the numbers stated above.

2026-11-20. Claude and Codex project attribution. Codex derived and numerically checked this reduction.


## Direct checks of both original Mellin integrals

At \(t=6\cdot10^{12}\), set \(n=\lfloor U/2\rfloor,\lfloor U\rfloor,\lfloor2U\rfloor\) in turn. The [direct Arb contour check](check_mellin.py) computes \(V_{a,t}(n)-\Phi(\log(n/U))\) from the four complex Gamma functions and the exact polynomial \(G_t\), independently of the formula for \(F_r\). The upper signs refer to the direct branch and the lower signs to the reflected branch before multiplication by \(q_t\). In increasing order of \(n\) the results are

| \(a\) | \(\lfloor U/2\rfloor\) | \(\lfloor U\rfloor\) | \(\lfloor2U\rfloor\) |
|---:|---:|---:|---:|
| \(7/8\) | \(-1.102684\) to \(-1.102682\) | \(-0.189778\) to \(-0.189777\) | \(0.793908\) to \(0.793911\) |
| \(1/8\) | \(-0.751780\) to \(-0.751777\) | \(0.104070\) to \(0.104073\) | \(0.964185\) to \(0.964188\) |

All entries are in units of \(10^{-26}\). On the Mellin line \(z=1+iu\), conjugation reduces the integral to the real part for \(u\ge0\), with factor \(1/\pi\). Use 60 panels of length \(1/4\) on \([0,15]\), each with the 32-point Gauss–Legendre formula. On the complex \(u\)-disc of radius \(1/2\) about each midpoint, \(1/2\le\Re z\le3/2,\ |\Im z|<16\), and \(B<0.01\) in (2)'s proof. Hence the absolute integrand before \(1/\pi\) is bounded by \(200\), using \((U/n)^{\Re z}\le3^{3/2}, |z|^{-1}\le2, |e^{z^2}|\le e^{9/4}\). The Taylor remainder through degree 63 and positivity of the quadrature weights give total numerical-integration error at most \(30\cdot200(1/4)^{64}/[(1-1/4)\pi]\). For \(15\le u\le t/2\), \(B\le0.01+u^2/2\), so the normalized tail is \(<10e^{-15^2/2}\). Beyond \(t/2\), the preceding large-height bound gives a further \(e^{-t/2}\), since \(U/(\pi n)<1\) in all three cases. The script checks the arithmetic at 224-bit precision.
