# A uniform bound for the complete hard-cutoff lcm polynomial

Let \(D(it)=\sum_{d,e\le z}\lambda_d\lambda_e[d,e]^{-it}\) for the exact [Selberg coefficients](../physical/BILINEAR.md). Use RH verified up to \(H_0=3\cdot10^{12}\). The following are upper bounds for \(|D(it)|/z^2\) on the full closed twist intervals indicated.

| \(\log z\) | \(|t|\le1\) | \(|t|\le e^{12}\) | \(|t|\le e^{20}\) | \(|t|\le e^{26}\) |
|---:|---:|---:|---:|---:|
|58|\(2.272\cdot10^{-11}\)|\(2.566\cdot10^{-10}\)|\(7.695\cdot10^{-10}\)|\(3.446\cdot10^{-9}\)|
|65|\(9.073\cdot10^{-14}\)|\(1.014\cdot10^{-12}\)|\(3.028\cdot10^{-12}\)|\(1.353\cdot10^{-11}\)|
|70|\(1.982\cdot10^{-15}\)|\(2.071\cdot10^{-14}\)|\(6.048\cdot10^{-14}\)|\(2.656\cdot10^{-13}\)|

Every lcm and every common divisor is retained. The hard cutoff at \(d,e\le z\) is included. These estimates can therefore be used on the [finite frequency integral](INVERSION.md).

## A sharp cutoff from a finite contour

Fix \(|t|\le T\) and set \(\rho(g)=g/\varphi(g)\). The [finite divisor identity](../../round8/physical_low/TOP_SIGNED.md) is algebraic for complex arguments. For squarefree \(g\), putting \(x=z/g\) gives
\[
 \sum_{g\mid d}\lambda_d d^{-it}
 =\frac{\mu(g)g^{-it}\rho(g)}{G(z)}
  \sum_{\substack{k\le x\\(k,g)=1}}\mu(k)c_t(k)k^{-it},
 \qquad c_t(k)=\prod_{p\mid k}\frac{1-p^{-1+it}}{1-1/p}.
\]
Write \(F_g(w)=\sum_{(k,g)=1}\mu(k)c_t(k)k^{-it-w}\) for \(\Re w>1\). Its continuation to a zero-free rectangle is
\[
 F_g(w)=\frac1{\zeta(w+it)}
 \prod_{p\nmid g}\frac{1-c_t(p)p^{-w-it}}{1-p^{-w-it}}
 \prod_{p\mid g}\frac1{1-p^{-w-it}}.
\]
Let \(s=.62\). Put \(m_p=2\), with the refinement \(m_p=2\sin(\min(T'\log p,\pi)/2)\) available whenever \(T'\ge T\). These bound both \(|1-p^{it}|\) and \(|1-p^{-it}|\). Set
\[
 A_p=1+\frac{m_p p^{-s}}{(p-1)(1-p^{-s})},\qquad
 E_g=\prod_{p\nmid g}A_p\prod_{p\mid g}(1-p^{-s})^{-1}.
\]
Since \(|1-c_t(p)|\le m_p/(p-1)\), the products converge absolutely on every positive real part away from the excluded finite local factors, and throughout \(\Re w\ge s\) one has \(|F_g(w)|\le E_g|\zeta(w+it)|^{-1}\). For all \(k\le z\exp(jh)\) we also have \(|c_t(k)|\le R\), where \(R\) is the product of \((p+1)/(p-1)\) over the longest initial prime segment with primorial at most \(z\exp(jh)\).

Take \(V=e^{25},\ j=32,\ h=8/V,\ u=1+1/\log z,\ T+V<H_0/2\). Average the indicator \(1_{k\le x e^{v_1+\cdots+v_j}}\) in \(0\le v_i\le h\). Its difference from \(1_{k\le x}\) is supported on \(x<k\le x e^{jh}\), and its absolute cost is bounded by \(R[1+x(e^{jh}-1)]\), including a noninteger cutoff. The averaged sum is the absolutely convergent Perron integral on \(\Re w=u\) with multiplier
\[
 x^w\, B(w),\qquad B(w)=\frac1w\left(\frac{e^{hw}-1}{hw}\right)^j .
\]
This follows by taking the Mellin transform of the averaged indicator, which is continuous at the endpoints. Move the portion \(|\Im w|\le V\) to \(\Re w=s\); the rectangle is zero-free for \(\zeta(w+it)\) by verified RH, and \(1/\zeta\) is regular at its zero at one. For \(0\le v\le V\), let \(C(v)\) be the uniform inverse-zeta bound at \(s\le\Re w\le u,\ |\Im(w+it)|\le T+v\). The program uses the [verified Poisson-power upper bound](../mobius/POISSON_POWERS.md) with \((k,m)=(245,20)\) and height \(\max(100,T+v)\). For the low rectangle it takes the maximum of that bound, the [certified low left edge](../mobius/selberg_band.py) and the Euler bound on the rightmost calibration line, by the maximum modulus principle.

Write \(b=(1+e^{hu})/h,\ \delta=b/V<1,\ v_*=\min(b,V)\). On the left line,
\[
 \frac1{2\pi}\int_{-V}^V \left|\frac{B(s+iv)}{\zeta(s+i(t+v))}\right|dv
 \le W:=
 \frac{e^{jhu}}{\pi}\sum_{[l,r]\subset[0,v_*]} C(r)
   [\operatorname{arsinh}(r/s)-\operatorname{arsinh}(l/s)]
 +\frac{C(V)}{j\pi}.
\]
The cuts are \(0,1,10,100,\ldots,v_*\), retaining only interior entries. The low integral uses the average representation of \((e^{hw}-1)/(hw)\); the rest uses \(b^j/|v|^{j+1}\). The two horizontal sides cost at most \(E_g x^u C(V)(u-s)\delta^j/(\pi V)\). Both tails of the original line together cost at most \(E_g x^u \zeta(u)\delta^j/(j\pi)\), using the absolutely convergent inverse-zeta series there. As \(x^u\le e x\), the hard cutoff sum in the first display has modulus at most
\[
 (E_g W+R)x^s+(E_g Y+R(e^{jh}-1))x,\qquad
 Y=e\delta^j\left[\frac{C(V)(u-s)}{\pi V}+\frac{\zeta(u)}{\pi j}\right].
\]

## Summing all common divisors

Write \(w_g=\prod_{p\mid g}m_p\), so that \(|J_{it}(g)|\le w_g\). For \(\ell=s,1\), let
\[
 N_\ell^2=\prod_p\left[A_p^2+
           m_p\left(\frac{\rho(p)p^{-\ell}}{1-p^{-s}}\right)^2\right],
 \qquad M_\ell^2=\prod_p[1+m_p(\rho(p)p^{-\ell})^2].
\]
These are exactly the square-sums of \(E_g\rho(g)g^{-\ell}\) and \(\rho(g)g^{-\ell}\), respectively, over all squarefree \(g\) with weight \(w_g\). Thus the [finite Jordan decomposition](INVERSION.md), triangle inequality and Minkowski applied to the preceding sum give
\[
 \frac{\sqrt{|D(it)|}}z
 \le \frac{z^{s-1}(N_s W+R M_s)+N_1Y+R(e^{jh}-1)M_1}{G(z)} .
\]
The sieve lower \(G(z)\ge\log z+1.331\) applies throughout the table. In the Euler products the code uses the individual \(m_p\) through 2000 and \(2\) afterward. For \(b>1\),
\[
 Z_b=\log\zeta(b)+\sum_{p\le2000}\log(1-p^{-b})
 \ge\sum_{p>2000}p^{-b}.
\]
With \(r=(1-1/2000)^{-1}\) and \(v=(1-2000^{-s})^{-1}\), the logarithmic tail for \(M_\ell\) is at most \(r^2 Z_{2\ell}\). For \(N_\ell\) it is at most \(2rv Z_{1+s}+v^2r^2 Z_{2\ell}\), by factoring out \(A_p\) and using \(\log(1+x)\le x\).

For a concrete transfer at \(L=116,\ n=1,\ \log z=58\), take \(T=1.4\cdot10^{12}\), so \(T+V<H_0/2\). Now \(|D(it)|/z^2<5.926\cdot10^{-9}\) for the whole integration range. For \(f=w\exp(iAe^{-u})\) of [the compact inversion](INVERSION.md), its absolute Fourier mass with measure \(dt/(2\pi)\) is at most \((\|f\|_2\|f'\|_2)^{1/2}\) by Cauchy–Schwarz with weight \(1+(t/b')^2\), optimal \(b'=\|f'\|_2/\|f\|_2\), and Plancherel. Moreover \(\|f\|_2^2\le Z+h'-U\) and \(\|f'\|_2^2\le4m/h'+(\eta T)^2/2\). Here \(h'=.1,\ m=384,\ \eta=.5\) are the lcm transition parameters. Indeed \(\|w'\|_1\le2,\ \|w'\|_\infty\le2m/h'\), while the phase and amplitude derivatives are in quadrature. Integrating \(A^2 e^{-2u}\) from \(U\) gives the last term. Thus the full large-lcm contribution has an *upper estimate* \(2.812\cdot10^{10}y\) under this uniform transfer, \(y=M/H\); its frequency truncation costs less than \(2.263\cdot10^{-93}y\). The upper estimate is too large for the physical proof. A successful transfer would need further cancellation or substantially sharper localized arithmetic control.

~~~powershell
python -B round7/inversion/hard_moment.py
~~~

2026-11-20. Joint project attribution to Claude and Codex. The complete hard-cutoff frequency estimates and their numerical integration bounds are by Codex.
