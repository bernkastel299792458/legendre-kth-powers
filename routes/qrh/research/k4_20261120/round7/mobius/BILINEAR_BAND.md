# Two signed sieve indices in a reciprocal exponential

At \(z=\sqrt2X,\ \delta=1/(32\sqrt2)\) define the finite bilinear sum
\[
 S=\sum_{d,e\le z}\lambda_d\lambda_e W_\delta(\log(d/X))W_\delta(\log(e/X))
               \exp(i\kappa X^2/(de)).
\]
The coefficients are the actual finite Selberg coefficients, and \(\kappa\) is in radians. Using the verified Riemann hypothesis to height \(3\cdot10^{12}\), the full sums obey the following bounds.

| \(\log X\) | \(\log\kappa\) | \(\log T\) | \(|S|/X^2\) below |
|---:|---:|---:|---:|
| 43 | 23 | 27 | .000147589 |
| 55 | 15 | 23 | \(1.424\cdot10^{-10}\) |
| 60 | 23 | 27 | \(2.211\cdot10^{-10}\) |
| 70 | 23 | 27 | \(6.245\cdot10^{-14}\) |

The reciprocal here contains \(de\). To apply the saving directly to the physical remainder involving \([d,e]\), one would also have to impose coprimality after fixing a common divisor, replace the Gaussian by the actual cutoffs and sum across all blocks.

Write \(u=\log(d/X),v=\log(e/X)\), and \(h_\pm(w)=e^{-w^2/(8\delta^2)}\) with the additional factor \(\exp(i\kappa e^{-w})\) for \(h_+\). Then the weight and phase in \(S\) factor exactly as
\[
 W_{\sqrt2\delta}(u)W_{\sqrt2\delta}(v)h_+(u+v)h_-(u-v).
\]
Use Fourier inversion with \(\widehat h(t)=\int h(w)e^{-itw}dw\). For frequencies \(t,s\), the remaining two factors are [signed one-index sums](SELBERG_BAND.md) at twists \(-t-s,-t+s\), up to phases of modulus one. Let \(U\) bound either one divided by \(X\) for every \(|\tau|\le T\). The high-ordinate proof in the single-index method applies for \(|\Im z|\ge100\). For the low rectangle \(\sigma\le\Re z\le u_0,\ |\Im z|\le100\), the verified zero-free region shows \(1/\zeta(z)\) is holomorphic, including its zero at \(z=1\). On the left edge the program recursively encloses \(\zeta(\sigma+it)\) with complex ball arithmetic on the full interval \(0\le t\le100\) until each ball has modulus \(>1/256\). Apply conjugacy, bound the right edge by the absolutely convergent Euler product and the horizontal edges by the high-ordinate bound. The maximum modulus principle now supplies \(U\) by the same finite shift for all \(|\tau|\le T\). At all twists the integral-plus-maximum bound for the Gaussian and \(|\lambda_d|\le1\) give \(V=\sqrt{2\pi}\omega e^{\omega^2/2}+1/X,\ \omega=\sqrt2\delta\).

The Fourier mass of \(h_-\), using measure \(ds/(2\pi)\), equals one. Modulate \(h_+\) by \(e^{i\kappa w}\). Cauchy–Schwarz with weight \(1+(t/b)^2\), Plancherel and the optimal choice of \(b=\|h_+'+i\kappa h_+\|_2/\|h_+\|_2\) give the upper \(J=(\|h_+\|_2\|h_+'+i\kappa h_+\|_2)^{1/2}\) for its absolute Fourier mass. Direct Gaussian integration gives
\[
 \|h_+\|_2^2=2\sqrt\pi\delta,\qquad
 \|h_+'+i\kappa h_+\|_2^2/\|h_+\|_2^2
 =1/(8\delta^2)+\kappa^2(1-2e^{\delta^2}+e^{4\delta^2}).
\]
Set \(a=1000,\ m=16\). Outside \(|s|\le a,\ |t|\le T-a\) the joint Fourier mass is bounded by
\[
 E=J\operatorname{erfc}(\sqrt2\delta a)
 +\frac{\|h_+^{(m)}\|_2(T-a)^{1/2-m}}{\sqrt{\pi(2m-1)}} .
\]
The second term follows by integrating \(t^{-2m}\) on the two tails and using Plancherel. To bound the derivative, apply the product rule to each \(w^k e^{-jw}h_+(w)\). The derivative produces the four coefficients \(k,-j,-1/(4\delta^2),-i\kappa\) with indices \((j,k-1),(j,k),(j,k+1),(j+1,k)\). Sum the absolute coefficient bounds and compute the norm of each resulting monomial from the \(2k\)-th moment of the normal distribution of mean \(-4j\delta^2\) and variance \(2\delta^2\), with squared norm factor \(2\sqrt\pi\delta e^{4j^2\delta^2}\). This also justifies absolute Fourier inversion. The table encloses \(J U^2+E V^2\).

~~~sh
python -B round7/mobius/bilinear_band.py
~~~
