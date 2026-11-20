# A sharp Möbius row in mean square on the verified frequency band

At \(Q=210,\sigma=.58,u=1.55,\kappa=6,w=e^{-22}\), the unnormalized integrals over the original \(I\) of the squared sharp prefix divided by \(Y^2\) are below .000179275, .000079080, .000035262, .000015976, .000007406 for \(\log Y\ge54,55,56,57,58\) respectively and \(\log Y\le60\).

~~~powershell
python -B round7/mobius/twisted_rms.py --q 210 --totient --fixed
~~~

For an interval \(I=[t_0,t_1]\) close to the origin or the top of the verification the same argument uses \(J=I+[-24/w,24/w]\). On the parts of \(J\) above 100 or below \(-100\), use the reciprocal mean with each part's own length and the [remote-zero bound at its actual terminal height](SHORT_SPECTRUM.md). For the intersection with \([-100,100]\), bound its length by 200, use the verified supremum 256 for the reciprocal and the positive missing-factor and totient products. The latter product sums \(1+p^{-\sigma}/((p-1)(1-p^{-\sigma}))\) multiplicatively through 1000 and exponentiates the same integral tail bound as above. This yields the wide-band applications in the coprimality calculation.

Put \(H=3000175332800,\ I=[H/8,H/4],\ D=|I|,\ Q=210\), and \(a(n)=\mu(n)(n/\varphi(n))\mathbf1_{(n,Q)=1}\). This is the numerator of the actual Selberg coefficient on \(z/11<n\le z\). The mean square below is an integral in ordinary Mellin height. It includes every twist in \(I\) with Lebesgue measure. It can be used with a finite sharp cutoff or a sharp interval.

Write \(F(s)=\sum a(n)n^{-s}\) on \(\Re s>1\). Its continuation to the verified zero-free portion of \(\Re s>1/2\) is
\[
 \frac1{\zeta(s)}
 \prod_{p\mid Q}(1-p^{-s})^{-1}
 \prod_{p\nmid Q}\frac{1-\rho(p)p^{-s}}{1-p^{-s}},
 \qquad \rho(p)=p/(p-1).
\]
The last product converges absolutely on compact subsets of this half-plane. We use the published finite-height RH verification; the [short-prime explicit formula](SHORT_SPECTRUM.md) uses a conservative height \(3\cdot10^{12}\). The calculations keep their entire rectangle strictly within that input.

## A reciprocal second moment

Use the [signed short-prime bound and its mean-value inequality](SHARP_MERTENS.md), now squared. With \(s=.58,u=1.55,\kappa=6\), the old modulus bound has the form \(C\exp(-\sum B_{p^j}\cos(jt\log p))\) with the bound \(\zeta(u)/\zeta(2u)\) on its right endpoint included in \(C\). For every \(p<e^\kappa\), replace that endpoint's elementary maximum \(1+p^{-u}\) by its phase-dependent factor \(|1-p^{-u-it}|\). Apply the sieved Euler corrections in the displayed formula at the same angles. In the squared estimate the result is the modulus squared of an absolutely convergent short-prime Euler series, times the squared constant. Its two diagonal norms are computed by integrating the Euler factors in angle at radii \(1\) and \(\sqrt p\) respectively. For the second norm the finite reciprocal geometric factors converge since \(s>1/2\). The constants \(1+p^{-u}\) remain unshifted. The \(\ell^1\) bound uses \(1+(\rho(p)-1)p^{-s}/(1-p^{-s})\) for a totient correction, \((1-p^{-s})^{-1}\) at the excluded primes, and at most one for a normalized right endpoint. For \(n_0=\lfloor e^\kappa\rfloor\), the log of the unexpanded tail is bounded by \((1+1/n_0)n_0^{-s}/(s(1-n_0^{-s}))\). The [program](prime_mean.py) encloses each angle integral and uses the earlier majorant of an interval of the specified length. Squaring and angle integration here retain correlations of all factors at the same prime.

## Taking Plancherel in the twist

Choose \(w=e^{-\ell},\ B=24/w\) and let \(J=I+[-B,B]\). Truncate \(F(s+it)\) to \(t\in J\) and extend it by zero. The normalized smoothed Perron integral in the [sharp prefix proof](SHARP_MERTENS.md) on \(I\) is its convolution with
\[
 \frac{1}{2\pi}\frac{Y^{iv}\exp(w^2(s+iv)^2/2)}{s+iv}
\]
up to reflection of the convolution variable and the factor \(Y^{s-1}\). Complete the convolution in the real variable \(v\). For \(t\in I\) its added portion comes only from \(|v|>B\), with absolute kernel integral bounded by \(e^{w^2s^2/2-(wB)^2/2}/(\pi(wB)^2)\). The original horizontal sides and the tails on the convergent line keep the explicit Gaussian bounds of the earlier proof. For these tiny terms it suffices to bound the totient product on the strip by \(\exp(2/(s(1-2^{-s})))\), and the finite missing Euler factors by their positive sums.

The inverse Fourier transform of \((s+iv)^{-1}\) is the one-sided exponential with supremum one in the angular-frequency convention above. Translation by \(\log Y+w^2s\) and convolution with the unit Gaussian do not increase this supremum. Plancherel bounds the full convolution operator on \(L^2(\mathbb R)\) by \(e^{w^2s^2/2}\). Thus its root mean square on \(I\) is at most
\[
 Y^{s-1}e^{w^2s^2/2}
 \left(D^{-1}\int_J|F(s+it)|^2dt\right)^{1/2}.
\]
This removes the logarithmic cost of integrating the absolute Perron kernel. The truncation takes place only in ordinate; no statement about the reciprocal beyond the verified rectangle is needed.

For \(a\le\log Y\le b\), in unsmoothing the prefix use the maximum of \(n/\varphi(n)\) on units through \(e^{2b}\), evaluated by the successive allowed primes. On \(n>Y^2\), use \(|a(n)|\le n\) and the Gaussian Markov bound \(e^{32w^2}(Y/n)^8\); the extra normalized sum is at most \(e^{32w^2}(Y^{-7}+Y^{-5}/6)\). On \(n\le Y^2\) use the earlier exact Gaussian indicator error. The [prefix and annulus calculation](twisted_rms.py) includes all these errors.

For the row \(\sum_{A<n\le B_1}a(n)n^{-1-it}\) take the difference of two smoothed Perron kernels. At the shifted line the Fourier transform of the sharp window is \(\int_{\log A}^{\log B_1}\exp((s-1+iv)y)dy\). Its inverse transform has supremum at most \(A^{s-1}\). The numerator difference removes the apparent pole at \(s-1+iv=0\). Each endpoint contributes its own horizontal and discarded tails. For the unsmoothing at \(Y=A,B_1\), use \(1/n\le2/Y\) above \(Y/2\). Below it, the Gaussian deviation is at least \((\log 2)/w\) and the harmonic sum is at most the coefficient maximum times \(1+\log Y\). These annulus bounds feed the [full coprimality inversion](../../round8/physical_low/COPAIR_BAND.md).
