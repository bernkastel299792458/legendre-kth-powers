# A verified-height estimate for smoothed Möbius sums

One source of loss in the [physical-side bilinear estimate](../physical/DILATION.md) is the replacement of the two Möbius signs by arbitrary bounded coefficients. This note gives a separate estimate in which the signs are retained. It uses RH verified through \(H=3\cdot10^{12}\) and allows every higher zero to have arbitrary real part in the critical strip. The published verification suffices. The estimates below concern smooth individual polynomials; an estimate for both full Selberg coefficients over the entire Fourier range remains open. [Platt–Trudgian, Theorem 1](https://arxiv.org/pdf/2004.09765)

Let \(1/2<\sigma<u<2\), \(u>1\), \(100\le |t|\le T\le H/2\), \(a=\sigma-1/2\), \(b=u-1/2\), \(h=u-\sigma\), \(\lambda=b\log(b/a)\). Set \(D(u)=-\zeta'(u)/\zeta(u)\). Then
\[
\left|\frac1{\zeta(\sigma+it)}\right|\le
\frac{\zeta(u)}{\zeta(2u)}
\exp\left\{\frac{\lambda-h}{2}\log\frac T{2\pi}
 +\lambda D(u)+0.04(\lambda+h)+32h\,\frac{\log H+1}{H}\right\}.
\]
The same right side bounds the reciprocal throughout the horizontal segment from \(\sigma+it\) to \(u+it\). Indeed both \(\lambda\) and \(\lambda-h\) decrease as \(\sigma\) increases.

For \(w=v+it\) the real logarithmic derivative of the completed zeta product gives
\[
\Re\,\zeta'/\zeta(w)=\sum_\rho\Re(w-\rho)^{-1}-C(w),\qquad
C(w)=\Re\left(w^{-1}+(w-1)^{-1}+\tfrac12\psi(w/2)-\tfrac12\log\pi\right).
\]
Here \(|C(w)-\frac12\log(|t|/(2\pi))|<.04\) in the indicated rectangle. The two reciprocal real parts contribute at most \(3/t^2\), and replacing \(\log|w|\) by \(\log|t|\) in the half-log costs at most \(1/t^2\). Euler summation for \(\psi(z)-\log z+1/(2z)\) bounds its remainder by \(\frac12\int_0^\infty|v+z|^{-2}dv\le\pi/(2|t|)\) for \(z=w/2\). The \(1/(2z)\) term has modulus at most \(1/|t|\).

Integrate from \(\sigma\) to \(u\). For each verified zero write \(y=t-\gamma\); its contribution satisfies
\[
\tfrac12\log\frac{b^2+y^2}{a^2+y^2}\le\lambda\frac b{b^2+y^2}.
\]
Apply the chord bound for \(-\log(1-(1-a^2/b^2)v)\) on \(0\le v\le1\) at \(v=b^2/(b^2+y^2)\). At \(u>1\) all Poisson kernels of the zeros are positive, hence the verified sum is at most \(C(u+it)+D(u)\). For each unverified zero the logarithmic derivative integrand has modulus in real part at most \(8/\gamma^2\), since \(|\gamma|>H\) and \(|t|\le H/2\). Integration of the bound \(N(v)\le v\log v\) on positive ordinates, and multiplication by two for conjugates, yields the last error. Finally the Euler product gives \(|1/\zeta(u+it)|\le\zeta(u)/\zeta(2u)\). For related estimates on the line \(v=1\), see [Chirre](https://doi.org/10.1017/S0004972723001338).

Take \(\delta=.1\), \(B=1000\), \(1100\le|\tau|\le H/2-B\), and define
\[
Q(X,\tau)=\sum_{n\ge1}\mu(n)n^{-i\tau}
      \exp\big(-(\log(n/X))^2/(2\delta^2)\big).
\]
Its Mellin representation on \(\Re s=u>1\) has integrand \(\sqrt{2\pi}\delta X^s e^{\delta^2s^2/2}/\zeta(s+i\tau)\). Move just the part \(|\Im s|\le B\) to \(\Re s=\sigma\). There are no poles inside by the verified height. If \(C\) denotes the reciprocal bound with \(T=|\tau|+B\), the new vertical integral is at most \(C X^\sigma e^{\delta^2\sigma^2/2}\). The two horizontal segments cost at most \(2\delta h C X^u e^{\delta^2(u^2-B^2)/2}\). The two tails on the original line have total cost at most \(\zeta(u)X^u e^{\delta^2u^2/2}\operatorname{erfc}(\delta B/\sqrt2)/\zeta(2u)\). These estimates incorporate the inverse-Mellin factor \(1/(2\pi)\).

For \((\log X,\log|\tau|)=(43,26),(55,15),(60,10)\) the normalized bounds \(|Q|/X\) are respectively below \(0.050124,0.000047545,0.00000060746\). The admissible parameters and full error estimates are recomputed by **python -B round7/mobius/finite_inverse.py**. The scale dependence matters when \(nt/(DF)\) varies over a physical-sieve Fourier block; the strongest row alone cannot be applied to every frequency.
