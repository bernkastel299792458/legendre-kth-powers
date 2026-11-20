# A finite-height bandlimited majorant for the reciprocal zeta function

The remote term also gives an explicit extension to \(H/2<T<H-2\). For \(|\gamma|>H,\ |t|\le T\), put \(\delta=1-T/H\). Then \(|\gamma-t|\ge\delta|\gamma|>2\); the real logarithmic derivative and complex-kernel bounds below are dominated by the same old \((24h+5C_z)/\gamma^2\) multiplied by \(\delta^{-2}\). Indeed \(|\Re((s+it-\rho)^{-1})|\le6/|\gamma-t|^2\) and \(1/(|\gamma-t|^2-1/4)\le(16/15)/|\gamma-t|^2\). The sum over both signs and all archimedean estimates are unchanged. On \(T\le H/2\) use the original sharper constant. This extension concerns frequencies inside a published verification, allowing all higher zeros throughout the critical strip.

Let \(s=1/2+a,\ u=1/2+b>1,\ 0<a<b,\ 100\le t_0\le |t|\le T\le H/2,\ H=3\cdot10^{12}\), and \(u\le6\). Write \(h=b-a\). Integrating the completed logarithmic derivative from \(s+it\) to \(u+it\) as in the [finite inverse estimate](FINITE_INVERSE.md) gives the verified-zero kernel \(\int_a^b v/(v^2+y^2)\,dv\), where \(y=t-\gamma\). Replace it on the real line by
\[
 G(w)=\int_a^b\frac{v}{v^2+w^2}\frac{\cosh(\kappa v)-\cos(\kappa w)}{\cosh(\kappa v)-1}\,dv .
\]
The multiplier is at least one on the real line. Its numerator cancels both apparent poles of the integrand. These are the classical bandlimited Poisson majorants; here zeros outside the verified region receive an explicit extra charge. [Carneiro–Chandee](https://arxiv.org/abs/1008.4970) · [Poisson kernels and the explicit formula](https://doi.org/10.1007/s00209-021-02820-9)

With transform \(\widehat G(\xi)=\int G(w)e^{-i\xi w}dw\), the transform of the integrand is zero for \(|\xi|\ge\kappa\), and equals \(\pi R(v,|\xi|)\) inside, with
\[
 R(v,\xi)=\frac{\sinh((\kappa-\xi)v)}{\cosh(\kappa v)-1},\qquad
 \widehat G(0)=\pi A,\quad A=h+\frac2\kappa\log\frac{1-e^{-\kappa b}}{1-e^{-\kappa a}} .
\]
This follows by translating the transform \(\pi e^{-v|\xi|}\) of the Poisson kernel. In particular \(|G(w)|\le G(0)=\log(b/a)=P\) on the real axis. Put
\[
 C=(b^2-a^2)/2+4P/\kappa^2,\qquad
 C_z=(b^2-a^2)/2+2(1+\cosh(\kappa/2))P/\kappa^2 .
\]
For real \(w\ne0\), \(0\le G(w)\le C/w^2\), by \(\coth^2 y=1+\sinh^{-2}y\). At \(w=x+i\theta,\ |\theta|\le1/2,\ |x|>1/2\), use \(|G(w)|\le C_z/(x^2-1/4)\). The latter uses \(|\cos(\kappa w)|\le\cosh(\kappa/2)\). For zeros above \(H\) in absolute ordinate the old integrated term costs \(24h/\gamma^2\), and the new complex kernel costs \(5C_z/\gamma^2\). The bound \(N(v)\le v\log v\) on positive ordinates yields combined error \(4(24h+5C_z)(1+\log H)/H\).

Apply the Guinand–Weil formula to \(G(t-\cdot)\); equivalently symmetrize the test under \(w\mapsto-w\) using both signs of the zeros. The pole corrections cost \(2C_z/(t_0^2-1/4)\). The arithmetic term is the actual cosine polynomial
\[
 -\sum_{p^j<e^\kappa} B_{p^j}\cos(jt\log p),\qquad
 B_{p^j}=\frac{\log p}{p^{j/2}}\int_a^b R(v,j\log p)\,dv .
\]
All \(B\) are positive. The integral is enclosed by both endpoint Riemann sums on the quadratic grid used in the code. Indeed \(R\) decreases with \(v\), since \(z\coth(zv)\) increases with \(z>0\) and \((\kappa-\xi)\coth((\kappa-\xi)v)<\kappa\coth(\kappa v/2)\). The difference-of-exponentials formula in the program is algebraically identical to \(R\).

The archimedean part of the explicit formula integrates \(\Re\psi(1/4+i y/2)-\log\pi\) with weight \(G(t-y)/(2\pi)\). Shift \(\psi\) once to \(5/4+iy/2\); the real part of the subtracted reciprocal is positive. Euler summation for \(\psi(z)\) yields
\[
 \Re\psi(1/4+iy/2)\le \log(5/4+|y|/2)+\min(.4,\pi/(2|y|)).
\]
Indeed the real part of \(-1/(2z)\) is nonpositive and the modulus of the integral remainder is at most \(\frac12\int_0^\infty |z+x|^{-2}dx\). On \(|y-t|\le |t|/2\) the last minimum is at most \(\pi/|t|\); on its complement the extra integrated mass is bounded by \(4C/|t|\). Separate \(\log(|t|/2)\), bound the shift by \(2.5/|t|+\log(1+|y-t|/|t|)\), and use \(P\) up to distance one and \(C/w^2\) thereafter. The excess over \(\frac A2\log(|t|/(2\pi))\) is at most
\[
 E_{\rm arch}=\frac{(2.5+\pi)A}{2t_0}
 +\frac{.4\,4C}{2\pi t_0}
 +\frac1\pi\left[\frac{P}{2t_0}+C\left(\log(1+t_0^{-1})+
 \frac{\log(1+t_0)}{t_0}\right)\right].
\]
The original integrated gamma correction contributes \(-\frac h2\log(|t|/(2\pi))+h\min(.04,20/t_0^2+(1+\pi/2)/(2t_0))\) as an upper bound. These inequalities give
\[
 |1/\zeta(s+it)|\le
 \frac{\zeta(u)}{\zeta(2u)}
 \exp\!\left(\frac{A-h}2\log\frac{T}{2\pi}+E_{\rm arch}
 +\frac{2C_z}{t_0^2-1/4}+\frac{4(24h+5C_z)(1+\log H)}H
 +h\min(.04,20/t_0^2+(1+\pi/2)/(2t_0))
 -\sum B_{p^j}\cos(jt\log p)\right).
\]
The unsigned version bounds \(-\cos\) by 1, and its entire right side increases as \(a\) decreases (in particular \(A-h\) does). For the paired, fixed-abscissa version, reinstate the exact Euler contribution of a small prime on the same phase arc as all its prime powers. The correction to the worst Euler factor is \(\frac12\log(1+p^{-2u}-2p^{-u}\cos\theta)-\log(1+p^{-u})\). The arc enclosures and arithmetic weights are evaluated with Arb. The only zero-location input is the published [finite verification](https://arxiv.org/abs/2004.09765).

~~~sh
python -B round7/mobius/short_spectrum.py
~~~
