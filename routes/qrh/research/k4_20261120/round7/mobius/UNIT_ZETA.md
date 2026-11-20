# A Poisson minorant for the unit zeta function on the one-line

Let \(Q=210,\ H_*=3000175332800,\ \zeta_Q(s)=\zeta(s)\prod_{p\mid Q}(1-p^{-s})\). Under the published finite-height RH verification, \(|\zeta_Q(1+it)|<2.650\) on \(H_*/8\le |t|\le H_*/4\) and \(<2.679\) on \(1\le|t|\le2.88\cdot10^{12}\). These upper bounds directly enter ordinary Mellin inversion of the actual unit multiples. The transfer uses both signs of the frequencies. [Finite-height verification](https://arxiv.org/abs/2004.09765)

For \(100\le t_0\le |t|\le T<H_*-2\) choose \(a=1/2,\ b=u-1/2,\ h=u-1\). Integrating the real logarithmic derivative from \(1+it\) to \(u+it\) expresses \(\log|\zeta(1+it)|-\log|\zeta(u+it)|\) as a gamma main term minus the sum of the verified zero kernels. In the notation of the [companion majorant](SHORT_SPECTRUM.md) use instead
\[
 G_-(w)=\int_a^b \frac{v}{v^2+w^2}\frac{\cosh(\kappa v)-\cos(\kappa w)}
                                      {\cosh(\kappa v)+1}\,dv .
\]
It is an entire minorant on the real axis. Its transform vanishes for \(|\xi|\ge\kappa\) and elsewhere equals \(\pi\int_a^b\sinh((\kappa-|\xi|)v)/(\cosh(\kappa v)+1)\,dv\), by modulation of the Poisson kernel. The area is \(\pi A\), with \(h-A=2\log[(1+e^{-\kappa a})/(1+e^{-\kappa b})]/\kappa\). The main growth of the upper logarithm is \((h-A)\log(T/(2\pi))/2\). In the explicit formula the signed prime term now has a positive cosine. For \(n=p^j<e^\kappa\) its coefficient is \(B_n=\log p\,\widehat G_-(\log n)/(\pi\sqrt n)\). To enclose the integral at each \(\xi\), multiply endpoint bounds for the decreasing \(e^{-v\xi}\) and the increasing \((1-e^{-2(\kappa-\xi)v})/(1+e^{-\kappa v})^2\).

For the convergent line take \(\log\zeta_Q(u)\). At \(p\mid Q\) retain the correction \(\log|1-p^{-1-it}|-\log|1-p^{-u-it}|\) at the very same angle as the kernel prime sum. Its coefficient at \(p^j\) subtracts \((p^{-j}-p^{-uj})/j\). Bound the absolute value only after this subtraction, including all omitted prime powers in the geometric tail. At \(p\nmid Q\) the upper estimate simply uses the positive \(B_n\). This calculation accounts for the correlation with the Euler factors that are removed.

For the lower archimedean integral use the companion bounds \(G_-(w)\le\min(P,C/w^2)\), \(P=\log(b/a)\). Globally \(\Re\psi(1/4+iy/2)>-5\): shift once to \(5/4+iy/2\), bound the Euler remainder by .4 and the subtracted reciprocal by 4. On \(|w|=|y-t|\le |t|/2\) the shift and the Euler remainder give
\[
 \Re\psi(1/4+iy/2)\ge\log(|t|/2)-2|w|/|t|-(2+\pi)/|t|-4/t^2 .
\]
Integrate \(2|w|\min(P,C/w^2)/|t|\) splitting at 1, and bound the exterior mass by \(4C/|t|\). The resulting error is at most
\[
 \tfrac A2[(2+\pi)/t_0+4/t_0^2]+
 [2(P+2C\log(t_0/2))+4C(\log(t_0/2)+5)]/(2\pi t_0).
\]
The pole term uses \(2C_z/(t_0^2-1/4)\). The integrated gamma error and distant zeros use the same absolute bounds as for the majorant. In particular for \(\Delta=H_*-T>2\), divide \(H_*<|\gamma|\le2H_*\) into unit intervals, each of mass at most \(12+2\log(2H_*+4)\). The resulting sum of inverse-square distances is at most \(2(12+2\log(2H_*+4))(\Delta^{-2}+\Delta^{-1})\). Above \(2H_*\) use \(|\gamma-t|\ge|\gamma|/2\) and \(N(v)\le v\log v\), giving \(16(1+\log(2H_*))/(2H_*)\). Multiply the sum by \(6h+2C_z\). The older remote estimates can still be used when smaller. [Unit-height count](../../round8/physical_low/PRIME_TWIST.md)

The [verifier](unit_zeta.py) uses 384 integral panels. The [physical calibration](../../round8/physical_low/row_calibration.py) uses \(u=1.60,\kappa=6\). For the wide interval, the first segment \(1\le|t|\le128\) uses the elementary periodic partial sum (<2.602). The next ends at \(10^6\) (<2.526), and the last gives <2.679. Consequently the physical coefficient per unit of unnormalized row energy is below .261896 on the original band and .264688 on the wide band. [Application to the full coprime rows](../../round8/physical_low/COPAIR_BAND.md)
