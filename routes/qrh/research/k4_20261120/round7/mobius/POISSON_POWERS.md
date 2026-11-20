# Keeping the powers of the Poisson kernel separately

Use the notation and the completed-zeta identity in the [single-kernel derivation](FINITE_INVERSE.md). The estimate below uses the same published finite-height RH verification and permits \(1<u\le6\). For every \(1/2\le v\le6\), \(|C(v+it)-\frac12\log(|t|/(2\pi))|<.04\) whenever \(|t|\ge100\); the reciprocal and logarithm corrections together are at most \(20/t^2\) and the digamma correction is at most \((1+\pi/2)/(2|t|)\).

For \(b=u-1/2,\ a=\sigma-1/2,\ \eta=1-a^2/b^2,\ v=b^2/(b^2+y^2)\) the exact integrated kernel for a verified zero is \(-\frac12\log(1-\eta v)\). Retain its first \(m-1\) powers. Bound the remaining positive series by its value at \(v=1\) times \(v^m\). Denote the resulting polynomial by \(\sum_{l=1}^m r_l v^l\). If \(w=b/(b+iy)\), then partial fractions give
\[
 v^l=\sum_{j=1}^l\frac{2}{2^{2l-j}}\binom{2l-j-1}{l-j}\Re w^j .
\]
Indeed \(v^l=[(1+iy/b)(1-iy/b)]^{-l}\); Taylor-expand either reciprocal factor at the pole of the other, retain orders up to \(l-1\), and use conjugacy. Let \(c_j=b^j\sum_{l\ge j}r_l\,2^{1-2l+j}\binom{2l-j-1}{l-j}\). All these coefficients are positive.

The ordinate integral of the exact logarithmic kernel is \(\pi h\), \(h=u-\sigma\). The integral of the polynomial majorant is \(\pi c_1\), since \(\int\Re(b+iy)^{-j}dy=0\) for \(j\ge2\). Thus \(c_1-h\ge0\). This difference increases as \(\sigma\) falls, because the majorant error is the sum of the positive terms \(\eta^l(v^m-v^l)/(2l)\) for \(l\ge m\). The individual \(c_j\) increase as well.

From the completed logarithmic derivative, differentiation \(j-1\) times gives the sums of \(\Re(u+it-\rho)^{-j}\) with factor \((-1)^{j-1}/(j-1)!\). For \(j\ge2\) the corresponding gamma correction has absolute value at most
\[
3/|t|^j+\pi/(4|t|^{j-1}).
\]
Indeed the polygamma series is bounded after dividing by its factorial by its first term plus the integral of \((z^2+(t/2)^2)^{-j/2}\) from zero to infinity. For \(j\ge2\), that integral is at most \((\pi/2)(2/|t|)^{j-1}\). The arithmetic term is at most \(D_j(u)=(-1)^{j-1}D^{(j-1)}(u)/(j-1)!\), \(D=-\zeta'/\zeta\), by its absolutely convergent prime-power series. Extend each verified-zero sum to all zeros, charging the omitted high terms in absolute value. For \(j=1\) their summands have real part of modulus at most \(24/\gamma^2\), and for \(j\ge2\) their modulus is at most \(4/\gamma^2\). The original integrated high term has the same first bound times \(h\).

It follows that an upper bound for \(\log|1/\zeta(\sigma+it)|\) is
\[
\log\frac{\zeta(u)}{\zeta(2u)}+
\tfrac12(c_1-h)\log(T/(2\pi))+.04(c_1+h)+\sum_{j=1}^m c_jD_j(u)
+\sum_{j=2}^m c_j(3/100^j+\pi/(4\cdot100^{j-1}))
+96(h+\sum c_j)(1+\log H)/H .
\]
This holds throughout the horizontal segment to \(u+it\) by the monotonicity just proved. The finite contour shift for the Gaussian Möbius sum therefore applies with exactly the same endpoints and tails as in the first proof. At \((\log X,\log|\tau|)=(43,26),(55,15),(60,25),(70,25)\), the respective upper bounds on \(|Q|/X\) are \(0.001136,\ 1.544\cdot10^{-6},\ 1.512\cdot10^{-6},\ 2.60\cdot10^{-8}\). These estimates concern the specified Möbius sums. The unsmoothed dyadic coefficients of a full Selberg rectangle require another transfer.

~~~sh
python -B round7/mobius/poisson_power.py --complete
~~~
