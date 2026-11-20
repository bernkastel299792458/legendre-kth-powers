# The complete coprimality condition on a two-row Mellin band

With the [finite-height Poisson minorant for the unit zeta function](../../round7/mobius/UNIT_ZETA.md), the ordinary Mellin calibration per unit row energy falls below .261896 on the original \(I\). For wider bands the integrated cost includes the residue, all \(|t|\le1\), and successive dyadic layers approaching the exact height of the published RH verification. On a layer ending at \(b\), the Gaussian width can be chosen so that \(24/w\le 3(H_*-b)/4\), keeping the extended vertical contour inside the verified range. The [edge replay](copair_edge.py) uses the more restrictive \(24/w\le 24(H_*-b)/32\) and takes the better of two certified real parts per layer. Through \(|t|\le3\,000\,000\,000\,000\), the whole cost for \(A=z/11,\ g\le11\) is below .001129094, including .000412359 for the newly treated edge above \(2.88\cdot10^{12}\). This still leaves the infinite tail of ordinary Mellin inversion.

~~~powershell
python -B round8/physical_low/copair_edge.py --lower-divisor 11 --gmax 11 --upper .001129094
~~~

Use the physical constants, positive majorant \(F\), and coefficient normalization from [the signed remainder](REMAINING_PHASE.md). Here \(I=[H/8,H/4]\) is a band in ordinary Mellin height \(t\), with length \(D=H/8\). Its endpoints do not describe a band in the additive phase \(\kappa=nX/(210q)\). The following bound applies to the ordinary Mellin inversion of the actual multiples on a specified set of divisor pairs. A further identification or a complementary estimate is needed before subtracting it from the additive remainder.

Set \(Q=210,\ A=z/11,\ B_g=\min(z,\sqrt{gX/23})\). For \(g=(d,e)\le g_0\), retain both \(d,e\in(A,B_g]\) and \((de,Q)=1\). The program verifies \(A^2/g>e^{70.7}\); also \([d,e]\le X/23\). Each nonzero retained coefficient has numerator \(\mu(d)\rho(d)\), where \(\rho(n)=n/\varphi(n)\), because the associated inner Selberg sum is one. The ordinary Mellin inversion on the line \(\Re s=1\), away from its pole at \(t=0\), contains \(\zeta_Q(1+it)\) for the actual unit multiples. The absolute majorant \(|\int F(x)x^{it}dx|\le\int F(x)dx\) is valid throughout. [Row calibration](row_calibration.py) bounds \(|\zeta_Q(1+it)|<7.493\) on \(I\) by periodic partial summation. Including \(\int F\), the physical factor \(P_0\), both signs of \(I\), \(1/(2\pi)\), and the square of the Selberg denominator gives cost at most .740522 per unit of the following **unnormalized integral**.

Write \(d=gu,\ e=gv\). Enforce \((u,v)=1\) by \(\sum_{h\mid(u,v)}\mu(h)\), then write \(u=hi,\ v=hj\). All divisions introduce exactly the factors \(\rho(g)^2/g\) and \(\rho(h)^2/h^2\) when divided by \([d,e]\). The signs \(\mu(g)^2,\mu(h)^2\) from the coefficient products have absolute value one on the retained indices. Up to unit phases depending on \(g,h\), the two independent sums multiply to the square of the same sharp row on \((A/(gh),B_g/(gh)]\), with coefficient \(\mu(i)\rho(i)/i\) on units modulo \(Qgh\). Hence its absolute integral is bounded by the row's \(L^2\) integral. This expansion retains the full inversion including every nonzero \(h\).

For \(h\le h_0=10^9\) use [the sharp annulus mean-square bound](../../round7/mobius/TWISTED_RMS.md) with \(\sigma=.58,\ u=1.55,\ \kappa_0=6,\ w=e^{-22}\). Omitting the additional primes dividing \(gh\) from the Dirichlet series multiplies the strip bound by at most \(C_g C_h\), where \(C_m=\prod_{p\mid m}(1-\rho(p)p^{-\sigma})^{-1}\). The positive denominators hold since every such prime is at least 11. The vertical multiplier at the lower endpoint gains \(h^{1-\sigma}\) relative to the base row at \(A/g\). This gain also upper bounds the tiny contour errors, using \(B_g/g\) for their upper endpoint. Let \(V_g\) be the resulting base vertical and contour root-mean-square bound. Let \(E_g\) be the worst unsmoothing bound using the lowest endpoint \(A/(gh_0)\) and the upper limit \(B_g/g\). The triangle inequality in the weighted sum of squares over \(h\) gives
\[
 D\,\frac{\rho(g)^2}{g}\left[
 C_gV_g\prod_{p\nmid Q}\left(1+\frac{\rho(p)^2p^{-2\sigma}}{(1-\rho(p)p^{-\sigma})^2}\right)^{1/2}
 +E_g\prod_{p\nmid Q}(1+\rho(p)^2/p^2)^{1/2}\right]^2 .
\]
For primes above 2000, the Euler product of the omitted \(p^{-2\sigma}\) terms is bounded using the remaining \(\log\zeta(2\sigma)\) after removing all prime factors through 2000. Use the largest possible local multiplier in that tail. This also applies at \(\sigma=1\) to the second product without the reciprocal factor.

For \(h>h_0\) use the separated-log mean value estimate with constant \(D+2\pi(B_g/(gh)+1)\). Here \(\rho(ghi)\le R\), the maximum totient ratio among units up to \(B_g\), bounds the original numerator and absorbs both outer totient factors. With \(a=A/(gh), b=B_g/(gh)\) the reciprocal-square mass is at most \((1+B_g/A)/a\) for \(h\le B_g/g\), since there are at most \(1+b-a\) terms of size at most \(a^{-2}\), and \(a^{-2}\le (B_g/A)a^{-1}\) can alternatively be combined with the decreasing integral bound \(a^{-2}+a^{-1}\). Summing \(1/h\) and \(1/h^2\) therefore costs at most
\[
 (1+B_g/A)R^2\left[(D+2\pi)(1+\log(B_g/g))/A+
              2\pi B_g/(Ag h_0)\right].
\]
The physical costs after summing over the squarefree unit \(g\le g_0\) are bounded as follows. Each entry includes both signs in Mellin height and every unit multiple on the entire retained square.

| \(g_0\) | Upper cost |
|---:|---:|
| 1 | .000106770 |
| 11 | .000251405 |
| 23 | .000668104 |
| 47 | .001093473 |
| 97 | .001655551 |

~~~powershell
python -B round8/physical_low/copair_band.py
~~~

## Lower rows and longer ordinate intervals

Replace the lower endpoint by \(A=z/M\). The exact numerator of the coefficient at \(ghi\) now includes \(\sum_{b\le z/(ghi),(b,Qghi)=1}\mu^2(b)/\varphi(b)\). After expansion, \(b<M\) and each inner \(i\) still forms a sharp interval, with upper endpoint reduced to \(\min(B_g,z/b)/(gh)\). Its missing-prime factor contributes at most \(C_b\) on the shifted contour. In the small-\(h\) bound multiply the analytic term by \(\sum_{b<M,(b,Qg)=1}\mu^2(b)C_b/\varphi(b)\) and the unsmoothing term by the same sum without \(C_b\). Dropping \((b,h)=1\) in these positive bounds is permissible after estimating each row. The latter sum squared also bounds the extra numerator in the large-\(h\) estimate. The [program](copair_band.py) encloses the resulting costs, retaining all actual small divisor corrections, for example .002126638 for \(M=23,g_0=23\), .001910874 for \(M=47,g_0=11\), and .001896937 for \(M=97,g_0=1\), each on the original \(I\).

On the much wider pair of ordinary Mellin bands \(1\le|t|\le2\,880\,000\,000\,000\), the complete cost for \(M=11,g_0=1\) is below .000910922 and for \(M=11,g_0=11\) it is below .002148735. Both include the part below the original \(H/8\) and all newly included frequencies up to the displayed height. The pole at zero remains outside the integration intervals.

~~~powershell
python -B round8/physical_low/copair_band.py --lower-divisor 23 --gmax 23 --upper .002126638
python -B round8/physical_low/copair_band.py --lower-divisor 47 --gmax 11 --upper .001910874
python -B round8/physical_low/copair_band.py --lower-divisor 97 --gmax 1 --upper .001896937
python -B round8/physical_low/copair_band.py --gmax 11 --tmin 1 --tmax 2880000000000 --upper .002148735
~~~

## The pole and the central unit of height

For the signed physical difference (actual unit multiples less their uniform mean) the positive and negative bands can be connected through \(t=0\). Shift from absolute convergence to the principal-value line 1. The half-residue left after subtracting the mean has absolute value at most \(\eta S/2\) in the following units. Write \(J(t)\) for the Mellin transform of the real \(F\) divided by its area, times the retained sum of the real numerator products \(q^{-1-it}\). Then \(J(0)\) is real. We bound \(|J(t)|\le S\) on \(|t|\le1\). The full normalization at the end of this computation is \(P_0\int F/G_Q(z)^2\).

To obtain \(S\), replace the root mean square of each sharp annulus by its pointwise upper bound. On \(|t+v|\le100\), use the reciprocal bound 256 and exact upper products of the missing Euler factors and totient correction. Here \(|v|\le101\). On \(y\le|t+v|\le y'\) with \(y\ge100,\ y'=\min(2y,24/w+1)\), the Perron denominator is at least \(y-1\), and Cauchy–Schwarz gives the local reciprocal root mean square times \((y'-y)/(y-1)\). Compare also with the unsigned bound on that actual piece. Include both sides of the ordinate and both annulus endpoints. This is implemented in the [central kernel](../../round7/mobius/twisted_rms.py). Use the same Euler-summed small \(h\) as above, now up to \(10^{15}\). For larger \(h\), the triangle inequality on each row and the decreasing \(1/h^2\) tail give at most \(R^2(1+\log(B_g/g))^2(\sum_b1/\varphi(b))^2/(g h_0)\) with the same squarefree-unit restrictions on \(b\).

Let \(M\) bound \(|J'(t)|\). Before the \(h\) inversion use the last positive bound without \(1/h_0\), multiplied by \(\log(X/(A^2/g))\) and summed over \(g\). This pays for differentiating the actual phase \(\log(x/q)\), which is positive because \(x/q\ge23e^{-4r}>1\) on the support. With \(D_Q\) the exact discrepancy of the unit counting function, partial summation on the line 1 gives \(|\zeta_Q(1+it)-\eta/(it)|\le\eta+\sqrt2 D_Q\) on \(0<|t|\le1\). Because \(J(0)\) is real, the singular contribution to the real part is bounded using \(\min(S,|t|M)\). For \(M>S\), the unsubscaled cost of the complete central contribution, inclusive of its half-residue, is at most
\[
  \eta S/2+\big[(\eta+\sqrt2D_Q)S+\eta S(1+\log(M/S))\big]/\pi .
\]
For \(M_{\rm row}=11,\,g_0=11\) (here \(M_{\rm row}\) denotes the lower divisor in \(A=z/M_{\rm row}\)), the normalized central cost is below \(2.351\cdot10^{-9}\). For \(M_{\rm row}=23,\,g_0=23\) it is below \(2.050\cdot10^{-8}\). The complete **ordinary Mellin** difference through \(|t|\le2\,880\,000\,000\,000\), including the inverse uniform term for the \(M_{\rm row}=11,\,g_0=11\) square, therefore costs less than **.002148738**. Its unbounded ordinate tail and other divisor pairs remain to be estimated.

~~~powershell
python -B round8/physical_low/copair_band.py --core --lower-divisor 11 --gmax 11 --upper 2.351e-9
python -B round8/physical_low/copair_band.py --core --lower-divisor 23 --gmax 23 --upper 2.050e-8
~~~
