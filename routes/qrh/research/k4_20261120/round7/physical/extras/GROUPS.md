# Simultaneous bounds for several Fourier indices

Use the [single-block notation and weight estimates](WEIGHT_ENERGY.md). For \(n\) in an integral group \(N\le n\le J_1\) let \(\alpha_n\ge0\), \(Z=\sum\alpha_n>0\), \(H=J_1-N\) and \(K_0=tg\,2^{i+j}/z^2\). Consider the normalized sum
\[
 {\cal S}=(DFZ)^{-1}\sum_{N\le n\le J_1}\alpha_n
 \sum_{x,w}a_x b_w e^{2\pi i n t/(gh^2xw)}.
\]
This is a uniform estimate at each fixed \(t\). With sampling points \(D/x\), combine equal rational frequencies \(K_0 F n/w\) before applying the sampling inequality. They span a frequency interval of length at most \((2J_1-N)K_0\). Two distinct frequencies differ by at least \(K_0/F\), since \(|nw'-n'w|\) is a positive integer and \(ww'\le F^2\).

The multiplicity of the frequency at \((n,w)\) is at most \(1+H(n,w)/n\). Indeed, writing \(n/w=a/b\) in lowest terms, each possible numerator in the group is a multiple of \(a=n/(n,w)\). Cauchy–Schwarz on each collection of equal frequencies therefore gives
\[
 \sum_\nu |b_\nu|^2
 \le \sum_n \alpha_n^2
 \left(\sum_w |b_w|^2 +\frac Hn\sum_w (n,w)|b_w|^2\right).
\]
Using \((n,w)=\sum_{r\mid n,\ r\mid w}\varphi(r)\) and counting at most \(F/r\) multiples gives the first bound
\[
 F^{-1}\sum_w(n,w)|b_w|^2\le L_w^2\tau(n).
\]
For the second bound use the actual \(A_w,B_w\) from the row proof. Only squarefree \(w\) have nonzero coefficient, so only squarefree \(r\) contribute. Since \(\varphi(r)\rho(r)^2/r=\rho(r)\), the divisibility estimate from that proof yields
\[
 F^{-1}\sum_w(n,w)|b_w|^2
 \le A_w C(n)+B_w D(n),\quad
 C(n)=\prod_{p\mid n}(1+\rho(p)),\qquad
 D(n)=\prod_{p\mid n}(1+p\rho(p)).
\]
The same inequalities hold for the differentiated row, with its primed coefficients \(A'_w,B'_w\) and sup \(2L_w\).

Put \(v_0=\sum\alpha_n^2/Z^2\), and for any one of the three nonnegative functions \(T=\tau,C,D\) put \(v_T=(H/Z^2)\sum\alpha_n^2 T(n)/n\). After merging the frequencies, their total squared mass divided by \(F Z^2\) is at most
\[
 U_w v_0+\min\left(L_w^2v_\tau,\ A_wv_C+B_wv_D\right).
\]
The new sampling factor is
\[
 P_{B_0}=C_{B_0}\left(1+\frac{(2J_1-N)K_0+B_0}{D}\right)
              \max(1/K_0,1/(B_0 F)).
\]
These are precisely the support and separation parameters needed in the single-block Paley–Wiener proof. Consequently \(|{\cal S}|^2\) is at most the product of \(U_x\), \(P_{B_0}\), and the last squared-mass bound. Transposing \(x,w\) gives another bound. For each block the code may also use the separately absolute frequency bounds already proved. The combined majorants remain nonnegative when some frequencies are absent.

For the Fejér terms use \(\alpha_n=2(1-n/(J+1))/(J+1)\). For the Vaaler main terms use \(\alpha_n=2\Phi(n/(J+1))/(\pi n)\). The two endpoint polynomials have the same coefficients, so their absolute difference can either be bounded by their separate grouped estimates, or by integrating the derivative from \(M\) to \(M+y\). In the derivative case use weights \(n\alpha_n\) and primed \(x,w\) energies. Its relative scale, after accounting for both endpoints, is
\[
 \frac{\pi g\,2^{i+j}}{c^2}\cdot\frac{\sum n\alpha_n}{\sum\alpha_n}.
\]
Thus grouping preserves the common sign of each endpoint polynomial without requiring any Möbius cancellation or cancellation between different dyadic blocks.

In the implementation, the integer divisor counts \(\tau(n)\) are sieved exactly and identify the primes by \(\tau(p)=2\). The arrays \(C,D\) multiply positive factors in binary64. Under \(J<2^{28}\) there are fewer than 28 distinct prime factors in any entry; each factor includes at most four rounded operations. Enlarging by \(1+2^{-40}\) safely bounds this error before conversion to a scalar moment. Those moments, including the positive cotangent-derived Vaaler weights, are summed in Arb. Each upper endpoint passed to the positive bilinear kernel receives the \(1+2^{-48}\) conversion margin. The zero entries for \(H=0\) are exact. Inputs for the reciprocal and direct bandwidth bounds are taken at separate allowed rectangle corners.

The command **python -B weight_energy.py --l 83 --ratio 16 --order 32768 --location-hi 116** gives on \(83\le\log y\le84,\ e^{114.98}\le M<M+y\le e^{116}\) a relative sieve error below **.000107404067** and denominator addition above **7.75284370**. Here \(z=16\sqrt y\) and the conventional upper bound for the prime count is \(2y/(\log y+\eta)\).

A common \(c=30,\ J=262144\) gives the following certified **lower** bounds on the denominator additions. Every row covers its closed length cell and the entire location interval \(e^{114.98}\le M<M+y\le e^{116}\).

| \(\log y\) | \(\eta\) exceeds |
|---|---:|
| 83 to 84 | 8.5736107148 |
| 84 to 85 | 8.9110835748 |
| 85 to 86 | 9.0536812626 |
| 86 to 87 | 9.0663769237 |
| 87 to 88 | 8.9687848413 |
| 88 to 89 | 8.7457382841 |

Recompute all six with the following PowerShell command in this directory.

~~~powershell
83..88 | ForEach-Object { python -B weight_energy.py --l $_ --ratio 30 --order 262144 --location-hi 116 }
~~~
