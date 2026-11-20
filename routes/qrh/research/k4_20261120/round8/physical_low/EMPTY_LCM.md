# Eliminating all moduli above the physical location

At \(L=116\), put \(x=e^L,\ c=L+\tfrac12\log(1+4e^{-L/4}),\ r=10^{-6},\ X=e^{c+r},\ z=C\sqrt{x/H}\). In the original Selberg expansion for any interval near the center, a modulus \(m=[d,e]>X\) has no multiples whatsoever. On this entire region its remainder for an interval of length \(y\) is exactly \(-y/[d,e]\). All Fourier harmonics can therefore be recombined before taking absolute values. The same identity holds by integration for all the near positive physical lobes. This note bounds the complete signed inverse moment on that region, including portions of rectangles crossed by \(m=X\).

Here are examples using the finite Mertens mean table supplied by the [separate verification](../../round7/mobius/sharp_mertens.py). The comparison is conditional on that input; the optional flags also preserve a version with just published Möbius bounds.

| \(C\) | Ordered dyadic/gcd cells meeting \(m>X\) | Upper cost for all near lobes on the whole region |
|---:|---:|---:|
| 3000000 | 4 | .000006070 |
| 4000000 | 11 | .00002082 |
| 10000000 | 89 | .000160976 |
| 30000000 | 746 | .000533854 |

This eliminates an actual part of every frequency simultaneously. Moduli with one or more multiples in the physical range and all other expenses of the \(L=116\) test remain to be bounded.

## Positive integration of real Möbius inputs

The [basic row identity](TOP_SIGNED.md) writes the coefficients \(\mu(u)\rho(u){\bf1}_{(u,q)=1}\) as \(\mu*c_q\). Use the published \(|M(y)|\le\sqrt y\) for \(y\le10^{16}\) ([Hurst, *Computations of the Mertens function*](https://www.ams.org/journals/mcom/2018-87-310/S0025-5718-2017-03275-0/S0025-5718-2017-03275-0.pdf)), and \(|M(y)|/y\le.006688/\log y\) above that point. The stronger optional tables give decreasing constants for \(s\le\log y\le66\). Our own rows satisfy \(\log z<66\). The flag **--perron** uses the earlier estimates with a first threshold 43; **--mean** uses the later mean-square estimates from 38 to 59. At each integer threshold take the smaller valid upper bound. Write the resulting step function for \(|M(y)|/y\) as \(E+\sum_j\Delta_j{\bf1}_{y<e^{s_j}}\), \(\Delta_j\ge0\), for \(10^{16}\le y\le z\); the same expression plus \(y^{-1/2}\) is valid for all \(y>0\).

Put \(R_s(k)=\prod_{p\mid k}(1-p^{-s}+p^{-s}/(p-1))^{-1}\), and keep \(C_s=\sum |c_1(a)|a^{-s}\). The finite or infinite Euler quantities required are
\[
 N(s,v)=C_s\left(\prod_p(1+\rho(p)^2R_s(p)^2/p^v)\right)^{1/2},\qquad v>1 .
\]
The code evaluates primes through \(Q=2000\). The two log tails are at most \(b_0 Q^{-s}/s\) and \(b_0^2 Q^{1-v}/(v-1)\), respectively, with \(b_0=((1-1/Q)(1-Q^{-s}))^{-1}\), by comparison with integrals over all integers.

For a dyadic variable \(d=ghu\in(z/2^{i+1},z/2^i]\), expand its positive \(G_{d}(z/d)\) over \(b<2^{i+1},(b,ghu)=1\). For each \(b\), restriction to \(u\le z/(ghb)\) leaves an interval inside the original row. Let \(\epsilon_{ghb,i}\) bound the absolute prefix of \(\sum\mu(u)\rho(u){\bf1}_{(u,ghb)=1}\), divided by its endpoint \(U\), for every \(U\) between \(z/(2^{i+1}gh)\) and \(z/(2^igh)\). Define
\[
 V_{g,i}^2=\sum_{h\le z}\frac{\mu^2(h)\rho(h)^2}{h^2}
 \left(\sum_{\substack{b<2^{i+1}\\(b,g)=1}}
        \frac{\mu^2(b)}{\varphi(b)}\epsilon_{ghb,i}\right)^2.
\]
Only squarefree coprime \(g,h\) occur in the actual sum. Enlarging the positive majorant to all \(h\) is harmless. Write \(W_i(s)=R_s(g)\sum_{b<2^{i+1},(b,g)=1}\mu^2(b)R_s(b)/\varphi(b)\). Use \(R_s(ghb)\le R_s(g)R_s(h)R_s(b)\), since each one-prime factor is at least one.

In the convolution let \(y=U/a\), where \(a\) is the positive convolution divisor. If \(y<e^{s_j}\), then \(a>z/(2^{i+1}ghe^{s_j})\). Rankin's bound with \(0\le t<1/2\) and Minkowski in \(h\) bound the contribution of this threshold to \(V_{g,i}\) by
\[
 \Delta_j
  \left(2^{i+1}g e^{s_j}/z\right)^t
          N(1-t,2-2t) W_i(1-t).
\]
Take the best of the printed finite set of \(t\) per threshold. The baseline is \(E N(1,2)W_i(1)\). The small-\(y\) term uses \(\sqrt{1/y}\); for any \(t>0\) its norm is bounded by
\[
   (2^{i+1}g z^{t-1})^{1/2} N(1/2,1+t)W_i(1/2),
\]
using \(h\le z\) to insert \(h^t\le z^t\). There is no truncation in \(h\). The special [top-row entry point](row_inputs.py) has \(g=1,i=0\). At \(C=3000000\), the complete corresponding norm \(V_{1,0}\) is at most .000670291 from published inputs, .0000744980 with the first table and .00000469535 with the mean table. Thus the true coprime top row at the first Fourier harmonic is at most \(7.651\,10^{-13}\) with the latter input.

## Complete and crossed rectangles

Write \(d\in(z/2^{i+1},z/2^i], e\in(z/2^{j+1},z/2^j]\), and let their actual gcd equal \(g\). If \(z^2/(g2^{i+j+2})\ge X\), the entire open-lower rectangle has \([d,e]>X\). After the coprimality inversion, \(1/[d,e]=g/(de)\). The two signed one-dimensional inverse-weight sums each use the \(2+\log2\) Abel constant of the [row proof](TOP_SIGNED.md). Cauchy over \(h\) therefore bounds the whole signed cell inverse moment by
\[
 \frac{\rho(g)^2(2+\log2)^2}{gG_-^2}V_{g,i}V_{g,j},\qquad
 G_-=\log z+1.331.
\]
In the remaining cells meeting the large-modulus region one has \(X<z^2/(g2^{i+j})<4X\) (including equality in the harmless upper comparison). For each fixed \(u=d/(gh)\), the condition \(de/g>X\) merely shortens the interval for the other variable, so its same signed Abel bound still applies. Take absolute values in the fixed variable. Its normalized harmonic mass is at most
\[
 2\,W_i(0)^*,\qquad W_i(0)^*=
 \sum_{\substack{b<2^{i+1}\\(b,g)=1}}\mu^2(b)/\varphi(b).
\]
Indeed \(\sum_{D/2<u\le D}\mu^2(u)\rho(u)/u=G(D)-G(D/2)\le2\). For \(D\ge32\), this follows from \(\log2+2.44(1+\sqrt2)/\sqrt{32}<2\) by [Ramaré, Theorem 3.1](https://www.impan.pl/shop/en/publication/transaction/download/product/113104). The integer cells below 32 are checked directly; \(D<1\) gives an empty interval. Apply Cauchy over \(h\) in the absolute and signed norms. Their remaining factor is \(\prod_p(1+(p-1)^{-2})^{1/2}\). The crossed-cell bound is
\[
 \frac{2(2+\log2)\rho(g)^2}{gG_-^2}
 \prod_p(1+(p-1)^{-2})^{1/2}
 \min\{W_i(0)^* V_{g,j},W_j(0)^* V_{g,i}\}.
\]
The [implementation](empty_lcm.py) runs over every \(g,i,j\) with \(g2^{i+j}\le z^2/X\), counting both orientations when distinct. Outside these cells no pair can have \([d,e]>X\). For the whole near positive area, the normalized multiple of the resulting scalar absolute moment is at most \((c+r)e^{3r/2}(1-a/\pi)\), by the exact exterior area of the Logan test. This proves the table.

~~~powershell
python -B round8/physical_low/row_inputs.py --mean
python -B round8/physical_low/empty_lcm.py --ratio 3000000 --mean --partial --upper .00000607
python -B round8/physical_low/empty_lcm.py --ratio 10000000 --mean --partial --upper .000160976
~~~


## A full-frequency cell containing an actual multiple

At \(C=3000000\), or the two alternatives in the commands below, take the full top pair \(z/2<d,e\le z,(d,e)=1\). Here \(2de>e^{c+r}\) throughout, so only the multiple \(de\) itself is possible in the physical range. This handles an actual nonempty cell without summing its separate Fourier harmonics. The same pair's subregion \(de>X\) in the preceding calculation must not be charged a second time.

Write \(A=\max(z/2,e^{c-r}/z),\ B=\min(z,2e^{c+r}/z)\). Every \(d\) in a pair with \(de\) in the near range belongs to \((A,B]\), up to an endpoint of measure zero in a moving level; the lower \(z/2\) is strict and \(e^{c-r}\) is a bound for the allowed support. For an ordinary interval \((M,M+y]\), given \(d\), count \(e\) in a span of length at most \(y/d\). The positive coefficient \(\mu^2(e)\rho(e)\) has, on any such interval contained in \((0,z]\), an upper bound \(C_1 y/d+E_1\). Take
\[
 C_1=\prod_{37<p\le1000}(1+1/[p(p-1)])e^{1/1000},\qquad
 E_1=(1+\log z)^2\prod_{p\le37}2p/(p-1).
\]
For \(p\le37\), write its local exact factor \(1+(\rho(p)-1){\bf1}_{p\mid e}-\rho(p){\bf1}_{p^2\mid e}\). Its mean is one and the sum of its absolute coefficients is \(2\rho(p)\). For larger primes discard the squarefree exclusion and use the positive squarefree-divisor convolution of \(1/(p-1)\). Its reciprocal moment is at most \(C_1\) by summing the tail over all integers. The sum of its coefficients through \(z\) is at most \(\sum_{n\le z}\tau(n)/n\le(1+\log z)^2\), since \(1/(p-1)\le2/p\). Counting the remaining small-prime divisibility expansions on intervals gives the asserted additive discrepancy.

Sum \(\mu^2(d)\rho(d)/d\) over the allowed \(d\). It is at most \(L_b=\log(B/A)+2.44(B^{-1/2}+A^{-1/2})\) by the same published \(G\) estimate. Its unweighted counterpart is at most \(B L_b\). Dropping further coprimality only in the positive spike majorant gives the half-open interval bound \(L_b(C_1y+E_1 B)/G_-^2\). Subtracting the Selberg main term requires the genuine signed top inverse moment, already bounded at \(n=0,r=1\) by **row_inputs.py**. Integrate scalars over all near positive lobes. Their area for both signs is at most \((1-a/\pi)I\), and their summed peaks are at most \(\sin a/a+(1+\cos a)/12\) by comparison with \(\sum_{j\ge1}j^{-2}\). These include all near lobes, also when cut by the radius \(r\). The upper costs for this entire true coprime cell are **.004818**, **.001621** and **.00013699**, at the three values of \(C\) below. Only published Mertens inputs are used. This cell does not by itself cover the location.

~~~powershell
python -B round8/physical_low/top_spike.py --ratio 3000000 --upper .004818
python -B round8/physical_low/top_spike.py --ratio 3300000 --upper .001621
python -B round8/physical_low/top_spike.py --ratio 3450000 --upper .00013699
~~~
