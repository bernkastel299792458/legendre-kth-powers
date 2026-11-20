# Genuine Selberg signs on the upper modulus annulus

For squarefree \(q\) let \(S\) be the product of those \(p\mid q\) with \(p\le z^2/q\). If \(\omega(S)\le3\), then
\[
 (-1)^{\omega(q)} B_z(q)\ge0 .
\]
In particular **every** four-prime \(q>z^{8/5}\) has \(B_z(q)\ge0\) and every five-prime \(q>z^{9/5}\) has \(B_z(q)\le0\). Indeed every prime factor of a contributing \(q\) is at most \(z\), so at least four small factors would imply \(q\le(z^2/q)^4 z^{\omega(q)-4}\). The thresholds include the tested upper annuli for \(m\le6000\) at \(L=116\). A negative coefficient removes the whole physical count from an upper estimate; a positive one makes the inverse mean-plus-low correction favorable, because \(C(q,v)>0\) on \(q\le X/23\).

For every contributing pair, its gcd is \(de/q\le z^2/q\). Thus the prime factors of \(q/S\) must be partitioned disjointly into \(D,E\) before assigning the small primes. Write \(U_i=A_{Di},V_j=A_{Ej}\) for \(i,j\mid S\), with the [nonnegative decreasing under divisibility Selberg weights](TRIPRIME.md). Each ordered partition contributes \((-1)^{\omega(q/S)}\sum_{[i,j]=S}\mu(i)\mu(j)U_i V_j\). For each row use its level decomposition \(U_i=\int_0^\infty 1_{\{U_i>t\}}\,dt\). Each nonempty level is a downward-closed family of subsets of the prime indices of \(S\). For two such families \(A,B\), the requisite integer is \(\sum_{i\in A,j\in B,i\cup j=S}(-1)^{|S|+|i|+|j|}\), where \(|S|\) now denotes the number of prime indices. With the empty family one gets zero. Enumerating the masks with the immediate-subset closure test gives the following exact results.

| Small prime count | Nonempty downward-closed families | Minimum | Maximum | Negative ordered pairs |
|---:|---:|---:|---:|---:|
|0|1|1|1|0|
|1|2|0|1|0|
|2|5|0|2|0|
|3|19|0|3|0|
|4|167|−2|6|22|

## True four- and five-dimensional reversals

Fix \(Q=210,\ z=1732099\sqrt{e^{116}/H}\) as in [the middle inequality](REMAINING_PHASE.md). In each row below \(q=S P R\), \(P,R\) are genuine primes. One has \(PR>z,\ S\) is exactly the product of the small primes just defined, both large primes exceed the two integer row cutoffs, and the only orders of the large-prime partition that contribute are \((P,R)\) and its reverse. Put \(u=\lfloor z/P\rfloor,\ v=\lfloor z/R\rfloor\). The normalized coefficient displayed is exactly
\[
 \frac{(-1)^{\omega(q)}G_Q(z)^2 B_z(q)}{2\rho(P)\rho(R)}
 =(-1)^{\omega(S)}\sum_{[i,j]=S}\mu(i)\mu(j)
 \rho(i)G_{Qi}(u/i)\rho(j)G_{Qj}(v/j).
\]
Every number in the sum on the right is rational. The program evaluates it with exact fractions. Primality is certified recursively for both large primes by factoring \(p-1\), checking the factor product and constructing a unit with exact order \(p-1\), with base case 2. The enveloping ratios and floor cutoffs use Arb.

| \(S\) | \(P\) | \(R\) | \(u,v\) | \(X/q\) | Normalized signed value |
|---|---:|---:|---:|---:|---:|
|\(11\cdot13\cdot17\cdot19\)|3658508167379016593839|47775479916824283154483|4224, 323|29.5878305|between −1.186856 and −1.186855|
|\(11\cdot13\cdot17\cdot19\cdot23\)|2066916449761638997057|2066916449761638997069|7477, 7477|52.6318372|between −9.740826 and −9.740825|

The two reversals occur for the actual presieved weights in the target middle region. They prevent a blanket extension of the favorable sign to all six- or seven-prime moduli.

The exact fractions in the first two rows are \(-68909789/58060800\) and \(-3732696851/383201280\), respectively.

The near-top sign threshold can be located much more closely. If \(z^2/q<247/11\), its eligible small prime divisors are at most \(11,13,17,19\). With all four present, a negative pair of downward-closed families would force \(z^2/q\ge13\cdot19/11\) by [the four-dimensional cell constraint](WRONG_SIGN.md); all other cases have dimension at most three. Thus the entire range below this threshold has the expected sign. Conversely, for the prime pair \(62572339081346530478137,\ 3680725828314515818009\) and these four small primes, the difference \(z^2/q-247/11\) is between \(9.62565\,10^{-14}\) and \(9.62566\,10^{-14}\); the normalized coefficient is exactly \(-3556553/12441600\).

There is also a counterexample on a true multiple in the first positive lobe rather than just in a modulus range. Use \(P=61698074862645331738339,\ R=3644365207573700579861\) and again \(S=11\cdot13\cdot17\cdot19\). Then \(q=10385611310559599636049806230046840693128903710131\), the two integer row cutoffs are \(250,4240\), and the normalized coefficient is again \(-3556553/12441600\). The admissible multiplier \(23\) gives \(H\log(23q/e^c)=3.141592680188665\) to the shown precision. The original leakage weight there exceeds .1384, as does its smooth majorant. These assertions use certified prime tests, interval evaluation of the ordinate and exact rational arithmetic in the same verifier.

~~~powershell
python -B round8/physical_low/boolean_sign.py
~~~

## Four-prime physical upper with two prescribed small factors

For \(q=abPR,\ a<b<P,R,\ PR>z\), put \(U_i=\rho(i)G_{Qi}(\lfloor z/P\rfloor/i)\), and similarly \(V_i\) for \(R\). Divide the true coefficient by \(2\rho(P)\rho(R)/G_Q(z)^2\). The result is
\[
 U_1V_{ab}+U_{ab}V_1+U_aV_b+U_bV_a+U_{ab}V_{ab}
 -U_{ab}(V_a+V_b)-(U_a+U_b)V_{ab}.
\]
It is nonnegative by the two-dimensional sign table (also directly, bounding the four negative terms respectively by \(U_bV_a,U_{ab}V_1,U_aV_b,U_1V_{ab}\) in the order \(U_{ab}V_a,U_{ab}V_b,U_aV_{ab},U_bV_{ab}\)). In each product cell evaluate an upper bound by using the upper rows for positive terms and lower rows for subtractions, reversing the choices and clipping at zero for a lower bound. All row values use finite squarefree divisor sums. Here the large primes exceed all their cutoff arguments.

For actual multiples \(kabPR\), apply the [Fejér / Brun–Titchmarsh per-cell physical estimate](FEJER_PRIMES.md) with \(k\) replaced by \(kab\). Sum \(k\) coprime to \(Q\) from 23 to \(m-1\) for the annulus \(X/m<q\le X/23\). Use the interval lower bound on the positive joint correction only on inner cells confined entirely to the annulus, as in the [two-prime calculation](SEMIPRIME_ANNULI.md), with the additional factor \(1/(ab)\). The spurious equal-large-prime contribution to that lower bound is at most \(5[\rho(ab)G_Q(abm+1)]^2(1+\eta)/(P_{\min}-1)\) before the normalization, using all five positive terms of the polynomial. The uniform high-tail bound is included in every final row.

| Small pair | \(m\) | Actual upper | Mean-plus-low lower | Whole middle upper |
|---|---:|---:|---:|---:|
|11, 13|200|.000017954749|.000004420446|.000013534303|
|11, 13|400|.000026187175|.000006860500|.000019326675|
|11, 13|1100|.000042346418|.000011157747|.000031188671|
|11, 17|200|.000014245929|.000003436125|.000010809804|
|13, 17|200|.000012393462|.000002997948|.000009395514|

At \(m=200\) the first row together with every two- and three-prime modulus costs less than .002362233. These are disjoint sets of moduli.

~~~powershell
python -B round8/physical_low/four_prime.py --small 11 13 --end 200 --cells 72 --upper .000013534303
~~~
