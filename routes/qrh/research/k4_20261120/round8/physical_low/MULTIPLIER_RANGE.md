# Aggregating the actual integer multipliers

Keep \(Q=23\#=223092870\) and all other parameters of [the physical second-moment estimate](PHYSICAL_L2.md). A complete collection from the opposite end works for the following pairs of cutoffs. Each row has paid every contribution at \(q\le Y\), including all unit multipliers and all frequencies, and every physical modulus \(q>X/m\).

| \(m\) | \(\log Y\) | small-\(q\) upper | remaining sufficient allowance |
|---:|---:|---:|---:|
|200|72|.004318807919|.00002442391|
|239|71.25|.002004209064|.00071933657|
|263|70.7|.001141279577|.00040208958|

At \(m=200\) this removes the entire further modulus range \(e^{70.7}<q\le e^{72}\) from the earlier condition. With \(m=263\) it retains the original lower cutoff and covers the whole opposite prefix with additional true multipliers through 257. The still-open signed sum has \(Y<q\le X/m,\ 1<nX/(Qq)\le4\cdot10^{18}m/210\).

## Ordered unit triples

For the [unit discrepancy cost](WHEEL_PREFIX.md) let \(t=\log Y,\ \ell=t/3,\ D=D_Q,\ \eta=\varphi(Q)/Q\). In the elementary dominating sum \(\sum_{q\le Y}|B_Q(q)|\le \sum_{uvw\le Y,(uvw,Q)=1}1\), order the three indices \(a\le b\le c\), paying multiplicity at most six. Then \(a\le Y^{1/3}\), \(a\le b\le\sqrt{Y/a}\) and \(Y/(ab)\ge Y^{1/3}\). Counting \(c\) by the full unit interval through \(Y/(ab)\) gives the upper
\[
 \sum_{q\le Y}|B_Q(q)|/Y
 \le6(\eta+D e^{-\ell})\sum_{\substack{a\le e^\ell\\(a,Q)=1}}a^{-1}
       \left(H_Q(\sqrt{Y/a})-H_Q(a^-)\right).
\]
Here \(D_Q\) is the exact periodic oscillation, or the elementary upper \(2^{\omega(Q)}\). For \(a\le M=65536\) compute \(H_Q(a^-)\) exactly up to outward rounding. The other harmonic is at most
\(H_Q(M)+\eta[(t-\log a)/2-\log M]+D/M\); its argument is at least \(M\) in the trials. For \(a>M\) the difference is bounded by \(V(a)=3\eta(\ell-\log a)/2+D/a\), by the closed-interval reciprocal unit bound. The positive decreasing function \(V(a)/a\) summed on units from \(M<a\le e^\ell\) costs at most
\(3\eta^2(\ell-\log M)^2/4+\eta D/M+D V(M)/M\).
These inequalities are the option --ordered-small. The remaining Poisson, high-pass and real-direction discrepancy estimates are those already given for the same \(Q\).

## A verified threshold for the full middle modulus band

Using the preceding single-\(k\) spectral bound independently for *all* \(k\) cannot close the remaining condition. In its \(g=b=t=1\) outer term alone the densities are at least \(\eta Z_Q\), and the log span is \(\log(kz^2/X_-)\). For the previous \(m=200,\log Y=70.7\) row, take only interior multipliers \(200<k\le\lfloor X_-/Y\rfloor\) in complete \(Q\)-periods, coprime to \(Q\), so their true modulus support is in \(Y<q<X/200\). For \(a=Q\lceil201/Q\rceil,\ b=Q\lfloor \lfloor X_-/Y\rfloor/Q\rfloor,\ R=z^2/X_-\), the function \(\log(Rk)/k\) decreases. Each full period contains exactly \(\eta Q\) candidates. Its right-endpoint sum bounds below the integral with both ends moved one period to the right. Thus the sum of these positive outer **caps** is at least
\[
 \frac{u B_\tau Z_Q^2\eta^3}{2G_-^2}
 \{\log^2(R(b+Q))-\log^2(R(a+Q))\}>1.40427235 .
\]
Here \(G_-\) is the actual numerical lower bound for \(G_Q(z)\) used in the estimator. The available allowance at the original small-\(q\) cost and \(m=200\) was .00176077404. This comparison measures a loss of more than a factor 797 in that chosen termwise estimation procedure. There is no lower bound of this order for the signed sum itself.

To keep correlations across multipliers, put a common rectangle on the two divisor rows and take \(K<k\le K'\le2K\) with their unit restriction before bounding the high spectrum. The Fourier multiplier is then \(\widehat f(w/H)\sum_{(k,Q)=1} k^{-1+iw}\), up to a common unit phase. By Abel summation with the discrepancy of the entire unit count, for every \(w\ne0\),
\[
 \left|\sum_{\substack{K<k\le K'\\(k,Q)=1}}k^{-1+iw}\right|
 \le {2\eta\over|w|}+{D_Q\over K}
       \bigl(2+\sqrt{1+w^2}\log 2\bigr).
\]
Indeed the continuous unit integral is at most \(2\eta/|w|\); the discrepancy endpoint terms are at most \(2D_Q/K\), and the derivative integral obeys \(\int_K^{2K} v^{-2}dv\le \log(2)/K\). Integration by parts gives \(|\widehat f(w/H)|\le H V_f/|w|\). Write \(t_0=.4H\); the product on **all** \(|w|\ge t_0\) is bounded by
\[
 H V_f\left[\frac{2\eta}{t_0^2}+
 {D_Q\over K}\left(\frac2{t_0}+\sqrt{1+t_0^{-2}}\log2\right)\right].
\]
For \(\log K=35,38,40,43,45\), its successive upper bounds are .056077364, .002791928, .000377847, .000018812, .000002546. These are bounds for the high-frequency multiplier on a *common* rectangle. They do not sum the low Fourier integral, coprimality corrections, or short divisor rows across the entire modulus range. For small \(K\) this bound grows as \(H/K\); a stronger way to use the actual finite exponential sums for these multipliers is still needed.

~~~powershell
python -B round8/physical_low/wheel_prefix.py --Q 223092870 --cut 200 --harmonic-limit 223092870 --tiny-log 72 --unit-small --ordered-small --fast-low --physical-spectrum --lower .00002442391
python -B round8/physical_low/wheel_prefix.py --Q 223092870 --cut 239 --harmonic-limit 223092870 --tiny-log 71.25 --unit-small --ordered-small --fast-low --physical-spectrum --lower .00071933657
python -B round8/physical_low/wheel_prefix.py --Q 223092870 --cut 263 --harmonic-limit 223092870 --tiny-log 70.7 --unit-small --ordered-small --fast-low --physical-spectrum --lower .00040208958
python -B round8/physical_low/multiplier_range.py
~~~


## Retaining both actual Selberg numerators on small moduli

There is a larger unconditional bound on the *range of moduli*, using a sharper upper on \(\sum_{q\le Y}|B_Q(q)|\). With \(Q=23\#\) the new rows are

| \(m\) | \(\log Y\) | All small-\(q\) spectral cost, upper | Remaining sufficient allowance |
|---:|---:|---:|---:|
|200|75|.003336577334|.00100665449|
|239|74.5|.002116554528|.00060699111|
|263|74|.001348755272|.00019461388|

The first row includes every modulus in the additional interval \(e^{70.7}<q\le e^{75}\) at the opposite end from the full true-multiplier prefix. The ratio of the upper endpoints is \(e^{4.3}>73\).

Write the current upper shell endpoint as \(y\) and the lower as \(y_0=ye^{-s}\). Set \(v_0=y_0/z>1,\ L=\log(z/v_0)\). On \(y_0<q=guv\le y\), both \(gu\le z\) and \(gv\le z\) hold. In particular \(u,v>v_0\) and \(g<z/v_0\). The two actual Selberg numerators admit the following upper on their product, after the factor \(\rho(g)^2\rho(u)\rho(v)/G_Q(z)^2\) is extracted:
\[
 Z_Q^2 (C+\eta\log(z/(g u)))(C+\eta\log(u/v_0)).
\]
Here \(G_Q(v)\le Z_Q H_Q(v)\le Z_Q(C+\eta\log v)\) for \(v\ge1\). For the second row one uses \(gv>y_0/u\). The first harmonic estimate follows by expanding \(\rho(n)\) into positive divisor weights; for \(C\) test \(H_Q(n)-\eta\log n\) at every permitted \(n\le65536\), and beyond use the harmonic unit discrepancy at 65536.

For fixed \(g,u\), the \(v\) interval has length at most \(y(1-e^{-s})/(gu)\). Its absolute \(\rho(v)\)-weighted count is at most \(Z_Q y[\eta(1-e^{-s})+Ez/y]/(gu)\), since \(gu\le z\), where \(E=D_Q(1+\log z)\). The remaining \(u\)-weight on \(v_0<u\le z/g\) is
\((C+\eta\log((z/g)/u))(C+\eta\log(u/v_0))/u\).
It is positive and decreasing since \(C\ge1>\eta\). Partial summation with the ordinary \(\rho(u)\)-weighted unit count bounds its sum by \(Z_Q V(l)\) for \(l=L-\log g\), where
\[
 V(l)=\eta(C^2 l+C\eta l^2+\eta^2 l^3/6)
      +E C(C+\eta l)/v_0.
\]
For the last \(g\)-row expand \(\rho(g)^2\) over its divisors with nonnegative local coefficients \(\rho(p)^2-1\). Its cumulative unit harmonic sum is bounded by \(Z_{Q,2}(C+\eta\log h)\), \(Z_{Q,2}=\prod_{p\nmid Q}(1+(\rho(p)^2-1)/p)\). Since \(V\) increases, Stieltjes partial summation from \(g=1\) proves the following complete shell estimate:
\[
 \frac1y\sum_{y_0<q\le y}|B_Q(q)| \le
 \frac{Z_Q^4 Z_{Q,2}}{G_Q(z)^2}
 [\,\eta(1-e^{-s})+Ez/y\,]
 \left(C V(L)+\eta\int_0^L V(v)\,dv\right).
\]
Dropping the remaining squarefreeness and coprimality conditions occurs only inside positive enlargements. Partition into successive shells of log thickness \(1/2\) while \(y_0>e^5z\), and use the ordered-triple bound on the final initial range. Remember the factors \(y/Y\) when normalizing each shell with respect to the final endpoint \(Y\). The code also tries a single larger shell and retains a valid minimum. Insert the result into exactly the displacement discrepancy or the smooth nonzero Fourier bound of the original wheel argument. Therefore each entire small-\(q\) range in the table pays every required phase, without an assumption on Liouville signs.

~~~powershell
python -B round8/physical_low/wheel_prefix.py --Q 223092870 --cut 200 --harmonic-limit 223092870 --tiny-log 75 --unit-small --ordered-small --selberg-small --fast-low --physical-spectrum --lower .00100665449
python -B round8/physical_low/wheel_prefix.py --Q 223092870 --cut 239 --harmonic-limit 223092870 --tiny-log 74.5 --unit-small --ordered-small --selberg-small --fast-low --physical-spectrum --lower .00060699111
python -B round8/physical_low/wheel_prefix.py --Q 223092870 --cut 263 --harmonic-limit 223092870 --tiny-log 74 --unit-small --ordered-small --selberg-small --fast-low --physical-spectrum --lower .00019461388
~~~


## Signed prefixes of the low Ramanujan sum

On a curved cell \(a\le w=X/q\le b\), the hard cutoff is \(n\le Q/w\). At fixed \(w\) the angles \(2\pi n(t/X)w/Q\) turn through at most one revolution for \(n\) in that range. Let \(N=\lfloor Q/a\rfloor\) and \(M_j(N)=\max_{v\le N}|\sum_{n\le v}n^j c_Q(n)|\) for \(j=0,1\). Abel summation and total variation at most four for the real sine or cosine over one revolution give bounds \(5M_0(N)\), \(5M_1(N)\) for the cosine sum and its sine derivative sum with the factor \(n\), respectively. Use the smaller of these and the old unsigned presums. Keep the full absolute Ramanujan weight of every discontinuity \(Q/b\le n\le Q/a\). This preserves both original hard frequency endpoints.

The optional scan initializes every \(c_Q(n)\) to \((-1)^{\omega(Q)}\) and multiplies by \(1-p\) on multiples of \(p\mid Q\). It verifies the unsigned zeroth or first moment bound before using signed 64-bit arithmetic. When the first absolute moment exceeds the chosen integer safety margin, Abel gives \(M_1(N)\le2N M_0(N)\). For exceptionally long prime wheels, write \(Q=B P\) with coprime \(B,P\) and use
\[
 c_Q(n)=\sum_{d\mid(P,n)}\mu(P/d)d\,c_B(n/d).
\]
For the base wheel \(B\), the signed zeroth moment over a full period vanishes and its first moment is \(B\varphi(B)/2\) by reflection of the classes. The first moment over \(h\) periods and a remainder \(v\) is \(h B[\varphi(B)/2+\sum_{n\le v}c_B(n)]+\sum_{n\le v}n c_B(n)\). Summing these envelopes for \(d\mid P\) gives the bounded-memory periodic scan. Similarly the unit-count discrepancy satisfies \(D_Q\le2^{\omega(P)}D_B\) by ordinary Möbius inversion, allowing the exact shorter-wheel discrepancy in the positive estimates.

In the spatial Fourier bound, \(h_2=h_1\cos a\), so on \(1\le s=1+v\le2\) the exact transform is \(I h_1\cos(av)\). Use \(I|h_1|\) on that complete band, and start the uniformly small convolution estimate at \(|s|\ge .3\), paying the actual twisted low-energy bound on \([0,.3H]\). On the \(29\#\) wheel the combined estimates give the following simultaneous cutoffs.

| \(Q\) | \(m\) | \(\log Y\) | Remaining allowance |
|---:|---:|---:|---:|
|6469693230|337|74|.00102753841|
|6469693230|401|70.7|.00098231497|
|6469693230|421|70.7|.00029668303|
|200560490130|401|70.7|.00176265174|
|7420738134810|431|70.7|.00087069311|

Each row bounds a different true presieved square; only costs computed with the same \(Q\) can be combined. The last row uses the period-based Ramanujan bound. Its remaining inequality still has \(e^{70.7}<q\le X/431\). The residual modulus span is large enough that these estimates do not prove the prime-interval assertion at \(L=116\).

~~~powershell
python -B round8/physical_low/wheel_prefix.py --Q 6469693230 --cut 337 --harmonic-limit 6469693230 --tiny-log 74 --unit-small --ordered-small --selberg-small --fast-low --physical-spectrum --exact-spectrum --signed-prefix --lower .00102753841
python -B round8/physical_low/wheel_prefix.py --Q 6469693230 --cut 421 --harmonic-limit 6469693230 --tiny-log 70.7 --unit-small --ordered-small --selberg-small --fast-low --physical-spectrum --exact-spectrum --signed-prefix --lower .00029668303
python -B round8/physical_low/wheel_prefix.py --Q 7420738134810 --cut 431 --harmonic-limit 7420738134810 --tiny-log 70.7 --unit-small --ordered-small --selberg-small --fast-low --physical-spectrum --exact-spectrum --signed-prefix --lower .00087069311
~~~


## Removing a full high-frequency band

The original smoothed \(F\) factors as the Fourier transform of its presmoothing dilation times 64 sinc factors. The dilation has total variation at most \(2S_0\) by superlevel intervals; hence for \(\kappa=\xi X\ge\kappa_1\) its transform, in the normalization \(H e^{-c}\), has bound \(M_1=\min(M,S_0 H e^{2r}/(\pi\kappa_1))\). Write \(s=2\pi\delta\kappa_1/(64X)\). For \(0<s<\pi\), the sinc envelope beyond \(s\) is at most \(R=\max(\sin(s)/s,1/4)\). This follows from monotonicity before \(\pi\), \(|\sin v|\le v-\pi\) through \(4\), and \(1/v\le1/4\) after \(4\). Apply \(64-\nu\) copies of this uniform bound and \(\nu\) copies of the inverse-linear bound, \(2\le\nu\le64\).

The absolute Ramanujan tail statement in [the original condition](REMAINING_PHASE.md), at threshold \(h>\kappa_1 Qq/X\), now bounds the entire normalized spectrum there by
\[
 2 u M_1\,2^{\omega(Q)}\eta_Q\, R^{64-\nu}s^{-\nu}
 \left[\frac{\kappa_1}{X(\nu-1)}\sum_{q\le q_0}|B_Q(q)|
                  +(1+\log q_0)^3\right].
\]
For the first positive sum use the all-shell genuine Selberg bound above with \(y=q_0\). For the second use \(\sum |B_Q(q)|/q\le(1+\log q_0)^3\). Restricting this absolute estimate to \(q>Y\) is valid. For \(Q=23\#,\ m=200,\ \kappa_1=2.5\cdot10^{17}\), the total is less than .000067041579. For \(Q=29\#,\ m=337\) it is below .000084895689.

One can also account for all \(nX/(Qq)\le j\) using exactly the same low-phase proof with integer cutoff \(jQ\). Each trigonometric prefix then turns through at most \(j\) revolutions; replace the numerical factor 5 in its signed Abel envelope by \(1+4j\). Retain all its actual jumps. For \(Q=23\#,\ m=200,\log Y=75,\ j=2\), the budget *before* this new upper-tail charge is above .0001061061590. Thus it suffices, at \(L=116\), that the **actual signed sum** over
\[
 e^{75}<q\le X/200,\qquad 2<nX/(Qq)\le 2.5\cdot10^{17}
\]
be below **.00003906457**. At the same cutoff with \(\log Y=74\), the four-sided band has allowance above .00202688664. Both are sufficient conditions; their remaining signed sums are not bounded here. A finite interior family with an actual zero coefficient in these sums is identified in [the exact Farey calculation](FAREY_RESIDUAL.md).

~~~powershell
python -B round8/physical_low/wheel_prefix.py --Q 223092870 --cut 200 --harmonic-limit 446185740 --tiny-log 75 --unit-small --ordered-small --selberg-small --fast-low --physical-spectrum --exact-spectrum --signed-prefix --lower .0001061061590
python -B round8/physical_low/spectral_tail.py --Q 223092870 --cut 200 --kappa 2.5e17 --upper .000067041579
~~~

2026-11-20. Joint project attribution to Claude and Codex.
