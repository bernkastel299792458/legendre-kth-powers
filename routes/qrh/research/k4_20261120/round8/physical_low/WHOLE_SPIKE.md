# A complete modulus annulus with an actual multiple at \(L=116\)

In [the signed middle condition](REMAINING_PHASE.md), the entire annulus \(X/29<q\le X/23\) has normalized signed cost below **.002332172**. This includes all moduli, all frequencies in the middle, all true multiples in every positive lobe, and integers \(n\) divisible by \(23^2\). There is no restriction on the prime factors of \(q\). It uses the given \(Q=210,\ X_\pm=e^{c\pm2r}, X=X_+,\ z=1732099\sqrt{e^{116}/H}\) and the compact physical weight \(F\).

| Annulus | All real multiples, signed upper | Joint main and low-mode cost, upper | Whole middle, upper |
|---|---:|---:|---:|
|\(X/29<q\le X/23\)|.002319771807|.000012399538|.002332172|
|\(X/31<q\le X/29\)|.002024399824|.000009883562|.002034284|
|\(X/37<q\le X/31\)|.001945553532|.000015567806|.001961122|

Each row is a separate constituent of the remaining sum. Adding the whole first row to the original accounting leaves only .000036428 for the other moduli. The repricing below gives a larger residual allowance.

## The actual physical count

On each row the only coprime multiplier meeting the support of \(F\) is the left table's smaller denominator \(k\). If \(n=kq\) is in the support, \(z^2/q<k\), since \(z^2<X_-<n\). The only nontrivial possible gcds of the squarefree \(d,e\) in \(B_z(q)\) are single primes when \(k<50\). Write \(A_g(q)=\sum_{[d,e]=q,(d,e)=g}|\lambda_d\lambda_e|\). Exactly,
\[
 \mu(q) B_z(q)=A_1(q)-\sum_{p<k}A_p(q),\qquad
 |B_z(q)|=\mu(q)B_z(q)+2E(q),\quad E(q)=(-\mu(q)B_z(q))_+ .
\]
Consequently the entire upper may use the \(g=1\) row only, subtracting a real lower bound for each chosen prime-gcd row and paying twice the [full wrong-sign physical mass](WRONG_SIGN.md) \(<9.043441\,10^{-8}\) in the first three annuli. For the earlier actual multipliers \(11,13,17,19\), the sign is exact since \(z^2/q<k<247/11\). These identities continue to hold if \(k\mid q\).

For \(g=1\) the procedure of [the presieved physical prefix](PRESIEVED_PREFIX.md) gives the upper slope and endpoint discrepancy. Use its exact finite small-prime conditions through 37, and its \(G_Q(z)\) replaced by the convolution lower bound from [the unit Selberg calculation](../../round7/physical/odd_sieve.py). With the physical normalizer \(P_0=(c+2r)e^r H e^{-c}/I\), multiply the slope by the full physical mass upper \(M=X A/H+2\delta S_0\) and the intercept by the summed peaks \(S_0\), as in the spline construction. At \(k=23\) the results are .002378557787 and .000001495878.

For \(g=p\) prime put \(d=pD,e=pE,\ (D,E)=1\) with \(D,E\) squarefree and coprime to \(Qp\). The actual multiplier becomes \(k p D E\), the sieve limit becomes \(z/p\), and the numerator is at least \(\rho(p)^2\rho(D)\rho(E)\) by retaining the divisor 1 in both Selberg numerators. Apply the [two-sided first-lobe squarefree row lower bound](SPIKE_FLOOR.md), with its [unit corrections](PRESIEVED_EMPTY.md), directly to \(D,E\) using modulus \(Qp\), effective spatial multiplier \(k p\), and limit \(z/p\). In this use only \(D,E\) must be coprime to \(Qp\); \(kp\) is an external multiplier. The first-lobe superlevels give lower charge
\[
 2P_0\frac{\rho(p)^2}{G_+^2}
 \left[\frac{e^{c-b/H}}{Hkp}\,S_1 A_1 - E_1\frac{\sin a}{2a}\right]_+ ,
\]
where \(b=2\pi-a\), and \(A_1,S_1,E_1\) are respectively the one-lobe area lower bound, arithmetic slope lower bound and additive count discrepancy in that proof. \(G_+\) bounds the *original* \(G_Q(z)\) from above. These charges are valid for \(F\) because \(F\) majorizes the original weight pointwise. At \(k=23\), the four deductions for \(p=11,13,17,19\) exceed .0000314148151, .0000196873226, .0000065971305, .0000027634577.

## The inverse mean and the low phases on a curved annulus

Put \(w=X/q\). Uniformly over \(t\in[X_-,X]\), the joint multiplier is
\[
 C(w,t)=\eta+\frac2Q\sum_{n\le Q/w}c_Q(n)\cos\!\left(2\pi n(t/X)w/Q\right).
\]
Use \(\eta=0\) in this expression when pricing the nonzero low modes alone. On \(a_0\le w\le b_0\), set \(M_0=|\eta|+(2/Q)\sum_{n\le Q/a_0}|c_Q(n)|\). Its total variation is at most
\[
 V_0=\frac2Q\left[\frac{2\pi(b_0-a_0)}Q\sum_{n\le Q/a_0}n|c_Q(n)|
 +\sum_{a_0 n\le Q\le b_0 n}|c_Q(n)|\right].
\]
Each mode drops at most once, and \(t/X\le1\). These estimates work with either convention at a grid endpoint. The multiplier in the inverse-only calculation is simply \(\eta\), with zero variation.

Use the [curved-cell Mertens proof](EMPTY_LCM.md) and its dyadic variables \(d=ghu,e=ghv\), where the factor \(h\) enforces \((d/g,e/g)=1\) by Möbius inversion. Omit cells whose possible products miss the annulus. In a retained cell fix \(u\). The signed \(v\) row has both endpoint contributions bounded by the normalized Mertens prefix bound; integrating the weight \(v^{-1}C\) costs in total at most the same prefix bound times
\[
 (2+\min(\log 2,\log(b_0/a_0)))M_0+V_0.
\]
Multiply by the existing \(V_{g,j}\) norm for the signed row and use Cauchy over \(h\). The norm used here includes the earlier finite Mertens mean table, including its low-argument remainder and the excluded conductor \(Qgb\).

The other row keeps its restriction to the units modulo \(210\). For \(h\le h_0=10^{14}\) the lower endpoint in the \(i\)-th row is at least \(L=z/(2^{i+1}g h_0)>1\). From the elementary unit harmonic bound in [the sign calculation](WRONG_SIGN.md), its \(\mu^2(u)\rho(u)/u\) mass is at most
\[
 D_i=Z_Q[\eta\log2+33(1+\log z)/L],\qquad
 Z_Q=\prod_{p\nmid Q}\left(1+\frac1{p(p-1)}\right).
\]
For \(h>h_0\) use the old uniform dyadic bound 2. Accordingly the absolute-row norm is at most
\[
 \left(\sum_{\substack{b<2^{i+1}\\(b,gQ)=1}}\frac{\mu^2(b)}{\varphi(b)}\right)
 \left[P_Q D_i^2+4 h_0^{-1/2}\exp\!\left(\frac{2(11/10)^2}{\sqrt{10}}\right)\right]^{1/2},
 \quad P_Q=\prod_{p\nmid Q}(1+(p-1)^{-2}).
\]
Indeed the large-\(h\) squared weight is bounded by \(h_0^{-1/2}\prod_{p\ge11}(1+\rho(p)^2/p^{3/2})\), with the displayed integral upper on its log. Use the cheaper orientation in each dyadic cell, and multiply each result by \(\rho(g)^2/(gG_Q(z)^2)\). The total coefficient is then multiplied by \(P_0 M\). The high-frequency remainder is bounded by \(2.03\,10^{-13}\) in each of the three whole signed rows.

~~~powershell
python -B round8/physical_low/whole_spike.py --k 23 --end 29 --upper .002332172
python -B round8/physical_low/whole_spike.py --k 29 --end 31 --upper .002034284
python -B round8/physical_low/whole_spike.py --k 31 --end 37 --upper .001961122
~~~

## Updated \(L=116\) sufficient inequality

For the original cutoff 23 the four possible physical multiples together cost at most .012019841894. The signed inverse mean over \(q>X/23\) costs at most .000009069887 and all nonzero low phases on \(q\le X/23\) at most .000038688064. The latter follows by adding disjoint \(w\)-intervals with endpoints \(23,29,36,46,59,75,94,119,150,185,210\), applying the preceding sign estimate without the constant \(\eta\). At larger cutoffs retain the remaining applicable endpoints. The underlying ordinary mean, remote terms, extra physical area, upper diagonal tail and \(q\le e^{70.7}\) terms remain as in the original [signed middle inequality](REMAINING_PHASE.md). The new cost bounds already use the full enlarged physical mass.

| Cut \(m\) | Whole actual prefix | Mean on the prefix | Low phases below the prefix | Sufficient allowance still open |
|---:|---:|---:|---:|---:|
|23|.012019841894|.000009069887|.000038688064|.0041616408|
|29|.014339613700|.000009388826|.000031755535|.0018484826|

At cut \(m\) the remaining sum has \(e^{70.7}<q\le X/m,\quad 1<nX/(Qq)\le (4\cdot10^{18})m/Q\), and the same normalization and positive weight. The entire first wide annulus is thus paid inside a single global budget at \(m=29\). The cutoff 31 upper estimate presently exceeds the total budget by .000170110.

~~~powershell
python -B round8/physical_low/repriced_prefix.py --cut 23 --lower .0041616408
python -B round8/physical_low/repriced_prefix.py --cut 29 --lower .0018484826
~~~
