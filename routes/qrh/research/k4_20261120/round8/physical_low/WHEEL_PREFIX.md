# Larger presieving wheels and complete physical modulus bands at \(L=116\)

Write \(Q=p\#\) for the product of all primes through \(p\). In the following computations the abscissa \(x=e^{116}\), the verified height \(H=3000175332800\), \(z=1732099\sqrt{x/H}\), positive weight \(F\), smoothing distance \(\delta=.0002 x/H\), support \((X_-,X)\), and the lower modulus cutoff \(Y=e^{70.7}\) are exactly as in [the signed-band condition](REMAINING_PHASE.md). Each change of \(Q\) uses the genuine Selberg coefficients for that \(Q\) and the genuine Ramanujan sum \(c_Q\). All primes in the leakage region exceed every prime of the wheel. The sufficient condition at cutoff \(m\) is the signed inequality
\[
 \frac{2P_0}{Q}\Re\sum_{Y<q\le X/m}\frac{B_Q(q)}q
 \sum_{1< nX/(Qq)\le (4\cdot 10^{18})m/210}
 c_Q(n)\widehat F\bigl(n/(Qq)\bigr)< \text{allowance}.
\]
The denominator 210 in the upper cutoff is fixed deliberately for comparison. The table removes genuine modulus annuli and all frequencies outside these inequalities. The inequality on the displayed remaining band is open.

| \(Q\) | \(m\) | Proved allowance above |
|---:|---:|---:|
|2310|43|.00090604766|
|30030|53|.00400862965|
|510510|67|.00515678571|
|9699690|89|.00390534618|
|223092870|97|.00483973544|
|223092870|127|.00042099453|
|223092870, three retained prime-gcd rows|131|.00007890020|

The last line includes every physically possible multiplier \(29,31,\dots,127\) coprime to \(23\#\), retains values with \(k^2\mid n=kq\), and includes all other contributions from \(q>X/131\). For \(Q=29\#,\ m=113\) the present upper estimates with the three retained rows exceed the budget by .001658.

For an independent check that does not move the Fourier boundary, keep the \(m=97\) condition and \(Q=23\#\). On the entire band \(X/113<q\le X/97\), the only possible multipliers are \(97,101,103,107,109\). The physical, joint inverse and high-tail costs are respectively below .004114004189, .000261485112 and \(3.802\,10^{-51}\). The whole signed middle there costs below **.004375489301**, inside the .00483973544 allowance. This includes all prime factorizations of \(q\). With the respective parent cutoffs \(53,67,89\), the individual complete bands \(X/59<q\le X/53\) at \(Q=13\#\), \(X/71<q\le X/67\) at \(Q=17\#\), and \(X/97<q\le X/89\) at \(Q=19\#\) cost below .001433855958, .001230533175 and .001056570058.

## Actual multiples, including repeated factors

Use [the physical slope/intercept calculation](PRESIEVED_PREFIX.md) with the primes of the requested wheel in both forced sets, the stronger convolution lower bound for \(G_Q(z)\), and, for a lower bound over a shared prime \(g\), the [actual two first lobes](WHOLE_SPIKE.md). Since \(z^2<X_-\), multiplier 1 contributes zero. The verifier checks \(X_-/k>X/m\) for every candidate \(2\le k<m\) coprime to \(Q\), hence collects complete physical contributions. At fixed \(k\), all prime gcds \(g\) are strictly below \(k\). The product of the two smallest allowed distinct primes is verified to be at least \(k\), so no composite gcd can occur. With \(A_g(q)\) denoting the sum of absolute coefficient products of exact gcd \(g\), one has \(\mu(q)B_Q(q)=A_1(q)-\sum_{p<k} A_p(q)\) on the true support. If the entire sign is certified by [the small-factor table](BOOLEAN_SIGN.md), deduct all the available prime-row lower bounds. Otherwise the first six lines of the table may simply add upper bounds for all the rows.

There is a further unconditional deduction on the actual physical counts. Let \(T\) consist of the first three permitted primes \(<k\), or all such primes if fewer. For each \(q\), set
\[
 C_T(q)= A_1(q)-\sum_{p\in T}A_p(q).
\]
Then \(C_T(q)\ge0\). Indeed, for every summand of these rows each prime of \(q\) outside \(T\) occurs on exactly one side. Fix its assignment. The remaining signed value is the level integral of the two downward-closed families on the at most three prime factors of \((T,q)\); every such pair has nonnegative signed union sum by the exact Boolean table. Sum over the assignments. Thus
\[
 |B_Q(q)|\le A_1(q)-\sum_{p\in T}A_p(q)+\sum_{p\notin T}A_p(q).
\]
The option --anchored subtracts the first three proved physical lower bounds from the \(g=1\) upper and charges all other rows. With \(Q=23\#,\ m=131\) it lowers the cost of the actual integer sums from .024546795088 to .024232938386, enough to pay the previously unpaid modulus interval \(X/131<q\le X/127\). Both computations count the integers divisible by \(k^2\).

## Small moduli with their original cutoff

Let \(\eta_Q=\varphi(Q)/Q,\ H_Q(v)=\sum_{j\le v,(j,Q)=1}1/j\). The facts \(|\lambda_d|\le1\) and \(|B_Q(q)|\le{\bf1}_{(q,Q)=1}d_3(q)\) yield
\[
 \sum_{q\le Y}|B_Q(q)|\le YZ,\qquad
 Z=3(\eta_Q+2^{\omega(Q)}Y^{-1/3})H_Q(Y^{2/3})^2.
\]
Choose a largest factor \(c\) of an ordered triple \(abc\le Y\), so \(ab\le Y^{2/3}\). The number of eligible third factors is at most \(\eta_QY/(ab)+2^{\omega(Q)}\). Sum and allow for the three choices. With \(v=Y^{2/3}>Q\), harmonic inversion and \(|H_{\lfloor u\rfloor}-\log u-\gamma|\le1/u\) for \(u\ge1\) bound \(H_Q(v)\) by
\(\eta_Q(\log v+\gamma+\sum_{p\mid Q}\log p/(p-1))+2^{\omega(Q)}/v\).

For \(Q_0\mid Q\) define \(D_{Q_0}\) as the oscillation over one period of \(\#\{1\le j\le t:(j,Q_0)=1\}-\eta_{Q_0}t\). Compute its numerator exactly by testing both sides of every integer jump. The largest modulus scanned, 223092870, has \(Q_0^2<2^{63}\), so all integer products in this pass are exact. Invert the coprimality condition from \(Q/Q_0\) by Möbius. For each divisor \(b\mid Q/Q_0\), the remaining unit sum has physical spacing \(bq\). Its centered counting discrepancy per superlevel interval is at most \(D_{Q_0}\); this survives the probability translation of the dilated original intervals. With \(M=XA/H+2\delta S_0\) and \(s=64\), its total cost at \(q\le Y\) is at most the smaller of
\[
 P_0 S_0 D_{Q_0} YZ,\qquad
 {2P_0 M Z\over Q_0 b}\zeta(s-1)
       \left({s Q_0 bY\over 2\pi\delta}\right)^s .
\]
The latter is the nonzero Poisson-mode estimate using \(|c_{Q_0}(j)|\le j\) and \(\sum_{q\le Y}|B_Q(q)|q^{s-1}\le Y^sZ\). The constant terms of the Möbius expansion sum to the required full-wheel mean. Add the smaller bound separately for each \(b\), then take the best \(Q_0\). On \(Q=23\#\) the small-\(q\) cost is below .002582457786.

## All nonzero phases \(nX/(Qq)\le1\)

The complete curved-cell Abel bound, with its cutoff jumps, is in [the full annulus estimate](WHOLE_SPIKE.md). Here its phase cutoff integer is \(Q\). For the increased number of modes use the exact identity
\[
 |c_Q(n)|=\sum_{d\mid(n,Q)}\prod_{p\mid d}(p-2).
\]
It gives both prefix sums \(\sum_{n\le b}|c_Q(n)|\) and \(\sum_{n\le b}n|c_Q(n)|\) by integer division. In particular the cut jump over a closed interval \(s\le X/q\le e\) uses just \(Q/e\le n\le Q/s\). Each interval has \(e/s\le 1.25+1/s\).

For the low-phase cells group the squarefree \(g\) into dyadic intervals \([l,h]\). On every signed norm inherited from [the Mertens calculation](EMPTY_LCM.md), replace the factor from \(g\) in \(R_\sigma(g)=\prod_{p\mid g}(1-p^{-\sigma}(p-2)/(p-1))^{-1}\) by its maximum under \(g\le h,(g,Q)=1\). This upper is the product for the largest number of successive smallest permitted primes with product at most \(h\). Each factor is decreasing for \(p\ge11,\sigma\ge1/2\), as follows by differentiating \(p^{-\sigma}(p-2)/(p-1)\). Since \(R_\sigma(Qgb)\le R_\sigma(Q)R_\sigma(g)R_\sigma(b)\), removing additional exclusions \((b,g)=1\) in the positive \(b\)-sum is safe. Through dyadic level 9 compute that sum for \(Q\) exactly. At later levels bound \(R_\sigma(b)\) by the same maximum at \(b\le2^{i+1}\) and bound the remaining positive harmonic sum by the smaller of the convolution bound for \(G_Q\) and \(Z_Q(1+\log(2^{i+1}))\), with \(Z_Q=\prod_{p\nmid Q}(1+1/[p(p-1)])\).

The absolute companion norm keeps \(h_0=10^{12}\) in the unit harmonic bound of the full annulus proof. Its effective lower endpoint is \(z/(2^{i+1}h h_0)\). Where this is below 1, or when it is sharper, the universal positive dyadic harmonic bound 2 applies to every inverted row. For the squared group weight keep exactly the intersection with
\[
 z^2/(4\cdot2^{i+j}q_{\rm hi})\le g\le z^2/(2^{i+j}q_{\rm lo}).
\]
Allow a lower integer endpoint rounded down. Sum \(\rho(g)^2/g\) on this intersection exactly up to upper limit 4000. Otherwise, with the extreme indices \(a,b\), bound it by \(\max_{g\le b}\rho(g)^2\min(\eta_Q\log(b/a)+(2^{1+\omega(Q)}+1)/a,\log(b/a)+1/a)\), using harmonic inversion on closed endpoints. On each group retain the better signed-row orientation, and give \(i\ne j\) multiplicity two. These uniform bounds avoid enumerating up to \(Q\) integers. The lower and upper frequency boundaries are disjoint from the small-\(q\) treatment by \(Y<X/Q\); restrict the absolute high-frequency bound to \(q>Y\).

~~~powershell
python -B round8/physical_low/wheel_prefix.py --Q 223092870 --cut 131 --harmonic-limit 223092870 --tiny-log 70.7 --unit-small --fast-low --anchored --lower .00007890020
python -B round8/physical_low/wheel_prefix.py --Q 223092870 --cut 97 --harmonic-limit 223092870 --tiny-log 70.7 --unit-small --fast-low --lower .00483973544
python -B round8/physical_low/wheel_annulus.py --Q 223092870 --cut 97 --start 97 --end 113 --upper .004375489301
python -B round8/physical_low/wheel_annulus.py --Q 510510 --cut 67 --start 67 --end 71 --upper .001230533175
~~~


## Three smaller actual factors and the weighted Liouville form

A sharper pointwise choice is to take \(T=T(q)\), the first three permitted primes **dividing** \(q\) among those \(<k\). For each possible prime gcd \(p\), removal of its row from the nonnegative core now requires that \(q/p\) have at least three distinct prime divisors \(r<p\). Put \(D_p(q)=A_p(q){\bf1}_{\#\{r<p:r\mid q\}\ge3}\). Then
\[
 |B_Q(q)|\le A_1(q)-\sum_{p<k}A_p(q)+2\sum_{p<k}D_p(q),\qquad
 0\le (-\mu(q)B_Q(q))_+\le \sum_{p<k}D_p(q).
\]
This also bounds the discrepancy in passing from the actual integer sum to a one-variable Liouville form whenever the multipliers are primes; \(\lambda_{\rm L}(kq)=-\mu(q)\) even if \(k\mid q\). The second inequality follows from nonnegativity of the core with these true first three factors.

For a prime gcd write \(q=p u v\) with \((u,v)=1\), and \(u,v\) coprime to \(pQ\). The verifier checks \(k\le p p_0\) for the first permitted prime \(p_0\). The auxiliary Selberg divisors \(b,t\) obey \(pbt<k\), hence \(b=t=1\), and the exact row weight is \((\rho(p)/G_Q)^2\rho(u)\rho(v)\). Any contributing exceptional row has a distinct triple \(r_1,r_2,r_3<p\) of permitted primes outside \(p\). Assign each of them to its actual side \(u=sU,\ v=tV\), so \(st=r_1r_2r_3\). By symmetry we may choose the orientation \(s\ge t\), counting the reflected assignment, and then discard further coprimality restrictions except those of a core wheel \(B\mid Q\). In particular \(\rho(sU)\le\rho(s)\rho(U)\).

For \(0<L<R\le z\), the ordinary and reciprocal \(\rho\)-weighted counts of \(B\)-units on \((L,R]\) have respective uppers \(Z_B[\eta_B(R-L)+E]\) and \(Z_B[\eta_B\log(R/L)+E/L]\), where \(E=D_B(1+\log z)\) and \(D_B\) is the exact unit-count oscillation. Expand \(\rho(n)=\sum_{j\mid n}\mu(j)^2/\varphi(j)\); the harmonic mass of this expansion is at most \(Z_B\), and the unsigned unweighted mass through \(z\) at most \(Z_B(1+\log z)\). The reciprocal result follows by ordinary Abel summation. Closed intervals can use the same bounds by a one-sided limit.

Set \(l_0=X_-/(kz),\ h=\log(z/(pl_0))\), and \(U_j=8\sum_{r_1<r_2<r_3<p}\prod_i r_i^j/(r_i-1)\) for \(j=0,1/2,1\), with all primes coprime to \(Q\). They are evaluated by the third elementary symmetric polynomial. For true \(F(k q)\), the projected outer \(U\) interval lies in \((l_0/s,z/(p s)]\). For the inner \(V\), apply the corresponding ordinary bound after each translated superlevel interval is clipped to its true range. The total physical count with the indicator in \(D_p\) is at most
\[
 P_0\left(\frac{\rho(p)Z_B}{G_Q(z)}\right)^2
 \left[\frac{\eta_B M}{kp}
       \left(\eta_B h U_0+\frac{E}{l_0}U_1\right)
       +S_0 E\left(\eta_B\frac{z}{p}U_{1/2}+E U_1\right)\right].
\]
In the first error use \(1/t\le1\); in the second use \(1/s\le 1/\sqrt{st}\). All \(2^3\) assignments are paid. Overcounting when more than three factors divide \(q\) increases this upper. Use the smallest result for \(B=210,2310,30030\) dividing \(Q\). For each \(p\), keep the better of its original absolute upper and twice this new bound minus the actual prime-gcd lower estimate. At \(Q=23\#,\ m=131\), the physical upper falls further to **.024002292137** and the remaining allowance exceeds **.00030954645**. The unbounded signed band remains open.

~~~powershell
python -B round8/physical_low/wheel_prefix.py --Q 223092870 --cut 131 --harmonic-limit 223092870 --tiny-log 70.7 --unit-small --fast-low --anchored --conditional --lower .00030954645
~~~


## Entire nonsquarefree physical subfamily

For \(Q=23\#\) and \(1\le m\le 401\), every admissible multiplier \(2\le k<m\) is prime. As \(B_Q(q)\) vanishes for nonsquarefree \(q\), the only repeated-prime case among these true physical multiples is \(k\mid q\). For \(q=g j l\) the inequalities \(g<k,\ (j,l)=1\) mean that \(k\) divides exactly one of \(j,l\). Write \(j=kJ,l=V\), and pay both orientations. Both new rows are units modulo \(Qk\), their true physical integer is \(k^2g J V\), and the added totient factor is exactly \(\rho(k)\). Keep the two auxiliary indices \(b,t\) *ordered*. In [the physical slope/intercept calculation](PRESIEVED_PREFIX.md) replace its outer interval by \(X_-t/(k^2 z)<J\le z/(gkb)\), its slope divisor by \(k^2 g\), and its finite forced sets by those with \(Qk\). The complete count of these repeated multiples in the actual prefix \(q>X/131\) is bounded in absolute mass by .000908713216, including every eligible \(k\). The cost on \(X/113<q\le X/97\) is below .000080623608. These are actual subfamilies of the physical counts already included in the main tables.

On the entire \(q>X/131\) prefix the signed identity replacing \(B_Q(q)\) by \(\mu(q)|B_Q(q)|\) has physical error below .000002814512. It follows by summing twice the smaller of the upper on \(D_p(q)\) above and the unrestricted \(A_p(q)\) upper. For each true \(n\), \(\mu(q)=-\lambda_{\rm L}(n)\), valid also in the repeated case. If the multiplier range is instead \(131\le k<401\), the entire repeated physical mass is below .000208611122 and the corresponding signed transfer error below .000063072075.

~~~powershell
python -B round8/physical_low/repeated_wheel.py --start 1 --end 131 --upper .000908713216 .000002814512
python -B round8/physical_low/repeated_wheel.py --start 97 --end 113 --upper .000080623608 .000001349559
~~~

2026-11-20. Joint project attribution to Claude and Codex.
