# Every three-prime modulus at the upper end of the signed middle

At \(L=116,\ Q=210,\ X=e^{c+2r}\), the whole middle contribution of every modulus with three prime factors in \(X/200<q\le X/23\) is less than **.001852669**. All prime-size ratios are included. Adding the [two-prime estimate](FEJER_PRIMES.md) gives a signed upper **.002348699** for the union, within the sufficient .00236860 for the entire remaining sum. At \(X/180\) the joint cost is less than .002175023. These statements leave the other moduli and lower parts of the two bands unresolved. The normalized quantity and Fourier cutoffs are those of [the remaining problem](REMAINING_PHASE.md).

## Sign of the real multiple count

For squarefree \(d\) coprime to \(Q\), put \(A_d=|\lambda_d|=\rho(d)G_{Qd}(z/d)/G_Q(z)\), with \(\rho(d)=d/\varphi(d)\) and \(G_M(y)=\sum_{n\le y,(n,M)=1}\mu^2(n)/\varphi(n)\). Set \(A_d=0\) for \(d>z\). If \(p\nmid Qd\), splitting the terms according to \(p\mid n\) gives
\[
 G_{Qd}(z/d)=G_{Qdp}(z/d)+(p-1)^{-1}G_{Qdp}(z/(dp))
 \ge \rho(p)G_{Qdp}(z/(dp)).
\]
Consequently \(A_{dp}\le A_d\). Repeated prime factors cannot occur in the lcm of the squarefree-supported coefficient pairs. For \(q=abc>z\) with three distinct admissible primes,
\[
 B_z(q)/2=A_{ab}A_{ac}+A_{ab}A_{bc}+A_{ac}A_{bc}
 -A_a A_{bc}-A_b A_{ac}-A_c A_{ab}.
\]
The three positive terms are bounded respectively by \(A_cA_{ab}, A_aA_{bc}, A_bA_{ac}\), so \(B_z(q)\le0\) and
\[
 -B_z(q)\le2(A_aA_{bc}+A_bA_{ac}+A_cA_{ab}).
\]
The physical count multiplied by \(B_z(q)\) is nonpositive for every such modulus. The sufficient upper cost is therefore the *reverse* mean-plus-low-frequency correction plus the uniform upper bound for the removed high frequencies. At \(q\le X/23\) the joint weight
\[
 C(q,v)=\eta+\frac2Q\sum_{1\le n\le Qq/X}c_Q(n)\cos\left(\frac{2\pi n v}{Qq}\right)
\]
is positive since \(\eta=48/210\) and \(\sum_{n\le9}|c_Q(n)|=20\). In particular the bound on \(-B_z(q)\) can multiply \(C(q,v)\). Use \(X_-\le v\le X\) over the support of the physical window and the upper mass \(XA/H+2\delta S\).

## Product cells and prime rows

For \(X/m<q\le X/23\) the displayed three pairings become a single positive sum over a semiprime \(d=p_1p_2\) and a prime \(b\). The factor two in the upper bound remains. The conditions \(d,b\le z\) and \(z^2<X\) give \(d,b>z/m\). Divide \([z/m,z]\) logarithmically into equally spaced cells. For a \(d\)-cell \((l,h]\), intersect the \(b\)-cell with \([X/(mh),X/(23l)]\); using both endpoints in an upper bound is safe. On each projected rectangle bound \(C(db,v)\) term by term, including zero among the possible values if the mode \(n\) is not always present. At most nine modes can occur in the true region. Apply \(G_{Qd}(z/d)\le G_Q(z/l)\) and the corresponding prime-row value at its lower endpoint. These last sums have arguments \(\le m+1\) and are evaluated directly.

The harmonic sum \(\sum_{a\le p\le b}1/p\) is at most
\[
 H(a,b)=[\log(b/a)+2E(b)/a]/\log a+1/a,\qquad E(b)=\sqrt b\log^2 b/(8\pi),
\]
on the applicable finite range \(599\le a\le b\le2.169\,10^{25}\). The last term handles any closed endpoint. This follows by partial summation of [Johnston, Proposition 3.1](https://arxiv.org/pdf/2109.02249). Hence the projected single prime row is bounded by \(aH(a,b)/(a-1)\). For the semiprime row write \(p=p_1\le\sqrt h\), and permit all primes \(s=p_2\in[l/p,h/p]\), including ones with \(s\le p\) for a positive enlargement. Put \(p\) in an integer dyad \((p_0,p_1]\); in the following formula truncate \(p_1\) to \(\sqrt h\) if necessary. Write \(s_0=l/p_1\). Uniformly in this group the sum of \(1/(s-1)\) over the inner row is at most
\[
 \frac{s_0}{s_0-1}\left[
   \frac{\log(h/l)+\sqrt{p_1 h}\log^2(h/p_0)/(4\pi l)}{\log s_0}+1/s_0
 \right].
\]
Multiply by the group sum of \(1/(p-1)\) and add over dyads. Admissible primes \(p\le65535\) are enumerated exactly, above which the group sum is bounded by \(p_0H(p_0,p_1)/(p_0-1)\) using the untruncated right endpoint. Every unordered semiprime occurs at least once; excess ordered pairs or a repeated prime only enlarge the bound. The program reuses the uniform absolute high-mode remainder (\(<2.03\,10^{-13}\)) independently for this family.

| \(m\) | Cells | All three-prime signed upper |
|---:|---:|---:|
|121|96|.001318327|
|180|144|.001722348|
|200|144|.001852669|
|230|144|.002034909|
|400|96|.002866960|
|1100|96|.004734130|

~~~powershell
python -B round8/physical_low/all_triprime.py --end 200 --cells 144 --upper .001852669
python -B round8/physical_low/semiprime_annulus.py --end 200 --cells 64 --fejer --upper .000496031
~~~

For sums of the rows the reported .002348699 uses the bounds .001852668488332 and .000496030188645. Alternatively, add the two upward roundings to the last value shown in each command for the slightly weaker <.002348700.

## One prescribed small factor

If the smallest prime is fixed to \(\ell\) and the other factors \(p,r\) satisfy \(pr>z\), the exact magnitude divided by two is \(A_{\ell p}A_r+A_pA_{\ell r}-A_{\ell p}A_{\ell r}\). In each cell use the separate upper bounds for these four weights, enlarging the \(A_p,A_r\) bounds if necessary to keep \(A_{\ell p}\le A_p\), \(A_{\ell r}\le A_r\) in the numeric bounds. This expression is increasing componentwise within that cone. The excluded prime \(\ell\) is retained in each \(G_{Q\ell}\) numerator. Integrating this sharper coefficient against the same upper \(C\), with both projected prime-axis intersections and both prime harmonic upper bounds, yields the true signed upper .000699043 at \(m=1100\) for \(\ell\) any of the following primes. The inequalities in the verifier ensure that \(pr>z,\ \ell<\min(p,r)\) on all the priced cells and actual tuples.

~~~powershell
python -B round8/physical_low/triprime.py --end 1100 --cells 72 --small 11 13 17 19 23 29 31 37 41 43 47 --upper .000699043
~~~
