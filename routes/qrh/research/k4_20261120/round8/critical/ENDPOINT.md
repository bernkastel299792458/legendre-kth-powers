# Integer Hilbert bounds at the actual fourth-moment endpoint

Let \(U\le\log T\), with \(Q=210,\ \alpha=1,\ w=.04,\ Z=384\). The complete normalized fourth moment of \(\zeta(1/2+it)E_{210}(1/2+it)\) satisfies the following uniform upper bounds.

| \(U\) | [Free covariance multiplier](MULTIPLIER.md) | Integer Hilbert endpoint | Weighted integer Hilbert endpoint |
|---:|---:|---:|---:|
|35|.001140886|.001084314|.000991964|
|37|.000989248|.000943520|.000869330|
|40|.000842988|.000806232|.000750741|

## The signed upper boundary

Fix one paired sharp cutoff \(Y\) at the upper endpoint. For either AFE branch put \(\xi_j=\mathbf1_{(j,Q)=1}\) or \(c_Q(j)\) before the dual normalization, and
\[
 b_n=\sum_{\substack{ab=n\\a,b\le Y}}\xi_a\xi_b,\qquad
 z_n=b_n e^{it\log n},\qquad a_n=z_n/\sqrt n.
\]
The upper endpoint in the [paired fourth moment](../../round6/phase/SMOOTH_PHASE.md) is the average of the quadratic forms in \(a\) with kernel \(1/[i\log(n/m)]\), off the diagonal. The signed matrix with entries \(1/\log(n/m)-\sqrt{nm}/(n-m)\) has each off-diagonal entry of absolute value at most .118, by the [reciprocal-gap bound](../../round5/left/OFF_FOURTH.md). Consequently the upper-boundary contribution before time and dual normalization is at most
\[
 \left|\sum_{n\ne m}\frac{z_n\overline z_m}{n-m}\right|
    +.118\left(\sum_n |a_n|\right)^2.
\]
The second term is at most \(.118(2M\sqrt{Y_{\max}}+D)^4\), where \(M,D\) are the mean and interval discrepancy of \(|\xi_j|\). Dividing by \(Y_{\max}^2\) gives \(16(.118)(M+D/(2\sqrt{Y_0}))^4\) uniformly for \(Y_{\max}\ge Y_0\). The signed lower-boundary derivative retains its separately proved off-diagonal estimate. For the upper boundary the integer Hilbert operator has norm at most .915503 on the forward unit support and \(\pi\) on the full dual support, by the [periodic spectral proof](../../round4/hilbert/PROOF.md). Thus its contribution is bounded by that norm times the published upper envelope on \(\sum_n b_n^2\). There is no conversion from a logarithmic neighbor gap in this estimate.

## Positive weights on dual product indices

For \(p=2,3,5,7\), fix \(t_p=1.625,3.75,10.5,18\), respectively, and let \(D_r^2=\prod_{p\mid(r,Q)}t_p\). The periodic compression proof applied with these diagonal factors shows
\[
 \|DHD\|\le \frac{\pi}{Q}\lambda_{\max}(D(I+iC)D),\qquad
 C_{rs}=\csc(\pi(r-s)/Q)\ (r\ne s),\quad C_{rr}=0
\]
on all residue classes, where \(H_{nm}=1/(n-m)\) off the diagonal. Indeed its period-block multiplier is, up to multiplication by \(i\), the scalar \(\pi/Q\), and diagonal unitary conjugation, \(D(aI+iC)D\) with \(|a|\le1\). The largest eigenvalue increases with \(a\); conjugation and a change of sign bound the most negative eigenvalue by the same positive endpoint. The diagonal phase commutes with \(D\). At 160-bit Arb precision the verifier certifies
\[
 (Q\cdot117.354/\pi)D^{-2}-I-iC\succ0
\]
by 210 positive Schur pivots. Therefore the integer endpoint costs at most \(117.354\sum_n |b_n|^2/D_n^2\) on the dual branch.

Each reciprocal weight is a sum with nonnegative coefficients obtained by expanding
\[
 D_n^{-2}=\prod_{p\mid Q}
 \left(t_p^{-1}+(1-t_p^{-1})\mathbf1_{p\nmid n}\right).
\]
A term with product \(d\) of the selected primes restricts \(n\) to \((n,d)=1\). Since \(n=ab\), its entire squared coefficient sum equals the endpoint Gram calculation with both raw coefficient sequences replaced by \(\xi_a\mathbf1_{(a,d)=1}\). The preceding coefficient-envelope code applies verbatim. In its primitive ratio parametrization the outer gcd classes are still \(h,k\mid Q,\ (h,k)=1\). If \(p\mid d\) divides \(h\) or \(k\), the inner sequence vanishes. Otherwise, for \((h,k)\ne(1,1)\), some \(p\mid hk\) lies outside \(d\); in that coordinate the product of the two Ramanujan factors equals \((p-1)c_p(g)\). Its complete period mean is zero, including the restrictions away from \(p\). Hence the signed prefix finds its maximum within the first period in every nonunit case. For \(h=k=1\) the inner sequence is just the restricted nonnegative square. These are exactly the cases in the original envelope. At \(U=37\) the weighted cost is approximately .293 times the unrestricted raw endpoint Gram, compared with \(\pi\) times that Gram before weighting.

The [basic verifier](endpoint_fourth.py) and the [weighted verifier](weighted_boundary.py) use the three original short slabs, followed as needed by slabs of unit length. At every integer increment past \(U+1\) the independently valid [rational half-line](RATIONAL.md) can supply the remainder. Each reported number is the maximum over all retained slabs and the final half-line. The AFE remainder and all other integrals are restored as in the preceding complete fourth-moment proof.

~~~powershell
python -B round8/critical/endpoint_fourth.py
python -B round8/critical/weighted_boundary.py
~~~

2026-11-20. Joint project attribution to Claude and Codex. Codex derived the integer endpoint transfer and the weighted Ramanujan product estimate.
