# Uniform short-height counts on the .865 rectangle

Assume QRH(7/8), let \(H=3000175332800,\ T=H\exp(7/4)\), and count with multiplicity all zeros of real part at least \(s=.865\). Every closed interval \(I\subset[H,T]\) of the indicated width has the following count.

| Width \(w\) | Upper bound on count | \(A\) | \(X\) | \(D\) | \(b\) |
|---:|---:|---:|---:|---:|---:|
| \(10^9\) | 1,002,859 | 47 | 250000 | 4 | .27 |
| 116,000,000 | 420,044 | 42 | 65000 | 3.2 | .48 |
| \(10^8\) | 395,544 | 42 | 65000 | 3.2 | .48 |

In particular, failure of the [second true rectangle](../../round6/reduction/OBSTRUCTION.md) requires its first and last exceptional ordinates to differ by over **116,000,000**. The earlier threefold six-rectangle test population places \(3\cdot420071=1260213\) exceptional ordinates in \([T-10^9,T]\). **No rearrangement within that support satisfies this additional zeta inequality.** An alternative scalar population can spread the same points equally in \([T-2\cdot10^9,T]\). The preceding \(1/16\)-log-height node is more than \(10^{12}\) below \(T\); hence the older finite-node counts and the other five populations are unchanged. Every interval of width \(10^9\) then sees at most 630108 of these points, and an interval of width 116,000,000 sees fewer than 74000. The other five populations in that example have real parts strictly below .865. Thus this support restriction by itself still leaves a global count problem.

## From the positive kernel to a cubic moment

Use \(c=1.4,\ \lambda=.4,\ \Theta=7/8\) and the polynomial \(J_A\), profile \(q_A\), and positive reflected-kernel inequality in [the right-edge calculation](RIGHT_EDGE.md). The present verifier checks that same pointwise kernel inequality again at \(A=42,47\). Write
\[
 v(p^k)=\log p\,[p^{-k\Theta}(1-k\log p/A)-\lambda p^{-kc}],
 \qquad p^k\le e^A .
\]
Charge a total \(P\) for all powers of \(p=2,3,5\) and the powers \(p^k,\ k\ge2\) at the other primes. For each of 2, 3, 5, the maximum negative real part of its finite trigonometric sum is bounded on 256 equal phase intervals in \([0,\pi]\) by the endpoint samples plus \((\pi/512)\sum_k k|v(p^k)|\); symmetry extends this to every phase. For \(5<p\le X\) sum absolute values of all the higher powers. For \(p>X\), sum instead over all integers \(n>X\), bounding their higher powers in absolute value by \((1+\lambda)(\log n)n^{-2\Theta}/(1-X^{-\Theta})\). The integral test bounds this last tail, since \((\log x)x^{-2\Theta}\) decreases in the range in use.

Put \(Z(t)=-\sum_{5<p\le X}v(p)p^{-it}\) and \(L(t)=-\sum_{X<p\le e^A}v(p)p^{-it}\). Write \(E=I+[-2/A,2/A]\), \(\ell=w+4/A\). Then
\[
 [-J_A(t)-D-P]_+\le [\Re Z(t)-D]_++|\Re L(t)|.
\]
For every complex \(z\), \(D,b>0\), the first term is bounded by \(4|z+b|^3/[27(D+b)^2]\) at \(z=Z(t)\). Indeed, for \(x=\Re z>D\) the maximum of \((x-D)/(x+b)^3\) occurs at \(x+b=3(D+b)/2\).

For a polynomial \(F(t)=\sum a_n n^{-it}\) supported on positive odd \(n\), the generalized Hilbert inequality implies
\[
 \int_E|F(t)|^2dt\ \le\ (\ell+4.2)\sum|a_n|^2+4.2\sum n|a_n|^2 .
\tag{1}
\]
The minimum spacing of a frequency \(\log n\) from the other frequencies is at least \(\log(1+2/n)\ge 2/(n+1)\), including \(n=1\) when present. The two time endpoints each cost at most \((4\pi/3)\sum |a_n|^2/\delta_n\) in the integrated quadratic form. Since \(4\pi/3<4.2\), this gives (1). The bound is unchanged on the doubled frequency set \(\{\pm\log p:p>X\}\), since the additional gaps are at least \(2\log X\). Thus for a real-part prime sum the right side of (1) has the extra factor \(1/2\), coming from its two coefficients \(v(p)/2\). See [Preissmann, generalized Hilbert inequality](https://www.e-periodica.ch/cntmng?pid=ens-001%3A1984%3A30%3A%3A30) and the [local statement of the constant](../../round3/low/FAREY.md).

Let \(d_j=\sum_{5<p\le X}p^j|v(p)|^2\), \(j=0,1\). Unique factorization separates the coefficients of \(Z^k\) from those of \(Z^{k'}\) if \(k\ne k'\). For a fixed product of \(k\) primes there are at most \(k!\) orderings. Cauchy–Schwarz therefore bounds the two coefficient sums in (1), for \(F=(Z+b)^3\), by \(M(d_0),M(d_1)\), respectively, where
\[
 M(z)=\sum_{k=0}^3 {3\choose k}^2 b^{6-2k} k! z^k .
\]
Writing \(U_j\ge\sum_{p>X}p^j |v(p)|^2\) with the finite cutoff understood, Minkowski gives the bound
\[
 \|[-J_A-D-P]_+\|_{L^2(E)}\le
 \frac4{27(D+b)^2}\sqrt{(\ell+4.2)M(d_0)+4.2M(d_1)}
 +\sqrt{[(\ell+4.2)U_0+4.2 U_1]/2}.
\tag{2}
\]

## Bounding the long-prime sum and collecting the zero contributions

Set \(u=\log X,\ k_j=1-2\Theta+j,\ G(v)=(1-v/A)^2+\lambda^2\exp(-2(c-\Theta)v)\). Since \(v\le A\), the two terms in the signed coefficient subtract and its square is bounded by the sum of their squares. The resulting sum is a Stieltjes integral of \(f_j(x)=(\log x)x^{k_j-1}G(\log x)\) against \(\vartheta(x)\) on \((X,e^A]\). This integrand is decreasing, since \(G\) decreases on \([u,A]\) and \((\log x)x^{k_j-1}\) decreases for these \(X\) and both \(j\). For \(C_0=1.01624\), use \(\vartheta(x)\le C_0x\) and the exact finite \(\vartheta(X)\). Partial summation yields
\[
 U_j=C_0\int_u^A v e^{k_jv}G(v)\,dv+[C_0X-\vartheta(X)]f_j(X).
\]
The integral is bounded above on 4096 equal cells by the right endpoint of the first factor, the larger endpoint of the exponential, and the left value of \(G\). The arithmetic input is [Rosser and Schoenfeld, Theorem 9, (3.32)](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf).

For \(R\) zeros in \(I\), positivity and superadditivity from [the right-edge proof](RIGHT_EDGE.md) give
\[
 \|[-J_A-D-P]_+\|_{L^2(E)}^2
 \ \ge\ 2R\int_0^{2/A}[q_A(y)-D-P]_+^2dy.
\tag{3}
\]
In detail, subtract the same nonnegative threshold from the sum of all positive pair contributions. The positive part squared dominates the sum of each individual excess squared. Integrating on \(E\) includes every root's full subinterval \(\gamma+[-2/A,2/A]\), also for roots on either endpoint of \(I\). The enlargement stays inside \([H-1,T+1]\) where the gamma and pole errors have been bounded. The verifier sums the decreasing integrand by 512 lower rectangles. For the first row the two terms of (2) are below 569.751 and 985.155, while the single-zero cost in (3) exceeds 2.410835. The resulting unrounded caps in the three rows are below \(1002859.358,\ 420044.468,\ 395544.084\), respectively.

~~~sh
python -B round7/qrh_strip/increment.py
~~~
