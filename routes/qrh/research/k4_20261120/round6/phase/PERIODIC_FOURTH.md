# Fourth moment with the same cutoff for every Euler term on each side

Let \(Q=6\) or \(30\), \(E_Q(s)=\prod_{p\mid Q}(1-p^{-s})\), \(s=1/2+it\), \(z=\sqrt{t/(2\pi)}\), \(a=\alpha\sqrt Q,\ b=Q/a\). For \(t\ge1000\) and \(x,y\ge1,\ xy=t/(2\pi)\), Simonič's explicit asymmetric approximate functional equation has error at most \(16\min(x,y)^{-1/2}\) at \(\sigma=1/2\). The theorem permits real \(x,y\) with the indicated product; the truncations use \(n\le x,\ m\le y\), also at an integer. Its multiplier is the common functional-equation factor \(\chi(s)\) of modulus one. [Simonič, Theorem 4, equation (8) and Table 2](https://arxiv.org/pdf/1910.08274#page=4)

For each \(d\mid Q\), take \(x_d=az/d,\ y_d=dz/a\), multiply the formula by \(\mu(d)d^{-s}\), and sum. The forward variable \(n=dj\) then always has cutoff \(az\), while the dual variable \(m=Qj/d\) always has cutoff \(bz\). The resulting identity with an explicit remainder is
\[
 \zeta(s)E_Q(s)=\sum_{n\le az,(n,Q)=1}n^{-s}
 +\chi(s)Q^{-s}\sum_{m\le bz}c_Q(m)m^{s-1}+{\cal R},
 \qquad |{\cal R}|\le K t^{-1/4},
\]
\[
 c_Q(m)=\sum_{e\mid(Q,m)}e\mu(Q/e),\qquad
 K=16(2\pi)^{1/4}\sum_{d\mid Q}d^{-1/2}
             \max(\sqrt{d/a},\sqrt{a/d}).
\]
The scalar outside the dual polynomial has modulus \(Q^{-1/2}\). In particular all of its raw real coefficients are the periodic Ramanujan sums. The code checks \(x_d,y_d\ge1\) at its lower cutoff. For the two ranges \(0\le t\le200\) and \(200\le t\le1000\), use respectively \(403\) and \(17\) for \(|\zeta(1/2+it)|\); the latter follows from the symmetric Riemann–Siegel inequality and \(\sum_{n\le y}n^{-1/2}\le2\sqrt y\). Multiplication costs \(\prod_{p\mid Q}(1+p^{-1/2})\) on these two ranges. [Riemann–Siegel remainder used in the preceding certificates](../../round3/critical/PROOF.md)

## Positive bounds for both diagonals

For either polynomial write \(v(n)=\mathbf1_{(n,Q)=1}\) or \(c_Q(n)\), \(Y=\sigma\sqrt{T/(2\pi)}\), where the length multiplier \(\sigma\) equals \(a\) or \(b\). At a single time with cutoff \(y\), the diagonal is
\[
 \sum_{(r,s)=1}\frac{1}{rs}
 \left(\sum_{g\le y/\max(r,s)}\frac{v(gr)v(gs)}g\right)^2 .
\]
This is the usual parametrization of equal products by two independent common factors and the coprime ratios \(r,s\). For \(h=(r,Q),\ k=(s,Q)\), keep \((h,k)=1\) and relax further coprimality. The inner sequence \(w(g)=v(gh)v(gk)\) depends only on the class pair. For the dual polynomial it factors locally over primes. If either \(h\) or \(k\) is divisible by \(p\mid Q\), exactly one is divisible, so its local factor has mean \((p-1)\sum_{j\bmod p}c_p(j)/p=0\). When \(h=k=1\), \(w=c_Q^2\) is nonnegative. For the forward polynomial only the unit/unit class can contribute, with \(w=\mathbf1_{(g,Q)=1}\).

Set \(H_w(x)=\sum_{n\le x}w(n)/n\). For any periodic real \(w\), let \(m_w=Q^{-1}\sum_{j\bmod Q}w(j)\) and
\[
 c_w=-Q^{-1}\sum_{j=1}^Q w(j)[\psi(j/Q)+\log Q].
\]
Then \(|H_w(x)-m_w\log x-c_w|\le K_w/x\), where \(K_w=2\sup_x|\sum_{n\le x}w(n)-m_w x|\). The constant follows by splitting into progressions and using \(\psi(y)=\log y+o(1)\); the endpoint and integral parts of the counting error each cost at most \(K_w/(2x)\). The supremum of the periodic piecewise affine error is found from integer points and their left limits.

The cumulative outer pair mass is \(H_h(x)H_k(x)\) for the two class indicators. Its convolution with the squared inner sum gives the diagonal of this class, where the outer cumulative counts \(\max(r,s)\). For each cumulative mass construct a positive dominating measure as follows. Through \(Z=96\) compute the exact harmonic fractions and the nonnegative jumps. For the signed zero-mean inner sum take the running maximum of its square. For \(x\ge Z\), a product \(H_f(x)H_g(x)\) of nonnegative harmonic sums has upper cumulative
\[
 (m_f\log x+c_f)(m_g\log x+c_g)+
 \frac{K_f(m_g\log Z+|c_g|)+K_g(m_f\log Z+|c_f|)+K_fK_g/Z}{Z}.
\]
This follows from the preceding endpoint bounds and \((\log x)/x\) decreasing. At \(Z\) add the positive gap to the exact cumulative. Its continued density in \(d\log x\) is nonnegative as checked at \(Z\) and has nonnegative slope. In a signed zero-mean inner class use the maximum of the running peak and \((|c_w|+K_w/Z)^2\) for the constant upper cumulative on \(x\ge Z\). Both steps give a genuinely nondecreasing majorant. Integrate either cumulative upper bound against the other positive measure to obtain an upper convolution, by layer-cake order for positive measures.

Write \(z_0=\log Z,\ \ell=\log y\). For the first and second dominating measures let \(m,n,k\) and \(M,N,K\) be the zeroth, first and second log moments of their finite atoms up to \(Z\), including the extra atom at \(Z\). Their additional cumulative tails at \(Ze^v\) are \(A v+a'v^2\) and \(B v+b'v^2\). At \(y\ge Z^2\), put \(l=\ell-z_0,\ p=\ell-2z_0\). The convolved cumulative is
\[
 mM+B(ml-n)+b'(ml^2-2nl+k)+A(Ml-N)+a'(Ml^2-2Nl+K)
 +ABp^2/2+(a'B+Ab')p^3/3+a'b'p^4/6.
\]
Here finite atoms times continuous density give the middle terms, and the final three integrate \((A+2a'x)(B(p-x)+b'(p-x)^2)\) on \(0\le x\le p\). Summing the class polynomials gives the raw diagonal \(P(\log t)\). Below \(T_*=2\pi Z^4/\sigma^2\), the true diagonal is bounded by \(\|v\|_\infty^4(1+2\log Z)^4\). The normalized uniform correction for extending \(P\) to the whole integration interval is at most \(T_*e^{-U}[\|v\|_\infty^4(1+2\log Z)^4+\sum_j |P_j|(\log T_*)^j]\).

## Shift contributions for a periodic row

For \(Y=\sigma\sqrt{T/(2\pi)}\), write \(\tau=|v|\), \(m\) for its periodic mean, \(D\) for its interval discrepancy, \(G=(i,k)\), \(M=\max(i,k)\), with \(i,k\) the outer raw indices. Each fixed quadruple is active on one real interval. The inequality
\[
 (\sqrt{ab}\log(a/b))^{-1}\le (a-b)^{-1}+.118/\sqrt{ab},\quad a>b,
\]
and the two-orientation factor \(4\) are justified in the [fourth-moment shift calculation](../../round5/left/OFF_FOURTH.md). Dropping \(1/G\le1\) and counting periodic classes by enclosing lattice squares gives
\[
 Y^{-2}\sum_{i,k\le Y}\tau(i)\tau(k)/G
       \le F=m^2(1+Q/Y_0)^2,\quad
 Y^{-2}\sum_{i,k\le Y}\tau(i)\tau(k)Y/M
       \le S=m^2[2+(4Q(1+\log Y_0)+4Q^2)/Y_0],
\]
where \(Y_0=\sigma\sqrt{e^U/(2\pi)}\). For the second inequality integrate the square counts at level \(M\le t\) against \(dt/t^2\), as in the cited calculation. The aggregate class weight is \(m^2\), the integral of \(1/\max(x,z)\) on the unit square is 2, and expanding by \([-Q,Q]^2\) costs at most \(4Q\min(t,Y)+4Q^2\).

For \(0<h=ij-kl\le GY\), the remaining \(j,l\) lie on a line of step lengths \((k/G,i/G)\). For \(w=h/G\bmod Q\), the weights on its integer parameter have period \(Q\), discrepancy \(d_w\), and mean \(r_w\). The sum of weights is at most \(d_w+r_wYG/M\). Every pair of reduced steps with triple gcd one mod \(Q\) is tested, and the period's \(Q\) shifts are precisely the solutions of the congruence. The mean over \(w\) of \(r_w\) equals \(m^2\). For each residue \(1\le j\le Q\), the upper harmonic endpoint constant
\(\kappa_j=\sum_{k=0}^{15}(j+kQ)^{-1}-\log(j+15Q)/Q\)
bounds the excess over \(\log Y/Q\), by integral comparison for \(Y\ge16Q\). Take \(D_0,D_1,R_1\) to dominate over all reduced step pairs the mean of \(d_w\), \(\sum_w d_w\kappa_w\), and \(\sum_w r_w\kappa_w\). The small-shift contribution divided by \(Y^2\) is at most
\[
 F(D_0\log Y+D_1)+S(m^2\log Y+R_1).
\]
For \(h\ge GY\), fix the inner variable multiplying the smaller outer index. The absolute weight of all its choices is at most \(mY+D\). For the remaining variable use the interval discrepancy in a layer-cake estimate against \(1/h\); this gives \(m\log Y/M+D/(GY)\), as \(h\le Y^2\). The normalized bound is \(F(mD+D^2/Y_0)+S(m^2+mD/Y_0)\log Y\). The .118 remainder for both orientations together divided by \(Y^2\) is at most \(32(.118)(m+D/(2\sqrt{Y_0}))^4\), using \(\sum_{j\le Y}\tau(j)/\sqrt j\le2m\sqrt Y+D\).

## Normalization

With the off-diagonal and early-time contributions added, integrate the diagonal polynomial from \(1000\) to \(T\) using its four-derivative antiderivative. Take positive coefficient parts to freeze \(U\le\log T\), and divide the raw dual fourth moment by \(Q^2\). Minkowski for the forward, dual and error terms gives the function **fourth** in [periodic_fourth.py](periodic_fourth.py).

At \(U=40,\alpha=3/2\), the resulting normalized fourth-moment upper constants are \(0.003660035\) for \(Q=6\) and \(0.002192887\) for \(Q=30\). Both apply at every \(T\ge e^{40}\). Recompute with **python -B periodic_fourth.py --q 6 --alpha 1.5** and **python -B periodic_fourth.py --q 30 --alpha 1.5**.
