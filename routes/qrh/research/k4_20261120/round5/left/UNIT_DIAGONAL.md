# The filtered fourth-moment diagonal

With the notation of [the diagonal decomposition](PROOF.md), let \(A=\{n:(n,6)=1\}\), \(H(t)=\sum_{n\le t,n\in A}1/n\), \(d=1/3,\ c=(\gamma+\log2+\frac12\log3)/3,\ k=4/3\). We use its established inequalities \(H(t)\le1+d\log t\) and \(|H(t)-d\log t-c|\le k/t\) for \(t\ge1\). Write \(y=\sqrt{t_{\rm time}/(2\pi)}\), \(\ell=\log y\). The original gcd diagonal is a sum of squares of inner signed harmonic sums. We replace the pure bulk, near-ratio, and far-ratio upper estimates separately.

## Pure bulk

In the bulk piece the outer coefficients are \(r,s\in A\), \((r,s)=1\), and the inner coefficient is \(H(y/\max(r,s))\). First drop the outer gcd restriction and denote the resulting positive sum by \(B(y)\). The cumulative mass of the measure of \(\max(r,s)\), with weights \(1/(rs)\), equals \(V(x)=H(x)^2\). Consequently \(B(y)\) is exactly the cumulative mass of the multiplicative Stieltjes convolution \(dV*dV\) through \(y\). Requiring only that \(r,s\) have no common divisor among \(5,7,11\) yields the upper bound
\[
  \sum_{m\mid385}\frac{\mu(m)}{m^2} B(y/m)
\]
for the bulk with its true gcd condition. In fact the condition \(m\mid r,s\) rescales the two outer integers while preserving membership in \(A\).

Fix \(Z=48,\ z=\log Z,\ H_0=dz+c\). For \(x\ge Z\),
\[
 |V(x)-(d\log x+c)^2|\le \varepsilon=k(2H_0+k/Z)/Z .
\]
The original error before freezing decreases on this domain, since \(H_0>d\). Construct two positive measures. For the upper measure retain all exact atoms of \(V\) through \(Z\), then add mass \(H_0^2+\varepsilon-V(Z)\) at \(Z\). For the lower measure multiply all atoms through \(Z\) by \((H_0^2-\varepsilon)/V(Z)\). Above \(Z\) both have density \(2d(d\log x+c)dx/x\). Thus their cumulative masses bound \(V\) from the two sides at every argument. This ordering is preserved under convolution of positive measures. In each factor integrate the nonnegative decreasing function of its variable induced by the cumulative mass in the other factor, or use the layer-cake formula.

For either finite atomic part let \(M_i=\sum w_n(\log n)^i\), \(0\le i\le2\). At \(y\ge Z^2\), write \(l=\ell-z\), \(p=\ell-2z\). The convolution of its measure with itself through \(y\) equals
\[
 M_0^2+
 2\{2H_0d(M_0l-M_1)+d^2(M_0l^2-2M_1l+M_2)\}
 +2H_0^2d^2p^2+\tfrac43H_0d^3p^3+\tfrac16d^4p^4 .
\]
The three pieces respectively count two atoms, one atom and one continuous variable, and two continuous variables. The last integral equals \(\int_0^p 2d(H_0+dx)[2H_0d(p-x)+d^2(p-x)^2]dx\). At an admissible integer \(n\) the exact atom of \(V\) is \(2H(n-1)/n+1/n^2\). The script combines the upper polynomial on positive sieve terms and the lower one on negative terms. It obtains a bulk majorant \(P(\log t_{\rm time})\) for \(y\ge385 Z^2\).

Put \(t_* = 2\pi(385Z^2)^2\). Below this threshold the original bulk is bounded by \(H(385Z^2)^4\le(1+d\log(385Z^2))^4\). Continuing \(P\) for the antiderivative used in [the normalization](../../round4/density/sieved_fourth.py) is valid after adding to the normalized integral the cost
\[
 \frac{t_*}{e^U}\left[(1+d\log(385Z^2))^4+
            \sum_j |P_j|(\log t_*)^j\right].
\]
This covers the entire interval \([200,t_*]\). If \(e^U\le t_*\), the script uses the published bulk bound instead.

## Harmonic tails sampled on their exact steps

Retain the quantities \(T_h,F_h,B_h,e_{X,h},c_h,\rho_h\) of the [diagonal proof](PROOF.md). Here \(T_h(t)\) is an unsigned sum over the allowed tail bands with arbitrary inner residue; \(F_h(t)\) is the signed tail restricted to inner units. On \(1/6\le t<R=96\) each has rational constant values on half-open intervals \([a,b)\). For an integer \(n\) in a physical band \((a_0,b_0]\), add its signed mass at \(t=n/b_0\) and remove it at \(n/a_0\). All contributing indices satisfy \(n\le6R\). For \(t\ge R\), denote by \(B_h^\infty,L_h^\infty\) the upper bounds supplied by summing the signed continuous contributions of the bands then charging \(1/(a_0 R)\) per residue and band. The residue-class harmonic error follows by partial summation with interval discrepancy one. The global upper bound for \(T_h\) remains the previously established \(B_h\).

On a fixed piece \(a\le y/s<b\), the condition on \(s\) is \(y/b<s\le y/a\), with \((s,6)=h\). Its weighted \(1/s\) mass is at most \(\rho_h\log(b/a)+2b/y\) by partial summation, since the class count on each interval has discrepancy at most two. For the step functions
\[
 f=T_h^2\quad\hbox{or}\quad F_h^2
\]
on \([1/6,R)\), and \(f=H T_1\) on \([1,R)\), define
\[
 I_f=\rho_h\sum_{[a,b)} f(a)\log(b/a),\qquad E_f=2\sum_{[a,b)} b f(a).
\]
The last function also has the unit-integer jumps of \(H\), included in the event list. Each \(f\) is nonnegative. Thus \(I_f+E_f/y\) bounds the respective sampled harmonic sum on the compact region, including all endpoint cases. The code freezes \(1/y\le1/10^6\). For \(y/s\ge R\), the harmonic mass of class \(h\) through \(y/R\) is at most \(J_h=c_h+\rho_h(\ell-\log R)\).

The near-ratio squared-tail contribution in the earlier proof is at most
\[
 2\sum_h\left\{\log6\,[(B_h^\infty)^2J_h+I_{T_h^2}+E_{T_h^2}/10^6]
              +B_h^2 e_{\mathbb N,h}\right\}.
\]
This bounds the inner ratio sum by \(\log6\) plus its positive discrepancy and uses the global \(B_h\) only on that discrepancy. For the far-ratio part the earlier factor \(2(1+d(\ell+\log6))\) still applies. Its remaining sum over \(h>1\) is at most \(\sum_{h>1}[(L_h^\infty)^2J_h+I_{F_h^2}+E_{F_h^2}/10^6]\).

For the cross term, \(r,s\) must both be units and \(s\le y\). On \(s\le y/R\), put \(w=\ell-\log R\). Integrating the bound \(1+d\log(y/s)\) for the inner \(H(y/s)\) over outer unit \(s\) gives at most
\[
 M=(1+d\log R)(1+dw)+d(w+dw^2/2).
\]
Indeed \(\sum_{s\le y/R,s\in A}\log(y/(Rs))/s\le\int_0^w(1+dv)\,dv\). The cross contribution is at most
\[
 4\{d\log6[B_1^\infty M+I_{HT_1}+E_{HT_1}/10^6]
          +B_1(1+d\ell)e_{A,1}\}.
\]
For \(y<10^6\) the difference between the old and new tail polynomials is majorized in absolute value by summing their coefficient differences in absolute value times powers of \(\log(2\pi 10^{12})\). The resulting normalized cost is this bound times \(2\pi 10^{12}/e^U\). If \(e^U\le2\pi10^{12}\) the script keeps both old bounds.

## Uniform fourth moment

With the [shift-split off-diagonal](OFF_FOURTH.md) and the existing Riemann–Siegel remainder, **python -B unit_diagonal.py** certifies
\[
 \int_0^T |\zeta(1/2+it) E_6(1/2+it)|^4 dt
       < .007607875\,T\log^4T\qquad(T\ge e^{40}).
\]
At \(\log T=40\) the bulk, near and far polynomial values are bounded by \(530.035,\ 162.098,\ 25.095\), respectively. The early-time integration corrections are charged separately.

The full half-line budget, using the existing radial estimate and this fourth moment, can be reproduced in the sibling spectrum directory with

~~~powershell
python -B height_budget.py --anchor 164.6 --polygon --short-core 2097152 --convex --tight --unit-fourth
~~~

The certificate treats every \(L=4\log n\ge164.6\) under QRH(7/8), with the finite-height Riemann-hypothesis verification used in the established spectral bound.

The 192-bit run gives a total in \(0.99905492\pm3.72\cdot10^{-9}\). The first integer is \(n=743392080770110514\).
