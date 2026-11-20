# Signed finite Möbius sums and a right endpoint for \(L\ge254\)

Assume QRH(7/8) and the same explicit analytic inputs as [the centered BV proof](../PROOF.md). Then a prime lies in \((x,x+4x^{3/4})\) for every \(L=\log x\ge254\). The scalar certificate uses the original \(D_5\) detector and trapezoid height bound from [the first-round proof](../../../upper/PROOF.md). It does not rely on the later improvement to that height kernel. This argument and its Arb code have not been formally verified.

Set \(U_0=62.8,\ T_0=e^{U_0},\ W=10,\ h=e^{-3.2},\ \delta=.75,\ \kappa=.105\). Throughout \(T\ge T_0,\ U=\log T,\ Y=hT,\ X=e^WY,\ Y_0=hT_0,\ e=2\delta/U,\ e_0=2\delta/U_0\). Use the same centered coefficients \(b_v(j)\) and their Selberg contraction
\[
 S(v)\le\zeta(v)\sum_{j\ge1} j^{-v}|b_v(j)|^2,\qquad
 b_v(j)=\frac1W\int_Y^X\sum_{m>z/j}\frac{\mu(m)}{m^v}\,\frac{dz}{z}.
\]
See the parent proof for the contraction, its absolute convergence, Littlewood rectangles for a fixed \(T\), and the transfer from cumulative heights to all \(x\).

## The norm at \(v=1+e\)

Let \(m(y)=\sum_{n\le y}\mu(n)/n\), \(S=\log32,\ C=.011,\ c=1.00303,\ t_*=\log 10^{14}\). Write
\[
 G_e(t)=\sum_{n\le e^t}\frac{\mu(n)}{n^{1+e}}(t-\log n),\qquad A(s)=\int_s^\infty M_0(e^t)\,dt ,
\]
where \(M_0\) is the parent proof's exact small-\(n\) unsigned envelope through 2047, followed by \(\sqrt{2/y}\). Helfgott's finite bound and the Ramaré–Zuniga-Alterman large-\(y\) bound in that proof give
\[
 |m(e^t)|\le M_0(e^t)+C/(1+\max(t,t_*)),\qquad
 |m(e^t)|\le\sqrt{2}e^{-t/2}\quad(0\le t\le t_*).
\]
All finite values here lie below \(t_*\). Ramaré–Zuniga-Alterman's logarithmic Möbius bound at exponent \(1\) gives \(0\le G_0(t)\le c\). [Helfgott, Lemma 5.10](https://webusers.imj-prg.fr/~harald.helfgott/anglais/PartI.pdf), [Ramaré–Zuniga-Alterman, Corollary 1.2](https://arxiv.org/html/2408.05969v2), [Ramaré–Zuniga-Alterman, Lemma 3.1](https://arxiv.org/pdf/2405.12662).

Cover \(0<e\le e_0\) by 64 closed intervals \([l,u]\). On each such cell put \(D=\exp(-2\delta-u\log h)\). Then \(Y^{-e}\le D,\ 1/U\le u/(2\delta)\) and \(\zeta(1+e)/U\le(1+u)/(2\delta)\).

**Head \(j\le Y\).** Put \(s=\log(Y/j)\). For \(0\le s\le S\), Abel summation in the above integral gives
\[
 \left|e^{es}b_{1+e}(j)
      +\frac{G_0(s+W)-G_0(s)}W\right|
 \le 2u A(s)+\frac{C}{1+t_*}.                                      \tag{1}
\]
Indeed, the first part before averaging is \(-e^{-et}m(e^t)\). Replacing \(e^{-e(t-s)}\) by 1 on \([s,s+W]\) costs at most \(uWA(s)\) before dividing by \(W\), since this whole finite interval is inside the Helfgott range. The other part is \(e\int_t^\infty e^{-ez}m(e^z)dz\). Its \(M_0\) contribution is at most \(uWA(s)\). Its second envelope contributes at most \(CW/(1+t_*)\) after multiplying by \(e^{es}\). Finally \(G_0'=m(e^t)\) away from the discrete breakpoints, so the unweighted signed integral equals \(G_0(s+W)-G_0(s)\).

Split \([0,S]\) into 192 equal intervals \([a,b]\). Evaluate \(F(s)=G_0(s+W)-G_0(s)\) at both endpoints. Inside the cell its absolute value is at most the larger endpoint modulus plus
\(\sqrt{2}e^{-a/2}(1+e^{-W/2})(b-a)/2\), by the finite bound on both derivatives and distance to the closest endpoint. Bound \(A(s)\) by the parent proof's \(A_{\lfloor e^a\rfloor}\), allowing a smaller index. The harmonic mass of this cell is at most \(b-a+e^b/Y_0\) by integral comparison. Sum this mass times the square of the upper bound from (1), including \(|F|/W\).

For \(s\ge S\) use (3) of the parent proof with \(u\) in place of \(e_0\). The energy \(E_{\rm far}\) for \(A(s)^2\) uses only \(n\ge32\) in its accompanying sum and is below \(0.028831\). The mass for \((1+s)^{-2}\) is bounded by \(V=(1+S)^{-1}+(1+\log Y_0)^{-2}+32/Y_0\), from the integral and the two endpoints of its decreasing-then-increasing profile as a function of \(j\). Thus this tail adds at most
\[
 \big[(1+uW)\sqrt{E_{\rm far}}/W+2C\sqrt V\big]^2
\]
to the preceding finite sum. Call their total \(B_H\). Here \(j^{-e}e^{-2es}\le Y^{-e}\), so the head's contribution before multiplication by \(\zeta(1+e)\) is at most \(D B_H\).

**Transition \(Y<j\le X\).** With \(t=\log(X/j)\), exactly \(b_{1+e}(j)=1/\zeta(1+e)-G_e(t)/W\). Integration by parts twice, or evaluation term by term on each \((t-\log n)_+\), gives
\[
 G_e(t)=e^{-et}G_0(t)+2e\int_0^t e^{-ez}G_0(z)\,dz
                  +e^2\int_0^t(t-z)e^{-ez}G_0(z)\,dz .             \tag{2}
\]
In particular, if \(g_-\le G_0(t)\le g_+\) with \(0\le g_-\le g_+\le c\) on \(t\in[a,b]\), then
\[
  e^{-ub}g_-\ \le G_e(t)\le c(1+ub)-e^{-ub}(c-g_+).
\]
For the upper bound integrate the constant \(c\) in both integrals in (2). Use \(l/(1+l)\le1/\zeta(1+e)\le u\). Consequently the maximum of zero and the two possible endpoint deviations bounds \(|b_{1+e}(j)|\). Denote this bound by \(B_{a,b}\).

Divide \([0,W]\) into 384 equal intervals, evaluate \(G_0\) at both endpoints, and expand the range by \(\sqrt2 e^{-a/2}(b-a)/2\) as above. Intersect with \([0,c]\). The implemented table evaluates \(G_0(t)\) by integer sieving and ball arithmetic on the two finite sums \(\sum_{n\le e^t}\mu(n)/n\) and \(\sum_{n\le e^t}\mu(n)\log n/n\). At a numerically ambiguous inclusion the certificate encloses both results. The term vanishes at its exact breakpoint.

The sum of \(1/j\) across this cell is at most \(b-a+1/Y_0\). Also \(j^{-e}=Y^{-e}e^{-e(W-t)}\). The transition thereby contributes at most \(D B_M\), with
\[
 B_M=\sum_{[a,b]}(b-a+1/Y_0)e^{-l(W-b)}B_{a,b}^2.
\]
For \(j>X\), \(b_{1+e}(j)=1/\zeta(1+e)\). The upper integral bound for \(\sum_{j>X}j^{-1-e}\) including one endpoint gives a contribution to \(S(1+e)\) of at most \(X^{-e}(1+e/X)\). Combining all regions yields
\[
 S(1+e)/U\le D\left[\frac{1+u}{2\delta}(B_H+B_M)
             + e^{-lW}(1+u/Y_0)\frac{u}{2\delta}\right].           \tag{3}
\]

## The norm at \(v=2+e\)

Set \(d=v-1\ge1,\ D_v=1/\zeta(v),\ F_v=\zeta'(v)/\zeta(v)^2\). The certificate checks \(D_v<.65\) by the first 64 terms of \(\zeta(2.025)\), since \(e_0<.025\). Also \(-.43<F_v<0\), since \(\sum_{n\ge2}n^{-2}\log n<1\), by explicit terms 2 and 3 followed by the integral from 3. Write
\[
 G_{v-1}(t)=tD_v-F_v+R_v(t),\qquad
 R_v(t)=\sum_{n>e^t}\frac{\mu(n)}{n^v}(\log n-t).
\]
For \(t\ge0\), the unsigned summand has a single maximum as a function of \(n\). Its sum is bounded by its integral plus its maximum, so
\[
 |R_v(t)|\le e^{-dt}\left(\frac1{d^2}+\frac{e^{-t}}{\exp(1)v}\right)<1.2e^{-dt}.
\]
For \(j\le Y\), \(Wb_v(j)=R_v(s)-R_v(s+W)\). Summing \(j^{d-1}\) up to \(Y\) bounds this region's contribution to \(W^2Y^d\sum_jj^{-v}|b_v(j)|^2\) by
\(H_2=[1.2(1+e^{-W})]^2(1+1/Y_0)\).

For \(j>Y\), set \(r=\log(j/Y)\), \(A=W/2\). While \(r\le A\), \(Wb_v(j)=rD_v+F_v-R_v(W-r)\). It follows that
\[
 |Wb_v(j)|\le \sqrt{.43^2+.65^2r^2}+C_2,\qquad C_2=1.2e^{-A}.
\]
The sum over \(j>Y\) of \(Y^d j^{-1-d}\) is at most \(1+1/Y_0\), and with the factor \(r^2\) it is at most \(2+4/Y_0\). For the latter estimate the integral is \(2/d^3\), and the unimodal summand has maximum below \(4/Y\). Minkowski therefore bounds this inner transition contribution by
\[
 M_2=\big[\sqrt{.43^2(1+1/Y_0)+.65^2(2+4/Y_0)}
                      +C_2\sqrt{1+1/Y_0}\big]^2.
\]
On \(r>A\) the parent bound \(|Wb_v(j)|\le1+r\) holds also for \(j>X\). The summand \(Y^d j^{-1-d}(1+\log(j/Y))^2\) decreases on \(j>Y\). Its integral from \(Ye^A\) and one endpoint give
\[
 R_2=e^{-A}\big[(1+A)^2+2(1+A)+2+(1+A)^2/Y_0\big].
\]
Thus uniformly over this \(e\)-cell,
\[
 TS(2+e)\le \frac{\zeta(2)D}{hW^2}(H_2+M_2+R_2).
                                                                     \tag{4}
\]
Insert (3) and (4) into the right-line Gaussian mean integral of the parent proof, using \(1/U\le u/(2\delta)\) for (4). Take the maximum over all 64 cells only after adding these contributions.

## Critical line and continuous \(L\) range

Two changes improve the left boundary for this same mollifier. For the critical-line sum of squared coefficients divided by \(n\), apply the squarefree estimate \(\sum_{n\le t}\mu(n)^2/n\le b\log t+c_1'\) from the parent proof for every \(t\in[Y,X]\). Averaging over \(d[-\omega(t)^2]\) replaces \(\log X\) by \(\log Y+W/3\), because this probability law has density \(2\log(X/t)/(tW^2)\) on that interval. For the unweighted squared-coefficient sum, the exact integral of \(\omega^2\) is \((2X/W^2)[1-(1+W)e^{-W}]\). The script verifies positive offset when replacing \(U\) by \(U_0\).

Use CS v2 Corollary 2, (9), Table 2 with threshold \(10^{20}\), \(\mathfrak M_1=29.364,\mathfrak M_2=9.6675\cdot10^{26}\). Its upper bound at \(Z=e^{U_0-6}\) gives the needed \(a_1\). For \(t\ge Z\) bound the fourth moment on \([Z,t]\) by the upper bound for the entire interval \([0,t]\). After dividing by \(t\log^4 t\), the leading term is at most \(1/(2\pi^2)\), and the last two terms are bounded by their values at \(Z\) because \((1-\log2/V)^3/V\) decreases for \(V>4\log2\). Finally, replace the pointwise factor \(2^{1/3}\) preceding CS (42) by the weighted convexity inequality
\[
 |z-1|^{4/3}\le(1+\eta)^{1/3}|z|^{4/3}+(1+1/\eta)^{1/3},
 \qquad \eta=.001.
\]
The proof follows by writing \((|z|+1)/(1+\eta)\) as a convex combination of \(|z|\) and \(1/\eta\). This modifies \(K_1,K_2\) separately. [CS v2, Corollary 2, Table 2 and (41)–(42)](https://arxiv.org/html/2507.15184v2).

The resulting moments satisfy \(K_1<2.031943,\ K_2<23.693304,\ K_3<.075848111\). The first-round \(D_5\) chord proof with the parent BV disk and right-edge bounds gives total normalized error below \(0.996133\) at \(L=254\). Each decay inequality is checked on the full half-line and the starting height exceeds \(e^{62.8}\). Thus the conclusion holds for every \(L\ge254\). Reproduce from this directory with Python and python-flint:

~~~text
python -B verify_fine.py
~~~

The modifications concern the Codex QRH route. Claude's fifth-power results and the project's attribution are as in the parent proof.

## A sharper optional \(TS(2+e)\) bound

The independent call \(\texttt{right_endpoint}(U_0,\delta,\kappa,W,\log h)\) supplies \(K_3\) and three diagnostics without invoking the critical-line computation. All parameters here are specified by the caller and the proof uses the validity checks in that function. The default call retains (4). Its optional argument \(\texttt{signed_high=True}\) replaces (4) by the following estimate. The parameter \(\kappa\) appears only in the coefficient of \(TS(2+e)\) in the final \(K_3\), as in the parent proof. For instance \(U_0=56,\delta=.75,\kappa=.36,W=10,\log h=-3.2\) then gives \(TS(2+e)<.066353,\ K_3<.069904\).

Let \(d=1+e,\ d_*=1+e_0,\ v=1+d\), and use \(m,t_*,C,D_v,F_v\) above. Abel summation rewrites the logarithmic remainder as
\[
 R_v(t)=e^{-dt}\int_0^\infty m(e^{t+r})e^{-dr}(dr-1)\,dr.
\]
There are no boundary terms, since the original weight is zero at \(r=0\) and decays at infinity. For every \(z\ge0\), the finite Helfgott estimate and the globally valid large-\(y\) estimate imply
\[
 |m(e^z)|\le \sqrt2 e^{-z/2}+C/(1+t_*).
\]
For \(a=d+1/2\) direct integration gives
\[
 \int_0^\infty e^{-ar}|dr-1|\,dr=(a-d+2d e^{-a/d})/a^2 .
\]
At \(a=d\) the corresponding value is \(2/(d\exp(1))\). Hence
\[
 |R_v(t)|\le e^{-dt}\left(E_0e^{-t/2}+E_1\right),\quad
 E_0=\sqrt2\,\frac{1/2+2d_*e^{-1-1/(2d_*)}}{(3/2)^2},\quad
 E_1=\frac{2C}{\exp(1)(1+t_*)}.
\]
For \(j\le Y\) use the exact difference \(R_v(s)-R_v(s+W)\), with \(s=\log(Y/j)\). Minkowski in the same \(W^2Y^d\)-scaled norm bounds the square root of the contribution by
\[
 H'=(1+e^{-W})\{E_0\sqrt{1/2+1/Y_0}+E_1\sqrt{1+1/Y_0}\}.
\]
Indeed the two scalar sums are bounded by using \(\sum_{j\le Y}j^{d}\le Y^{d+1}/(d+1)+Y^d\) and \(\sum_{j\le Y}j^{d-1}\le Y^d/d+Y^{d-1}\), respectively.

Put \(\ell_v=-\zeta'(v)/\zeta(v)>0,\ c'=.55\). The script bounds \(D_v\) between \(D_-=1/\zeta(2)\) and \(D_+=(\sum_{j\le256}j^{-2-e_0})^{-1}\). It computes \(z_0=\sum_{j=2}^{256}(\log j)j^{-2-e_0}\) and \(z_2=\sum_{j=2}^{256}(\log j)j^{-2}+(\log256+1)/256\). The latter includes the decreasing tail's integral. Thus \(z_0D_-\le\ell_v\le z_2D_+\), with \(\Delta=\max(|z_0D_--c'|,|z_2D_+-c'|)\) a uniform bound on its distance from \(c'\).

For \(Y<j\le X\) the exact numerator is \(D_v(r-\ell_v)-R_v(W-r)\), \(r=\log(j/Y)\). The weighted sum of \((r-c')^2\) over \(j>Y\) is at most
\[
 Q=2-2c'+c'^2+5/Y_0 .
\]
Its continuous integral in \(r\) is bounded by \(\int_0^\infty (r-c')^2e^{-r}\,dr\). For the discrete correction, as a function of \(j\) the summand has two possible maxima, the left endpoint and \(r=c'+2/(1+d)\). After scaling, each extremal value is at most \(1/Y\). Comparing on the three monotone pieces gives a correction smaller than \(5/Y_0\). The analogous total mass is at most \(1+1/Y_0\). The linear part therefore contributes at most \(M'=D_+[\sqrt Q+\Delta\sqrt{1+1/Y_0}]\) to the norm. The residual contributes at most \(R'=(E_0+E_1)\sqrt{e^{-W}(1+1/Y_0)}\), since
\[
 Y^d\sum_{Y<j\le X}j^{-1-d}e^{-2d(W-r)}
 \le Y^{-d}e^{-2dW}(X^d/d+X^{d-1}).
\]
For \(j>X\), \(b_v(j)=D_v\). Thus the replacement for (4) is
\[
 TS(2+e)\le\frac{\zeta(2)D}{h W^2}
 \left[(H')^2+(M'+R')^2+(W D_+)^2e^{-W}(1+1/Y_0)\right].
\]

## Signed convolution at \(v=1+e\)

The separate optional argument \(\texttt{signed_low=True}\) computes (2) using its nonnegative deficit and can be combined with the preceding optional estimate. The same \(U_0=56,\delta=.75,\kappa=.36,W=10,\log h=-3.2\) example then gives \(S(1+e)/U<.014580\) and \(K_3<.060287\). On every \([l,u]\), (3) takes the smaller of the following bound and the original bound for each of the finite head \(s\le S\) and the transition. The infinite head \(s>S\) and tail \(j>X\) retain their original bounds.

Write \(q(t)=c-G_0(t)\ge0\) and define
\[
 I_e(t)=\int_0^t e^{-ez}q(z)\,dz,\quad
 J_e(t)=\int_0^t (t-z)e^{-ez}q(z)\,dz,\quad
 A_e(t)=e^{-et}q(t)+2eI_e(t)+e^2 J_e(t).
\]
Equation (2) gives the exact identity \(G_e(t)=c(1+et)-A_e(t)\). Subdivide \([0,W+S]\) into 768 equal parts. On each \([a,b]\), the smaller and larger endpoint values of \(q\), enlarged by \(\sqrt2 e^{-a/2}(b-a)/2\) and clipped to \([0,c]\), bound \(q\) everywhere. Let \(B=e^{-ub}q_{\min},\ D'=e^{-la}q_{\max},\ h'=b-a\). When advancing from \(a\) to \(b\), \(I_e\) increases by a quantity in \([h'B,h'D']\), while \(J_e\) increases by \(h'I_e(a)\) plus a quantity in \([h'^2B/2,h'^2D'/2]\). This yields rigorous lower and upper arrays at every grid node, including \(I_e(0)=J_e(0)=0\).

For each needed query \(t\), the script finds a grid prefix ending at \(a\le t\) and checks \(r=t-a<(W+S)/250\). On this final piece the bounds \(0\le e^{-ez}q(z)\le c\) suffice. Consequently \(I_e(a)\le I_e(t)\le I_e(a)+cr\), and similarly \(rI_e(a)\le J_e(t)-J_e(a)\le rI_e(a)+cr^2/2\). The bounds for \(A_e(t)\) now follow from its positive terms, using the separately tabulated \(G_0(t)\) at each query and \(e\in[l,u]\).

For \(0\le s=\log(Y/j)\le S\), the two finite truncations give the exact formula
\[
 b_{1+e}(j)=\frac{1}{\zeta(1+e)}-ce+
               \frac{A_e(s+W)-A_e(s)}{W}.
\]
The first two terms have sum in \([-(c-1/(1+u))u,0]\). With \(m_e(t)=\sum_{n\le e^t}\mu(n)n^{-1-e}\), Abel summation gives \(m_e(t)=e^{-et}m(e^t)+e\int_0^t e^{-ez}m(e^z)\,dz\). The derivative of \(G_e\) equals \(m_e\) away from the discrete breakpoints. Subtracting these Abel expressions at \(s+W\) and \(s\) now bounds the derivative of \(b\) in modulus by
\[
 \frac{\sqrt2 e^{-s/2}}{W}(1+e^{-W/2}+2u).
\]
Thus on a head cell \([a,b]\) the endpoint bounds for \(b_{1+e}(j)\), enlarged by this derivative cap at \(a\) times \((b-a)/2\), hold everywhere. Here the tabulated bound is for \(|b_{1+e}(j)|\) itself. After extracting \(Y^{-e}\) the head weights satisfy \(j^{-e}/Y^{-e}=e^{es}\le e^{ub}\).

For the transition \(t=\log(X/j)\in[0,W]\), the control of \(A_e(t)\) gives endpoint bounds for \(1/\zeta(1+e)-G_e(t)/W\) by using \(1/\zeta(1+e)\in[l/(1+l),u]\). The same Abel formula bounds its derivative in modulus by \(\sqrt2(e^{-a/2}+2u)/W\) throughout \([a,b]\). The original transition weights and cell mass bounds complete this variant of (3).
