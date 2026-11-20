# A complete subfamily of the actual shifted convolution

Use the sample \(T=H=3\cdot10^{12}, D=T/10,\ X=10^{10},\sigma=7/8,r=3/4\). With the notation of [the exact progression decomposition](README.md), set \(p=ab\), \(h=|am-bn|\), \(\alpha=4/3\). Take all terms with
\[
                         h\ge1,\qquad p\le P h^\alpha .               \tag{1}
\]
The restriction is independent of the common divisor \(g\). The following are upper bounds for the moduli of the complete, scaled Gaussian integrals on this set, with both orientations, all original Gamma weights and all \(t\in I\). The continuous column bounds the integrals defining \(\mathcal C\).

| \(P\) | Lattice \(\mathcal O\) | Continuous \(\mathcal C\) | Discrepancy \(\mathcal O-\mathcal C\) |
|---:|---:|---:|---:|
| \(10^7\) | 0.00004276 | 0.000000402 | 0.00004316 |
| \(3\cdot10^7\) | 0.00059651 | 0.000002436 | 0.00059894 |
| \(10^8\) | 0.009919 | 0.00001780 | 0.009937 |
| \(2\cdot10^8\) | 0.041345 | 0.00005609 | 0.041401 |

Since \(p\le X^2\), the \(P=10^8\) row includes **every shift \(h\ge10^9\)**. In the combined variance test of the exact decomposition, it suffices to bound the signed discrepancy of the complementary cases \(1\le h<10^9,\ p>10^8 h^{4/3}\) by \(0.27864\), with the K5 arithmetic input on \(Q_X\) stated there. The estimate on that complementary set is still needed. [Arb verification](check_wedge.py)

## Counting primitive pairs

Only squarefree \(p\) occur where the mollifier product is nonzero. The number of ordered, coprime factorizations \(p=ab\) is \(2^{\omega(p)}\). Let \(M(Y,d)=\sum_{p\le Y}\mu^2(p)2^{\omega(p)}p^{d-1}\) for real \(d\ge1\). Here \(p\) is an integer modulus, not necessarily prime. The following explicit majorant is used to evaluate sums in \(h\). Let \(Q=210,\rho=\phi(Q)/Q=8/35,\ L_Q=\prod_{\ell\mid Q}(1+2/\ell)\) over prime divisors, \(C_Q=\gamma+\sum_{\ell\mid Q}\log\ell/(\ell-1)\) and \(\epsilon=\sqrt{Q/P}\). For \(Y=P h^\alpha\) and our \(P>Q^3\),
\[
 \frac{M(Y,d)}{Y^d}\le 2L_Q\left[
 \frac{\rho}{d}\left(\rho(\tfrac12\log P+C_Q+\tfrac{\alpha}{2}\log h)
                          +32\epsilon\right)+4\rho\epsilon+8\epsilon^2\right]. \tag{2}
\]
To prove this, extract \(m=(p,Q)\), whose weight is \(2^{\omega(m)}\); for the remaining integer replace its number of factorizations by the divisor function, with both factors coprime to \(Q\). Put \(V=Y/m\). Sum in the half with first factor \(j\le\sqrt V\) and double. Counting units to \(x\) modulo \(Q\) differs from \(\rho x\) by at most 2, verified on one period including both limits between adjacent integers. Thus their sum with weights \(n^{d-1}\) to \(v\) is at most \(\rho v^d/d+4v^{d-1}\), by partial summation. The remaining sums in \(j\) are the unit count and the unit harmonic sum. For \(y=\sqrt V\ge Q\), inclusion–exclusion and \(|\sum_{n\le u}1/n-\log u-\gamma|\le2/u\) at \(u\ge1\) bound that harmonic sum by \(\rho(\log y+C_Q)+32/y\). Now \(1/y\le\epsilon\), and summing \(2^{\omega(m)}/m\) gives \(L_Q\), proving (2).

Write \(B(P,d,s)\) for the sum of the majorant (2) against \(h^{-s}\) for \(h\ge1\). The program uses the upper bound \(\zeta(s)\) for the constant part and \((s-1)^{-2}+(es)^{-1}\) for \(\sum h^{-s}\log h\). The latter follows from comparison of a nonnegative unimodal function with its integral plus its maximum.

## The lattice sum with all shifts

By the [finite-band theorem](../../round3/offdiagonal/THIN_BAND.md), it suffices to bound the elementary sum on \([T,4T]\) with \(mn\le N_*\) and \(D|\lambda|\le18\) at extra cost \(0.00001390\), also for the chosen subset. Here \(\lambda=\log((v+h)/v)\). For \(c>0\) put
\[
 C_c=\frac1{2\sqrt\pi}\left(\frac{e^{c^2}}c+\frac{e^{(c+r)^2}}{c+r}\right).
\]
On shifting the height by \(i\eta D\) with \(|\eta|\le3\), the elementary profile has modulus at most \(e^{0.023} C_c (|z|/(2\pi mn))^c\), where \(z\) is the complex height. Indeed \(|\arg z|<0.3\) and \(|\Phi(x+iy)|\le e^{y^2/4}\Phi(x)\). For \(q>0\), completing the square in the Gaussian integral and bounding its remaining exponential by 1 gives \(e^{qx}\Phi(x)\le e^{q^2}/(2q\sqrt\pi)\). Apply this with \(q=c,c+r\).

For the positive-frequency phase choose \(\eta=\min(3,D\lambda/2)\), and reverse its sign for the conjugate phase. The horizontal damping becomes \(A(D\lambda)\), where
\[
 A(x)=\begin{cases}e^{-x^2/4},&0\le x\le6,\\e^{9-3x},&x\ge6.\end{cases}
\]
For \(w=(\Re z-2T)/D\) on the displaced segment, \(|z|\le2.3T e^{|w|/23}\). The normalized integral of \(e^{-w^2+c|w|/23}\) is \(e^{(c/46)^2}(1+\operatorname{erf}(c/46))\). The two vertical connectors cost \(<10^{-18}\) in total: the absolute complex envelope \(B_1\) of the finite-band theorem gives at most \(3B_1(1.3e^{-91}+4.3e^{-391})/\sqrt\pi\), uniformly in the possibly term-dependent \(\eta\) by summing the same positive majorants.

Put \(j=\sqrt{v(v+h)}\). Exactly \(\lambda=2\operatorname{arsinh}(h/(2j))\). On the retained band \(h/(2j)\le\sinh(9/D)\), so \(\lambda\ge(1-1/D)h/j\) by \(\operatorname{arsinh}x\ge x-x^3/6\) there. Put \(D'=D-1\). Points of a single progression in \(v\) are separated by \(p\), and their \(j\)-coordinates are also separated by at least \(p\), as \(dj/dv\ge1\). For \(m=2\sigma+2c\), the profile \(j^{-m}A(D'h/j)\) is nonnegative and unimodal: regarded as a function of \(x=D'h/j\), it is proportional to \(x^mA(x)\), whose logarithmic derivative changes sign once. Its sum on any such points is at most its integral divided by \(p\) plus its maximum, by integrating the number of points in its interval superlevel sets. We may now discard band and product restrictions in this positive majorant.

Write \(v_1=m-1\),
\[
 I_{v_1}=2^{v_1-1}\Gamma(v_1/2)+e^9\,3^{-v_1}\Gamma(v_1,18),
 \qquad M_m=\max((2m/e)^{m/2},\,6^m e^{-9}).
\]
For our \(m<18\), these bound respectively \(\int_0^\infty x^{v_1-1}A(x)dx\) and \(\sup x^m A(x)\). The preceding integral and maximum are consequently bounded by \((D'h)^{-v_1} I_{v_1}\) and \((D'h)^{-m}M_m\). The density term has also the factor \(1/p\). Sum primitive pairs with (2), and \(g^{-2\sigma}\) with \(\zeta(2\sigma)\). Thus before the connector and finite-band costs, the bound is
\[
 2X^r\zeta(2\sigma) C_c e^{0.023+(c/46)^2}
 (1+\operatorname{erf}(c/46))
 \left(\frac{2.3PT}{2\pi D'^2}\right)^c D'^{\,1-2\sigma}
 \left[I_{v_1} B(P,c,r+(2-\alpha)c)
       +\frac{P}{D'}M_m B(P,c+1,2\sigma+(2-\alpha)c-\alpha)\right]. \tag{3}
\]
The factor 2 accounts for the two orientations. The four rows use \(c=2.9,2.55,2.15,1.9\) respectively. All arguments of \(\zeta\) in (3) are greater than 1.

## The continuous comparison on the same family

Now use the actual Mellin integral for each \(h\) in (2) of the exact decomposition, retaining only \(p\le Ph^\alpha\) in \(A_X(z)\). Shift to \(c_2=13/8\); here \(\Re w=5/2,\Re s=4\). In addition to the cancelled initial poles, each sign crosses the simple beta pole \(z=2-\sigma\pm it\). Its residue is negligible. Specifically its gamma quotient after extracting the residue of \(\Gamma(1-w\pm it)\) is \(2\pm 2it\); \(|P_t(z)|<10^4e^{-t^2}\) from its polynomial and Gaussian. The unrestricted arithmetic absolute sum is \(<X^3\) there by \(d,e\le X\) and \(p\le X^2\). The factor \(h^{-s}\) costs at most \(h^{-3}\). Finally \(|h_t(2\pm it)/h_t(\sigma)|<10^4 t e^{2t}\) by the Gamma integral and the denominator Stirling lower bound. Summed over \(h\) and both poles and scaled by \(X^r\), the cost is \(<10^{-18}\).

On the new line, (3) of the exact decomposition applies with the factor \(\zeta(s)\) divided out, since the arithmetic condition depends on \(h\). There are no zeros of \(\zeta\) on this line. Here \(|J_t(w)|\le1\) as \(\Re\cos(\pi w)=0\). For \(u=\Im z\),
\[
 \left|\frac{\zeta(1-s)}{\zeta(s)}\right|
 =\frac{2}{(2\pi)^4}\sqrt{\pi |u|\coth(\pi|u|)}
       \prod_{j=1}^{3}\sqrt{j^2+4u^2}
 \le\frac{2(1+2|u|)(3+2|u|)^3}{(2\pi)^4}.
\]
Indeed this follows from the functional equation, the Gamma recurrence, and \(|\Gamma(1+iy)|^2=\pi y/\sinh(\pi y)\), with the removable value at zero. Also \(x\coth x\le1+x\).

For \(|u|\le t/2\), the absolute ratio \(U^{r+c_2}|h_t(1-w)/h_t(\sigma)|<1.6\). To see this, recur once from real part \(-1.5\) to \(0.5\) in both Gamma factors. This costs \(4\pi^2/(t^2-u^2)\le(4/3)U^{-2}\). Apply the Stirling bounds of §3 of the previous diagonal calculation to the remaining ratio at real parts \(0.5,\sigma\), costing at most \((1.001/.999)^2(3/4)^{-1/4}\) after normalization. The auxiliary Gaussian bound is \(|P_t(z)|\le130e^{-.99u^2}\), from \(e^{c_2^2}/c_2+e^{(c_2+r)^2}/(c_2+r)<128\) and the four polynomial factors. On \(|u|>t/2\), Gamma recurrence bounds each numerator \(\Gamma((-1.5+iy)/2)\) by \(\Gamma(1/4)/(3/4)<6\). Denominator Stirling gives the normalized ratio \(<10^5t^3e^{2t}\). After the Gaussian and the degree-four zeta bound just proved, the two tails have normalized integral less than 1 since \(t\le2|u|\), \(t\ge H\). No height-dependent factor remains in that bound.

Write \(K=1+\frac{1.6\cdot260}{(2\pi)^5}\int_\mathbb{R}(1+2|u|)(3+2|u|)^3e^{-.99u^2}du\) and \(U_0=T/(2\pi)\). The normalized continuum integral throughout \(I\) is bounded by
\[
 (X/U_0)^r(P/U_0)^{c_2}\zeta(2\sigma) B(P,c_2,r+(2-\alpha)c_2)K+10^{-18}.
\]
Use (2) on the restricted arithmetic factor and integrate against Gaussian mass at most one; in the sample \(T=H\), \(U\ge U_0\) on \(I\). This completes the bounds for the same family on the two sides of the progression comparison.

2026-11-20. Claude and Codex project attribution. Codex derived the complete-family estimate and verified its constants.
