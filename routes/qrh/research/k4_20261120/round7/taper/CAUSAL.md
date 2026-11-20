# Real-variable Mellin energy

Let \(g(u)=\min(1,\max(0,u/W))\), \(\mu_Q(n)=\mu(n){\bf1}_{(n,Q)=1}\), and
\[
 H(u)=\sum_{n\le e^u}\frac{\mu_Q(n)}n g(u-\log n),\qquad
 F(z)=\frac{1-e^{-Wz}}{Wz^2\zeta_Q(1+z)}.
\]
Extend \(H\) by zero to \(u<0\). For \(\Re z>0\), its Laplace transform is precisely \(F(z)\). The interchange of the series and integral is justified by the convergent Dirichlet series of absolute values at \(1+\Re z\). Also \(|H(u)|\le1+u\) for \(u\ge0\), so Fourier–Plancherel at \(z=e/2+it\) gives the identity
\[
 I_e=\frac1\pi\int_0^\infty|F(e/2+it)|^2\,dt
     =\int_0^\infty e^{-eu}|H(u)|^2\,du,\qquad e>0 .
\]
It follows at once that \(I_e\) is nonincreasing and completely monotone. For \(e\) in a closed positive cell with lower endpoint \(l\), \(I_l\) alone suffices. The function \(H\) here is a different representation of the same Fourier *modulus* as in the pre-existing bilateral discrete-transfer proof; its use does not change the original discrete transfer.

### Finite prefix and interpolation

Write \(G(t)=\sum_{n\le e^t}\mu_Q(n)(t-\log n)/n\), zero for \(t<0\). Then \(WH(u)=G(u)-G(u-W)\). Choose \(S=16,\ d=1/512\), with \(W/d\) an explicitly checked integer. At each \(t=id\le S\), an Arb exponential certifies the unique integer \(\lfloor e^t\rfloor\). Use the signed 64-bit prefix sums of the integer approximations to \(K\mu_Q(n)/n\) and \(K\mu_Q(n)\log n/n\), \(K=2^{44}\). The former approximation truncates the exact rational magnitude to an integer. The latter truncates after the [already bounded binary64 integer logarithm](../../round5/left/FAST_SHORT.md), an exact binary rescaling and one division. The relative error before integer truncation is at most \(160\cdot2^{-52}\) for positive \(n>1\). For \(n=1\) the logarithm is exactly zero. Since \(\sum_{n\le e^t}\log n/n\le(1+t)^2\), the final enclosure for the exact \(G(t)\) has radius at most
\[
 \frac{\lfloor e^t\rfloor}{K}(1+t)+160\cdot 2^{-52}(1+t)^2 .
\]
The two prefix sums and all their intermediates fit in signed 64 bits by \(K(S+2)^2<2^{62}\); the sieve products, array indices and logarithm arguments are also checked within range. The integer sieve sets \(\mu=0\) at nonunits and square multiples and multiplies by \(-1\) at each prime divisor.

On \(a\le t\le b=a+d\) the single positive hinge \((t-\log n)_+\) differs from its linear chord by at most \(d/4\), as follows by maximizing \((\log n-a)(b-\log n)/d\). Hinges with no interior breakpoint agree exactly with their chord. Therefore the error of linear interpolation for \(G\) is bounded by
\[
 \frac d4\big(\lfloor e^b\rfloor-\lfloor e^a\rfloor\big)e^{-a}.
\]
This estimate includes an endpoint breakpoint even though its actual interpolation error is zero.

### Explicit tail

Write \(\eta=\phi(Q)/Q,\ Z_j=\prod_{p\mid Q}(1-p^{-j})^{-1}\) and \(\xi=1-1/(12\log 10)\). For even \(Q\) define
\[
 A=.0336\cdot1.4378(1-2^{-\xi})Z_\xi,\qquad
 C=(4.86\sqrt3(\sqrt2-1)/2+2.93)Z_{1/2}.
\]
For \(t\ge S\) the [previously proved sieved logarithmic Möbius remainder](../../round4/density/MELLIN_LOW.md) gives
\[
 |G(t)-1/\eta|\le A/t+Ce^{-t/2}.
\]
Indeed take the shift \(e\downarrow0\) in its finite logarithmic sum. In the comparison main term \(tD-F\), \(D=1/\zeta_Q(1+e)\to0\) and \(F=-(1/\zeta_Q)'(1+e)\to-1/\eta\), using the simple pole of \(\zeta_Q\) of residue \(\eta\). The constants of the uniform estimate may be taken with \(e_0\downarrow0\). The cited theorem states \(X\ge15,\ 1\le\sigma\le1.1\); its first error term also contains the indicator \(X\ge 10^{12}\), which may be dropped in this upper bound. [Ramaré–Zuniga Alterman, Theorem 1.3](https://arxiv.org/html/2312.05138v2#S1)

For \(t\in[S,S+W]\), approximate the first \(G\) by \(1/\eta\) with the displayed decreasing endpoint error and still use the finite grid for \(G(t-W)\). On every cell the absolute value of \(WH\) is bounded by the linear interpolation between two nonnegative endpoint upper bounds \(L,R\), each enlarged by the sum of the two applicable uniform errors. Thus the unweighted cell mass is at most \(d(L^2+LR+R^2)/(3W^2)\). Multiply this by \(e^{-la}\).

For \(u\ge S+W\), both residuals are bounded by \(A/(u-W)+C e^{-(u-W)/2}\), so the entire tail mass beyond the last grid endpoint is at most
\[
 e^{-l(S+W)}\,\frac4{W^2}
 \left(\frac{A^2}{S}+\frac{4AC}{S} e^{-S/2}+C^2e^{-S}\right).
\]
Summing the positive cell masses in reverse order with common ratio \(e^{-ld}\) gives an upper bound of \(I_l\). Every floating intermediate in the large prefix carries the explicit preceding error. All proof bounds and evaluations after it use Arb.

For \(Q=2310,W=9.5,e=2/37\), even the scale \(1/256\) with \(S=16\) gives \(I_e<1.266928\). The default uses \(1/512\). In the bridge, the optional **--real** mode splits each old \(e\)-cell into eight. It retains the old local-energy upper bound from the containing cell and recomputes the other factors on each closed subcell. Its input is the original single taper on both boundaries.

On \(U=37,V=37.5,\delta=1,W=9.5,\log h=-3\), the fixed-frequency result is \(I_{2/37}<1.266858629\), and the entire right-mean constant with 128 original local cells is below **.003703682**. On the following full physical interval the real-variable certificate gives
\[
 146.4\le L\le146.71,
 \qquad \text{normalized total}<.997709669 .
\]
Its maximum occurs in the first physical cell. The [first improved integral certificate](MELLIN.md) joins at \(146.7\), and the previous upper half-line joins at \(147.2\). Thus, with the same QRH and analytic inputs, the pointwise conclusion holds for all \(n\ge7\,855\,576\,054\,835\,258=\lceil e^{146.4/4}\rceil\).

~~~powershell
python -B mellin_bridge.py --first 146.4 --last 146.71 --cells 128 --nheight 96 --mesh 128 --real
~~~

Using the independent complex disk evaluation at the lower \(e\) endpoint also gave a total below **.999778798** on \([146.45,146.71]\). That command uses **--causal**, 64 exponent cells, 96 height samples per half-unit and mesh 128.

2026-11-20. Project AI authors are Claude and Codex. Codex derived and computed the present QRH-route bounds.
