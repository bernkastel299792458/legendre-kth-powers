# A negative part of the genuine finite phase band

Fix \(L=116,\ Q=23\#=223092870,\ z=1732099\sqrt{e^{116}/H},\ C=e^c,\ X=C e^{2r},\ X_-=C e^{-2r},\ Y=e^{75}\). Use the precise normalized physical weight \(P_0F\) from [the signed phase condition](REMAINING_PHASE.md). Let \(P_q\) denote the actual real, normalized contribution of modulus \(Y<q\le X/200\) to the four-sided sum with \(2<hX/(Qq)\le2.5\,10^{17}\). Define the set of moduli
\[
 {\cal S}=\{q:B_Q(q)>0,\quad 2500\le w=C/q\le10^{10},\quad
 \operatorname{dist}(w,\{k\in{\mathbb Z}:(k,Q)=1\})>
 D(w)\},\qquad D(w)=5(w/H)^{1/3}.
\]
Then each \(P_q\le0\) on \({\cal S}\), and its complete contribution satisfies
\[
                    \sum_{q\in{\cal S}}P_q<-.02133994 .
\]
These terms include every harmonic in the four-sided band for each selected modulus. Thus at this location a sufficient inequality on its disjoint complement is \(\sum_{q\notin{\cal S}}P_q<.02137900\), using [the prior allowance .00003906457](MULTIPLIER_RANGE.md). The complement remains open. The estimate already includes true physical multiplier counts if a sidelobe meets an integer.

## A pointwise comparison for every modulus in the class

Let \(\eta=\varphi(Q)/Q\), \(\tau=2^{\omega(Q)}\), \(\kappa_*=2.5\,10^{17}\), \(M_0=u_0e^{-2r}(A-4/[Hr(1-(a/(Hr))^2)])\le P_0\int F\). Here \(u_0=(c+2r)e^r/I\). Factoring out the positive \(B_Q(q)/q\), Poisson gives the complete nonzero spectrum as
\[
      P_0 q\sum_{(k,Q)=1}F(kq)-\eta P_0\int F .
\]
For \(v=X/q\), let \(N=\lfloor 2Q/v\rfloor\) and \(M(N)=\max_{j\le N}|\sum_{n\le j}c_Q(n)|\). Abel summation of the true cosine at each physical \(t\le X\) costs at most \(9M(N)\) through two turns. Removing the low harmonics incurs at most \(18M(N)P_0\int F/Q\). Write \(U(v)\) for the per-modulus upper-frequency cost, before the same \(B_Q(q)/q\) factor. The [64-sinc and total-variation proof](MULTIPLIER_RANGE.md) gives
\[
 U(v)=\min_{2\le j\le64}
 2u_0 M_1\tau\eta R^{64-j}s^{-j}\left(\frac{\kappa_*}{(j-1)v}+1\right),
\]
where \(s=2\pi\delta\kappa_* /(64 X)\), \(R=\max(\sin(s)/s,1/4)\), \(M_1=S_0H e^{2r}/(\pi\kappa_*)\). These bounds hold for both strict and non-strict endpoint inclusions using the actual integer cutoff. The high-frequency upper is for \(hX/(Qq)>\kappa_*\).

Dilation and the 64-fold convolution give \(F(kq)\le\sup_{|b|\le2\delta} W(kq+b)\), \(\delta=.0002 e^{116}/H\). When the right side is positive, \(\max(kq+b,C)\le C e^{2r}\). Hence \(H|\log((kq+b)/C)|\ge H e^{-2r}(|k-w|-.0004w/H)/w\). For \(|k-w|>D=D(w)\) and \(t=w/(HD)\) define
\[
  E_0=(1-.0004t)^2-(a e^{2r}t)^2,\qquad
  U_F(w)=\frac{4u_0 e^{4r}(w/H)(D^{-2}+D^{-1})}{E_0}.
\]
The program checks both \(1-.0004t>0\) and \(E_0>0\). The numerator of the Logan weight is at most two. Also \(\sum_{k:(k,Q)=1}|k-w|^{-2}\le2(D^{-2}+D^{-1})\) by counting the integers on either side from distance \(D\). Since \(P_0 q=u_0H/w\), we obtain \(P_0q\sum F(kq)\le U_F(w)\). This upper increases with \(w\), as seen termwise after substituting \(D=5(w/H)^{1/3}\).

For all selected moduli this proves
\[
 \frac{qP_q}{B_Q(q)}
 \ \le\ - M_0[\eta-18M(N)/Q]+U(v)+U_F(w).
\]
The bracket is positive. Two full intervals, cut at \(w=10000\), verify strict negativity: on each take the maximal signed Ramanujan prefix at its lower endpoint (\(v\ge w\)), and \(U_F\) at the upper endpoint. Use \(U(2500)\) on both. True signed integer maxima are obtained by the [prefix scan](ramanujan_prefix.py).

## Lower bound for the subtracted mass

The size estimate counts just semiprimes \(q=pr\), \(p\ne r\). In each tested cell \(q>z\), so its positive coefficient is exactly \(2|\lambda_p\lambda_r|\). Divide prime denominators into bins \(p\in(A,B]\) with \(A=z/b_{i+1},B=z/b_i,\ b_i=10^{10i/260}\), and likewise for the other prime \(v'\in(a,b]\). The Selberg numerator in \(|\lambda_p|\) is at least \(G_Q(\min(\lfloor b_i\rfloor,10^6))\), omitting also the factor \(p/(p-1)\ge1\). All tested primes exceed \(10^6\). Subtract the diagonal equality \(v'=p\) at most once per outer prime, at reciprocal price \(1/A\).

The ordinary prime harmonic in \((a,b]\) is at least
\[
 H(a,b)=\bigl(\log(b/a)-2E(b)/a\bigr)/\log b,\qquad
 E(b)=\sqrt b\,\log^2(b)/(8\pi).
\]
This follows by partial summation of the verified bound for \(\vartheta\) through \(2.169\cdot10^{25}\). Each prime endpoint lies between 599 and this upper limit. [Johnston, Proposition 3.1](https://arxiv.org/pdf/2109.02249)

For fixed \(p\), put \(l=C/(Bb)\), \(h=C/(Aa)\), and \(d=D(h)\). Remove every \(v'\) for which \(|C/(pv')-k|\le d\) for some unit \(k\). Uniformly in the actual \(p\), the count of candidate \(k\)'s is at most
\[
 n_k=\eta[C(1/a-1/b)/A+2d]+\tau .
\]
Indeed the exact \(k\) lie in \([C/(pb)-d,C/(pa)+d]\); the unit count of a real closed interval costs at most its length times \(\eta\) plus \(\tau\) by divisor inversion. Each full excluded prime interval has endpoints \(a_k=C/[p(k+d)], b_k=C/[p(k-d)]\). When it meets \([a,b]\), put \(L=l-2d,\ R=h+2d\). Then
\[
 b_k/a_k-1\le 2d/L,\quad
 a_k\ge a L/(l+2d),\quad
 b_k-a_k\ge y_{\min}=2daL/[(l+2d)R].
\]
Indeed \(k\in[l-d,h+d]\) and an intersection forces \(b_k\ge a\). For shorter endpoint conventions an extra prime costs at most \(1/a_k\). Thus the excluded harmonic for each \(k\) is at most the smaller of
\[
 \frac{4d}{L\log y_{\min}}+\frac{l+2d}{aL},
 \qquad
 \frac{2d/L+2E(b)/a}{\log a}+\frac1a.
\]
The first is the interval Brun–Titchmarsh bound on the full interval; the second is the finite \(\vartheta\) estimate on the clipped interval. In all rows \(y_{\min}>10\). [Montgomery and Vaughan, The large sieve, Theorem 2](https://doi.org/10.1112/S0025579300004708)

Call this smaller bound \(E_1\). The surviving ordered harmonic mass is at least \(H(A,B)\max(0,H(a,b)-n_k E_1-1/A)\). Its transposed estimate also holds, so the larger of the two can be used. Multiply by the corresponding two positive lower Selberg numerators, divide by \(G_+^2\) and multiply by the uniform positive lower \(M_0[\eta-18M(N)/Q]-U(v_{\min})-U_F(h)\) for the cell. The ordered sum accounts for the factor two in \(B_Q(pr)\); for different bins both orientations are included, and for a single bin the full ordered sum already includes both. All omitted moduli of \({\cal S}\) are nonpositive by the pointwise proof.

The program also verifies a second class at \(v=X/q\ge2500\) comprising all positive-coefficient moduli with no actual unit integer in \([X_-/q,X/q]\). Its physical term is exactly zero and the whole remaining four-sided sum over that class is below \(-.00362951\), using the simpler clipped prime interval of log length \(4r\). This separate figure is not added to the preceding bound.

~~~powershell
python -B round8/physical_low/prime_gap_block.py --top 10000000000 --grid 260 --spatial-tail --lower .02133994
python -B round8/physical_low/prime_gap_block.py --top 1000000 --grid 96 --lower .00362951
~~~

## Narrow prime rows and the published stronger theta estimate

All prime endpoints in the certificate exceed \(10^6\). The verifier now uses \(E(t)=\sqrt t\,\log t\,(\log t-2)/(8\pi)\) from equation (3.2) of the same Proposition 3.1. At 260 bins this gives the strict lower bound .02137508 in place of .02133994. The earlier rounded bounds stay valid.

The optional refined calculation also uses \(D_Q\le2^{\omega(Q/B)}D_B\) on the small wheels \(B\mid Q\) through 510510 from [the exact oscillation proof](WHEEL_PREFIX.md). This sharpens the unit-interval numerator intercept in \(n_k\) to \(D_Q\). For an edge \(t>M=10^6\), there is a further lower bound
\[
 G_Q(t)\ge G_Q(M)+\max\!\left(0,(\eta-R_2)\log(t/M)-D_Q/M-2/\sqrt M\right),
 \qquad R_2=\sum_{\ell\nmid Q,\ \ell\ {\rm prime}}\ell^{-2}.
\]
Indeed among \(M<n\le v\), the number of squarefree units is at least \((\eta-R_2)(v-M)-D_Q-\sqrt v\), by removing multiples of every prime square \(\ell^2\le v\). Partial summation against \(1/n\le1/\varphi(n)\) gives the claim, with \(\sqrt v\) costing at most \(2/\sqrt M\). The bound for \(R_2\) sums through 2000 with remainder \(1/2000\). Since the actual prime exceeds the argument allowed in this partial lower bound (indeed \(z/b_i\gg b_i\) on every contributing cell here, and the explicit verifier requires \(z/b_{i+1}>10^6\)), this argument gives a valid lower numerator for the actual \(|\lambda_p|\). More precisely, for the refined rows the verifier also checks \(z/b_{i+1}>b_i\), which excludes the prime from every term used in that extension.

~~~powershell
python -B round8/physical_low/prime_gap_block.py --top 10000000000 --grid 220 --spatial-tail --refined --lower .02229166
~~~

2026-11-20. Joint project attribution to Claude and Codex.
