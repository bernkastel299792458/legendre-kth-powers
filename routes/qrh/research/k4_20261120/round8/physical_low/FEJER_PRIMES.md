# A positive Fejér estimate for the genuine semiprime physical count

Use the notation and unit normalization of [the middle-phase inequality](REMAINING_PHASE.md) and the compact physical weight \(F\) with \(\delta=.0002 e^{116}/H\). For \(m=6000\), the contribution of **every semiprime** in \(X/m<q\le X/23\) to the whole signed middle problem is **less than .002302599** (96 cells). For \(m=200\) it is **less than .000496031** (64 cells), leaving room for [the entire three-prime family](TRIPRIME.md). Neither estimate covers all moduli. The number \(H=3000175332800\) here is the exact verified height in Theorem 1 of [Platt and Trudgian](https://arxiv.org/pdf/2004.09765).

## Spatial majorant

Write \(g_a(u)=(\cos a-\cos u)/(u^2-a^2)\), \(a=(1-10^{-12})H(c-116)\). Before dilation the supported leakage is bounded by \(1_{\{|v|\ge a\}}g_a(v)_+\). The dilation and ensuing probability convolution move its argument by less than \(d=.001\) in the variable \(u=H\log(t/e^c)\). The function is even. On \(a-d\le u\le2a+d\), one has
\[
 g_a(v)_+\le g_a(\max(a,u-d))\quad (v\ge a,\ |u-v|\le d).
\]
The identity \(2g_a(v)=\operatorname{sinc}((v-a)/2)\operatorname{sinc}((v+a)/2)\) proves the claimed decrease since both arguments are in \([0,\pi]\) on this range. Divide by \(\operatorname{sinc}^2(u/2)\), also decreasing there. The 256 interval enclosures in the program pair the numerator at the left end with the denominator at the right and give a uniform upper .402. At \(u\ge2a\) with positive numerator, \(\cos u\le\cos a+d\), and comparison first with \((\cos a-\cos v)/(1-\cos v)\) gives
\[
 \frac{\cos a-\cos v}{1-\cos u}\le (1+\cos a)/2+d/(1-\cos a-d).
\]
Also \(2(v^2-a^2)/u^2\ge2[(1-d/(2a))^2-1/4]\). These yield the same upper. For \(u<a-d\) the contribution is zero. On the support \(t/e^c\le e^{2r}\). This proves
\[
  F(t)\le C\,e^c\,t^{-1}\operatorname{sinc}^2\!\left(\tfrac H2\log(t/e^c)\right),
  \qquad C=.402e^{2r}.
\]

## Whole-height genuine prime rows

For \(l<p\le b\le2l\) write \(P(t)=\sum p^{-1-it}\), \(J(t)=\int_l^b v^{-1-it}dv/\log v\) and \(D=\log(b/l)\). Use the norm with measure \(h_H(t)\,dt=(1-|t|/H)_+dt\). Plancherel gives \(\|J\|_{h_H}\le(2\pi D/(\log l\log b))^{1/2}\). The bound on \(\|P-J\|_{h_H}\) is uniform over physical subintervals and includes the verified-height edges.

Put \(s=H-|t|,\ T_0=1000\). For \(s\ge T_0\), use the [Gaussian explicit formula and removal of the endpoint smoothing](PRIME_TWIST.md) with \(w=20/s,\ w_*=20/T_0\). Uniformly over upper endpoints \(y\le b\), the pole differs from \(\int_l^y v^{-1-it}dv\) by at most \(2w\), since its multiplier is \(\exp(-w^2t^2/2)\) and the integral has modulus at most \(\min(D,2/|t|)\). The logarithmic derivative's positive Poisson sum on \(\Re s=2\) is bounded by \(5+\tfrac12\log(3+|v|)\) as in the linked derivation. Integrating it between \(t-U-8\) and \(t+U+8\) bounds the number of verified zeros at distance \(\le U\) from \(t\) by
\[
 c_0(U+8),\quad c_0=(5+\tfrac12\log(3H+20))/\arctan(8/(3/2)),\qquad 0\le U\le2H.
\]
Every such zero has real part \(1/2\) and contributes at least \(2\arctan(8/(3/2))\) to the integrated Poisson sum. Partial summation with \(\min(D,2/U)\) now bounds the verified-zero part by
\[
 Z=e^{w_*^2/8}\,l^{-1/2}c_0\{8D+2+2\log(1+HD)\}.
\]
For the unverified zeros and the shifted line, the cited derivation applies with \(1/w\le H/20,\ wj_0\ge20(1-2/T_0)\). In its far spatial tail bound replace the endpoint by the global upper \(2.169\,10^{25}\). Denote these three nonnegative bounds by \(B_h,B_v,B_f\), respectively, exactly as evaluated by variables high, line and far in [the implementation](fejer_primes.py). The prime-power count improves to \(\sqrt b-\sqrt l+1+b^{1/3}\log b/\log2\). The two near-endpoint smoothing errors cost at most \(8\log(2b)/l+4w\log(2b)e^{w_*^2/2}\). Partial summation to divide the prefix error by \(\log l\) consequently gives \(|P(t)-J(t)|\le E_0+w E_1\), where
\[
 E_0=\{Z+B_h+B_v+B_f+8\log(2b)/l
 +(\log b/l)[\sqrt b-\sqrt l+1+b^{1/3}\log b/\log2]\}/\log l,
 \quad E_1=(4\log(2b)e^{w_*^2/2}+2)/\log l.
\]
Here \(\log b/l\) in the square-bracket coefficient means \((\log b)/l\). On \(s<T_0\), bound the two rows separately by \(E_*=[2D+2E(b)/l]/\log l\), \(E(b)=\sqrt b\log^2 b/(8\pi)\), using [Johnston, Proposition 3.1](https://arxiv.org/pdf/2109.02249). Integrating the squared factors \(1,\ 20/s,\ 1_{\{s<T_0\}}\) against \(h_H\) proves
\[
 \|P-J\|_{h_H}\le \sqrt H E_0+20E_1\sqrt{2\log(H/T_0)/H}+T_0 E_*/\sqrt H .
\]
Function normrow rounds \(\log l\) down to a multiple of \(1/20\) and \(D\) up to a multiple of \(1/1024\). The elementary displayed bounds and their explicit \(B_h,B_v,B_f\) versions increase with \(D\), and decrease with \(\log l\ge40\) at fixed \(D\). For the power term, separate \((e^{D/2}-1)l^{-1/2},l^{-1},e^{D/3}l^{-2/3}(\log l+D)/\log2\), all multiplied by \((\log l+D)/\log l\). The same comparison applies to \(E(b)/l\). All cell projections meet this domain.

## Returning to the genuine physical middle

Within the same integer \(k\) and outer prime cell \((l,h]\) as in [the annular decomposition](SEMIPRIME_ANNULI.md), the inner prime ranges from \(X_-/(kh)\) to \(\min(z,X/(kl))\). A physical lower endpoint equality contributes zero because the support lies strictly above \(X_-\). Keep exactly the same upper Selberg weights. By the Fejér identity
\[
 \operatorname{sinc}^2(Hv/2)=H^{-1}\int h_H(t)e^{itv}\,dt,
\]
the raw prime-pair cost on that rectangle is at most \(Ce^c\|P_1\|_{h_H}\|P_2\|_{h_H}/(Hk)\). The \(1/k\) and both prime reciprocals come from the \(1/t\) in the spatial estimate. Take the better of this and the prior per-cell Brun–Titchmarsh bound; the mean, true low phases, and absolute upper bound for the high remainder retain the same accounting.

~~~powershell
python -B round8/physical_low/semiprime_annulus.py --end 6000 --cells 96 --fejer --upper .002302599
python -B round8/physical_low/semiprime_annulus.py --end 200 --cells 64 --fejer --upper .000496031
~~~

## Two sampling obstructions for weights of bandwidth \(H\)

Put \(f(u)=F(e^{c+u/H})\). In the scaled variable use the transform \(\widehat B(v)=\int B(u)e^{-ivu}\,du\). If \(B\) is integrable with Fourier support in \([-1,1]\), then \(\widehat B(\pm1)=0\) by continuity. For the nonnegative periodic Fejér kernel \(D_N(v)=\sum_{|k|\le N}(1-|k|/(N+1))e^{ikv}\), it follows that \(\int B(u)D_N(u-\theta)\,du=\int B\). For \(f\), the limit of this expression instead equals \(2\pi\sum_j f(\theta+2\pi j)\), since \(f\) has a continuous periodization of finite multiplicity. Pointwise ordering of \(B\) and \(f\) gives the corresponding ordering of \(\int B\) and that shifted-grid sum.

On the even lattice \(u=2\pi j\), the original physical weight vanishes on the entire \(.001\)-neighborhood of each point. The dilation and convolution therefore leave \(f(2\pi j)=0\). Thus any real minorant \(B\le f\) of bandwidth one has \(\int B\le0\). In particular the verified-height band alone cannot give a favorable *positive integral* minorant for the negative-signed three-prime physical count.

On the odd lattice \(u_j=(2j+1)\pi\), the original near weight equals \((1+\cos a)/(u_j^2-a^2)\) for \(|u_j|\le U=Hr\), and \(F\) majorizes that original weight. The logarithmic derivative of the convergent cosine product (or the partial fractions of the tangent) gives
\[
 \sum_{j\in\mathbb Z}\frac1{((2j+1)\pi)^2-a^2}=\frac{\tan(a/2)}{2a}.
\]
Consequently every such majorant \(B\ge f\) satisfies
\[
 \int B\ge I-
 \frac{4\pi(1+\cos a)}{1-(a/U)^2}
 \left(\frac1{U^2}+\frac1{2\pi U}\right).
\]
The tail estimate compares each decreasing grid sum to its first possible summand plus the integral with density \(1/(2\pi)\). Here \(I=\pi\sin a/a\), the subtracted term is below \(6.963\,10^{-7}\), and the resulting lower bound exceeds \(1.94489177\,A\), with \(A=I(1-a/\pi)\) the original upper bound on outer area in the log variable. This is a restriction on a universal bandlimited spatial majorant. The separate moments for *prime* rows above do not apply that expansion to the entire sieve square.
