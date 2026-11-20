# Squared Selberg weights in reciprocal bilinear sums

Use the notation and the exact Selberg weights of [the physical sieve](../BILINEAR.md), with \(z=c\sqrt y\) and \(G_*=\ell/2+\log c+1.331\le G(z)\) on \(\ell\le\log y\le u\). Write \(\rho(m)=m/\varphi(m)\). After the gcd extraction and coprimality inversion put \(k=gh\). The two variables are \(d=kx,\ e=kw\), with \(D/2<x\le D,\ F/2<w\le F\). The phase in cycles is \(A/(xw)\), \(A=nt/(gh^2)\), \(M\le t\le M+y\). The coefficients are the original \(\lambda_{kx},\lambda_{kw}\).

## Actual weights on a dyadic row

If \(k\) is not squarefree, both rows vanish. Otherwise \(\lambda_{kx}=0\) unless \(x\) is squarefree and coprime to \(k\). On the row \(D=z/(k2^i)\), divide the \(x\) interval into \(R=8\) equal half-open pieces. On piece \(j\), \(D(R+j)/(2R)<x\le D(R+j+1)/(2R)\), \(0\le j<R\), the largest integer that can enter \(G_{kx}(z/(kx))\) is at most
\[
 V_{ij}=\left\lceil 2^{i+1}R/(R+j)\right\rceil-1 .
\]
In particular \(V_{0j}=1\). This uses the strict lower endpoint of each piece.

Let \(P=210\). For \(s\mid P\) put \(h_s(x)={\bf1}_{(x,P)=s,\ (x/s,s)=1}\), zero when \(s\nmid x\). This detects squarefreeness at each prime of \(P\). The exact period is bounded by \(Ps\) and \(Ps\) is a period. Calculate its mean \(r_s\) and the oscillation \(d_s\) of \(\sum_{m\le t}h_s(m)-r_s t\) over a full period, taking both the left and right values at every integer. Then each half-open interval \(I\) has count at most \(r_s |I|+d_s\).

Let \(k_0\) be the product of the specified singleton values among \(g,h\). Nonzero terms have \((s,k_0)=1\). Set \(H_{ijs}=G_{sk_0}(V_{ij})\), an upper bound on the original inner sum on that piece. Through \(V_{ij}=2048\) sum the integer ceilings of \(2^{32}\mu^2(a)/\varphi(a)\) over the allowed \(a\), then divide by \(2^{32}\). The positive prefix is below \(2^{45}\). For larger cutoffs use \(G(v)\le\log v+2+2.44/\sqrt v\) from the previous proof. Choose \(B\ge\rho(k)\). For an exact \(k\), use \(\rho(k)\). Otherwise \(\rho(m)\) on \(m\le m_0\) is at most \(\rho\) of the largest initial primorial at most \(m_0\). Use the smaller of the bound for the product \(k\le g_{\max}h_{\max}\) and the product of bounds for its known and unknown parts.

For \(p>7\), dropping the squarefree condition gives the positive divisor expansion \(a(p)=\rho(p)^2-1=(2p-1)/(p-1)^2\), extended multiplicatively to squarefree divisors. Every \(r\) so obtained is coprime to \(P\), and \(h_s(rm)=h_s(m)\). Applying the interval count on \(I/r\) gives
\[
 \sum_{x\in I}h_s(x)\prod_{p\mid x,\ p>7}\rho(p)^2
 \le r_s |I| C_2+d_s(1+\log z_{\max})^3,\qquad C_2=\prod_{p>7}(1+a(p)/p).
\]
Indeed \(a(p)\le3/p\) and \(\sum_{r\le D}a(r)\le\sum_{r\le D}\tau_3(r)/r\le(1+\log D)^3\). The product beyond \(p=1000\) costs at most \(\exp(3/1000)\). Empty \(D<1\) rows make no contribution. Consequently
\[
 U_i=\frac1D\sum_{D/2<x\le D}|\lambda_{kx}|^2\le A_i+B_i,\quad
 A_i=\frac{B^2}{G_*^2}\sum_{j,s}\rho(s)^2H_{ijs}^2\frac{r_s C_2}{2R},
 \quad B_i=\frac{B^2}{G_*^2D_{\min}}\sum_{j,s}\rho(s)^2H_{ijs}^2d_s(1+\log z_{\max})^3 ,
\]
where \(D_{\min}=z_{\min}/(g_{\max}h_{\max}2^i)\) and \((s,k_0)=1\). For \(U'_i=D^{-1}\sum(D/x)^2|\lambda_{kx}|^2\), insert \((2R/(R+j))^2\) in both sums. The earlier supremum bound \(L_i\) gives alternative caps \(d_0L_i^2,4d_0L_i^2\), where \(d_0=\min(1,1/2+1/D_{\min})\).

For the [joint Fourier bound](GROUPS.md), restriction to \(r\mid x\), with \(r\) squarefree, costs at most \(\rho(r)^2(A_i/r+B_i)\) after division by \(D\). Put \(x=rv\), use the dimension \(D/r\), bound \(\rho(kr)\le B\rho(r)\), and omit the additional coprimality restrictions at primes of \(r\). The piece thresholds are unchanged. If \((r,k)>1\) the original coefficient vanishes. The same argument retains \(D/x=(D/r)/v\), proving the primed version.

## Sampling and the large sieve

The points \(\xi_x=D/x\) belong to \([1,2]\) and are separated by \(1/D\). The frequencies \(\eta_w=A/(Dw)\) span an interval of length \(K=A/(DF)\) and are separated by \(K/F\). Take \(b=\min(K/F,B_0)\), \(0<B_0\le3/4\), and \(g(t)=\operatorname{sinc}(\pi b(t-3/2))/\operatorname{sinc}(\pi b/2)\). Then \(|g(\xi_x)|\ge1\). Its frequency support has length \(b\), and the transform of \(|g|^2\) is zero at every \(|\nu|\ge b\), including equality. Hence \(H(t)=g(t)\sum b_w e^{2\pi i\eta_wt}\) has frequency support of length \(K+b\), and
\[
 \int |H|^2=\frac{\sum |b_w|^2}{b\operatorname{sinc}^2(\pi b/2)}.
\]
For \(H\) with Fourier support in an interval of length \(L\), \(\sum_x|H(\xi_x)|^2\le (L+D)\int |H|^2\). By Plancherel and duality this is the mean-square estimate for \(\sum a_x e^{2\pi i\xi_xt}\) on an interval of length \(L\). Its integrated off-diagonal is the difference of two Hilbert sums, each bounded by \((\pi D)/(2\pi)\sum|a_x|^2\). This is the uniform-separation real-line inequality, Theorem 2, equation (1.6). [Montgomery–Vaughan, *Hilbert's Inequality*](https://personal.science.psu.edu/rcv4/personal/Publications/s2-8-1-73.pdf)

Cauchy–Schwarz over \(x\) now bounds the squared bilinear sum divided by \(D^2F^2\) by \(U_xU_w\) times
\[
 C_{B_0}\left(1+\frac{K+B_0}{D}\right)\max(1/K,1/(B_0F)),\qquad
 C_{B_0}\ge\{\pi B_0/(2\sin(\pi B_0/2))\}^2 .
\]
Arb checks \(1.001,1.014,1.06,1.235,1.627\) for \(B_0=1/32,1/8,1/4,1/2,3/4\), respectively. Use both orientations. The upper and reciprocal bounds for \(K\) come from separate box corners.

The [older first-derivative bound](../BILINEAR.md) also admits the factor \(U_xU_w\). Cauchy over \(x\) leaves \(\sum|a_x|^2\). For each shift \(r\), the sum over the disjoint runs of \(|b_wb_{w+r}|\) is at most \(\sum|b_w|^2\). The number of runs and the inner diagonal count retain the old bounds. The trivial squared factor is \(d_0 e_0 U_xU_w\).

## Exact Fourier coefficients, zero mode and endpoint difference

The zero term uses \(\sum|\lambda_d|=G(z)^{-1}\sum_{k\le z}\mu^2(k)\sigma(k)/\varphi(k)\). For \(p\le p_0\), put \(u_p=(p+1)/(p-1)\). The local weight has expansion \(1+(u_p-1){\bf1}_{p\mid k}-u_p{\bf1}_{p^2\mid k}\), mean \(1+1/p^2\), and sum of absolute coefficients \(2u_p\). For larger primes use the positive expansion with \(a_1(p)=2/(p-1)\le3/p\). Floor counting gives
\[
 \frac1z\sum_{k\le z}\frac{\mu^2(k)\sigma(k)}{\varphi(k)}
 \le \prod_{p\le p_0}(1+p^{-2})\prod_{p>p_0}(1+a_1(p)/p)
 +\frac{(1+\log z_{\max})^3}{z_{\min}}\prod_{p\le p_0}2u_p .
\]
For each large-prime divisor \(r\) the small-prime weight is counted up to \(z/r\); its pointwise counting error is at most the product of absolute local coefficients. As above the divisor error sum is bounded by \((1+\log z_{\max})^3\). The product tail beyond 1000 costs at most \(\exp(2/1000)\). Taking the least among the tested cuts gives \(C_1\). The Vaaler zero term divided by \(z^2\) is then at most \((C_1/G_*)^2/(J+1)\).

For \(1\le n\le J\), write \(v=n/(J+1)\). The scales including both endpoints are \(2\Phi(v)/(\pi n)\) in the main term, where \(\Phi(v)=\pi v(1-v)\cot(\pi v)+v>0\), and \(2(1-v)/(J+1)\) for the Fejér error. At integral inputs the Fejér correction bounds either limiting endpoint value. [Vaaler, Theorem 18](https://doi.org/10.1090/S0273-0979-1985-15349-2)

The main endpoint phases have opposite signs. Integrating their derivative from \(M\) to \(M+y\) inserts \(2\pi i n/(gh^2xw)\), so the new energy inputs are the primed ones. Relative to charging both endpoints, the extra factor is \(\pi n y/(gh^2DF)=\pi n g\,2^{i+j}/c^2\), for the two dyadic indices \(i,j\). The same sampling estimates hold at every intermediate location. The undifferentiated estimate is also available. The Fejér error keeps both positive endpoint charges.

## Tails and directed computation

Both \(g,h\) must be squarefree for a nonzero summand. In nonsingleton groups majorize this by \(p^2\nmid m\) for every \(p\mid210\). The mean \(\delta\) and the integer-endpoint oscillation \(\Delta\) are computed from a full period \(210^2\). Abel summation bounds the mass on \([a,b]\) by \(\delta(1/a^2+1/a-1/b)+\Delta/a^2\); the old bound remains available. The unchanged tails for \(g,h>2^{32}\) and dyadic index at least 38 are charged to every frequency.

Arb encloses all real inputs. Exact residue counts and positive divisor ceilings are converted only after summation. The main binary64 kernel adds only nonnegative summands. Each finite upper or lower input carries the preceding \(1\pm2^{-48}\) rounding margin. The tested \(83\le\ell\le88,\ M+y\le e^{116},\ c\le256,\ J<2^{28}\) and cutoffs above give normal floating intermediates: \(D_{\min},F_{\min}>2^{-50}\), \(K_{\rm top}<2^{190}\), ordinary row bounds, coefficients and squared weights well inside \(10^{-150}\) and \(10^{220}\). The positive arithmetic of a single summand has fewer than 250 relative rounding factors, including all squarings. At most \(2^{23}\) positive terms are added, checked explicitly. Thus \(1+10^{-7}\) covers the summation and per-term rounding losses. The original \(c^2\) normalization and denominator conversion are applied after returning to Arb.

This establishes location-sensitive upper sieve bounds. Use of such bounds to certify a prime in a particular fourth-power interval requires the separate physical-kernel argument. Project AI authors are Claude and Codex. Codex derived and evaluated the present bounds.
