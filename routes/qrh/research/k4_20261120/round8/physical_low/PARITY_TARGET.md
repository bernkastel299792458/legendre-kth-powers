# A signed Liouville test at a fourth-power location

At \(L=116\), the prime-interval problem has the following sufficient signed-moment tests under the project's QRH(7/8) and published finite-height verification. These are finite reduction targets. The moment itself is not established here. Each row has a different sieve length \(z\) and frequency range; the bandwidth shown concerns the compact pre-Gaussian transform.

| \(\log z\) | Bandwidth | Normalized upper allowance for the negative signed moment |
|---:|---:|---:|
| 31 | \(25H\) | .0047354 |
| 31 | \(31H\) | .0184476 |
| 34 | \(13H\) | .0304206 |
| 36 | \(9H\) | .0323249 |
| 38 | \(7H\) | .0387663 |
| 40 | \(5H\) | .0142998 |

## Pointwise inequality and the actual signed quantity

Take \(x=e^{116},K=H=3000175332800\), \(d=\log(1+4e^{-116/4})/2,\ c=116+d,\ a=(1-10^{-12})Kd,\ I=\pi\sin a/a,\ Q=10000,\ D=e^{c/2}I/K\). Define \(g(u)=(\cos a-\cos u)/(u^2-a^2)\) by continuity. Write \(\mathcal B=\{u:\cos u\le\cos a\}\) and \(W(u)=g(u){\bf1}_{\mathcal B}\). This is exactly the positive exterior of the test at the slightly smaller boundary \(a\). In the absence of primes in the target it upper bounds the whole signed prime contribution.

Let \(S_J(u)=\sum_{j=0}^J b_j\cos(ju)\ge{\bf1}_{\mathcal B}(u)\) everywhere, with \(S_J\ge0\), and put \(P(u)=g(u)S_J(u)\). Let \(\ell(n)=(-1)^{\Omega(n)}\) be the completely multiplicative Liouville function and let \(B_z(n)=\sum_{d\mid n}\lambda_d\) for the exact [Selberg weights](../../round7/physical/BILINEAR.md). For primes \(p>z\), \(B_z(p)=1,\ell(p)=-1\), so \(W\le P_+=(|P|-\ell(p)P)/2\). For composite integers the expression \((|P|-\ell P)B_z(n)^2/2\) is nonnegative. Consequently it suffices to bound the full ordinary term and the *negative of the signed moment*
\[
 \mathcal T=-\frac1{2D}\sum_{n\ge1}\frac{\log n}{\sqrt n}
 e^{-Q^2(\log n-c)^2}\,P(K(\log n-c))\,
                   \ell(n) B_z(n)^2                                        \tag{1}
\]
from above. The sign on (1) is essential. Small primes \(p\le z\) are all in the old remote region \(|\log p-c|>.01\); the inherited far charge covers them. The test is integrated over every integer, including those outside the target and far from the center.

In \(\Re s>1\) the Dirichlet series without the logarithm in (1) factors exactly as
\[
 \sum_{n\ge1}\frac{\ell(n)B_z(n)^2}{n^s}
  =\frac{\zeta(2s)}{\zeta(s)}
     \sum_{d,e\le z}\frac{\ell([d,e])\lambda_d\lambda_e}{[d,e]^s}
  =\frac{\zeta(2s)}{\zeta(s)}D_z(s).
\]
For \(d=gu,e=gv,\ (u,v)=1\), every nonzero coefficient has squarefree \(g,u,v\) pairwise coprime. Thus \(\ell([d,e])\lambda_d\lambda_e=\mu(g)|\lambda_d\lambda_e|\). The signs of both remaining variables have canceled, with one sign depending on the gcd.

## All ordinary main and error terms

The periodization of \(g\) is \(I/(2\pi)\) by its Fourier support in \([-1,1]\) and vanishing of its endpoint transform. On \(\mathcal B\) all contributing translates are nonnegative. On \([-a,a]\) only the central translate is positive. Therefore the exact mass is
\[
 \frac{\|P\|_1}{I}=b_0+
  2\int_0^a \left(\frac{2g(u)}I-\frac1\pi\right)S_J(u)\,du.              \tag{2}
\]
This computes the whole infinite mass without a spatial truncation.

For \(f(t)=(\log t)t^{-1/2}e^{-Q^2(\log t-c)^2}|P(K(\log t-c))|\), \(t\ge1\), each sum over multiples of \(m\) differs from \(\int_1^\infty f(t)\,dt/m\) by at most \(\tfrac12\operatorname{Var}(f)\), by partial summation against the centered sawtooth; both boundary values vanish. The Selberg quadratic density is \(1/G(z)\), \(G(z)\ge G_-=\log z+1.331\), and \(\sum|\lambda_d|\le zC/G_-\) with \(C\) the Euler product in the cited sieve proof. Changing variables \(v=\log t-c\) and using \(c+v\le c e^{v/c}\) where \(c+v\ge0\) bounds the half ordinary normalized main term by
\[
  \frac{c}{2G_-}\exp\left(\frac{(1/c+1/2)^2}{4Q^2}\right)
       \frac{\|P\|_1}{I}.
\]
The amplitude \((c+v)_+ e^{-v/2-Q^2v^2}\) is log concave in its support, with variation twice its maximum. If \(B_j=\sum k^j|b_k|\), then \(\|P'\|_1+2\|P\|_\infty\le4B_0+6B_1\). Indeed \(\|g\|_\infty\le1/2,\ \|g\|_1\le6,\ \|g'\|_1\le3\). On \(|u|\le4\) use \(|g'|\le1/6\) from the [signed-lobe proof](../../round7/physical/WEIGHTED_LOBE.md). Beyond 4 use \(a<2,\ |g|\le(8/3)u^{-2},\ |g'|\le(4/3)u^{-2}+(64/9)|u|^{-3}\). Thus the half ordinary normalized remainder is at most
\[
 \frac{c K e^{-c}}{4I}
 e^{(1/c-1/2)^2/(4Q^2)}
       \left(\frac{z C}{G_-}\right)^2(4B_0+6B_1).
\]
The prime powers, remote small-prime allowance, pole loss, verified zeros and archimedean term are from the [edge proof](../../round2/local/EDGE.md). The unverified positive Gaussian tail uses the QRH formula there at \(K-H=0\). These inherited positive costs total below \(4.648\,10^{-8}\). The code subtracts all these ordinary costs before printing the allowance in (1).

## Finite polynomial certification

The [stored coefficients](majorants.json) are rational decimals from a floating-point search. The [verifier](parity_target.py) uses no optimization software. On each of \([0,a]\) and \([a,\pi]\), it evaluates 2049 grid points and raises the constant coefficient by the largest detected deficit plus the bound \((\Delta u)^2\sum j^2|b_j|/8\) on linear interpolation error. The resulting majorization holds throughout both closed intervals, including \(\pm a\). To certify (2), use 2048 trapezoids, \(g(u)=\tfrac12\operatorname{sinc}((a+u)/2)\operatorname{sinc}((a-u)/2)\), \(|g''|\le 1/12\), and the printed bound on the integrand's second derivative. The Fourier transform of \(P\) is the exact sum of translates of \(\widehat g\), hence vanishes outside \([-(J+1),J+1]\).

~~~powershell
python -B round8/physical_low/parity_target.py
python -B round8/physical_low/parity_target.py --degree 6 --logz 38 --margin .0387663
~~~

## Why moving the same correction below the verified height does not suffice

At this test location \(p=|\mathcal B\cap[-\pi,\pi]|/(2\pi)=1-a/\pi>1/2\). With the true target boundary \(Kd\) in place of \(a\) the same strict inequality holds. For *any* integrable real test \(T\) of bandwidth at most \(K\), periodization against the class of arcs with boundary \(Kd\) gives \(\int_\mathcal B T=p\int T\) in angular coordinates. For any real \(P\) of the same bandwidth this implies \(\int_\mathcal B P_+\le p\int|P|\): subtracting \(p\int|P|\) leaves \((1-2p)\int_\mathcal B P_- -2p\int_{\mathcal B^c}P_-\le0\). For a signed original test \(T\) of mass \(I_T>0\), the ordinary positive remainder to a parity correction must cover \((T-P_+)_+\) on the exterior. On \(\mathcal B\) its integral is at least \(p(I_T-\int|P|)\). If the available comparison uses constant nonnegative ordinary densities \(\rho_o,\rho_P\), their best even idealized cost is at least
\[
 \frac{\rho_P}2\int|P|
     +\rho_o\max(0,p(I_T-\int|P|))
       \ \ge\ I_T\min(\rho_o p,\rho_P/2).
\]
This includes translations and signed linear combinations. On an actual truncated physical window, subtract the lost \(|T|\) and \(|P|\) tails from the relevant terms before applying the lower bound. Thus at \(L=116\), taking \(\rho_P=c/G_-\) for \(\log z\sim31\) cannot give a pointwise test by this particular wholly low-frequency splitting, even if its signed moment vanished. The table instead uses explicitly specified higher-frequency bands.

## The unverified bands require phase information

Choose any fixed \(\sigma\in(7/8,1]\). On the Mellin line of (1), with \(\eta=\sigma-1/2\), put
\[
 \Psi_\eta(t)=K\int_\mathbb R e^{-Q^2v^2+\eta v}P(Kv)e^{itv}\,dv .
\]
After taking absolute values the corresponding normalized integral has density \(e^{-(1-\sigma)c}|D_z(\sigma+it)\zeta(2\sigma+2it)/\zeta(\sigma+it)|\,|c\Psi_\eta+\partial_\eta\Psi_\eta|/(4\pi I)\). Its part on \(1.2K\le t\le1.4K\) alone exceeds **785** on every displayed polynomial. This concerns the absolute majorant on that constant line; the needed quantity (1) retains the phase \(e^{itc}\).

Indeed on this band only the first and second cosine sidebands contribute to \(\widehat P(t/K)\), and \(b_1,b_2<0\). Its modulus is at least \(\pi |b_1|\sin(.6a)/(2a)\). The full transform is Lipschitz with constant \(\pi B_0\) and bounded by \(\pi B_0/a\). Gaussian convolution changes it by at most
\[
 \pi B_0\frac{2Q}{\sqrt\pi K}+\frac{\pi B_0}{a}
 \left(e^{1/(16Q^2)}-1+\frac{e^{1/(16Q^2)}}{2Q\sqrt\pi}\right)
\]
using the absolute first moment of a Gaussian of variance \(2Q^2\). Differentiating its complex multiplier bounds \(|\partial_\eta\Psi_\eta|\le e^{1/(16Q^2)}(\pi B_0/a)(1/(4Q^2)+1/(Q\sqrt\pi))\). The kernel including the factor \(c\) has modulus greater than 54 on the specified interval.

The finite polynomial \(D_z\) has constant coefficient 1. Its sum of absolute coefficients with weights \(m^{-\sigma}\) is at most \(\sum_{d,e\le z}[d,e]^{-7/8}\le64z^{1/4}\sum_g g^{-9/8}\le576z^{1/4}\), by extracting the gcd and summing the two one-variable harmonic powers. Thus the integral of \(|D_z|\) on the band of length \(K/5\) is at least \(K/5-1152z^{1/4}/\log2\). Also \(|1/\zeta(2\sigma+2it)|\le\zeta(7/4)\le7/3\). Euler summation through \(N=2K\) gives \(|\zeta(\sigma+it)|<350\). For this bound use \(\sum_{n\le N}n^{-7/8}\le1+8N^{1/8}\), the main tail \(N^{1/8}/t\), and endpoint/integral remainder \((1+(1+t)/(7/8))N^{-7/8}\). Multiplying these independent lower bounds and \(e^{-c/8}/(4\pi I)\) proves the diagnostic, including the factor \(1/2\) in (1). A proof of the signed moment through the unverified high bands remains open.

~~~powershell
python -B round8/physical_low/high_absolute.py
~~~
