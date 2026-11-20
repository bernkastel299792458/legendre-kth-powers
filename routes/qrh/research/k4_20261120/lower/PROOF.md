# A finite-height prime interval up to \(\log x=114.96\)

**Proposition.** For every real \(x\) with \(113.1\le L=\log x\le114.96\),
there is a prime in \((x,x+4x^{3/4})\). In particular this proves the desired
assertion for \(1904041788884\le n\le3031261544136\), on setting \(x=n^4\).
The proposition uses published unconditional results, including verified RH
to finite height. The numerical inequalities are checked by 256-bit Arb
in [check_lower.py](check_lower.py). The analytic argument is written mathematics.

The estimate combines an explicit formula with an upper bound for the exterior
prime terms, following the approach of Carneiro, Milinovich and Soundararajan
(CMS). Here the spectral cutoff comes from finite-height RH. The signed test
function has an exact expression for its positive mass outside the target.
The primary inputs are [CMS, Lemmas 6 and 9 and (6.10)](https://arxiv.org/pdf/1708.04122),
[Montgomery–Vaughan, Theorem 2](https://doi.org/10.1112/S0025579300004708)
and [Platt–Trudgian, Theorem 1](https://arxiv.org/pdf/2004.09765).

## 1. A test function with a computable exterior cost

Use angular Fourier transform \(\widehat f(t)=\int f(v)e^{itv}\,dv\).
Set \(H=3\cdot10^{12},\ Q=10^6,\ K=H-128Q,\ r=10^{-4},\ a=79/40\).
Write \(d=\tfrac12\log(1+4e^{-L/4}),\ c=L+d\). The log interval is
\((c-d,c+d)\), and the certificate verifies \(Kd>a\) throughout by
evaluating \(d\) at its minimum.

Define
\[
g(u)=\frac{\cos a-\cos u}{u^2-a^2}
     =\frac1a\int_0^1\sin(a(1-t))\cos(ut)\,dt,\qquad
F(v)=g(Kv)e^{-Q^2v^2}.
\]
The second expression follows by integration and fills the removable
singularities. It implies \(|g|\le g(0)=(1-\cos a)/a^2=:g_0\).
The spectrum of \(g(Kv)\) equals
\[
G_0(t)=\frac{\pi}{aK}\sin(a(1-|t|/K))\,\mathbf1_{|t|\le K}.
\]
In particular it is nonnegative, has \(L^1\) norm \(V=2\pi g_0\),
and \(\int g(u)\,du=I:=\pi\sin(a)/a>0\).

For \(|u|>a\), \(g(u)>0\) exactly when the residue of \(u\) modulo
\(2\pi\) lies in \((a,2\pi-a)\). At the removable points the values do
not affect the integrals. The periodization \(\sum_jg(u+2\pi j)\)
converges uniformly on a period by quadratic tail decay. Its nonconstant
Fourier coefficients vanish, including the coefficients at the two spectral
endpoints. Its constant value is \(I/(2\pi)\). On the stated residue
interval every translate is positive and exterior. Consequently
\[
 \int_{|u|>a} g(u)_+\,du=(1-a/\pi)I. \tag{1}
\]

Each positive exterior lobe and each of its nonempty strict superlevel
sets is an interval. Indeed
\[
 g(u)=\tfrac12\operatorname{sinc}((u+a)/2)
                 \operatorname{sinc}((u-a)/2),
 \qquad \operatorname{sinc}(s)=\sin(s)/s .
\]
On each interval of nonvanishing, \(\log|\operatorname{sinc}s|\) is
concave because its second derivative is \(1/s^2-1/\sin^2 s\le0\),
with the removable value at zero understood. On the first positive
exterior lobe \(a\le u<2\pi-a\) both sinc factors decrease as their
arguments range in \([0,\pi]\). Its maximum is \(g(a)=\sin a/(2a)\).
On \((2\pi j+a,2\pi(j+1)-a)\), \(j\ge1\), the numerator is at most 2
and the denominator is at least \(4\pi^2j^2\). Reflection gives the
following bound for the sum of maxima over all exterior lobes on both sides,
also after intersection with \(|u|\le Kr\),
\[
 S_*=\frac{\sin a}{a}+\frac16 . \tag{2}
\]

## 2. Upper bound for the arithmetic side if the interval is empty

Let \(D=e^{c/2}I/K\). At every arithmetic occurrence of \(F\) we may use its
positive part for an upper bound. Consider first the primes from
\(F(\log p-c)\) with \(|\log p-c|\le r\). If the target open interval
contains no prime, all these primes lie in \(|\log p-c|>a/K\), since
\(a/K<d\), including any primes at the target endpoints.

For \(Y=e^c/K,\ U=\log Y=c-\log K\), set
\[
 A=2(U-1)/U^2,\qquad B=2Y/U^2.
\]
Every interval near \(e^c\) of arithmetic length \(y\) contains at most
\(Ay+B\) primes. For \(y\ge e^2\), the tangent at \(Y\) to the concave
function \(2y/\log y\) on that range gives this from Montgomery–Vaughan.
This holds also for a closed interval by expanding the interval on the left
and taking a limit. For \(0\le y<e^2\), it follows from the integer count
\(y+1<10<B\). The monotonicity of \(2e^U/U^2\) for \(U>2\) justifies
checking the last inequality at \(U=L_- -\log K,\ L_-=113.1\).

On each exterior lobe use the level sets of \(g(Kv)_+\), intersected with
\([-r,r]\). Their images under \(v\mapsto e^{c+v}\) are intervals of
arithmetic length at most \(e^{c+r}\) times their log length. Sum the
tangent bound and integrate in the level. The integrated log lengths are
at most \((1-a/\pi)I/K\) by (1). The integrated number of nonempty lobe
intervals is at most \(S_*\) by (2). Each prime weight
\(\log p/\sqrt p\) is at most \((c+r)e^{-(c-r)/2}\), and the Gaussian
factor is at most 1. The normalized exterior prime contribution is therefore
bounded by
\[
 2(c+r)e^{3r/2}\frac{U-1}{U^2}(1-a/\pi)
 +2(c+r)e^{r/2}\frac{S_*}{U^2 I}. \tag{3}
\]
This uses only upper counts in intervals. The sign of every discarded
arithmetic term is taken into account by positive-part majorization.

In (3) both coefficients decrease with \(c\) over this range. For the first,
put \(J=\log K+r>2\), so that
\((c+r)(U-1)/U^2=1+(J-1)/U-J/U^2\), decreasing for \(U>4\).
The second is proportional to \(1/U+J/U^2\). Thus \(c=L_-\) in (3)
gives a uniform upper bound.

For the near-center prime powers of exponent at least two, use the elementary
\(\psi(y)-\theta(y)\le\sqrt y\,(\log y)^2/(2\log2)\). It follows by
bounding each \(\theta(y^{1/j})\), \(j\ge2\), by
\(\sqrt y\,\log y/2\), and the number of exponents by \(\log y/\log2\).
The unnormalized near prime-power sum is at most
\[
 g_0 e^r(c+r)^2/(2\log2). \tag{4}
\]

For the terms \(F(\log m-c)\) with \(|\log m-c|>r\), and every term
\(F(\log m+c)\), bound \(\Lambda(m)\le\log m\). Extract
\(\exp(-(Qr)^2/2)\) from each Gaussian. Completing the square gives
\(m^{3/2}\exp(-Q^2(\log m\mp c)^2/2)\le
\exp(3c/2+9/(8Q^2))\) for either sign. Since
\(\sum_{m\ge2}(\log m)/m^2<2\) (compare the decreasing function from 2
onward with its integral), their combined unnormalized upper bound is
\[
 4g_0\exp(3c/2+9/(8Q^2)-(Qr)^2/2). \tag{5}
\]

## 3. Lower bound from the explicit formula

Write \(G(z)=\int F(v)e^{izv}\,dv,\ h(z)=\cos(cz)G(z)\). Real-axis
Gaussian convolution and analytic continuation give
\[
 G(z)=\frac1{2\sqrt\pi Q}\int_{-K}^K G_0(t)e^{-(z-t)^2/(4Q^2)}\,dt .
\]
Thus \(h\) is entire, with Gaussian decay in every fixed horizontal strip.
The arithmetic sums converge by their log-Gaussian factors. With CMS
Lemma 6 one obtains
\[
 \sum_{m\ge2}\frac{\Lambda(m)}{\sqrt m}
  [F(\log m-c)+F(\log m+c)]
 =2\cosh(c/2)G(i/2)-\sum_\rho h(\gamma-i(\beta-1/2))+\mathcal A ,
\]
where \(\mathcal A=(2\pi)^{-1}\int h(t)\Omega(t)\,dt\),
\(\Omega(t)=\Re\psi_\Gamma(1/4+it/2)-\log\pi\).
In CMS's cyclic-frequency convention \(\widehat h(\log m/(2\pi))\)
equals \(\pi[F(\log m-c)+F(\log m+c)]\). The two symmetric prime terms
in the source formula yield the coefficient shown above.

Evenness gives \(G(i/2)=\int g(Kv)e^{-Q^2v^2}\cosh(v/2)\,dv\).
The multiplier lies between \(e^{-Q^2v^2}\) and 1, using
\(\cosh z\le e^{z^2/2}\) on the real axis. For \(|u|\le2a\) we have
\(u^2|g(u)|\le4a^2g_0\le8\); for \(|u|>2a\) the quotient formula gives
\(u^2|g(u)|\le8/3\). Integrating the resulting bound against
\((1-e^{-Q^2v^2})/v^2\), whose integral is \(2\sqrt\pi Q\), yields
\[
 G(i/2)\ge I/K-16\sqrt\pi Q/K^2>0.
\]
Hence the pole divided by \(D\) is at least \(1-16\sqrt\pi Q/(KI)\).

Finite-height RH puts every nontrivial zero with \(|\gamma|\le H\) on the
critical line. For real \(t\), \(|G(t)|\le\pi/(aK)\) by convolution with a
probability density. CMS Lemma 9 gives \(N(t)\le t\log t\le t^2\)
for \(t\ge H\), by bounding its main term by \((t/2)\log t\) and
its remaining terms by \(0.15\log t+4\). The low zero sum in modulus
is at most \(2H\log H\,\pi/(aK)\).

For \(\gamma>H\), \(|\beta-1/2|\le1/2\) and
\[
 |G(\gamma-i(\beta-1/2))|\le
  \frac{V e^{1/(16Q^2)}}{2\sqrt\pi Q}
  e^{-(\gamma-K)^2/(4Q^2)}.
\]
The translated cosine contributes at most \(\cosh(c/2)\). Stieltjes
integration by parts with \(N(t)\le t^2\) for \(t\ge H\) gives
\[
 \int_{(H,\infty)} e^{-(t-K)^2/(4Q^2)}\,dN(t)
 \le H^2(1+4Q^2/(H-K)^2)e^{-(H-K)^2/(4Q^2)}.
\]
Indeed one may discard the nonpositive lower endpoint term and use
\(K+v\le Hv/(H-K)\) for \(v=t-K\ge H-K\) in the remaining elementary
Gaussian moment. Multiply by 2 for conjugate zeros. Using
\(2\cosh(c/2)/D\le2K/I\) gives the normalized high-zero bound in the code.

Finally \(|\Omega(t)|\le7+\log(1+|t|)\). To see this, put \(b=|t|/2\).
The increase of \(\Re\psi_\Gamma(1/4+ib)\) over \(\psi_\Gamma(1/4)\) is
the sum of \(b^2/[z(z^2+b^2)]\) over \(z=j+1/4,\ j\ge0\).
The first term is at most 4. The subsequent terms, bounded by a first
value and a decreasing integral from 1, sum to at most
\(1+\tfrac12\log(1+b^2)\). Use
\(-5<\psi_\Gamma(1/4)=-\gamma_E-\pi/2-3\log2<0\).
This series follows directly from the [digamma expansion](https://dlmf.nist.gov/5.7.E6).
The Gaussian convolution has absolute first displacement moment \(2Q/\sqrt\pi\).
Applying Jensen's inequality to the logarithm and \(|h(t)|\le G(t)\)
on the real axis bounds \(|\mathcal A|\) by
\[
 \frac{V}{2\pi}\left(7+\log(1+K+2Q/\sqrt\pi)\right).
\]

## 4. Uniform comparison

The scalar check uses \(D\ge e^{L_-/2}I/K\) and
\(c\le 114.96+d(L_-)\) wherever needed in (4), (5) and the small
analytic errors. The sum of the pole loss, the zero and gamma terms, and
the arithmetic upper bound under the empty-interval hypothesis is at most
\(0.997662D\). Thus the upper
bound under that hypothesis is strictly smaller than the explicit-formula
lower bound. This proves the proposition. The margin exceeds \(0.002338D\).

Replay with Python and python-flint using `python -B check_lower.py`.
The scalar verification covers the entire real interval by the monotonic
comparisons above, and checks the two adjacent integer endpoints separately.
