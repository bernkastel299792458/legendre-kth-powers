# Simultaneous radial estimates from two boundary integrals

Use the bounded analytic function \(G\) on the interpolation strip from [WEIGHTED_GREEN.md](WEIGHTED_GREEN.md). On the real zero-detection rectangle its role is \(|f|\le N|G|\). Fix the same taper, radial polynomial \(D\) of multiplicity \(\mu\), auxiliary line \(\ell\), and right line \(r\) at every source in the following sum. Write \(p=4/3,q=2\), and let \(L,R>0\) be upper bounds for the half-line integrals of \(|G(\ell+it)|^p\), \(|G(r+it)|^q\). They are the existing left and right boundary inputs after multiplication by \(e^U U^2\) and \(U\), respectively. The even symmetry of their absolute values will be used.

Define \(F(y)=\mu^{-1}\log\max_{|z|=e^y}|D(z)|\). It is nonnegative because \(D(0)=1\), increasing by the maximum modulus principle, and convex by the three-circles theorem. At the source abscissa \(a_i\) put

\[
 t_i=(r-a_i)/(r-\ell),\quad 1/\nu_i=t_i/p+(1-t_i)/q,
 \quad P_i=\nu_i t_i/p,\quad s_i=\log N+(t_i/p)\log L+((1-t_i)/q)\log R .
\]

Suppose the angular source measure on that line has nonnegative density \(S_i(t)\) with mean \(b_i\). For the cosine polynomials in [COUPLED.md](COUPLED.md), define \(B_i=b_i(1+2h\epsilon)\), where \(h\) is the number of harmonics and \(\epsilon\) bounds their attenuation on each normalized Poisson boundary. The quantity \(B_i\) then bounds both normalized Poisson convolutions of \(S_i\) on the whole real line. Higher harmonic attenuations decrease, so the first-frequency bound suffices. For constant sources one may use \(B_i=b_i\).

The complete sum of source contributions divided by \(2\pi\mu\) is bounded by

\[
 \frac1{2\pi}\left[
 \sup_{x\in\mathbb R} e^{-x}\sum_i B_iP_i F(s_i+x/\nu_i)
 +\sup_{y\in\mathbb R} e^{-y}\sum_i B_i(1-P_i) F(s_i+y/\nu_i)
 \right]. \tag{1}
\]

To prove it, use the left boundary variable \(X=\log(|G(\ell+iu)|^p/L)\) and the right boundary variable \(Y=\log(|G(r+iu)|^q/R)\). At each ordinate write \(E_{L,i},E_{R,i}\) for integration against that source's two normalized strip Poisson probability measures. The strip subharmonic inequality gives

\[
 \log(N|G(a_i+it)|)
 \le P_i E_{L,i}(s_i+X/\nu_i)+(1-P_i)E_{R,i}(s_i+Y/\nu_i).
\]

The equality of the coefficients on the two edge logarithms is immediate from \(P_i/\nu_i=t_i/p\) and \((1-P_i)/\nu_i=(1-t_i)/q\). Apply convexity and monotonicity of \(F\) as one Jensen inequality to the combined probability measure. Multiply by \(S_i(t)\) and integrate. The nonnegative majorants allow extension from the true rectangle to the full half-line. Evenness gives half the full-line integral. Interchanging the positive kernel integrals replaces \(S_i\) by its convolution on each respective edge, bounded by \(B_i\). Thus the remaining integrands at a given left ordinate are functions of the **same real number** \(X\), even though the original kernels and probabilities at the different abscissae were different. Sum first, use the first supremum in (1), and integrate \(e^X\), whose half-line mass is at most one. The right calculation is identical. Limits at zeros are legitimate by monotone regularization of boundary logarithms, or by viewing \(F(-\infty)=0\). The unchanged angular and right logarithmic costs of Green's identity must be added separately.

## One-dimensional verification

[shared_radial.py](shared_radial.py) bounds the nine existing radial polynomials on the same 257 radii and 257 angles as [the radial polynomial proof](../../round5/kernel/RADIAL.md). On a radius grid point use the upper angular second-derivative correction before taking the logarithm. Linear interpolation in log-radius is an upper bound for \(F\). For \(r\le1/16\), \(F(\log r)\le c r^2\) with \(c=\mu^{-1}\sum_{k\ge2}|D_k|16^{2-k}\). For \(r\ge16\), \(F(\log r)\le A+d\log(r/16)\), where \(A=\mu^{-1}\log\sum |D_k|16^k\), \(d=\deg(D)/\mu\).

The finite \(x\)-grid is chosen so that every source lies on the small branch at its left end and on the large branch at its right end. The small majorants divided by \(e^x\) increase because \(\nu_i<2\). On the large side one verifies \(A+d(s_i+x/\nu_i-\log16)\ge d/\nu_i\) at the endpoint, so all large majorants divided by \(e^x\) decrease from there. For the interior, the **true** sum \(\sum_i B_iP_iF(s_i+x/\nu_i)\) is convex in \(x\). If its grid values are bounded by \(C e^x\), its secants on a mesh of width \(h\) are bounded by \(C e^x(1+h^2 e^h/8)\). The same reasoning applies to the right edge. The reference calculation uses width \(1/8\), and all numerical enclosures use Arb. The source grid and its bounds apply to any nonnegative source means, including the program's angular repairs. The old radial price for each source can also be recovered by applying \(F(y)\le C_{\nu_i}e^{\nu_i y}\) in (1).

With \(U=35,\omega=137,\ell=.484\), the sixth taper on the frozen row, and the program's four-mode source coefficients, the positive and absolute estimates give

| Source | Sum of individual radial prices | Common-boundary price | Separate edge charge |
|---|---:|---:|---:|
| Positive cosine | 0.585025517959 | 0.566645120059 | 0.001515558 |
| Absolute cosine | 0.684417332244 | 0.675887638045 | 0.001109090 |

The two strict source improvements are verified by the following invocation in this directory. These two representative rows alone do not certify a physical interval.

~~~powershell
python -Bu shared_radial.py
~~~

2026-11-20. Joint project attribution to Claude and Codex.
