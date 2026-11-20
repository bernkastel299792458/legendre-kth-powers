# A translated-window extension at the lower fourth-power endpoint

The assumptions are QRH(7/8), the published finite-height RH verification through \(H=3000175332800\), and the analytic inputs in the [preceding low-end proof](FROZEN_FOURTH.md). The interval to contain a prime is \((x,x+4x^{3/4})\), for real \(x=e^L\). The new slab starts at \(L=115.034000\). The analytic inequalities below are handwritten. Arb checks the scalar inequalities and the finite arithmetic.

## Frozen fourth mean

Write \(R=D/2,\ C=H+R,\ v=1.01,\ M=2048,\ B=C+vR\). Use the translated rational weight \(G(t)=\min(1,(vR/|t-C|)^M)\) from [the preceding proof](MOVING_WINDOW.md). Freeze the Riemann–Siegel polynomial at \(y=\lfloor\sqrt{C/(2\pi)}\rfloor\), and select \(J=\tau vR,\ \tau>1\). With \(p=1+4/\log B\) the half integral of \(G|\zeta E_6|^4\) outside \(|t-C|\le J\) is at most
\[
 C_4(\log B)\,B\log^4B\,\frac M{M-p}\tau^{p-M}.
\]
In the layer representation of \(G\), only interval radii \(u\ge J\) contribute there. Both positive and negative portions of that interval are bounded by the cumulative moment to \(C+u\), cancelling the factor \(1/2\). For \(u\ge vR\), \(C+u\le B u/(vR)\) and \(\log^4(C+u)\le\log^4B\,(u/(vR))^{4/\log B}\). Integrating in \(u\) gives the displayed bound. The Riemann–Siegel remainder and varying-prefix fourth norm on the shorter interval are evaluated with its actual \(J\).

On the core, let \(c_n\) be the coefficients of the square of the frozen filtered polynomial. For the linear frequencies \(n/u\) with unrestricted positive integer \(n\), folding the interval of length \(2J'\) with period \(2\pi u\) gives a half integral at most \((J'+\pi u)\sum|c_n|^2\). Indeed the number of copies is at most \(J'/(\pi u)+1\) almost everywhere. The [short log-window convolution and Taylor estimate](../../round4/hilbert/FOLDED.md) apply verbatim with this scalar Parseval bound. Absorb the translation by \(C\) into the coefficients. The half integral on the core is at most
\[
 \frac{\exp((1+\epsilon)\epsilon e^{2\epsilon^3})}{1-4\epsilon/\pi}
 \left[(1+\epsilon)J\sum|c_n|^2+\pi\sum n|c_n|^2\right],
 \qquad \epsilon=J^{-1/5}.
\]
The second norm is an exact nonnegative sum over coprime gcd parameters in the [finite Gram argument](FROZEN_FOURTH.md). Impose just \((\gcd(i,j),30030)=1\) by ordinary inclusion–exclusion on \(2,3,5,7,11,13\), leaving an upper bound. The norm without the \(n\) retains its directed harmonic Gram upper bound. Minkowski on the core and addition of the remote integral finish this estimate. These computations permit independent choices of \(\tau\) at each height. [Frozen fourth moment calculation](compressed_fourth.py)

## A finite exponent on the right boundary

Use \(Q=210,\ U=\log R,\ Y=R e^{\ell_h},\ X=Ye^W,\ e=2\delta/U,\ t=1+e\). The right mean needs only this particular \(e\). Existing finite-head, transition, and remote-head bounds from the [centered Selberg norm](../../round2/right/fine/PROOF.md) apply with both exponent endpoints equal to \(e\). Write \(S=\log32\). After extracting \(Y^{-e}\), the region \(j<Y e^{-S}\) retains its earlier remote-head estimate. Beyond \(X\) one uses \(\exp(-eW)(1+e/Y)/(e\zeta(t))\) after the Selberg factor.

For \(Y e^{-S}\le j\le X\) introduce \(r=\log(X/j)\) and
\[
 G_e(u)=\sum_{m\le e^u}\mu(m)m^{-t}(u-\log m),\qquad
 b(j)=\zeta(t)^{-1}-\frac{G_e(r)-G_e(r-W)}{W}.
\]
The formula follows by expanding the piecewise linear taper. \(G_e(u)=0\) for \(u<0\). Tabulating the two finite Möbius prefixes computes \(G_e\) exactly up to Arb rounding. On a cell \([a,b]\) in \(r\), the slopes of the two \(G_e\)'s lie between the minimum and maximum of the corresponding ordinary cumulative sums of \(\mu(m)m^{-t}\). The outward integer cutoff ranges in the script include all derivatives on the cell. Its \(Y^e\sum j^{-1-e}\) is at most
\[
 e^{-e(W-b)}(e^{b-a}-1+e^b/X).
\]
Indeed the count is at most \(X(e^{-a}-e^{-b})+1\) and \(j\ge X e^{-b}\). This bounds the finite middle of the unsieved norm directly. The other choice is the earlier finite signed estimate.

An additional positive part of the [exact variance](../../round4/density/VARIANCE.md) can be removed for the same range of coprime \(j\). Let \(Z=\prod_{p\mid Q}(1-p^{-t})^{-1}\). Write \(w_k=k^{-t}\) for \(Q\)-smooth integers \(k\); their full weight is \(Z\). The saving before extraction of \(Y^{-e}\) is \(\zeta(t)/Z\) times
\[
 \sum_{(j,Q)=1}j^{-t}\sum_{k<l}w_kw_l(b(jk)-b(jl))^2 .
\]
In one cell retain all \(k\le64\) and all \(k\ge\max(65,\lceil e^b\rceil)\). On the latter set \(b(jk)=1/\zeta(t)\); its full weight is determined by subtracting a finite smooth prefix from \(Z\). For the former set compute the signed values \(a_k=\zeta(t)^{-1}-b(jk)\) at the midpoint using the same \(G_e\). Every derivative in absolute value is at most \(1+1/W\), by bounding the total harmonic sum in a ratio-\(e^W\) interval by \(1+W\). This also applies if the lower endpoint of that interval is below 1. Set \(W_s\) equal to the total weight of both retained groups. The square root of the retained pairwise variance is \(\sqrt{W_s}\) times the norm of the conventionally centered vector in weighted \(L^2\). Orthogonal projection and the triangle inequality give the following uniform lower bound on the square:
\[
 \left[\sqrt{W_s\sum w_ka_k^2-(\sum w_ka_k)^2}
          -W_s(1+1/W)(b-a)/2\right]_+^2.
\]
The coprime \(j\) in the half-open cell carry \(Y^e\)-rescaled mass at least
\[
 e^{-e(W-a)}
   \big[\tfrac{\varphi(Q)}{Q}(1-e^{-(b-a)})-16e^a/X\big]_+.
\]
The count has error at most \(2^4\) by inclusion–exclusion. The cells are disjoint when deductions are made. Use the larger of this deduction and the earlier variance savings on the whole \(j\) range. The resulting normalized low Selberg norm and the preceding explicit high norm may be used with either of the [affine folded mean](../../round4/hilbert/FOLDED.md) or the [local right edge](../mean/RIGHT.md). Each supplies a bound on the same half integral with arbitrary translated phases. [Finite variance calculation](window_variance.py)

On the critical line the critical mollifier's harmonic and unweighted squared norms are bounded from the [squarefree discrepancy](../spectrum/PROOF.md) with \(\rho,c\) as there, \(C_0=18\). The harmonic sum for the base squarefree coefficients is at most \(\rho(\log Y+W/3)+c+3C_0/\sqrt Y\). For the unweighted sum integrate the cumulative count against \(-d\omega^2\), giving \(\rho(2X/W^2)(1-(1+W)e^{-W})+C_0\sqrt X\). The four possible Euler-factor divisors \(r\mid35\) supply factors \(\sum_{r\mid35}1/r\) and 4, respectively. Apply the affine fold modulo 6. Where \(\log R>20\), the existing localized critical mean provides another permitted bound.

## Angular Jensen estimates

For a horizontal edge at either \(H\) or \(H+D\), Jensen uses the holomorphic symmetrization \(F(z)=(P(f_Q(z+it))+P(f_Q(z-it)))/2\) about the real axis. Use circles \(|z-2|=R_c<2\). Put \(N=\lceil H+D+6\rceil\). At real part \(\sigma>0\) on these circles, the imaginary part of each zeta argument has modulus at least \(H-2\) and its full modulus is at most \(N\). Euler summation through the integer \(N\) gives
\[
 |\zeta(s)|\le N^{(1-\sigma)_+}
        (1+\log N+(H-2)^{-1}+\sigma^{-1}).
\]
Here the ordinary sum costs \(N^{(1-\sigma)_+}(1+\log N)\), the pole term uses \(|s-1|\ge H-2\), and the sawtooth remainder is at most \(|s|N^{-\sigma}/\sigma\). The mollifier costs \(X^{(1-\sigma)_+}(1+\log X)\); the Euler factor costs \(\prod_{p\mid210}(1+p^{-\sigma})\). Add 1 to the product to bound \(|f_Q|\). For \(\sigma>1\) the separate bound from vanishing coefficients through \(Y\) is
\[
 Y^{1-\sigma}\sigma\left(\frac{1+\log Y}{\sigma-1}
                     +\frac1{(\sigma-1)^2}\right)
\]
using \(\sum_{n\le u}d(n)\le u(1+\log u)\). On each of 96 equal angular cells on the upper semicircle take the smaller available bound at its smallest real part. The Dirichlet coefficient majorant is valid throughout that half-plane. The lower semicircle has the same real parts. The resulting mean of \(\log(1+|f_Q|)\) bounds \(\int\log|F|/(2\pi)\) after multiplication by the polynomial's degree, since the two summands have the same pointwise majorant.

All tested detection polynomials satisfy \(|[z^k]P|\le{\deg P\choose k}\), and all degrees are at most 15. Thus \(\Re F(2)\ge 2-(1+a_2)^{15}>1/2\), \(a_2=2(\log Y+2)/Y\). Divide Jensen's bound by the multiplicity \(m\ge1\) of the detector root at \(-1\). The resulting degree factors are \(q+1\) for the earlier elementary detectors, 5 for the quintic, and at most 8 for the new [simple and triple root detectors](../kernel/RADIAL.md). The center penalty can use the full \(-\log(2-(1+a_2)^{15})\) for all of them. The right edge retains its \(2a_2^2\) estimate. For radius \(u\) on the real horizontal part, integrate \(1/\log(R_c/u)\) with its right-endpoint sum on 48 cells of \([0,2-s]\). Choosing one whole outer circle separately for each degree is valid. The argument-variation allowance for the two horizontal edges is \(2(2-s)\), as in the earlier proof. [Angular Jensen calculation](circle_mean.py)

## Transfer to real \(x\)

For every ordinate cutoff, compute the scalar bounds on \(\sum_{H<\gamma\le H+D}(\beta-s)_+\), with \(s=.640,.642,\ldots,.874\). Include \(s=.875\) with value zero by QRH. Any selected subsequence of the abscissae that retains both ends gives positive jumps of the successive secant slopes for \(e^{(\beta-1)L_{\min}}\). The chosen lower convex hull of the available bounds yields such a subsequence. Add the verified Riemann–von Mangoldt difference for the mass at \(s=.640\), as in the [moving-window certificate](MOVING_WINDOW.md). The step envelope at the cumulative ordinate cutoffs and the Gaussian tail are from the same certificate. The prime-side and verified-zero costs use the [physical exterior bound](PHYSICAL_TAIL.md) on the whole closed \(L\) slab. All analytic terms and prime powers are included. [Combined verifier](narrow_cover.py)

For \(115.034000\le L\le115.034900\), take \(K=H+3\,200\,000\,000\), 32 equal height cells, \(\delta=.64,\ W=8,\ \ell_h=-2.8\). The full normalized cost is at most \(0.999993372571\), including \(0.001197347386\) for the unverified zeros. The last integer \(n\) with \(4\log n\le115.034900\) is \(3\,088\,556\,668\,063\). All bounds apply throughout the closed real slab.

~~~sh
python -B round5/low/narrow_cover.py --lo 115.034000 --hi 115.034900 --size 3200000000 --parts 32 --case .64,8,-2.8 --check
~~~




## Centered frequency approximation

In any short log window \(u<n\le ue^w\), put \(D_n=\log(n/u)-(n/u-1)\). The inequality for \(\log(1+z)\) gives \(-d\le D_n\le0\) with \(d=(e^w-1)^2/2\). Remove the common phase of the midpoint \(-d/2\). The Taylor series now uses \(|D_n+d/2|\le d/2\). Let \(V\ge V_0\) be a time half-length and use independent slack \(b>0\), enlarged half-length \((1+b)V\), and
\[
 w=w_0(V_0/V)^{2/3},\qquad
 w_0=\left(\frac4{\pi b(1+b)V_0^2}\right)^{1/3}.
\]
The short-window convolution loses at most \(4/(\pi bVw)\). The square of the Taylor norm multiplier is at most \(\exp((1+b)V(e^w-1)^2/2)\). One has \(Vw\ge V_0w_0\) and \(V(e^w-1)^2\le V_0(e^{w_0}-1)^2\), since \(Vw^2\) decreases and \((e^w-1)/w\) increases with \(w\). Hence the common multiplier is bounded by
\[
 C_b=\frac{\exp((1+b)V_0(e^{w_0}-1)^2/2)}
                 {1-4/(\pi b V_0w_0)}.
\]
If the linear Fourier mean on the enlarged interval is bounded by \(\alpha(1+b)V+\beta n\) per unit squared coefficient, integration in \(d(-G(V))\) gives \(C_b[\alpha(1+b)\overline y T\sum|a_n|^2+\beta\sum n|a_n|^2]\), where the mean of \(V\) is \(\overline yT\). For a single fixed core half-length \(J\), take \(T=V_0=J,\overline y=1\). The code uses \((\alpha,\beta)=(1,\pi)\) for the unrestricted integers, \((1,\pi/3)\) for the left modulus 6 and \((1.274,48\pi/210)\) for the right modulus 210. The last two are from the earlier certified Gram bounds. It minimizes over finitely many positive choices of \(b\) for each complete mean. [Centered folded estimate](center_fold.py)

## Reusing a certified high-zero sum after a sieve improvement

At fixed \(K\), increase the two real slab endpoints from \(l_0,h_0\) to \(l,h\), where \(l\ge l_0,\ h\ge h_0\). Suppose both kernel parameters \(a(h_0),a(h)\) lie in \([\pi/2,\pi)\). Then \(a(h)\le a(h_0)\) and \(\sin a(h)\ge\sin a(h_0)>0\). Each spectral numerator on the finite ordinate steps,
\[
 \min\!\left(1,\,
 \sin(\min(\pi/2,[a(1-\gamma/K)]_+))
             +2Qa/(\sqrt\pi K)\right),
\]
decreases when \(a\) decreases. The caps divide this expression by \(\sin a\); each is therefore bounded by the corresponding old cap. The true zero weights \(e^{(\beta-1)l}\) decrease. Consequently the old step function evaluated against the old weights bounds the entire new finite high-zero contribution. This argument uses pointwise domination of the step function and requires no order comparison of differences between consecutive caps. The negligible remote Gaussian tail is separately reevaluated with the new kernel. The verified-zero, prime, and other terms are reevaluated with both new endpoints and the specified sieve addition. The sieve addition must hold uniformly for lengths at least \(e^{70}\). [Fast transfer](reuse_spectrum.py)

For the first additional slab under the previous sieve addition, \(115.034900\le L\le115.035000\), put \(K-H=3800000000,\ \delta=.67,\ W=8,\ \ell_h=-2.9\), using 40 height cells with right edges \((K-H+1280000)z(1/4+3z/4),\ z=i/40\). The cost is below \(0.999994972161\), and its unverified-zero portion is below \(0.001479724675\). The centered folded estimate above permits a further reduction. With the strengthened sieve addition \(1.16613\), the same finite high-zero bound covers \(115.035000\le L\le115.035950\); the full sum is below \(0.999996781334\). [Squarefree Farey proof](SQUAREFREE_FAREY.md)

~~~sh
python -B round5/low/narrow_cover.py --lo 115.034900 --hi 115.035000 --size 3800000000 --parts 40 --mesh 1/4 --case .67,8,-2.9 --check
python -B round5/low/reuse_spectrum.py --lo 115.035000 --hi 115.035950 --eta 1.16613 --row 40 --check
~~~

For transfer to an earlier lower slab endpoint \(l<l_0\), all weights increase by at most \(e^{l_0-l}\), since \(\beta>0\). A sharper bound splits at \(s_*=.64\). For \(\beta\ge s_*\), use \(e^{(1-s_*)(l_0-l)}\) times the entire old upper bound. The remaining finite ordinates contribute at most
\[
 2e^{1/(16Q^2)}c(H)N_H(D)e^{(s_*-1)l}
\]
with the old height cap \(c(H)\), \(D=K-H+1280000\), and the [same explicit counting bound](MOVING_WINDOW.md). This extra term is evaluated before any overall change to the spectral cap. If \(h<h_0\), put \(r=a(h)/a(h_0)\ge1\). For \(z\ge0\),
\(\sin(\min(rz,\pi/2))\le r\sin(\min(z,\pi/2))\) by the decrease of sinc on \([0,\pi/2]\). The additive numerator term scales by \(r\), and the outer truncation at 1 preserves the inequality with this factor. Thus multiply the whole finite charge by at most \(r\sin(a(h_0))/\sin(a(h))\). The new tail is still evaluated independently.

**Final coverage.** One 64-window bound on the finite high-zero sum suffices for both closed intervals below, taking the strengthened sieve addition \(1.16613\). The first interval begins at the finite-height RH endpoint from [the physical-tail certificate](PHYSICAL_TAIL.md).

| Lower \(L\) | Upper \(L\) | Upper bound on complete normalized cost |
|---:|---:|---:|
| 115.033660 | 115.036045 | 0.999999179725 |
| 115.036030 | 115.036065 | 0.999999485750 |

In the reference high-zero computation take \(K-H=4100000000,\ \delta=.68,\ W=8,\ \ell_h=-3,\ l_0=115.035950,\ h_0=115.036100\), using the same quadratic mesh with 64 cells. Its finite high-zero charge is less than \(0.001598181923\). Its *full* cost at those reference endpoints is greater than 1. The interval conclusions use only the certified spectral part there, followed by either of the two separate transfers. At \(L=115.036065\) the last integer is \(n=3\,089\,456\,341\,201\). These calculations close this lower extension under QRH(7/8); the overall middle interval still needs a proof.

~~~sh
python -B round5/low/narrow_cover.py --lo 115.035950 --hi 115.036100 --eta 1.16613 --size 4100000000 --parts 64 --mesh 1/4 --case .68,8,-3 --check-high .001598181923
python -B round5/low/reuse_spectrum.py --row 64 --eta 1.16613 --lo 115.033660 --hi 115.036045 --check
python -B round5/low/reuse_spectrum.py --row 64 --eta 1.16613 --lo 115.036030 --hi 115.036065 --check
~~~

2026-11-20. Project AI authors Claude and Codex. Codex derived and checked the short-window estimates and their finite arithmetic.
