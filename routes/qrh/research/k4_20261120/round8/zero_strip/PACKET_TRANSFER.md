# Transferring the signed neighbor deficit to a positive strip test

If the second rectangle contains \(R\ge420071\) exceptional zeros, then for \(A=33.25\) their actual prime phases satisfy
\[
 -R^{-1}\sum_{p\le e^A}v_p\Re\sum_{i=1}^R p^{i\gamma_i}
 >7.00219,\qquad
 -(\sum v_p)^{-1}R^{-1}\sum_{p\le e^A}v_p\Re\sum_i p^{i\gamma_i}>.06242.
\]
At this same bandwidth the [single-root bound](STRIP_BOUNDARY.md) gives \(6.85817570\) and .06114286. The increase uses the signed high-frequency Gram terms. The hypotheses permit multiplicity and arbitrary placement, with no single-root or independence assumptions on the surrounding zeros.

Use the [rational power certificate](POWER_PACKET.md) with \(U=33.66,\ v=4.60,\ \eta=.75,\ D=1,\ m=5,\ h=2.13,\ \lambda=.77\). It gives a signed deficit exceeding .31967 per selected root. For these slightly wider packets, in place of the bound 3 in (2) use \(-\zeta'(q)/\zeta(q)\) with \(q=1-\Theta+U/v^2>1\) whenever \(U/v^2<2\). This is simply the Euler series after dropping the remaining negative Gaussian factor \(e^{-(\log n)^2/(2v^2)}\).

The shared prime-energy routine also allows a wider Gaussian when the logarithmic derivative of \(f\) at \(X=e^{16}\) ceases to be positive. In that branch the derivative of \(xf\) is positive up to \(X\), as verified by its logarithmic derivative at \(X\). Hence \(x(-f')_+\le f\) there. Integrating by parts with \(\psi(x)<1.04x\) bounds the early contribution by \(1.04[X f(X)+I_\mathrm{early}]\), with \(I_\mathrm{early}\le B_0\,16v\sqrt\pi\,\operatorname{erfc}((m_0-16)/v)/2\), where \(m_0=U+(1+j-2\Theta)v^2/2\) and \(B_0\) is as in PACKET.md. This follows by restricting the Gaussian to \(u=\log x\le16\) and replacing its linear factor \(u\) by 16. The routine uses the exact Gaussian integral over \(x\ge X\) in the large-\(x\) term. These alternatives preserve the preceding narrow-band formulas.

To convert disappearance of arithmetic energy to an actual lower bound for another detector, let \(F_A(x)=(1-\cos(Ax))/(Ax^2)\). Its even harmonic continuation with the same boundary data on both sides of \(|\Im z|\le B=\Theta-1/2\), evaluated at distance \(a_j=\Theta-\beta_j\) from the upper boundary, is the pair contribution \(G_A(\beta_j,y)\) in the strip formula. It is a positive convolution against the boundary data. The total harmonic measure of the shifts \(|x|\le w\) is
\[
 M(a_j,w)=\frac2\pi \arctan\left(\frac{\sinh(\pi w/(2B))}
                             {\sin(\pi a_j/(2B))}\right).
\]
Indeed the sum of the two usual strip Poisson densities equals
\(\cosh(\pi x/(2B))\sin(\pi a_j/(2B))/(2B[\sinh^2(\pi x/(2B))+\sin^2(\pi a_j/(2B))])\). This also follows by mapping the strip to a half-plane by an exponential. Integrate by substitution \(z=\sinh(\pi x/(2B))\). At \(a_j=0\) the measure is a unit atom at zero. Throughout \(0\le a_j\le\Theta-.75<B\), \(M\) decreases with \(a_j\).

Partition \(a_i\in[0,.01]\) into eight cells, \(a_j\in[0,\Theta-.75]\) into 64 and \(y=|\gamma_i-\gamma_j|\in[0,1]\) into 384. For a cell \([l,r]\) and each ordered \(w_k=k^2/10000,\ 1\le k\le48\), let
\[
 f_k=\frac{[1-\sup_{u\in[l-w_k,r+w_k]}\cos(Au)]_+}
             {A(r+w_k)^2}.
\]
These lower bounds for the boundary function on the indicated shifted intervals decrease with \(k\). If \(b_j\) is the upper endpoint of the \(a_j\)-cell, the weighted sum \(\sum_k[M(b_j,w_k)-M(b_j,w_{k-1})] f_k\), with initial cumulative mass zero, bounds \(G_A\) from below. This follows by summation by parts using the lower bounds for the true cumulative masses. Uncovered shifts have nonnegative boundary data.

On each cell the verifier divides this lower bound by an upper bound on the negative part of the Gaussian product \(-\Omega_{ij}\) from (1) in PACKET.md. The frequency range of its cosine is obtained directly from the cell bounds on \(a_i,a_j,y\); when its negative part vanishes, no payment is required. The absolute envelope uses the lower endpoints for the two decreasing \(k\)-factors and \(y^2\), and drops the factor \(e^{-v^2(a_i-a_j)^2/4}\le1\). Divide also by \(2/(2-\lambda)\) to handle both possible \(c_{ij}\). Consequently, summing \(G_A\) over all retained negative neighbors on each row of (4) contributes more than .14401 per root on average whenever \(R\ge420071\). Positive off-diagonal terms in (4) only raise the required absolute negative sum. The retained neighbors have distinct ordinates, so the earlier own reflected pair is still available in full. Adding these two contributions to the explicit formula gives the displayed bounds.

~~~powershell
python -B packet_transfer.py
~~~

2026-11-20. Joint project attribution to Claude and Codex.
