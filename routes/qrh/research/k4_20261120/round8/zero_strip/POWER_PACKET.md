# A positive rational comparison across the QRH strip

This strengthens the [signed Gaussian pair condition](PACKET.md). All heights, real parts, multiplicities and neighbor conventions are those of that proof. In every row a neighbor must have a distinct ordinate at distance at most 1.5, real part exceeding the displayed cutoff, and negative real Gaussian inner product from equation (1) there.

| Real-part cutoff | \(m,h\) | \(U,v,\lambda\) | Maximum roots without such a neighbor | Minimum roots with such a neighbor if the count fails | Signed deficit per root |
|---:|---:|---:|---:|---:|---:|
| .800 | 5, 1.507 | 33.295, 3.616, .507 | 132055 | 288016 | \(>.22523\) |
| .815 | 6, 1.575 | 33.633, 3.917, .463 | 212245 | 207826 | \(>.12112\) |
| .820 | 6, 1.553 | 33.745, 4.020, .447 | 268452 | 151619 | \(>.07471\) |
| .825 | 6, 1.530 | 33.840, 4.110, .440 | 363046 | 57025 | \(>.02181\) |

These are necessary conditions if there are at least 420071 roots to the right of .865 in the second rectangle. Each row uses its own packet.

## The prime series on the units modulo 210

Delete all powers of \(2,3,5,7\) from \(P\). The one-sided bound for the resulting error in place of the even-prime term in (2) is \(M^{-1}k(\Theta)\sum_{p\mid210}(\log p+M)\), by completing the square on each unimodal lattice sum. Negative frequencies are still bounded as one series. For the redefined \(P\) and \(J=[H-b,T+b]\), \(b=10\), the compressed integer Hilbert operator bound \(K_{210}\le.915503\) and the sliding frequency window give
\[
 M^2\int_J |P|^2\le\frac{1}{1-\epsilon}\min\{(T+b+B)S_0+K S_1,\ (|J|+2B)S_0+2K S_1\},
\]
where \(B=10^9,\ w=.001,\ \epsilon=4/(\pi wB),\ K=.915503+ e^{w/2}(e^w-1)^2/12\). The first inequality discards the interval to the left of \(H-b\), applies the centered sliding-window estimate on \([-(T+b),T+b]\), and halves by real-coefficient symmetry. The second applies the two-endpoint estimate on the interval of length \(|J|+2B\) centered at the midpoint of \(J\), retaining both endpoint costs. Both permit the same unrestricted diagonal norm bounds \(S_0,S_1\). The verifier certifies the modulus-210 spectral constant by positive Schur pivots. [Integer Hilbert spectrum and sliding window](../../round4/hilbert/PROOF.md)

## The zero comparison

Replace the Poisson mass used to bound omitted zeros by the following kernel. Write \(z_i=(\rho_i-1/2)/i\). For \(c=h+1/2>1\), select an integer \(m\ge1\) with \(m\arcsin((\Theta-1/2)/h)<\pi/2\), and use
\[
 K_{m,h}(x)=(h^2/(h^2+x^2))^m,\qquad \mathcal P(t)=\sum_\rho \Re K_{m,h}(t-z_\rho).
\]
For a mirror pair \(\beta,1-\beta\), \(b_\beta=\beta-1/2\ge0,\ y=(t-\gamma)^2\), its total is
\[
 2\Re\left[\frac{h^2}{h^2-b_\beta^2+y+2i b_\beta\sqrt y}\right]^m.
\]
The denominator has positive real part and argument of modulus at most \(\arcsin(b_\beta/h)\), so the pair weight is positive on the full QRH strip. At a selected zero its own pair contributes at least \(2(h^2/[h^2-(s-1/2)^2])^m\). For the critical line assign half of a coincident pair, as before.

Put \(d_j=2^{1-2m+j}{2m-j-1\choose m-j} h^j\). Partial fractions at the two poles give the meromorphic identity
\[
 K_{m,h}(x)=\frac12\sum_{j=1}^m d_j[(h+ix)^{-j}+(h-ix)^{-j}].
\]
At real \(t\), reflection of the zero multiset then gives \(\mathcal P(t)=\sum_{j=1}^m d_j \sum_\rho\Re(c+it-\rho)^{-j}\). The \(j=1\) sum is understood by conjugate symmetry or as the absolutely convergent sum of its real parts. By the completed logarithmic derivative and its derivatives, uniformly \(H\le t\le T\),
\[
 \mathcal P(t)\le\sum_{j=1}^m d_j\,[D_j(c)+G_j],
\quad D_j(c)=\frac{(-1)^{j-1}}{(j-1)!}
             \left(\frac d{dc}\right)^{j-1}(-\zeta'/\zeta)(c).
\]
Indeed the bound for the arithmetic part is its real Euler series with phases removed. Here \(G_1=\tfrac12\log[(T+3)/(2\pi)]+10^{-8}\), and \(G_j=3/H^j+\pi/(4 H^{j-1})\) for \(j\ge2\), by the convergent polygamma series and its integral comparison. These estimates use \(1<c<6\); positivity of the comparison extends over the full strip by the explicit angle condition. [Completed derivatives and partial fractions](../../round7/mobius/POISSON_POWERS.md) [Large-height first derivative](../../round7/qrh_strip/RIGHT_EDGE.md)

The sign in the real Euler series for the actual zero sum is negative, common to every derivative after multiplication by its partial-fraction sign. Thus each prime power's surplus over its true contribution is \(w_{p,k}[1+\cos(kt\log p)]\), where \(w_{p,k}=(\log p)p^{-ck}\sum_j d_j(k\log p)^{j-1}/(j-1)!\). Retain \(p<300,\ 1\le k\le9\) in this nonnegative surplus. For each prime minimize the resulting trigonometric polynomial over \([0,\pi]\). Its minimum is at a stationary point, including both endpoints, and its second derivative has modulus at most \(\sum k^2 w_{p,k}\). Subtracting \((\pi/128)^2\sum k^2 w_{p,k}/8\) from the minimum of its 129 grid samples bounds the actual minimum from below. Sum the positive parts of these lower bounds and subtract from the preceding mass ceiling.

It remains to bound each omitted pair's Gaussian envelope divided by its positive mass. The exact ordinate-weight ratio is
\[
 \frac{e^{-v^2y/4}}2
 \frac{\big[(h^2-b_\beta^2+y)^2+4b_\beta^2 y\big]^{m/2}}
 {h^{2m}\cos(m\arctan(2 b_\beta \sqrt y/(h^2-b_\beta^2+y)))}.
\]
For the exponential times the modulus numerator on a rectangle use \(z=b_\beta^2,\ d=v^2/4\). Its squared modulus before raising to a power is \((h^2+y+z)^2-4h^2z\), convex in \(z\), so take the two endpoints. At either endpoint the exponential times the \(m\)-th power of the modulus increases up to the point \(y=[m/d+\sqrt{(m/d)^2+16h^2z}]/2-h^2-z\) and decreases afterwards; clamp that point to the rectangle. For the angle, increase \(b_\beta\) and then maximize in \(y\) by clamping \(h^2-b_{\beta,\max}^2\) to the rectangle. On \(y\ge9\) use \(|h^2+(\sqrt y+i b_\beta)^2|\le h^2+y+b_\beta^2\) and the uniform angle bound. The resulting polynomial times the exponential decreases there, as checked by \(m/(h^2+9)<v^2/4\).

Split each of \([1/2,\eta]\) and \([\eta,\Theta]\) into 72 real-part cells and each of \([0,D^2]\), \([D^2,9]\) into 144 squared-distance cells. For a low pair use the upper endpoint for the sum of the two \(k\)-factors. For a high pair outside the distance bound, do the same but restrict to \(y\ge D^2\). For its uncounted left member use the lower endpoint of the real-part cell for \(k(\Theta+\beta-1)\). Charge the maximum of these three case bounds against \(\mathcal P(t)\) minus the own-pair lower bound, and the own left member separately. This gives the replacement for \(A_0\) in (4). All other steps of the signed inequality stay valid.

~~~powershell
python -B power_packet.py
~~~

2026-11-20. Joint project attribution to Claude and Codex.
