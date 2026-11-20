# Sampling the explicit formula at the steps of a progression

Assume QRH(7/8) and use the [second rectangle and its prime weights](STRIP_BOUNDARY.md). All comparison ordinates in this statement are in \([H,T]\), with no restriction on where in this interval their progressions begin. If the rectangle contains \(R\ge420071\) exceptional zeros, their ordinates, in any order, obey the following lower bounds on their distance from a union of up to \(r\) arithmetic progressions. Distances are measured after a one-to-one matching, with multiplicities. Each progression with at least two points has step at least 20. The range covered imposes no further upper cutoff on the steps.

| \(r\) | \(A,K\) | Mean absolute ordinate displacement exceeds | Number of entries that must differ |
|---:|---|---:|---:|
| 1 | 44,650 | .00023802 | 2200 |
| 6 | 44,300 | .00015816 | 1462 |
| 20 | 42,200 | .00006779 | 599 |
| 34 | 43,164 | .00000371 | 34 |

For \(r=1\) the mean-displacement result extends to every nonnegative step. The [local density argument](PROGRESSIONS.md) handles steps below 20 and yields the stronger .00030 there. In particular the single-progression test covers an equally spaced population spanning the whole height interval, where some candidate spacings exceed thirty million.

## Uniform pointwise Fejér bound

Put \(D_M(y)=\sin(My)/(M\sin y)\), with continuous values at integers times \(\pi\). For \(K\ge80\) and all positive integers \(N\),
\[
  |D_N(y)|\le |D_K(y)|^2+.37K/N .                                      \tag{1}
\]
Reduce to \(0\le y\le\pi/2\). Put \(x=Ky,\ z=Ny,\ v=K\sin y\). If \(x\ge2.8\), then \(1/v<.37\), because \(K\sin(2.8/K)\ge 2.8a,\ a=1-2.8^2/(6\cdot80^2)\). For \(0<x\le2.8\), one has \(ax\le v\le x\). The left side of (1) less its square term, times \(N/K\), is
\[
 v^{-1}\left[|\sin z|-\frac{\sin^2 x}{xv}z\right].
\]
Replacing the slope by \(r=(\sin x/x)^2\) increases the expression. The supremum of \(|\sin z|-rz\) on \(z\ge0\) is attained in the first quarter-wave and equals \(\sqrt{1-r^2}-r\arccos r\). For \(x\le.1\) it is bounded by \((\pi/2)(1-r)\le\pi x^2/6\), using \(\sin z\le z\) at the maximum. For \(.1\le x\le2.8\) the verifier uses 4096 intervals. The last displayed supremum decreases with \(r\), and \(r\) decreases with \(x\), so division by \(a x_{\rm left}\) and the value of \(r\) at the right endpoint give rigorous upper bounds. Each is less than .37.

## Prime mass of the squared short progression

Write \(V=\sum v_{p,1}\) and \(E=\sum_{p,k\ge2}v_{p,k}\), using the previously certified upper bounds. For the real trigonometric polynomial of first primes, positivity of the zero-strip transform gives for \(20\le t\le Z\), \(Z\ge10^8\),
\[
 \sum_p v_{p,1}\cos(t\log p)
 \le \tfrac14\log(Z/(2\pi))+.005+E+C_A/t^2.                           \tag{2}
\]
For the gamma integral let \(v=\sqrt Z\). On \(|y|\le v\) the digamma upper bound from [the earlier explicit formula](../../round7/qrh_strip/RIGHT_EDGE.md) gives \(\Re\psi(1/4+i(t+y)/2)\le\log((Z+v+1)/2)+.001\). Indeed for \(|t+y|\ge4000\) the asymptotic error costs at most \(\pi/4000\), and for the smaller arguments one uses \(\log(4002)+1\). For \(|y|>v\), the normalised density decays as \(1/(\pi y^2)\). Its upper contribution to the excess, including the factor \(1/4\), is at most \([\log(Z+3)+\log(1+v)+3]/(2\pi v)\). The last expression decreases with \(Z\ge10^8\), as does \(\log(1+(v+1)/Z)\). The verifier checks the .005 total at \(10^8\).

For the poles the combined contribution after division by two is the cosine transform at \(t\) of \(w(u)F(u)\), where \(F=\cosh(u/2)/\cosh(3u/8)\) and \(w=(1-u/A)_+\). Put \(h=1/8,\ e=7/8\). Direct differentiation bounds \(F,|F'|,|F''|\) by \(e^{hu}, e\,e^{hu},e^2e^{hu}\) on \(u\ge0\). Twice integrating by parts bounds the pole term by \(C_A/t^2\), where endpoint derivatives, the cross derivative and the remaining integral contribute
\[
 C_A=\frac{1+e^{hA}}{A}
      +\frac{2e(e^{hA}-1)}{Ah}
      +\frac{e^2(e^{hA}-1-hA)}{Ah^2}.
\]

For one comparison progression of length \(N_i\), step \(d_i\), its normalized absolute phase is \(|D_{N_i}(d_i\log p/2)|\). Use (1), expand the Fejér square, and apply (2) at each \(t=j d_i,\ 1\le j<K\) with \(Z_i=\max(10^8,Kd_i)\). The zeroth term is \(V/K\). The nonconstant weights have total \(1-1/K\), and their polar error is at most \(\pi^2 C_A/(3K d_i^2)\) by summing \(1/j^2\). The comparison error from (1) is at most \(.37KV/N_i\). The starting phase disappears after taking an absolute value.

Mix the progressions with weights \(N_i/R\), allocating step 20 to singletons. Every progression has \(N_i d_i\le2(T-H)\), since its endpoints lie in the height interval. Concavity of \(\log\) bounds the mean of \(\log Z_i\) by \(\log Z_*\), with \(Z_*=10^8+2Kr(T-H)/420071\). Thus the maximum absolute weighted prime sum per ordinate is
\[
 B_*=\frac VK+
 \left(1-\frac1K\right)\left[\tfrac14\log(Z_* /(2\pi))+.005+E\right]
 +\frac{\pi^2 C_A}{3K\cdot20^2}+\frac{.37rKV}{420071}.
\]
The actual exceptional zeros require a negative prime sum of magnitude at least \(D_A R\). The table follows by dividing \(D_A-B_*\) by \(AV\) for mean absolute displacement, or multiplying it by \(420071/(2V)\) and rounding upwards for the necessary number of changed entries. These are structural restrictions on exceptional zeros; they do not bound their unrestricted global count.

~~~sh
python -B round8/zero_strip/stepped_phases.py
~~~
