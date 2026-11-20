# A polygonal weight for the explicit formula

Use the [logarithmic interval and normalized explicit formula](../../round2/spectrum/PROOF.md) with a symmetric, nonnegative piecewise linear density \(\phi\) on \([0,1]\). Write \(N=64,\ h=1/(2N)\). At \(1/2\pm jh\) prescribe the height \(H_j/(hS)\) from the integer array in [polygon.py](polygon.py), where \(H_N=0,\ S=H_0+2\sum_{j=1}^{N-1}H_j\). Connect adjacent nodes linearly, and set the weight to zero outside the interval. Its mass is exactly one. The integer inequality \(6N\max H_j\le4S\) gives \(\|\phi\|_\infty\le4/3\); the maximum is below \(1.333322917\). The endpoint values and the bound for prime powers therefore agree with the hypotheses of the earlier proof at \(a=1/4\). The polygon has a derivative of bounded variation. A discretized linear program for the monotone spectral majorant suggested the integers; all inequalities below use these fixed integers.

Let \(F(y)=\int_0^1\phi(t)e^{iy(t-1/2)}dt\), a real function, and set \(G(y)=-y^2F(y)\). Two integrations by parts show
\[
 G(y)=\frac1{h^2 S}\sum_{j=0}^N b_j\cos(jhy),\qquad
 b_0=2(H_1-H_0),\quad b_j=2(H_{j-1}-2H_j+H_{j+1})\ (j\ge1),
\]
with \(H_{N+1}=0\). These are the signed jumps of the derivative with symmetric nodes combined. The total variation is \(B=(h^2 S)^{-1}\sum |b_j|\). The numerator satisfies \(|G''|\le S^{-1}\sum |b_j|j^2\). For the denominator bound, write the centered density as a mixture of translates of the triangular density \((1-|t|/h)_+/h\), using masses \(H_0/S\) at zero and \(H_j/S\) at each signed \(jh\). This gives
\[
 |F''(y)|\le h^2\left(\tfrac16+2\sum_{j=1}^N H_jj^2/S\right).
\]

For a grid cell \([s,t]\), \(s>0\), the maximum of a twice differentiable real absolute value is at most the larger endpoint absolute value plus \((t-s)^2\sup|F''|/8\), by linear interpolation of \(F\). Apply this both to \(F\) and to \(G\), in the latter case dividing the bound by \(s^2\). The script computes the endpoint cosines together as a signed Chebyshev polynomial. Both estimates therefore retain cancellation between the different parts of the interval density before taking absolute values.

If \(\epsilon=(1-\beta)d\in[0,d]\), the uncentered integral with the factor \(e^{-\epsilon t}\) differs from its undamped value in modulus by at most \(\epsilon\int_0^1t\phi(t)dt\le d/2\). Its modulus is also at most 1. Integrating the damped exponential twice against the piecewise linear weight directly gives the separate bound \(B/|-\epsilon+iy|^2\le B/y^2\); endpoint derivative jumps are included in \(b_N\). Use the minimum of these bounds, rounding up to multiples of \(10^{-9}\). Form the decreasing majorant by cumulative maxima from right to left. On \(y\ge Y_*=192\), use \(\lceil10^9 B/Y_*^2\rceil\,10^{-9}(Y_*/y)^2\). The explicit tail bounds every height, including all damping at every smaller \(d\). On \(y<1/2\) use 1. The jump at an upper grid endpoint accounts for both endpoint conventions of the zero count.

The resulting \(\texttt{height_groups(d,a,floor,step,tail)}\) has the [same six outputs and logarithmic tangent bound](../../round3/spectrum/verify_height.py). At \(L=168,\ y_{\min}=1.45\), with \(r=1+p\), step denominator 256 and the same quadratic-tail cutoff, the ratios of the new total height moments to the old certified ones are below:

| \(p\) | .34 | .37 | .40 | .45 | 1 |
|---:|---:|---:|---:|---:|---:|
| new/old | .980469 | .979685 | .979126 | .978779 | 1.104586 |

The \(p=1\) entry above uses \(r=2\), for a like-for-like comparison with the other rows. The actual total-zero-count base uses \(p=r=1\) and has ratio below 1.089651. The rectangle-edge term with \(p=0,r=1\) has ratio below .998456. The full budget recalculates both terms. The knot slopes, prime-power estimate, trivial-zero bound and finite-height hypotheses retain the forms used in the full fourth-power certificate. When freezing the envelope at an anchor, the error term \(d/2\) decreases for larger \(L\).

~~~sh
python -B polygon.py
~~~

## Lower bound valid for every positive weight in the interval

For \(b=1.45\) and \(p=2/5\), consider the undamped moment \(J=\int\max(b,y)^p\,(-dE(y))\), where \(E(0)=1\), \(E\) decreases to zero, and \(E\) majorizes the modulus of the Fourier transform of a probability measure supported on \([0,1]\). The measure can be nonsymmetric or discrete. Integration by parts gives \(J=b^p+\int_b^\infty p y^{p-1}E(y)\,dy\), including the case \(J=+\infty\).

Choose \(b=y_0<y_1<\dots<y_m\) and real \(c_i\) with \(\sum_{i\le j}|c_i|\le y_j^p-b^p\) for every \(j\). The integral over \([y_{i-1},y_i]\) costs at least \((y_i^p-y_{i-1}^p)E(y_i)\). Summation by parts with decreasing \(E(y_i)\) shows that the total is at least \(\sum_i |c_i|E(y_i)\). The centered real part of the transform is \(\int\cos(y(t-1/2))\,d\mu(t)\), so
\[
 J\ge b^p+\min_{0\le t\le1/2}\sum_i c_i\cos(y_i t).
\]
The [dual certificate](dual.py) uses rational \(y_i,c_i\) and verifies every prefix inequality with Arb. A finite linear program proposes the \(c_i\). On the spatial interval, the code evaluates the cosine polynomial at 4097 equally spaced points and subtracts \(\sum |c_i|y_i^2/[8\cdot8192^2]\), using the linear interpolation inequality once more. This proves **\(J>1.8940647\)**. The implemented polygon, with the actual damping allowance at \(L=168\), has \(J<1.924769\). Hence, at this exponent, replacing the polygon by any new positive interval weight can shave at most another \(1.596\%\) off this particular spectral envelope bound. For a fixed damping \(0\le\epsilon\le d\) and unit normalization of the envelope at zero, subtract at most \(d\sum |c_i|\) from the displayed lower bound, by comparing the real transforms. The argument concerns the monotone envelope and does not bound the signed arithmetic sum over zeta zeros from below.

~~~sh
python -B dual.py
~~~

2026-11-20. Joint project AI authors are Claude and Codex. Codex developed this interval weight, its curvature calculation and the Arb verification.
