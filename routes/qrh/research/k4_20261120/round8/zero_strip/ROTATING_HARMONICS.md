# Rotating estimates for nonconstant angular source measures

Keep the fixed degree-nine detector, the signed majorant \(A(z)=\log(|D(z)|+b(|z|))\), the outer growth bounds, and the interval exchange of [ROTATING_SIGNED.md](ROTATING_SIGNED.md). The scalar source argument extends to each source of a [nonnegative, multiple-harmonic Green test](COUPLED.md). At one abscissa its proven nonnegative density is \(S(t)=b_0+\sum_{m\in M}d_m\cos(m\omega t)\). The \(d_m\) may have either sign. The physical target either uses the positive cosine or its absolute value. Shifting every occurrence of \(\omega t\) by \(\pi\) handles a negative cosine part at the same cost.

Multiply the rotated strip submean at \(z_0=a+it_0\) by \(S(t_0)\) and integrate. In the interval exchange, retain \(S(u-v)\) unchanged under both indicators. Consequently the exchange penalty is at most \((b_0+\sum_m|d_m|)\) times the previous per-unit penalty. The remaining mark is \(u\in I\), with no restriction on \(v=u-t_0\). Let \(Q(k)\) denote the positive characteristic function of the normalized strip Poisson density on the chosen boundary. It is even, is one at zero, and for \(k>0\) is at most

\[
 \min\left(1,\frac{e^{-gk}}{m_0(1-e^{-2wk})}\right),
\]

where \(g\) is the distance from the source to that edge, \(w\) the full strip width, and \(m_0\) the probability of that edge. To cover a frequency ball one may evaluate this decreasing upper bound at the lower endpoint of its absolute value.

Write \(r_0\) for the scaled boundary modulus, \(p\in\{4/3,2\}\), and use the normalized complex Fourier coefficients on a circle. For a radius bin choose bounds

\[
 0\le\widehat A_0(r_0)/r_0^p\le C_0,\qquad
 |\widehat A_j(r_0)|/r_0^p\le C_j\quad(j\ge1).
\]

The contribution from the constant angular source has coefficient at most \(C_0+2\sum_{j\ge1}C_jQ(j\lambda)\). For an individual cosine \(\cos(m\omega(u-v))\) its absolute coefficient is at most

\[
 C_0Q(m\omega)+\sum_{j\ge1}C_j\big(Q(|j\lambda-m\omega|)+Q(j\lambda+m\omega)\big). \tag{1}
\]

Expand \(A(r_0e^{i(\phi+\lambda v)})\) in its complex Fourier modes and write the physical cosine as its two half-weighted exponentials. The two signs of \(j\) cancel the factors \(1/2\) in (1). The unknown edge angle \(\phi\) and \(m\omega u\) have unit-modulus exponentials. Fejér polynomials justify this computation for the continuous circular function \(A\), and the absolute bounds after convolution are summable because \(Q\) decays exponentially. At a fixed edge modulus all the coefficients use the **same radius bin**. Add the constant column with weight \(b_0\) and the other columns with weights \(|d_m|\), then take the maximum over bins. Apply the left or right boundary moment to this maximum exactly as in the scalar rotating inequality. Different edges have their own maximum. The full source acquires its interval-exchange penalty; the whole determinant also pays \(9/8\) times its angular-gradient factor and the stored three-edge bound.

## Radius bins and Fourier constants

Write \(A=\log|D|+E\), where \(E\ge0\). At isolated circle roots the first logarithm and the difference are integrable. Jensen's circle formula gives the mean of \(\log|D|\) as \(J_0(r)=\log^+r+J\log^+(r/J)\). For nonzero indices the Fourier coefficient is exactly

\[
 \frac{(-1)^{j-1}\min(r,1/r)^j-J\min(r/J,J/r)^j}{2j}. \tag{2}
\]

This follows by expanding \(\log(1-z)\) inside the unit circle and factoring out the modulus outside. Radial limits at a circle root give the same integrable coefficients. Since \(|\widehat E_j|\le\widehat E_0\), an upper bound for \(\widehat E_0/r^p\) can be added to the absolute value of (2) divided by \(r^p\), and to \(J_0(r)/r^p\).

The global bound for \(E\) in [rotating.py](rotating.py) uses the previously verified upper arc mean of \(A\) less the exact Jensen expression. Between adjacent log-radius nodes the Jensen expression is affine, because \(1\) and \(J=8\) are nodes. Thus the same exponential secant estimate applies to the mean difference. At the small end use \(b(r)/(1-r)^2\). At \(r\ge16\), \(b(r)/[(r-1)(r/J-1)^J]\) decreases termwise, so the log correction divided by \(r^p\) is at most its value at 16. On a finite bin disjoint from both roots, the code can further bound the numerator \(b(r)/r^p\) at its right endpoint and the denominator factors \(|1-r|,|1-r/J|\) by their respective minima. The circular constants for the padded mean may also be sharpened by [jensen_circle.py](jensen_circle.py).

The bins in [rotating_bins.py](rotating_bins.py) cover zero through infinity and include both root radii. On each bin the maximum of \(J_0(r)/r^p\) is attained at an endpoint or at the unique stationary point of the corresponding affine numerator in \(\log r\) divided by \(r^p\). The normalized absolute value of (2) for \(j\ge2\) is monotone on either exterior part. In \(1\le r\le J\) it is the absolute value of the difference of a decreasing positive power and an increasing one for odd \(j\), or a sum of two convex exponentials in \(\log r\) for even \(j\). The maximum occurs at an endpoint in either case. Index one additionally uses \(r=\sqrt{(p+1)/(p-1)}\) clipped to the bin. At zero the only nonzero limiting coefficient among these indices has \(j=p=2\). All omitted coefficients have normalized modulus below one: the global pad bound is below .1, index one from (2) is at most .5, and for \(j\ge2\) the two endpoint bounds on the middle range are \((1+J^{1-j})/(2j)\) and \((J^{-j}+J)/(2jJ^p)\).

For the minus-frequency branch of (1) retain all positive \(j\) from \(\max(1,\lfloor m\omega/\lambda\rfloor-3)\) through \(\max(3,\lfloor m\omega/\lambda\rfloor+4)\). The approximate midpoint locates this block only. For the omitted portions the verifier checks a positive initial distance \(k_0\), then bounds the sum of attenuations on a progression of spacing \(\lambda\) by

\[
 \frac{e^{-g k_0}}{m_0(1-e^{-2wk_0})(1-e^{-g\lambda})}.
\]

The entire plus-frequency branch starts at \(m\omega+\lambda\) and obeys the same bound. For the constant source column four nonzero modes are kept and both tails are charged. Radius coefficients are rounded up on scale \(2^{24}\); the folded frequency matrix is rounded up on scale \(2^{28}\). Matrix multiplication is over nonnegative signed 64-bit integers with an explicitly checked upper bound below \(2^{63}\), followed by upward integer division. In pricing a source, normalize its nonnegative coefficient vector by its total mass and round every coordinate upwards on scale \(2^{28}\), with another overflow check. Zero mass contributes zero. Each logarithmic height may use an interval of width \(1/64\) enclosing the true frozen \(\log(T+.1)\); the actual observed taper moments remain fixed in that enclosure. The angular frequency interval covers the entire physical cell or group of cells.

## Complete physical use

[rotating_phase_bridge.py](rotating_phase_bridge.py) prices every cumulative positive and absolute cosine row from [complete_green.py](complete_green.py). The same positivity argument gives the negative-cosine row. It attaches the explicitly named finite near-height rows, then invokes the rigorous signed spatial-density validator and the joint height allocation. Each physical cell uses fixed outward bounds; neighboring integers or zeros do not need simultaneous phase choices. The option to optimize the angular proposals against the folded radius tables changes only the proposed coefficients, each of which still passes the source-positivity, whole-strip, angular, radial, finite-window, and Green edge calculations. A representative closed physical cell can be verified with

~~~powershell
python -Bu rotating_phase_bridge.py --first 117.95 --last 117.975
~~~

The whole upper budget on this interval is below **0.987300381029277**.

### Closed interval from 116 through 120

From the directory containing this note, the following single invocation covers every real \(L\in[116,120]\) using 40 adjacent closed cells. The largest upper bound is **smaller than 0.974018046178990**, attained on \([117.2,117.3]\).

~~~powershell
python -Bu rotating_phase_bridge.py --first 116 --last 120 --pieces 40 --reuse 3 --opt
~~~

The inputs are the default `early_green_rows.json` and the three finite-height tables `companion_original_100.json`, `companion_original_350.json`, and `companion_rows_600.json` in `round7/first_selected`. The default height and angle parameters are `--nh 2 --sub 8 --step 6 --top 41 --source-floor .775`; the spatial polygon uses `--n 24 --limit 60`. Each candidate is checked at 160-bit precision. A proposed polynomial or spatial polygon reused across cells is verified with the bounds of the current cell. A second partition with 120 cells independently covers the same interval. Only the first of its three commands requests the angular proposal optimization.

~~~powershell
python -Bu rotating_phase_bridge.py --first 116 --last 117.5 --pieces 30 --reuse 5 --opt
python -Bu rotating_phase_bridge.py --first 117.5 --last 118.5 --pieces 40 --reuse 5
python -Bu rotating_phase_bridge.py --first 118.5 --last 120 --pieces 50 --reuse 5
~~~

| Closed range of \(L\) | Number of cells | Strict upper bound for the maximum budget |
|---|---:|---:|
| \([116,117.5]\) | 30 | 0.965870932713336 |
| \([117.5,118.5]\) | 40 | 0.998154316354090 |
| \([118.5,120]\) | 50 | 0.982034885201371 |

The verifier forms the cell boundaries as exact rational numbers and checks the decimal serialization on input to interval arithmetic. The upper bounds in the table have been rounded outward. For the physical explicit formula, strict inequality below one in each row gives a prime throughout that row under the upstream QRH and verified-height assumptions of the project. These runs used Python 3.12.10, python-flint 0.9.0, NumPy 2.5.4 and SciPy 1.18.1. The corresponding SHA-256 hashes of the input tables are

| Input | SHA-256 |
|---|---|
| `early_green_rows.json` | `6cfc5297aad784ba7b112de2ee6804099dc0ef53c78a19c2b68ae7e8003a1a58` |
| `companion_original_100.json` | `7f9d57d0dba75bc66c377c33b37885f8bb4d2fea9712ede14cd242c61868dd35` |
| `companion_original_350.json` | `95af62f93705c1795c34cfab16ad0b2f6402a2b6ca0e04244cd7af17e07bcd49` |
| `companion_rows_600.json` | `51dfe6886b4402048b6ad1b2f16bffd91911c4c8d44ee29964f9fea24539acc2` |

2026-11-20. Joint project attribution to Claude and Codex.
