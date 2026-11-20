# Joint zero measures at successive heights

**Six true finite zero counts suffice for the fourth-power assertion under QRH(7/8).** Write $H=3{,}000{,}175{,}332{,}800$, $T_k=H\exp(k/4)$ and count positive zeta-zero ordinates with multiplicities, including the upper ordinate. At the following pairs $(k,1000s)$ suppose
$$
N_{>s}(T_k)\le 6\log(T_k)\,T_k^{3(1-s)/(3s-1)}:
\quad (6,851),(7,865),(9,826),(12,842),(19,863),(31,856).
$$
The six counts are unproved. With these assumptions the following closed intervals are covered. Each physical step is $1/24$, the ordinary log-height step is $1/16$, and the coupled part ends at $H e^8$. The real-part nodes contain all six thresholds, $7/8$ and the points $.650+.003j<.875$. The older separated bound continues to use its full $.001$ mesh.

| Physical interval in $L$ | Verified upper budget | Left endpoint of a largest cell | Candidate linear programs checked |
|---|---:|---:|---:|
| $[115.035950,124]$ | .997913182 | $115.702616666\ldots$ | 161 |
| $[124,147.2]$ | .997819690 | $124.666666666\ldots$ | 96 |

The [lower endpoint proof](../../round5/low/NARROW_COVER.md) and [upper endpoint proof](EXACT_BRIDGE.md) meet these two intervals. The explicit formula proves that $(x,x+4x^{3/4})$ contains a prime for $x=e^L$ in the middle. At $x=n^4$ this is inside $(n^4,(n+1)^4)$. The calculation uses the matched five-detector menu and genuine translated initial windows described below. Its largest half-axis repair for a proposed dual vector is less than $1.32\cdot10^{-7}$. Both ranges use the previous 64-cell right-boundary estimate for $f_{2310}$ and the previously certified physical polygon.

Consequently a counterexample requires at least **420,071** positive zeta-zero ordinates counted with multiplicity in
$$
.826<\beta\le7/8,\qquad H<\gamma<6{,}965{,}124{,}291{,}625{,}027 .
$$
At 200-bit precision the floors plus one of the six required right sides are $1089900,420071,10495930,3630069,1158145,5070970$. The greatest tested ordinate is strictly between $6965124291625026$ and $6965124291625027$. Each one of the six scalar counts is independent of the other five within the set of previously computed finite upper inequalities. The [test-population check](OBSTRUCTION.md) also gives direct unconditional-under-QRH upper bounds for the individual rectangles.

The analytic deductions are handwritten. The default verifier checks both closed intervals, the scalar bounds for the analytic height slabs and the integer thresholds with Arb. Run it from the research directory with python-flint, NumPy and SciPy installed.

~~~sh
python -B round6/reduction/coupled.py
~~~

Assume the same QRH(7/8), verified-height input and finite counts as in the [irregular-grid method](IRREGULAR.md). The following transfer imposes the nonnegativity of **each increment of the actual zero measure**. It permits bounds on the real-part distribution at different cumulative heights to be used together for the same prime interval.

Let $H=t_0<t_1<\cdots<t_M$. Set $E_i=E(d(b)t_i)$ for a closed physical cell $a\le L\le b$, where $E$ is the monotone polygon majorant, frozen at the overall lower physical endpoint. Subdivide the real axis from $.650$ through $7/8$ into nodes $s_j$, including each conditional threshold. Move real parts below $.650$ up to the first node, then distribute the mass of each zero between its two neighboring nodes by linear interpolation. Let $x_{ij}\ge0$ be the resulting mass at $s_j$ for zeros with $t_{i-1}<\gamma\le t_i$.

All tested hinges $(\beta-s_j)_+$ are unchanged, because they are affine on each subinterval. The total mass is unchanged. At a tested real threshold $s_j$, the redistributed mass with real part strictly greater than $s_j$ cannot increase. In the first interval to its right a portion can move onto the threshold itself. The exponential reward is convex, so $e^{(\beta-1)a}$ is at most the expectation of the reward after this redistribution. Consequently the initial Stieltjes sum is bounded above by
$$
\sum_{i=1}^M\sum_j x_{ij}(E_{i-1}-E_M)e^{(s_j-1)a}.
$$
For the exact monotone envelope, the coefficient of an increment at row $i$ is the telescoping sum $\sum_{r=i}^M(E_{r-1}-E_r)=E_{i-1}-E_M$. The certified calculation encloses this endpoint difference directly. The floating-point solver may use independently rounded decrements to select a candidate vector. All later spectral decrements, including the continuous tail, retain the [ordinary positive-part bounds](IRREGULAR.md).

Write $R_{ij}=\sum_{k\le i}x_{kj}$. At height $t_i$, use the explicit total-count bound $D_i$ and all selected analytic bounds $A_{i\ell}$ on $\sum_j R_{ij}(s_j-s_\ell)_+$. A count rectangle with limit $C$ supplies $\sum_{s_j>s}R_{ij}\le C$ at its largest included height node $t_i$ up to $t_M$. The conditional grid points are present in the height mesh. These are valid inequalities with nonnegative right sides, including for the redistributed measure.

For any chosen nonnegative multipliers on these inequalities, let $P_{ij}$ be the sum of the resulting coefficients on $x_{ij}$. Compute it by adding coefficients from all rows at or beyond $i$. Define
$$
D_{ij}=\min\!\left(D_i,\min_{s_\ell<s_j}
 \frac{A_{i\ell}}{s_j-s_\ell},\min_{\substack{s<s_j\\T\ge t_i}} C(s,T)\right),
$$
with empty inner sets omitted. Each $x_{ij}\le R_{ij}\le D_{ij}$. Thus an upper bound on the initial sum is the sum of all multiplier times right-hand-side products, plus
$$
\sum_{i,j}D_{ij}\left((E_{i-1}-E_M)e^{(s_j-1)a}-P_{ij}\right)_+ .
$$
This formula applies even when some proposed coefficients vanish. The [verifier](coupled.py) uses a floating-point linear program only to select nonnegative multipliers. It converts their binary64 values to Arb, divides by the rigorously computed corresponding right sides, reconstructs every $P_{ij}$ with interval arithmetic, and adds the entire displayed correction. No solver feasibility tolerance enters the resulting inequality.

Both signs of the zeta ordinates, the initial verified zeros, all later effective heights, the prime powers and the trivial zeros are then included in the [ordinary normalization](IRREGULAR.md). A joint bound may always be replaced by the smaller existing separated-height certificate. Numerical tests at selected cells alone do not certify the whole physical interval.

With `--strong`, the [finite-height rows](strong_rows.py) add the same matched $Q=2310$ boundary norms and [pointwise interpolated radial constant](EXACT_BRIDGE.md) to each half-unit slab from $28.5$ to $44$. The short core is $2^{20}$, the critical factor is $\zeta E_{210}$, the folded depth is 12, and the fourth moment uses the [centered phase estimate](../phase/CENTERED_PHASE.md) with parameters $(1,.04,384)$. The five triples $(\delta,W,\log h)$ are $(1.1,9.5,-3),(1.28,9.5,-2.75),(1.34,8.5,-2.75),(1.16,9,-3),(1.04,9.5,-3.5)$. Each right norm has 64 intervals in its exponent parameter and uses the $100T$ split. The angular boundary includes the prime 11. The original rows remain available. With `--moving`, the first two units above $\log H$ also retain the [centered-ordinate detector](../../round5/low/MOVING_WINDOW.md) on the complete interval $[H,H\exp(j/8)]$, at the first upper eighth-log grid point containing the tested ordinate. This estimate uses critical factor $\zeta E_{30}$ with its [periodic fourth moment](../phase/PERIODIC_FOURTH.md), the folded $E_7 C_{210}$ remainder at depth 12, and the unaltered modulus-210 right norm. The factor two for the translated full-axis bound is included in [the calculation](centered.py).

2026-11-20. Joint project attribution to Claude and Codex. The six-rectangle proof combines analytic work credited in the cited project records with the joint real-part and height calculation by Codex.
