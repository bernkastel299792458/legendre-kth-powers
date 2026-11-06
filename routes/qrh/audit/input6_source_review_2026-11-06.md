# Input 6 source review: CHJII short-interval explicit formula

Date: 2026-11-06. Reviewer: Codex (AI-assisted source audit).
Repository baseline: `9087d46124fa69cab9d3d95f8b4bafc8cc2546f7`.
Scope: the external proposition `LegendreK6.CHJIIShortInterval` in
[`LiteratureInputs.lean`](../lean/LegendreK6/LiteratureInputs.lean), including its
definitions of zeros and multiplicity in
[`ZetaZeros.lean`](../lean/LegendreK6/ZetaZeros.lean).

## Result and limits

The current Lean proposition agrees with **the statement** of CHJII,
arXiv:2402.04272v3, Theorem 1.3 and the first row of Table 1. The relevant
statement, table, shared-truncation argument, and Section 4 proof are also
identical in the downloaded v2 and v3 TeX sources. There is no v2-to-v3 change
in the input used by this project.

The paper's publication in *Functiones et Approximatio Commentarii
Mathematici* 73(2), 223–242 (2025), DOI
[10.7169/facm/241110-18-11](https://doi.org/10.7169/facm/241110-18-11), is
independently supported by the publisher's issue contents, Crossref's DOI
record, and the author's publication list. **The exact journal text has not
been compared with the arXiv text.** The publisher's full-text endpoints
returned a security-check page; the author's page supplied only the arXiv and
journal links, and this search did not obtain a separately identified accepted
manuscript. No access control was bypassed.

Thus, this audit closes the **arXiv-to-Lean statement transcription** and
**v2-to-v3 relevant-version** checks. It does not close the journal-to-arXiv
text comparison, independently reprove the analytic theorem, certify the
authors' numerical optimization, or provide a Lean proof of this external
proposition. In particular, a Lean theorem taking `CHJIIShortInterval` as an
argument remains conditional on that proposition.

## Exact statement correspondence

Put `y = x + h`. The specialized input is the existence of one
`Tstar ∈ [T, 2T]` such that

\[
\left|\psi(y)-\psi(x)-h+
 \sum_{|\operatorname{Im}\rho|\le T^*}
 m(\rho)\frac{y^\rho-x^\rho}{\rho}\right|
\le \frac{1447}{500T}\bigl(y\log y+x\log x\bigr).
\]

The following table records the mathematical transcription checks, not new
formal proofs of the external theorem.

| Item | Source and current Lean correspondence | Result |
| --- | --- | --- |
| Base variable | Table 1 has `log(x_M)=40`; Theorem 1.3 applies to `x ≥ x_M`. For positive real `x`, this is equivalent to Lean's `40 ≤ Real.log x`. The separate Lean premise `0 < x` supplies the log domain. | Matches |
| Interval length | The source allows any nonnegative function `h(x)`, with no upper bound on `h` in its statement. Fixing any nonnegative constant function supplies each real `h ≥ 0` in the Lean proposition. | Matches |
| Parameters | The first Table 1 row has `α=1/2`, `ω=0`, `λ=0.43`, `M=2.894`. `λ` is an internal optimization parameter, not an extra theorem hypothesis. | Matches |
| Lower height bound | Both strict bounds are `max{51,(log x)^2} < T`. Neither endpoint is weakened to a non-strict inequality. | Matches |
| Upper height bound | At `α=1/2`, `(x^α−2)/4` equals `(Real.sqrt x−2)/4` for positive `x`. The inequality is strict on both sides of the transcription. | Matches |
| Existential height | The source's single height satisfies `T ≤ Tstar ≤ 2T`. Lean allows that height to depend on the supplied `x,h,T`, as needed by the pointwise statement. | Matches |
| Shared height | Theorem 1.3 directly uses one sum for the difference of the endpoints. Corollary 3.3 and its proof construct one height for the interval difference; the following paragraph expressly explains why two independent single-endpoint applications would not suffice. | Matches |
| Error coefficient | `2.894 = 2894/1000 = 1447/500` exactly. The Lean coefficient is a rational real constant; no floating-point rounding of this decimal is introduced. | Matches |
| Error shape | `ω=0` makes the two logarithmic exponents equal to one. Factoring out `M/T` gives exactly `M/T * (y*log y+x*log x)`. The denominator is `T`, not `Tstar`. | Matches |
| Sign | Moving the zero increment to the left gives `psi(y)−psi(x)−h + truncatedZeroIncrement x y Tstar`, exactly as in Lean. | Matches |
| Norm | The explicit `O*` bound controls the absolute size of the residual. Lean states this using the complex norm, which is the complex modulus. It does not merely bound the real part of a potentially complex residual. | Matches |
| Counting function | The paper defines `psi(x)` using all positive integers up to and including `x`. Mathlib's `Chebyshev.psi` sums von Mangoldt over `Ioc 0 floor(x)`. Thus the interval is `(x,x+h]`; there is no half-weight convention at a prime power endpoint. | Matches |
| Zero set | The paper sums the nontrivial zeros with `|γ| ≤ Tstar`, including both signs of the imaginary part. `allZetaZeros` uses `0 < Re ρ < 1` and the same closed absolute-height cutoff, retaining any real-axis zero until separately excluded. | Matches the usual nontrivial-zero convention |
| Multiplicity | The displayed source sum uses the customary zero sum with multiplicity. Lean explicitly multiplies each distinct zero by `analyticOrderNatAt riemannZeta ρ`. It does not assume that zeros are simple. | Matches the usual multiplicity convention |
| Powers and logarithms | Both bases `x` and `x+h` are strictly positive. Therefore the principal complex power used in Lean has the usual value `exp(ρ log x)` and introduces no branch ambiguity. | Matches |

For the counting-function check, the dependency revision recorded in the
project's build report is Mathlib
`9d581dfff2e41de989072ea63abf3daf69311520`; its
`Mathlib/NumberTheory/Chebyshev.lean`, lines 69–71, supplies the definition.
This audit used the dependency checkout already identified by the existing
build report and did not change or compile it.

## Version comparison and visual verification

The [v2 record](https://arxiv.org/abs/2402.04272v2) dates that version to
2024-11-11. The [v3 record](https://arxiv.org/abs/2402.04272v3) dates v3 to
2026-02-23 and describes minor corrections. The v3 date is later than the
journal's 2025 publication; chronology alone cannot prove which exact text
was reviewed.

Both versioned PDFs and both versioned source archives were downloaded
directly from arXiv. A full unified diff of `main.tex` was inspected, and the
following delimited source spans were compared exactly after decoding:

| Span | v2 equals v3 | SHA-256 of compared UTF-8 text |
| --- | --- | --- |
| Theorem 1.3 | yes | `877dd674ed1a5cb5819f382c86c430b5ecb15ee991163345dbe69b47f1788b08` |
| Table 1 | yes | `5ba2464aef1c1705a69bb740f9e2d484fecf9c677d137aa9efb25040c42bc0d9` |
| Corollary 3.3, its proof and shared-height explanation | yes | `79c8cadf22488c8e04a4fbac33b859bd69ec720ea6d0b40761823302b58c882d` |
| Section 4 proof | yes | `b460041dc06da389c990c7655e68122c7619af3b1066ab83120b0f459de8e141` |

The mathematical edits in v3 occur in Section 5's application to primes
between powers: positivity of a difference of `psi` counts prime powers, and
the revised application subtracts a `psi−theta` correction before claiming
the existence of primes. The other edits concern first-page footnote
formatting and acknowledgements. These edits neither alter the cited
Theorem 1.3 nor its `M=2.894` row. This project's input 6 is the `psi`
explicit formula, not the Section 5 prime-existence application.

PDFs were rendered using Poppler and inspected visually:

- v2 page 3 and v3 page 3: Table 1, all five entries of its first row, the
  complete statement of Theorem 1.3, both strict `T` bounds, the shared sum,
  and both error terms;
- v3 pages 10–11: Corollary 3.3, the shared-height argument and explanation;
- v3 pages 11–12: the proof's error terms and its final instruction to use
  Corollary 3.3 for Theorem 1.3.

Text extraction had a font-parser warning on v2; the conclusion above uses
the TeX sources and visual page inspection, rather than relying on that
extraction for mathematical symbols.

## Observed source typo and unperformed upstream checks

On page 11, after defining `κ=1+1/log x`, both arXiv versions print the
denominator `1−κ` in an intermediate bound and equate its reciprocal to
`log x`. That equality has the wrong sign: the intended denominator is
`κ−1`. The next numbered bound, (4.3), actually uses the positive quantity
`log x`. This is a directly observed sign typo, not an OCR artifact; the
rendered PDF and TeX agree. It does not appear in the theorem statement or
the Lean input. This audit has not checked whether the journal fixes it.

The paper obtains Table 1 by combining the explicit-formula error estimate
with the bounds in Section 4 and optimizing `λ`. It links its
[author-maintained supplementary code](https://github.com/DJmath1729/Riemann-von-Mangoldt-estimates),
whose Section 3/4/Appendix B calculations are in a Mathematica notebook.
This review establishes the location and stable value of the published
arXiv constant. The supplemental calculation below independently checks the
first row's scalar arithmetic and rounding, but does **not** certify an
optimization over parameters or all the analytic steps leading to it. A
source-transcription match must not be described as an independent analytic
proof.

## Supplemental first-row arithmetic audit

The author notebook was downloaded at the pinned repository commit
`60a723c24f094c890c03ab1f7f48f3811e0277e5`:
[RVM II Sections 3,4 and Appendix B.nb](https://github.com/DJmath1729/Riemann-von-Mangoldt-estimates/blob/60a723c24f094c890c03ab1f7f48f3811e0277e5/RVM%20II%20Sections%203%2C4%20and%20Appendix%20B.nb).
Its SHA-256 is
`eceec0f0cf038b14c2980907b90e89c3cd4c44b6acb969d898df6d7ac5c5e6b8`.
The notebook was read as text and not executed. Its displayed Table 1 setup
is for a different row; this audit explicitly substitutes the first row's
parameters. The original verifier
[`verify_input6_constant.py`](verify_input6_constant.py) implements only
the inspected formulas. Its output is
[`input6_constant_check_2026-11-06.json`](input6_constant_check_2026-11-06.json).

The calculation uses 80-decimal-digit `mpmath` arithmetic for an independent
numerical recomputation and **256-bit Arb ball arithmetic** for rigorous
scalar comparisons. All terminating decimals enter the verifier as rational
integer quotients. Nine scalar comparisons passed, including `M<2.894`,
`K<2.033`, the rounding of `4N`, and the bracket for the auxiliary root.
This is an Arb certification of these scalar expressions, not a Lean proof
of CHJII or a numerical sweep certifying every admissible `x,T`.

### Composition of 2.894

Write `z=log x`, set `z=40`, and use

\[
\lambda=0.43,\quad \theta_0=0.8029,\quad q=1.785,\quad K=2.033,
\quad c=1+\frac{e^\lambda-1}{\lambda}.
\]

After dividing the error in (4.6) by `x log(x)/T`, and applying the
notebook's deliberately loose upper bound `T < x^(1/2)`, the remaining
scalar expression is

\[
K+A(z)+B(z)+C(z),
\quad A(z)=\frac{q e}{2\lambda^2z^2},
\]
\[
B(z)=q e^{(1+1/z)\lambda}
\frac{c}{\theta_0z}\left(4+\frac{4\lambda}{z}\right),
\]
\[
C(z)=\frac{q e^{(1+1/z)\lambda}}{2\theta_0^2}
\left(\frac{a_1e^{\lambda/2}}z+
\frac{a_2e^{-z/6+\lambda/3}}z+e^{-z/2}\right).
\]

Here the notebook uses `a1=1+1.9337840×10^−8` and `a2=1.0432`.
Its `a1` is slightly larger than the displayed paper value
`1+1.93378×10^−8`; using the larger value is conservative.

| Contribution | Recomputed value at `z=40` |
| --- | --- |
| Rounded upstream `K` | `2.033` |
| `A(40)` | `0.00820060347451222915278210035215742049…` |
| `B(40)` | `0.78543358250241188453682474462628478058…` |
| `C(40)` | `0.06676522688159649964630602302943437051…` |
| Sum | `2.89339941285852061333591286800787657159…` |
| `2.894 − sum` | `0.00060058714147938666408713199212342840…` |

Arb encloses the sum with radius less than `5.28×10^−76` and encloses
the last difference with radius less than `5.39×10^−76` at the reported
precision. In particular, the positive rounding margin is certified; it is
not inferred from printing a rounded decimal.

### Upstream K and auxiliary constants

For this row, the notebook's Appendix B calculation has `α=1/2`,
`R=5.558691`, and `t0(z)=max(51,z)`. Its scalar upper bound for `K` is

\[
\frac{e^{-z/2}\log(2\pi)}z+
\frac{e^{-z}(9+z/2)}{2\pi z}+
\frac{e}{\pi(1-1/t_0(z))}
\left(1+\frac14+\frac{21}{2z}\right)+e^{-2/R}.
\]

At `z=40` the small, non-zero-free-region, and zero-free-region
contributions are respectively
`0.000000000094703674815865579118…`,
`1.334873662269126963305222056726…`, and
`0.697818012142786945504170690750…`.
Their sum is
`2.032691674506617583625258326595… < 2.033`, with certified positive
margin `0.000308325493382416374741673404…`.
This agrees with the notebook's saved numerical result and its stated
upward rounding.

The exact Section 3 expression gives
`N=0.446004428978631443791374688595…`, so both `N<0.4461` and
`4N<1.785` hold with certified margins. For
`f(y)=2N/y²−1−3y/(2π)`, Arb certifies
`f(0.8029)>0` and `f(0.8030)<0`.
Since `f` is continuous and strictly decreasing for positive `y`, its
unique positive root lies between these two endpoints. Consequently the
use of `0.8029` in denominators is conservative. No numerical root finder
is trusted for that bracket.

### Applicability and endpoint reduction

A scalar evaluation at `z=40` alone cannot establish a bound for all
admissible `x,T`. The relevant elementary endpoint reductions were checked
separately on paper for this row:

- `z≥40` implies `T>z²≥1600`, so the Section 3 condition
  `lambda ≥ theta'/T` is satisfied using `theta'≤0.8030`.
- The theorem's upper bound gives `T < x^(1/2)/4`, hence also the weaker
  `T < x^(1/2)` used in the scalar calculation. The Arb check
  `c*theta0>1` makes the denominator estimate
  `log(c*theta' x/T) ≥ (1/2)log x` valid. Also
  `1+(c−1)lambda=e^lambda`, which gives the displayed `B(z)`.
- For `z≥40`, every positive factor in `A(z)`, `B(z)`, and `C(z)` is
  constant or decreasing. Their maximum is therefore attained at `40`.
  The notebook's truncations of negligible terms at log-heights 100 and
  500 do not affect evaluation at the first row's base height 40; no term
  was dropped in this verifier.
- In the displayed `K` bound, both small terms decrease with `z`;
  `t0(z)` increases, so `1/(1−1/t0(z))` decreases; the remaining factor
  `1+1/4+21/(2z)` decreases and the final term is constant. Its maximum
  is likewise at `40`. The `t0=max(51,z)` here is the Appendix B
  integral estimate's weaker lower-height bound, and is not confused
  with Theorem 1.3's stronger `max(51,z²)` requirement.
- Since `Tstar≤2T`, the Theorem 1.3 upper bound places `Tstar` below
  `x^(1/2)/2−1`, the Appendix B integral theorem's upper limit. Its lower
  bound also follows from `Tstar≥T>z²`.

These are elementary mathematical checks of the reductions used in this
particular scalar reconstruction. They have not been formalized in Lean
or encoded as an Arb verification over an unbounded domain. The underlying
analytic error estimates, the uniform short-interval argument for arbitrary
`h`, and the source's upstream zero-free-region theorem remain literature
dependencies. This audit found **no first-row rounding failure or missing
parameter restriction in these numerical reductions**, but does not claim
to have independently proved every analytic step in Theorem 1.3.

## Publication evidence and the remaining comparison

Primary evidence obtained:

- [Publisher's volume 73(2) contents](https://press.amu.edu.pl/media/productattach/s/p/spis_tresci_functiones_vol73.2_2025_amup.pdf)
  lists the paper starting at page 223 and the next article at page 243.
- [Crossref DOI record](https://api.crossref.org/works/10.7169/facm/241110-18-11)
  gives volume 73, issue 2, pages 223–242 and publication date 2025-12-12.
- [Daniel R. Johnston's publication list](https://sites.google.com/view/danielrjohnston/research)
  identifies the article as a 2025 journal publication and links both versions
  of the work (arXiv and journal).
- The journal's [editorial ethics statement](https://fa.amu.edu.pl/html/ethics.pdf)
  identifies its peer-review procedure. Publication is not inferred merely
  from an arXiv journal-reference field.

The unresolved step is to obtain the journal article, or an explicitly
identified accepted manuscript, and compare its Theorem 1.3, Table 1 first
row, and relevant conventions. The arXiv sources are publicly supplied by
the authors but neither downloaded archive identifies itself as the accepted
manuscript. Their matching statements are strong version-stability evidence;
they are not proof that no intervening journal edit occurred.

## Reproducibility and files

Downloaded materials, extracted source, full version diff, rendered page
images, and acquisition metadata are in the ignored local directory
`routes/qrh/tmp/input_review_6/`. They are not republished by this report.
The companion
[`input6_source_review_2026-11-06.json`](input6_source_review_2026-11-06.json)
records source URLs, hashes, the exact Lean files audited, comparisons and
outstanding checks. Source archives and PDFs remain obtainable from the
versioned arXiv links in that record.

No Lean source, existing manuscript, certificate or historical review was
modified. No new theorem was compiled or asserted by this source audit.
