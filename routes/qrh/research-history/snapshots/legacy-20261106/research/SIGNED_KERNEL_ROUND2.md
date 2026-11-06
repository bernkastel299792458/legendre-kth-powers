# Signed Jacobi kernels at L=120: a finite-dimensional experiment

Date: 2026-11-06. This experiment permits genuine sign changes; it does not impose positivity on the kernel. In the tested one-, two-, and three-parameter families, the unrestricted numerical LP optima returned to kernels whose negative mass is numerically zero. The best three-parameter candidate improves the sampled full error budget from about 2389.91 to 2271.61. A forced signed candidate with (L^1) ratio 16.29 gives a much worse budget, about 46129. Neither result approaches the sufficient condition (\Delta<1).

These are reproducible **exploratory computations**, not interval certificates. In particular, sampled suffix maxima are not proofs of a continuous-frequency supremum. The experiment is restricted to (L=120), at most three Jacobi coefficients, and the stated objective; it does not prove that signed kernels in general cannot work.

Artifacts: `code/signed_kernel_round2.py` and `results/signed_kernel_round2.json`. The script imports the source-checked density envelope from `density_envelope_round2.py` and leaves all earlier files and certificates unchanged.

## 1. Signed kernels still imply a prime when the budget passes

Let

\[
\phi(v)=v^2(1-v)^2\left(1+\sum_{j=1}^{d}a_jP_{2j}^{(2,2)}(2v-1)\right),
\quad 0\le v\le1,\quad d\le3,
\]

extended by zero. Jacobi orthogonality gives (I=\int\phi=1/30>0) exactly, irrespective of the coefficients. It is convenient to work with (Q=\phi/I=30\phi), whose integral is 1. No positive or negative part of its support leaves ([0,1]). The factors (v^2(1-v)^2) preserve the zero endpoint value and zero first derivative needed for the smooth explicit formula.

For (x=e^{120}), (h=4x^{3/4}), put (F(t)=\phi((t-x)/h)). If the explicit formula proves

\[
\sum_m\Lambda(m)F(m)>
\max(0,\max\phi)\,[\psi(x+h)-\theta(x+h)],
\]

then the sum of prime contributions is positive, so a prime has positive (F(p)). Consequently (x<p<x+h). Signed prime contributions do not invalidate this implication; all prime powers of exponent at least 2 have been bounded above using the **positive** maximum. A bound by (\max|\phi|) would be permissible but unnecessarily larger.

## 2. Full norm and frequency bookkeeping

The code computes

\[
R_0=\int_0^1|Q|,\quad R_1=\int|Q'|,\quad R_2=\int|Q''|,
\quad R_3=\int|Q'''|+|Q''(0)|+|Q''(1)|.
\]

The final two terms in (R_3) are the jumps of the zero extension. Polynomial real roots split the absolute integrals for candidate evaluation; critical points give the positive maximum. These root computations are floating-point, not certified root isolation. The LP itself uses positive Gauss quadrature and absolute-value auxiliary variables for these norms, and every resulting candidate is reevaluated with the polynomial-root method.

With (\epsilon=h/x=4e^{-30}), (w=|\gamma|\epsilon), the derivative envelope is

\[
g_{\rm old}(w)=\min_{0\le j\le3}R_j\left(\frac{1+\epsilon}{w}\right)^j.
\]

Its first entry is (R_0), not 1. The centered Fourier transform of (Q) has the explicit real basis

\[
B(w)=\sum_{j=0}^{d} a_jB_j(w),\qquad a_0=1,
\]

\[
B_j(w)=(-1)^j\frac{15}{2}(2j+1)(2j+2)
\frac{j_{2j+2}(w/2)}{(w/2)^2}, \tag{1}
\]

where (j_m) is the spherical Bessel function. Rodrigues' formula and repeated integration by parts prove (1). The code explicitly sets (B_0(0)=1) and (B_j(0)=0) for (j>0). As checks, (B_0(w)=1-w^2/56+O(w^4)) and (B_1(w)=-w^2/42+O(w^4)).

The signed Mellin-to-Fourier comparison uses absolute moments, not signed moments. Define

\[
M_{2,\rm abs}=\int_0^1v^2|Q(v)|\,dv.
\]

For (0\le\beta\le1), the amplitude error is bounded by (\epsilon v), and the phase error by (|\gamma|\epsilon^2v^2/2). Symmetry of (|Q|) gives (\int v|Q|=R_0/2), hence

\[
\frac{|\widehat F(\beta+i\gamma)|}{hI x^{\beta-1}}
\le |B(w)|+\epsilon\left(\frac{R_0}{2}
+\frac{wM_{2,\rm abs}}2\right). \tag{2}
\]

At every sampled frequency, candidate evaluation uses the smaller of (2) and (g_{\rm old}), then takes the suffix maximum. The initial plateau is therefore determined by all future sampled frequencies and (R_0); it is not artificially set to 1. The forced signed example has initial envelope about 9.36.

## 3. Low frequencies and the infinite BV tail

The frequency grid begins at (w_0=64\epsilon). All positive-height zeros with (|\gamma|\le64) are separately charged the full safe amount

\[
2e^{-L/2}\frac{64\log64}{2\pi}R_0.
\]

This uses finite RH and the total-count upper bound already established in the density pipeline. Later cumulative Stieltjes sums include some of these zeros again; the duplication is conservative and numerically negligible. No zero block is omitted to create an apparent gain.

For (w>W), the envelope is the analytic BV bound

\[
G(w)=C/w^3,\qquad C=R_3(1+\epsilon)^3.
\]

The value (C/W^3) is included in **every** finite-grid suffix maximum. A possible downward seam jump is explicitly charged. This prevents an upward jump at the transition, which would invalidate use of the positive measure (-dG).

Let (\Phi_L(T)) be the weighted cumulative positive-height zero upper bound from `density_envelope_round2`, retaining its symmetry layer factor, CS v2, Appendix (119), legal Bellotti–Wong local cap and source-row monotonicity. Above (W/\epsilon), the code evaluates

\[
2\int_{\log(W/\epsilon)}^{U}
\Phi_L(e^u)\,3R_3q^3e^{-3u}\,du,
\qquad q=(1+\epsilon)/\epsilon,
\]

and adds the full QRH/total-count analytic remainder

\[
\frac{3R_3}{\pi}q^3e^{-L/8-2U}(U/2+1/4).
\]

The integral is floating-point quadrature, but the remaining infinite interval is not discarded. These are cumulative Stieltjes tails, so residual weights from lower zeros are included. The fine runs use (W=512) and (1024), not a handful of selected zeros of (B).

Finally the positive prime-power maximum is charged its usual elementary bound. The trivial-zero integral is bounded by **(R_0/(x^3-x))**. The old nonnegative mass-only bound is not silently reused.

## 4. The finite LP objective

The LP has (d\in\{1,2,3\}) free coefficients, nonnegative variables (G_i) for the sampled nonincreasing envelope, quadrature variables for (|Q|) and (|Q'''|), an endpoint absolute-value variable, and a positive-maximum variable. It enforces both signs of (1), includes the error in (2), requires (G_i\ge G_{i+1}), and requires the final value to dominate (C/W^3). It does not constrain the sign of (Q).

The finite zero budget is

\[
2\sum_{i=0}^{n-1}\Phi_L(w_{i+1}/\epsilon)(G_i-G_{i+1}),
\]

plus the seam jump and complete tail. It can be rewritten with nonnegative coefficients of the (G_i). The coefficient of (R_3) in that rewrite is the full tail per (R_3), minus

\[
2\Phi_L(W/\epsilon)(1+\epsilon)^3/W^3.
\]

The code checks this adjusted coefficient is positive. This subtraction is **integration by parts of the kernel budget**, not subtraction of two density upper bounds. The complete objective also includes the positive-maximum prime-power cost, the low-height (R_0) cost and the trivial-zero (R_0) cost.

The solver is SciPy HiGHS. Coefficients are allowed in ([-10000,10000]); no optimum touches this limit. The design grid has spacing 0.25 above 0.05, additional small-frequency and finite-RH cuts, (W=512), and 80 positive Gauss nodes for the LP norms. A subsequent three-variable Nelder–Mead check converged back to the same candidate after 112 evaluations. This is numerical optimization of the stated finite objective, not a global theorem for the continuous problem.

## 5. Actual results

The free coefficient vectors returned were:

| Dimension | Coefficients |
| ---: | --- |
| 1 | (0.2232764285) |
| 2 | (0.3102619897, 0.1330642881) |
| 3 | (0.3518066678, 0.2012830217, 0.0869634768) |

Their evaluated (R_0) values differ from 1 by at most (7\cdot10^{-12}), consistent with numerical polynomial integration noise. Their evaluated minima are zero up to rounding. Thus permitting signs did not cause these optima to exploit negative mass.

A separate constrained LP requires (Q(1/2)\le-50), ensuring a genuinely signed polynomial. It returned coefficients approximately

\[
(12.5318028965,\;2.0213078756,\;19.4626741756).
\]

Its actual (R_0\approx16.28969453), negative mass (\approx7.64484726), positive maximum (\approx27.87668), and (R_3\approx298249.23) are included in its budget. The constraint acts on the polynomial, so it cannot be satisfied merely by inflating an auxiliary (L^1) variable.

With candidates held fixed, the dense-grid checks give:

| Candidate | W=512, frequency step 1/16 | W=1024, frequency step 1/32 |
| --- | ---: | ---: |
| Original beta kernel | 2393.03009 | 2389.91421 |
| Free one-parameter LP | 2322.35190 | 2319.09597 |
| Free two-parameter LP | 2291.02111 | 2287.69689 |
| Free three-parameter LP | 2274.99243 | 2271.60725 |
| Forced signed three-parameter LP | 46149.51054 | 46128.97726 |

Both dense runs use sigma quadrature order 24 and retain the full infinite tail. In the final free three-parameter result, the high-frequency tail contributes approximately 0.0746393 and prime powers (3.47\cdot10^{-10}). In the forced signed result, these contributions are approximately 8.73124 and (6.77\cdot10^{-9}). The large signed cost is already present in the full finite frequency envelope; it is not explained solely by a deliberately loose tail.

The best free candidate is about 4.95% below the original beta kernel evaluated with the same actual-Fourier sampled machinery. Comparison against older derivative-envelope scans mixes two changes and should be labeled accordingly. The change from the first to the second dense run is about 0.15%, much smaller than the gap to 1; no precision near a passing threshold is being inferred.

For context, the independent structural model in `research/STRUCTURAL_ROUND2.md` already permits an adverse configuration for signed kernels with (R_0<11.81128\ldots). The forced signed control exceeds that particular threshold but still performs much worse in this budget. This comparison concerns an admissible model class, not the actual location or phases of zeta zeros.

## 6. Reproduction, APIs and limits

Run from the repository directory:

```powershell
python code/signed_kernel_round2.py
```

The full recorded run took about 21 seconds in this environment. It writes only `results/signed_kernel_round2.json`, recording the source-code hashes, coefficients, norms, every budget component, LP settings, local optimizer status and both dense-grid comparisons.

Reusable functions:

```python
budget = make_budget(L=120, dimension=3, end=1024,
                     step=.03125, sigma_order=24)
result = evaluate([a1, a2, a3], budget)
candidate = optimize_lp(3, budget, negative_center=None)
signed_candidate = optimize_lp(3, budget, negative_center=50)
```

`fourier_basis` and `kernel_stats` expose the analytical basis and the floating norm evaluation separately. `evaluate` includes all low/high-frequency and prime-power costs; it cannot be replaced by values at a few strategically chosen frequencies.

The remaining limits are substantive: a sampled suffix maximum may miss an inter-grid peak; polynomial roots and absolute integrals are not enclosed; source-density quadrature is not rigorous; the LP norms are quadrature approximations; and only a fixed low-dimensional family was tested. No passing certificate or general impossibility claim follows. The reproducible negative result is that this finite, explicitly budgeted attempt did not find a useful signed-kernel escape at (L=120).
