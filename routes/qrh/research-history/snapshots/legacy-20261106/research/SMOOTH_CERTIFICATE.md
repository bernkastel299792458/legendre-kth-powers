# A conditional Arb certificate for the fourth-power segment

Date: 2026-11-06. This certificate assumes that every nontrivial zeta zero has real part at most (7/8). It establishes, conditional on that hypothesis and the published density input below, a prime in

\[
(x,x+4x^{3/4})\qquad(400\le\log x\le700).
\]

Consequently it covers consecutive fourth powers for every integer (n) with (100\le\log n\le175). It does **not** establish the statement for all (n). In particular, it does not bridge the interval between the separately established small-range endpoint and (\log x=400), or prove an infinite tail. The numerical part is an Arb interval certificate, not a Lean formalization of the analytic inputs.

The script is `code/certify_smooth_segment.py`; its saved output is `results/smooth_segment_certificate.json`. All 60 closed cells of width 5 cover ([400,700]) exactly, with a strictly positive margin. The largest certified upper bound is on ([400,405]):

\[
\Delta\le
\frac{862339984538098379495241}{10^{24}}
=0.862339984538098379495241<1.
\]

The saved Arb ball before decimal outward rounding is
`[0.8623399845380983794952402691369004305887 +/- 1.85e-42]`.

## 1. Inputs and source version

The density input is Chourasiya–Simonič, *An explicit form of Ingham's zero density estimate*, [arXiv:2507.15184v2](https://arxiv.org/html/2507.15184v2), Corollary 1 and the first 12 rows of Table 1. For (T\ge H=3\cdot10^{12}), on each listed closed row,

\[
N(\sigma,T)\le cT^{p(\sigma)}(\log T)^{2+p(\sigma)}
+d(\log T)^2+e\log T,
\qquad p(\sigma)=\frac{3(1-\sigma)}{2-\sigma}.
\]

Here (N(\sigma,T)) counts zeros with (\beta\ge\sigma) and (0<\gamma\le T), with multiplicity. The script copies all three constants for every row ([i/32,(i+1)/32]), (16\le i\le27); it does not extrapolate constants to other rows. The logarithmic exponent is the **v2** exponent ((7-5\sigma)/(2-\sigma)=2+p(\sigma)), not the earlier uniform power 3.

Equation (11) of the same source gives, in this height range,

\[
N(T)\le\frac{T}{2\pi}\log\frac{T}{2\pi e}+0.43\log T<T\log T.
\]

The final inequality follows already from (\pi>3) and (T\ge H). Only the weaker (N(T)\le T\log T) is used. Every height where the kernel has nonzero decreasing mass is above (H); this certificate does not require applying either input below its stated domain. It does not need a separate finite-height RH calculation.

## 2. Smooth explicit formula and regularity

Put (h=4x^{3/4}), (Y=x+h), and

\[
\phi(v)=v^2(1-v)^2\quad(0\le v\le1),\qquad
F(t)=\phi((t-x)/h),\qquad
I=\int_0^1\phi(v)\,dv=\frac1{30},
\]

with both functions extended by zero off their supports. Then (F\in C^1), (F') is absolutely continuous, and (F'') is integrable and has bounded variation. Both (F) and (F') vanish at both support endpoints.

The integrated explicit formula can be written, for (t>1), as

\[
\Psi_1(t)=\frac{t^2}{2}
-\sum_\rho\frac{t^{\rho+1}}{\rho(\rho+1)}
-t\log(2\pi)+\frac{\zeta'(-1)}{\zeta(-1)}
-\sum_{m\ge1}\frac{t^{1-2m}}{2m(2m-1)}.
\]

Here (\Psi_1(t)=\int_1^t\psi(u)\,du), with the usual harmless convention at jumps. On the fixed compact interval ([x,Y]), the zero series converges absolutely and uniformly: its terms are bounded by a compact-interval constant times (1/|\gamma|^2), and the zero-count estimate implies convergence of that scalar series. The trivial-zero series is also absolutely and uniformly convergent there. Thus it is legitimate to integrate the series against (F''\in L^1). Twice integrating each term by parts, with both boundary terms zero, gives

\[
\sum_{m\ge1}\Lambda(m)F(m)
=hI-\sum_\rho\int_x^Y F(t)t^{\rho-1}\,dt
-\int_x^Y\frac{F(t)}{t(t^2-1)}\,dt. \tag{1}
\]

One can equivalently obtain the left side as (\int F''(t)\Psi_1(t)\,dt) in the distributional sense. The affine terms disappear. For the trivial terms, two integrations by parts give (-\sum_{m\ge1}\int F(t)t^{-2m-1}dt), which sums to the final integral. This argument never differentiates the conditionally convergent unsmoothed zero series.

## 3. A bounded-variation Mellin kernel

Set (q=Y/h=1+e^{L/4}/4), where (L=\log x). Repeated integration by parts gives, for (j=0,1,2),

\[
\frac{1}{hI}\left|\int_x^YF(t)t^{\rho-1}dt\right|
\le x^{\beta-1}R_j(q/|\gamma|)^j.
\]

Indeed, the denominator is (\rho(\rho+1)\cdots(\rho+j-1)), whose modulus is at least (|\gamma|^j); on the support (t^{\beta+j-1}\le x^{\beta-1}Y^j). The exact derivative ratios are

\[
R_0=1,\quad R_1=\frac{15}{4},\quad
R_2=\frac{40}{\sqrt3}<24.
\]

A third integration by parts uses the measure (dF''), rather than an ordinary third derivative with discarded endpoint terms. For the zero extension of (\phi''), its total variation is

\[
\int_0^1|\phi'''(v)|dv+|\phi''(0)|+|\phi''(1)|
=6+2+2=10.
\]

The endpoint jumps are essential. Dividing by (I) gives (R_3=300). Therefore a valid envelope is

\[
g_q(t)=\min\{1,\tfrac{15}{4}q/t,24(q/t)^2,300(q/t)^3\}. \tag{2}
\]

This function is continuous and nonincreasing, is exactly 1 for (t\le15q/4), and equals (300(q/t)^3) for (t\ge(25/2)q). Its quadratic or cubic decay also ensures absolute convergence of the transformed zero sum in (1).

## 4. Uniformity across each closed (L)-cell

For a cell ([a,b]\subset[400,700]), take (q_b=1+e^{b/4}/4). For each individual zero and each (L\in[a,b]),

\[
e^{(\beta-1)L}g_{q(L)}(|\gamma|)
\le e^{(\beta-1)a}g_{q_b}(|\gamma|). \tag{3}
\]

This uses (\beta<1) and monotonicity of (g_q(t)) in (q). It establishes a common envelope **before** Stieltjes integration. No comparison of the parameter-dependent measures (-dg_q) is asserted.

Define the actual cumulative weighted count

\[
A_a(T)=\sum_{0<\gamma\le T}e^{(\beta-1)a}.
\]

Layer integration and the assumed (\beta\le7/8) give

\[
A_a(T)\le e^{-a/2}N(T)
+a\int_{1/2}^{7/8}e^{(\sigma-1)a}N(\sigma,T)\,d\sigma. \tag{4}
\]

For (\beta\ge1/2), the corresponding single-zero identity is exact; for (\beta<1/2), the baseline (e^{-a/2}) overestimates its weight. No symmetry subtraction is needed. Zeros exactly at a sigma endpoint are harmless for this integral and are included by the source's (\beta\ge\sigma) convention.

Conjugation pairs the positive and negative imaginary parts. Stieltjes integration by parts yields the total normalized zero bound

\[
Z\le2\int_0^\infty A_a(t)(-dg_{q_b}(t)). \tag{5}
\]

The boundary term at infinity vanishes by (N(t)=O(t\log t)) and cubic decay; at zero the cumulative count is zero. Although (g) is constant below its first breakpoint, zeros at those lower heights are still included in (A_a(t)) at all later heights.

## 5. Positive rectangular sums and the infinite height tail

The sigma interval is divided at exact rational points with spacing (1/1024), giving 384 cells. Every cell is contained in a single source row. On ([s_0,s_1]), the contribution to (4) is bounded above by

\[
a(s_1-s_0)e^{(s_1-1)a}
\big[c e^{p(s_0)u}u^{2+p(s_0)}+du^2+eu\big],\qquad T=e^u. \tag{6}
\]

This follows by taking the increasing exponential at (s_1) and the decreasing zero count at (s_0). Thus it does not require a quadrature remainder estimate. The powers are evaluated as (u^2\exp(p(s_0)(u+\log u))) with Arb.

The log-height grid has exact spacing (1/8). Its starting point is rounded downward from (\log q_b+\log(15/4)), and the script certifies (g(e^{u_0})=1) and (u_0>\log H). Thus there is no omitted decreasing mass below it. For each grid interval ([u_i,u_{i+1}]), the actual increasing count (A_a(e^u)) is bounded by its value at the right endpoint. If (\Phi_a(e^{u_{i+1}})) denotes (4) bounded using (6) and (N(T)\le T\log T), then

\[
2\int_{u_i}^{u_{i+1}} A_a(e^u)(-d g(e^u))
\le 2\Phi_a(e^{u_{i+1}})
\big(g(e^{u_i})-g(e^{u_{i+1}})\big). \tag{7}
\]

The script checks every difference is certainly nonnegative. It never assumes that an independently supplied density upper bound itself is monotone in height.

The end point (U) is rounded upward to the grid and checked to lie in the cubic part of (2). The remaining tail is bounded using the full cumulative count

\[
A_a(e^u)\le e^{-a/8}N(e^u)\le e^{-a/8+u}u.
\]

Since (-d g(e^u)=900q_b^3e^{-3u}du) there, the resulting bound is

\[
2\int_U^\infty A_a(e^u)(-dg(e^u))
\le1800q_b^3 e^{-a/8-2U}\left(\frac U2+\frac14\right). \tag{8}
\]

This is the **tail of the Stieltjes integral**, not just a sum over zeros with (\gamma>e^U). It includes the residual (g(e^U)) weight of lower zeros, so no boundary correction has been lost.

## 6. Removing higher prime powers and trivial zeros

An elementary bound sufficient here is

\[
\psi(Y)-\theta(Y)\le\frac{\sqrt Y(\log Y)^2}{2\log2}.
\]

To see it, write the left side as (\sum_{r=2}^{\lfloor\log Y/\log2\rfloor}\theta(Y^{1/r})), use (\theta(z)\le z\log z), and bound each term by (\sqrt Y\log Y/2). Also (\max\phi/I=15/8). Consequently the normalized higher-power contribution is at most

\[
\frac{15}{8}\frac{\sqrt Y(\log Y)^2}{2h\log2}.
\]

For an entire cell, put (\epsilon=4e^{-a/4}); using (\log Y\le b+\log(1+\epsilon)) gives the script's upper bound

\[
P_{a,b}=\frac{15}{8}\frac{\sqrt{1+\epsilon}
 [b+\log(1+\epsilon)]^2}{8\log2}e^{-a/4}. \tag{9}
\]

The normalized last integral of (1) is at most

\[
V_a=\frac{e^{-3a}}{1-e^{-2a}}. \tag{10}
\]

The certificate checks (\Delta=Z_{a,b}+P_{a,b}+V_a<1). Therefore (1) has more positive mass than all higher prime powers can account for. Some prime (p) has (F(p)>0), hence (x<p<x+4x^{3/4}). The kernel vanishes at both endpoints, so the resulting interval is open. With (x=n^4), its upper endpoint (n^4+4n^3) is smaller than ((n+1)^4).

## 7. Reproduction and audit

The saved run used Python 3.12, python-flint 0.9.0, and 160-bit Arb arithmetic. Decimal source constants are parsed directly as Arb balls, not through binary floating-point. Rational grids and coverage endpoints use exact integer ratios. Floating-point formatting is only for progress display; the proof comparison uses Arb and the saved exact outward rational bound.

From this repository directory, regenerate with:

```powershell
python code/certify_smooth_segment.py
```

Perform a read-only full replay, without rewriting the JSON:

```powershell
python code/certify_smooth_segment.py --verify
python code/certify_smooth_segment.py --verify results/smooth_segment_certificate.json
```

The Python entry point `verify_certificate(path=OUTPUT)` returns a summary dictionary or raises `ValueError`. It checks the script SHA256, the source constants and kernel, the exact endpoints and continuous coverage, and replays every stored cell at its recorded precision. Each saved rational upper bound must enclose the recomputed outward bound and remain below 1. It does not trust the saved decimal display or a stored success flag alone. Normal `--single 400 401` prints one cell without writing results.

The independent reviewer checked the Mellin and bounded-variation constants, the common envelope across cells, the source row domains, the layer integral, and the analytic tail. A separate 512-bit implementation replayed cells ([400,405]), ([550,555]), and ([695,700]), agreeing with the saved balls and rational upper bounds. A full `--verify` replay also passes. These checks are independent computational and mathematical review, not an external peer-review claim.

Stable artifact hashes:

| Artifact | SHA256 |
| --- | --- |
| `code/certify_smooth_segment.py` | `ec7e6d218e09967d9161f44074c35ecdce09eb6a3a3a3d307db1e5b36083d21e` |
| `results/smooth_segment_certificate.json` | `7e3768054da03709927d63a3f2d5766b7d0b26a7f600d4a8005621413e1a2a7f` |

The JSON contains the script hash. Its own hash is recorded here rather than recursively inside itself. Regeneration changes timestamp/runtime metadata and therefore the JSON hash, even if all mathematical values agree.
