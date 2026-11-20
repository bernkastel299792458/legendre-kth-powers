# Bandwidth and first-harmonic requirements at 115.1 and 115.2

At \(L=115.1\) and \(115.2\), the freedom to change a signed bandlimited test includes arbitrary real integrable linear combinations, evenization, and physical translations. A scaled periodic density gives a simultaneous dual bound for all of them. The estimates below include an explicit term for their physical tails. They describe the sieve inputs and normalized angular mean; the model is a synthetic positive measure and makes no claim concerning the full zeta explicit formula.

Let \(H=3000175332800\), \(d=\log(1+4e^{-L/4})/2\), \(c=L+d\) and \(R=10^{-4}\). For a physical test \(F(v)\), write \(I_F=\int_{\mathbb R}F(v)\,dv>0\) and
\[
  T_F=\frac{\int_{|v|>R}F(v)_+\,dv}{I_F},\qquad
  \widehat F(t)=\int_{\mathbb R}F(v)e^{itv}\,dv.
\]
For any angular base frequency \(h\) used below, put \(b=hd,\ s=2\pi-2b,\ A=2\pi/s\), and \(P_b(u)=A\,\mathbf1_{\operatorname{dist}(u,2\pi\mathbb Z)>b}\). Use the restricted arithmetic measure
\[
 d\mu_h(t)=\lambda\,\frac{e^{-(\log t-c)/2}}{\log t}\,
       P_b(h(\log t-c))\,dt,\qquad |\log t-c|\leq R.
\]
It has no mass in the open target. At each \(L\), all rows below satisfy the known interval bounds with numerators 2, both for \(\eta=1.1328,\ y\geq e^{70}\) and \(\eta=1.09,\ y\geq e^{50}\). The middle column lists an upper bound for the numerator *before* multiplying by \(\lambda\). The last cell on each line gives the scale factor actually allowed. The estimates hold for each individual \(h\) in an indicated range.

| \(L\) | \(h/H\) | Local sieve numerator | \(\lambda\) |
|---:|---:|---:|---:|
| 115.1 | 1 | 1.961531 | 1.01960 |
| 115.1 | 1 to 1.005 | 1.976889 | 1.01160 |
| 115.1 | 1.0126 | 1.999969 | 1.000015 |
| 115.2 | 1 | 1.890362 | 1.05798 |
| 115.2 | 1 to 1.025 | 1.961943 | 1.01930 |
| 115.2 | 1.0381 | 1.999522 | 1.00023 |

To verify the table, apply the [interval maximization for the periodic density](../../round4/low/DUAL.md) replacing its frequency \(H\) by \(h\). The angular integral on every interval of length \(2\pi k+w,\ 0\leq w<2\pi\), is bounded by \(2\pi k+A\min(w,s)\). On the first period of lengths the logarithmic sieve ratio is largest at \(w=s\) for a clipped arithmetic length above the sieve threshold. At longer lengths use \(S(w)/w\leq4\pi/(2\pi+s)\); for clipped intervals shorter than the threshold use the pointwise density. On a box of frequencies, enclose \(s\) by its values at the two endpoints. Substitute the smallest \(h\) in \(-\log h\) and the first-period Jacobian \(e^{2\pi/h}\). Each of these substitutions increases the estimate. [Certified 192-bit interval arithmetic](bandwidth_dual.py) also checks that the resulting density is less than \(0.03\) and that the previous integer rounding allowance of \(3(\log y+\eta)/y\) fits within every row. The signed-sum identity below is for the continuous measure; the integer version has the additional bounded-variation error given in the cited proof.

**Exact extremality for a constant exterior density.** If \(\operatorname{supp}\widehat F\subset[-h,h]\), then \(\int FP_b(hv)\,dv=I_F\). In fact the periodization of \(F(u/h)\) has all nonconstant Fourier coefficients zero, including those at the boundary by continuity. Since \(P_b\) vanishes for \(|v|<d\) and \(P_b\leq A\),
\[
    \int_{|v|\geq d} F(v)_+\,dv\ \geq\ (1-b/\pi)I_F.
\]
For \(g_b(hv)=(\cos b-\cos(hv))/((hv)^2-b^2)\) equality holds. On the occupied arcs \(g_b\) is positive; outside the target every positive value lies on an occupied arc up to endpoints. Thus this kernel optimizes the constant-density exterior functional. The length-dependent version is constrained by the scaled measure in the table.

**Necessary harmonic or tail contribution.** If \(F\) is real with Fourier support inside \([-2h,2h]\), only the modes \(0,\pm1\) of its periodization can be nonzero. The Fourier coefficient of \(P_b\) at 1 is \(-2\sin b/s\). Consequently
\[
 \int F(v)P_b(hv)\,dv=I_F-\frac{4\sin b}{s}\Re\widehat F(h).
\]
The same identity holds for arbitrary \(F\) if the other sampled harmonics vanish. For a general smoother \(F\) with absolutely convergent sampled product, the further terms are \(-4\sin(nb)\Re\widehat F(nh)/(ns)\), \(n\geq2\). Truncating the model to \(|v|\leq R\) loses at most \(A\int_{|v|>R}F_+(v)\,dv\) in its signed integral. Finally, the Jacobian, the prime weight \((\log t)/\sqrt t\), and the exponential in \(d\mu_h\) leave exactly \(e^{c/2}\,dv\). Hence any purely local sieve majorant for the exterior positive contribution smaller than \(e^{c/2}I_F\) must satisfy
\[
 \frac{4\sin b}{s}\frac{\Re\widehat F(h)}{I_F}+A T_F
      > 1-\lambda^{-1},
 \qquad \operatorname{supp}\widehat F\subset[-2h,2h].                 \tag{1}
\]
This also applies when the proposed majorant uses overlapping interval bounds, since the same measure satisfies them simultaneously. Formula (1) is stronger than its version with \(|\widehat F(h)|\) on the left.

At \(h=H\), if the cutoff is at most \(H\), (1) requires \(T_F>.0075274\) and \(T_F>.0222828\), respectively. With arbitrary bandwidth up to \(2H\), it instead requires \(\Re\widehat F(H)/I_F\) to exceed \(0.0125447\) and \(0.0365645\), respectively, minus \(AsT_F/(4\sin b)\). For the continuous frequency ranges in the table, the zero-tail lower bound on that same harmonic is greater than \(0.0069\) and \(0.0116\) *at every frequency in the range*. Here one can use the weaker \(\sin b\leq1\). The last frequency at each \(L\) supplies a positive margin even for cutoffs \(1.0126H\) and \(1.0381H\), subject to (1)'s tail term. These are lower requirements for escaping this positive-measure comparison. They do not assert the existence of an admissible kernel meeting the prime-interval budget or of a zero beyond the verified height.

**A concrete class including translated kernels.** Let \(F(v)=\sum_j c_jg_{a_j}(\kappa_j(v-v_j))\), with real coefficients, \(0<a_j<\pi\), \(H/2\leq\kappa_j\leq h\), \(|v_j|\leq1000/H\), and \(I_F>0\). Define its coefficient ratio
\[
  B=\frac{\sum_j |c_j|/\kappa_j}{I_F},\qquad
  z=(H/2)(R-1000/H).
\]
Integrating \(2/(u^2-a_j^2)\) separately on the two tails yields \(T_F\leq4B/(z(1-\pi^2/z^2))\). The script checks this is smaller than \((1-1/\lambda)/A\) for each \(h=H\) row if \(B\leq10^5\); it remains smaller even on both increased-bandwidth rows if \(B\leq200\). The harmonic at the band endpoint vanishes, so (1) rules out each of those whole test classes at the respective target. The coefficient ratio allows arbitrary signs and a large amount of cancellation of total mass.
