# Reflecting a subset of the Euler factors on the critical line

At \(Q=210,\ F=42,\ B=5,\ \alpha=1.06,\ w=.34,\ Z=384\), the full fourth-moment coefficient on \(\log T\ge U\) is below **.000810500** at \(U=35\), **.000729891** at \(U=37\), and **.000652476** at \(U=40\). The [one-sided Euler orientation](SWEEP.md) gave .000839933, .000743574 and .000659672.

Write \(Q=FB\) with \((F,B)=1\), and \(E_k(s)=\prod_{p\mid k}(1-p^{-s})\). For \(s=1/2+it\), the modulus of \(\zeta(s)E_F(s)E_B(1-s)\) is precisely \(|\zeta(s)E_Q(s)|\). Multiply the [asymmetric AFE](../../round6/phase/PERIODIC_FOURTH.md) by \(\mu(d)\mu(e)d^{-s}e^{s-1}\) for \(d\mid F,\ e\mid B\). Write \(z=\sqrt{t/(2\pi)},\ a=\sqrt Q\,\alpha\). In each row choose the forward cutoff \(aze^{v}e/(Bd)\) and its complementary dual cutoff, where \(v\) is uniform on \([-w,w]\). The forward index \(n=Bdj/e\) and the dual index \(m=Fej/d\) now have common cutoffs \(ae^vz\) and \(Qe^{-v}z/a\), respectively. After removing the common phase \(B^{it}\), the two real coefficient sequences, including their normalizations, are
\[
 A_n=\frac{\mathbf1_{(n,F)=1}c_B(n)}{\sqrt B},\qquad
 B_m=\frac{\mathbf1_{(m,B)=1}c_F(m)}{\sqrt F}.
\]
The elementary multiplier between them is the previous one. The total high-time AFE error is at most \(K t^{-1/4}\), where
\[
 K=16(2\pi)^{1/4}e^{w/2}\sum_{d\mid F,\,e\mid B}
    \frac{\max(\sqrt{Bd/(ae)},\sqrt{ae/(Bd)})}{\sqrt{de}} .
\]
The initial sharp time still suffices because \(Bd/e\) ranges between 1 and \(Q\). The bound on the early \(\zeta E_Q\) factor is unchanged.

The [two moving Hilbert endpoints](SWEEP.md) apply separately to the two periodic sequences. In the outer gcd pair \(h,k\), an excluded prime dividing \(hk\) makes the inner sequence zero. A Ramanujan prime dividing \(hk\) instead gives a zero-mean multiple of \(c_p(g)\). The unit/unit pair again uses its own nonnegative square. This verifies the cumulative and arithmetic squared-prefix envelopes for both sequences. The [weighted integer Hilbert symbol](ENDPOINT.md) now keeps only the allowable unit residues and applies the diagonal weights to the remaining Ramanujan primes. Its positive pivots are verified independently. Floating point proposes the spectral ceiling only; Arb certifies the resulting bound. The remaining signed contour for the fourth harmonic uses the two actual periodic absolute means and interval discrepancies. Its proof uses no other restriction on the sequences. The mixed squared norm may always use the geometric mean of the two individual fourth coefficients.

For every full product \(k=nm\), all its \(F\)-prime powers must occur in \(m\), all its \(B\)-prime powers in \(n\). The factors away from \(Q\) can be assigned in precisely \(\tau(k_{\perp Q})\) ways. Each term has the same raw sign and product \(c_B(n)c_F(m)=c_Q(k)\). Thus the complete short-product coefficient, its diagonal, and all its spacing estimates in the [nonstationary removal](INTERFERENCE.md) are the same as before. The branch one-norms in those estimates and the two square harmonic bounds for the center of \(S\) use the newly normalized sequences. In the elementary uniform bound for the mean of \(V\), the product of the two raw maxima bounds each raw coefficient product.

Only the arithmetic in the [stationary rational projections](GROUPED.md) needs a further check. The projections still use \(r,s\) coprime to \(Q\), so the two signed \(S\)-diagonals are the appropriate branch squares. The absolute endpoint strips use the raw means and discrepancies of both branches, with common \(1/\sqrt Q\). The finite Fourier coefficients of the raw dual sequence \(j\mapsto\mathbf1_{(j,B)=1}c_F(j)\), normalized by \(1/Q\), are
\[
   \mathbf1_{(h,F)=1}\,c_B(h)/B.
\]
This follows by the Chinese remainder theorem and multiplication by units in each local Ramanujan sum. Their absolute sum is \(\varphi(F)\sum_{j\bmod B}|c_B(j)|/B\). In the principal arithmetic phase the constant frequency requires \(s\mid n\). At \(n=sk\) its multiplier, including the raw forward coefficient, is \(\mathbf1_{(k,F)=1}c_B(k)^2/B\). This nonnegative sequence has mean \(\varphi(Q)/Q\); its harmonic error constant bounds its interval discrepancy. The remaining geometric errors over \(n\bmod Qs\) have the earlier bound multiplied by the raw forward maximum and the displayed Fourier one-norm in place of \(\varphi(Q)\). All individual geometric sums and the signed-rational Hilbert projection are otherwise unchanged.

The [branch bounds](balanced_branch.py) and [complete half-line implementation](balanced_fourth.py) include closed finite slabs followed by a uniform tail from the same branches using the elementary uncentered Cauchy estimate. A test at modulus 2310 did not improve the full bound in the parameter choices examined. The displayed certificate uses modulus 210 only.

~~~powershell
python -B round8/critical/balanced_fourth.py
~~~

2026-11-20. Joint project attribution to Claude and Codex.
