# Both moving boundaries of the smoothed fourth moment

For the complete normalized fourth moment of \(\zeta(1/2+it)E_{210}(1/2+it)\), uniformly in \(u=\log T\ge U\), the coefficient is below **.000839933** at \(U=35\), **.000743574** at \(U=37\), and **.000659672** at \(U=40\). The [last upper-endpoint estimate](ENDPOINT.md) gave respectively .000991964, .000869330 and .000750741. This calculation uses \(\alpha=.82,\ w=.34,\ Z=384\). These internal cutoff parameters may change between certificates for the same zeta factor.

## Difference of the two endpoint forms

Use the [paired-cutoff proof](../../round6/phase/SMOOTH_PHASE.md), and fix either individual fourth power. Write its two extreme lengths as \(Y_+(t)=\sigma\sqrt{t/(2\pi)}\), \(Y_-(t)=\eta Y_+(t)\), where \(\eta=e^{-2w}\). At each height the actual cutoff is \(Y_+(t)e^{-r}\) with \(r\) uniform on \([0,2w]\). For a fixed quadruple of indices let \(m\) be their maximum. The averaged indicator \(G_m(t)\) has derivative almost everywhere
\[
 G_m'(t)=\frac{\mathbf1_{m\le Y_+(t)}-\mathbf1_{m\le Y_-(t)}}{4wt}.
\]
The antiderivative in each off-diagonal frequency \(\log(n/n')\) produces the usual upper boundary and an integral against \(G_m'\). At each \(t\), the latter summed kernel is exactly the difference of the two sharp signed quadratic forms at \(Y_+(t)\) and \(Y_-(t)\), divided by \(4wt\). This follows term by term, since the maximum condition restricts all four original indices to the same cutoff. Both positive and negative orientations are included. Their sum can be bounded by applying the [integer Hilbert estimate](ENDPOINT.md) to each true endpoint. The older shift computation is also available for this integral, so the verifier takes the lesser completed fourth-moment bound for each branch.

Let \(K=\max(2Q,192)\), \(b=K(K+1)+10\), and \(t_e=(2\pi/\sigma^2)(b/\eta)^2\). For \(t\ge t_e\) both cutoffs exceed \(K(K+1)\). The upper bound for the signed form of length \(y\), divided by \(y^2\), is an affine function of \(\log y\) with nonnegative slope after freezing its reciprocal length terms at \(b\). Indeed the [endpoint Gram formula](../../round6/phase/SMOOTH_PHASE.md) has its logarithm only in the positive \(\mu^2\,2\rho^2\log y\) term. Its positive mixtures receive the same upper bound by evaluating at \(\ell=\log Y_+(T)\). Include \(16(.118)(M+D/(2\sqrt b))^4\) for the logarithmic reciprocal remainder, where \(M,D\) are the periodic absolute mean and discrepancy. Write the resulting bound as \(F(\ell,b)\). The two late endpoint costs together, divided by \(Y_+(T)^2\), are at most
\[
 \frac{1+\eta^2}{4w}F(\ell,b),
\]
because \(Y_+(t)^2/t=Y_+(T)^2/T\).

For early times let \(M_*=\max_j|\xi_j|\). If \(y\ge1\) the complete product energy obeys
\[
 \sum_n |b_n(y)|^2
 \le M_*^4\sum_{(r,s)=1,\,r,s\le y}
        \left\lfloor \frac{y}{\max(r,s)}\right\rfloor^2
 \le 2M_*^4 y^2(1+\log y).
\]
Here \(a/c=r/s=d/b'\) parametrizes \(ab'=cd\) with two free common factors. There are at most \(2h\) ordered reduced pairs of maximum \(h\). Also \(\sum |b_n(y)|/\sqrt n\le4M_*^2y\). The polynomial vanishes for \(y<1\). Using the unrestricted integer Hilbert constant \(\pi\), the early range increases \(F\) in the preceding formula by at most
\[
 \frac{t_e}{e^U}M_*^4\,[2\pi(1+\log (b/\eta))+16(.118)] .
\]
The replay checks \(t_e<e^U\).

## Average of the actual upper endpoint and diagonal

At \(T\) let \(Y_0=Y_+(e^U)\). Every sharp length is at least \(\eta Y_0\). Bound its \(F\) by \(F(\ell,\eta Y_0)\) and retain the actual square of the cutoff in front. Its averaged ratio to \(Y_+(T)^2\) is \((1-\eta^2)/(4w)\).

For the exact diagonal, let \(D(v)\) be the published degree-four polynomial envelope at length \(e^v\), applicable once that length exceeds \(Z^2\). When \(Y_-(t)\ge Z^2\) the averaged envelope is
\[
 \frac1{2w}\int_0^{2w}D(\ell_t-r)\,dr
  =\sum_{j=0}^4 D^{(j)}(\ell_t)\frac{(-2w)^j}{(j+1)!},
 \qquad \ell_t=\log Y_+(t).
\]
The early cutoff in the time antiderivative therefore moves to \(t_*=2\pi Z^4 e^{4w}/\sigma^2\). Below this cutoff, \(Y_+(t)\le e^{2w}Z^2\), so the elementary harmonic majorant is \(M_*^4(1+2\log Z+2w)^4\). The integral of the absolute continued polynomial over that short interval is restored using the same coefficientwise bound as in the published diagonal proof.

These changes only affect the two individual fourth-power estimates. The mixed-product bound, rational and short-product covariance, the disjoint initial interval and the AFE error retain all their previous terms. The verifier covers the first unit by three adjacent slabs, then adds unit slabs until the known rational half-line with \(\alpha=1,w=.04\) takes over or its fixed fallback is reached. At that fallback the maximum explicitly includes the complete tail.

~~~powershell
python -B round8/critical/sweep_boundary.py
~~~

2026-11-20. Joint project attribution to Claude and Codex. Codex derived the simultaneous moving-boundary and averaged-diagonal estimates.
