# A compact ordinate rectangle for every remaining fourth-power gap

Assume the analytic hypotheses in the [round-four Euler detector](../../round4/euler/PROOF.md), including QRH(7/8). Set \(H=3\,000\,175\,332\,800\), the verified Riemann-hypothesis height. An integer \(n\) for which \((n^4,(n+1)^4)\) is prime-free would require **at least 62,001** nontrivial zeros, counted with multiplicity, satisfying
\[
 .8<\beta\le7/8,\qquad H<\gamma\le 13\,044\,374\,116\,075\,977\,902.
\]
For a counterexample with \(L=4\log n\le123\), the same count is necessary below **25,451,176,504,948**. Compared with the [previous \(\beta>.8\) first rectangle](../../round3/low/FIRST_BOX.md), the ordinate ceiling is more than 458 times smaller and the required count increases from 51,327. The [earlier compact-height alternative](../../round4/low/NEAR_HEIGHT.md) admitted the wider strip \(\beta>.72\).

In the short interval \(115.033340<L\le115.050\), a counterexample would satisfy **all three** conditions below.

| Strict lower edge for \(\beta\) | Upper ordinate, with lower endpoint \(H\) excluded | Required count |
|---:|---:|---:|
| .80 | 3,024,178,015,463 | 75,001 |
| .81 | 3,150,185,379,441 | 230,001 |
| .82 | 3,150,185,379,441 | 19,001 |

The result localizes an additional zero-count input that would rule out counterexamples. No upper bound on the actual population of these rectangles is asserted. The short-interval rows reach the previously identified [bandwidth obstruction](../../round4/low/DUAL.md) by using frequencies *above* \(H\).

## Signed spectrum and cumulative integration

On a fixed cell \(l\le L\le h\), put \(d=\frac12\log(1+4e^{-h/4}),\ Q=10^4,\ K>H,\ a=(1-10^{-12})Kd,\ I=\pi\sin(a)/a\). Use the signed Gaussian-smoothed test and its explicit formula from the [finite-height proof](../../round2/local/EDGE.md). The pole-normalized cost \(B\) of the prime side, pole and archimedean errors and all ordinates \(\le H\) is its scalar budget with the high-zero term removed. Require \(0<a<\pi\). The [published-input sieve](../../round3/low/FAREY.md) with \(\eta=1.090\) suffices here. The smallest tangent scale is at least \(1/1024\), as checked in each cell, all scales are at most 7 and \(\log(7e^c/K)+\eta<140\) in all the cells used here (checked below). The tangent intercept satisfies \(2e^l/(1024K\cdot140^2)>e^{50}+1\) throughout each cell, so its use for lengths below \(e^{50}\) follows from integer counting. [Base formula and Gaussian tail](../../lower/PROOF.md).

For an unsmoothed zero of real angular frequency \(t\), the ratio of the spectrum to \(I/K\) is \(\sin(a(1-|t|/K))/\sin a\) on \([-K,K]\), and zero outside. For every real \(t\) its numerator is majorized by the nonincreasing envelope
\[
 D(t)=\sin\left(\min\{\pi/2,\ a(1-t/K)_+\}\right).
\]
Both the actual numerator and \(D\) are bounded by 1. The latter has Lipschitz constant \(a/K\). If \(X\) is centered Gaussian of variance \(2Q^2\), then \(\mathbb E D(\gamma-X)\le D(\gamma)+2aQ/(\sqrt\pi K)\). Taking modulus in the same complex Gaussian convolution as the base argument costs at most \(e^{1/(16Q^2)}\). Thus the spectrum at \(\gamma-i(\beta-\tfrac12)\), in units \(I/K\), is bounded by \(e^{1/(16Q^2)}C(\gamma)\) where
\[
 C(t)=\frac{\min\{1,D(t)+2aQ/(\sqrt\pi K)\}}{\sin a}.
 \tag{1}
\]
This captures the sine instead of using its full triangular majorant. For all zeros with \(\gamma>T_1=K+128Q\), the Gaussian tail using \(N(t)\le t^2\) contributes \(E_\infty<10^{-1700}\) in each cell, for every \(0<\beta<1\), exactly as in the [earlier compact-height proof](../../round4/low/NEAR_HEIGHT.md).

Divide \([H,T_1]\) into 32 equal subintervals with endpoints \(t_0,\ldots,t_{32}\). Write \(C_j=C(t_j)\) for \(0\le j<32\) and assign \(C_{32}=0\). Each ordinate in \((t_j,t_{j+1}]\) has cap \(C_j\). For a cutoff \(\theta\le7/8\) let \(F_\theta(T)\) majorize
\[
 \sum_{\substack{H<\gamma\le T\\\beta\le\theta}}e^{-(1-\beta)l}.
\]
The pair of conjugates at \(\pm\gamma\) contributes the cosine majorant \(e^{-(1-\beta)c}+e^{-\beta c}\). Reflection \(\beta\leftrightarrow1-\beta\) permutes all positive ordinates at their original heights, with multiplicities. Since (1) is independent of the real part, replacing \(c\ge l\) by \(l\) expresses the bound on the complete sum as twice the positive-ordinate sum of \(e^{-(1-\beta)l}\). Take the \(\theta\) cutoff *after* making this symmetry reduction. Summation of the nonnegative staircase, including its final endpoint mass, gives the total normalized cost
\[
 B+E_\infty+
 2e^{1/(16Q^2)}\sum_{j=0}^{31}(C_j-C_{j+1})F_\theta(t_{j+1})
 +2e^{1/(16Q^2)}C_0 e^{-l/8}\,Z_\theta(T_1),                     \tag{2}
\]
where \(Z_\theta\) counts the right zeros \(\theta<\beta\le7/8\), with \(H<\gamma\le T_1\). The final term could also use the sum of weights \(e^{-(7/8-\beta)l}C(\gamma)/C_0\) instead of the count. Formula (2) is a sufficient upper budget; any value strictly below 1 forces a prime in the open interval.

## Modulus-210 hinge at each ordinate

Apply the [Euler detector](../../round4/euler/PROOF.md) at the *actual* integration height \(T\), with frozen constants computed for \(U=28.7,\ \delta=.86,\ W=9,\ \log h_0=-3.3,\ Q_{\rm sieve}=m=210\). Use the density mode of the folded matrix and the direct high norm with the variance comparison. The low norm here only needs the variance bound. The [folded mean-value theorem](../../round4/hilbert/FOLDED.md) applies uniformly for all the heights in each integral. The resulting \(K_1,K_3,\mathcal N\) bound the two boundary moments and the analytic-window normalization. All heights \(T\ge H>e^U\) satisfy the hypotheses.

At \(u=\log T\) and a horizontal node \(s\), use the exact detector parameters
\[
  \nu=\frac{2+4\delta/u}{2-s+3\delta/u},\qquad
  P=\frac{3(1-s)+3\delta/u}{2-s+3\delta/u}.
\]
The Euler-detector interpolation and its Littlewood rectangle bound
\(\Lambda_s(T)=\sum_{0<\gamma\le T}(\beta-s)_+\) by
\[
 \frac{c_\nu\mathcal N^\nu}{2\pi}
       (TK_1u^2)^P(K_3u)^{1-P}+E_0+\frac{27u}{\log(15/14)},       \tag{3}
\]
where
\[
 E_0=\frac{162h_0^{-1}}{2\pi}
 +2\left(2+\frac{\log 2+9\log(11\sqrt{210h_0e^W})}{\log(15/14)}\right).
\]
For \(c_\nu\) the code uses the certified detector coefficient covering the whole range of \(\nu\) at that node and the additional quintic option when certified. Thus it can be reused for every \(T\) in the ordinate staircase. The exact \(P,\nu\) still vary with each height. [Derivation of the interpolation and hinge inequality](../../round2/spectrum/PROOF.md).

Upper-bound \(e^{(\beta-1)l}\) for \(\beta\le\theta\) by its convex chord interpolant between \(0.650,0.652,\ldots\) and the final endpoint \(\theta\), leaving the last segment at least \(0.014\). Below \(0.650\) use the constant \(e^{-.35l}\). Write the interpolant as this base plus the consecutive positive differences of chord slopes times \((\beta-s)_+\). Bounding each hinge by (3) for *all* positive ordinates can only increase the result. All zeros below \(H\) are on the critical line and hence contribute no hinges. For the base count use the smaller of \(T\log T\) and the fixed-endpoint estimate
\[
 (.3\log H+6)+\left(\frac{\log(H/(2\pi))}{2\pi}+\frac{.15}{H}\right)(T-H)
 +\frac{(T-H)^2}{4\pi H}.
\]
This bounds \(N(T)-N(H)\) by [the local Riemann–von Mangoldt argument](../../round2/local/EDGE.md). Their sum with the hinge terms gives the \(F_\theta(T)\) in (2).

## Coverage and checks

On \([115.03334,123]\) use cells of length \(1/8\), starting the first cell at \(115.03334\). On \([123,176]\) use unit cells. For each cell the verifier chooses the first \(A_0\) in
\[
 2.03,\ 2.1,\ 2.2,\ 2.25,\ 2.3,\ 2.4,\ 2.45,\ 2.5,\ 2.55
\]
such that \(Kd=A_0\) and (2) is strictly below 1 when \(Z_{.8}(T_1)=62000\). Each cell has a passing option. The maximum of the rounded upper ordinates encountered is shown below at selected endpoints.

| All cells through \(L=\) | Cumulative upper ordinate |
|---:|---:|
| 116 | 4,521,035,721,718 |
| 117 | 6,309,917,728,789 |
| 120 | 12,429,224,868,563 |
| 123 | 25,451,176,504,948 |
| 140 | 1,665,314,126,209,105 |
| 160 | 238,916,045,840,855,288 |
| 176 | 13,044,374,116,075,977,902 |

For the three separate tests through \(115.05\), use the single cell \([115.03334,115.05]\). Take \(K/H=1.008\) with \(\theta=.80\), and \(K/H=1.05\) with \(\theta=.81,.82\). The unrounded allowable counts from (2) exceed \(76027.62,\ 234224.18,\ 20010.96\), respectively. The table near the top uses conservative integer roundings. All rectangles can use closed upper ordinates rounded upwards.

For \(L\le115.03334\) use the [correlated-neighbor sieve result](../../round4/low/CORRELATED_FAREY.md). For \(L\ge176\) use the [remote half-line theorem](../../round4/euler/PROOF.md). Since \((n^4,n^4+4n^3)\subset(n^4,(n+1)^4)\), the stated necessary conditions follow for the fourth-power problem. Reproduce with \(\texttt{python -B short_box.py}\) using 192-bit Arb. The evidence is a written conditional argument and interval-arithmetic checks; it has no independent Lean formalization. Project attribution to Claude and Codex. Codex derived the compact spectral transfer.
