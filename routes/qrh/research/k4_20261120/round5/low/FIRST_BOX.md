# The first geometric-height rectangle

The lower height is \(H=3000175332800\), the upper endpoint is \(W=H e^{1/4}\), and \(\Delta=W-H\). Finite-height RH makes the interval count \(N_{>s}(W)-N_{>s}(H)\) equal to the cumulative count for these abscissae. At this height the sufficient target tested here is \(6(\log W)W^{3(1-s)/(3s-1)}\). [Finite-height reduction](../spectrum/DENSITY_TARGET.md)

**Two positive estimates for the actual count.** The [replay script](first_box.py) uses both the cumulative fixed-height interpolation and the genuinely centered short-interval interpolation. For the cumulative estimate it calls the same five certified boundary choices from the [same-height comparison](FINITE_POINTS.md), with the exact logarithmic height \(\log W=\log H+1/4\). For the centered estimate take \(C=(H+W)/2,\ R=\Delta/2,\ U=\log R\) and replace the critical-line fourth moment by the smaller of the interval's [frozen estimate](FROZEN_FOURTH.md) and the global [sieved fourth-moment](../left/PROOF.md) averaged over the centered rational window. The latter averaging is explicitly given in [the centered-window proof](MOVING_WINDOW.md). The remaining critical mollifier uses the sharper harmonic/arithmetic norm from the [fifth-round mean calculation](../spectrum/PROOF.md), computed at scale \(R\). The right norm uses the single cell containing the fixed exponent. Both Dirichlet mean estimates are invariant under translation of the integration center: translating multiplies each coefficient by a phase, and the bounds use its absolute square. Use the full-axis to half-axis factor of 2 only for the centered interpolation; the cumulative prescription uses its usual evenness. The taper, pole correction, right-side divisor tail, radial detector and both horizontal Jensen integrals are retained as in the named proofs. This gives valid upper bounds, with a gap still present at the first full geometric height.

**An independent obstruction for a direct Selberg/AFE proposal.** Consider the displayed local inequality in [rStation 168, Theorem 1, v1](https://rstation.ai/problems/riemann_hypothesis/papers/168), irrespective of the status of its proof. One can drop *all* of its remainder and horizontal-edge costs and already prove the resulting numerical output too large, uniformly for every legal \(X,x,\sigma'\). The two terms retained are its centered Selberg head \(A_\Delta\) and its dual AFE norm \(B_\Delta\). This is a restriction on the formula as printed, not a claim about the actual zeta zeros or a lower bound on the true moments.

Write \(b=2\sigma-1,\ a=2\sigma'-1\), with \(0<a<b\). On each of 768 equal cells \(l\leq a\leq u\), the possible distance satisfies \(\sigma-\sigma'\leq (b-l)/2\). Since \(a\zeta(1+a)\leq1+a\), the Selberg head obeys
\[
 A_\Delta\geq P X^{-u},\qquad P=1/(1+u).
\]
It follows already that \(V_\Delta\geq P(2\pi/H)^u\). If \(l>0\), the source's \(D\geq1,\ D/\zeta(1+a)\geq l/(1+l)\) give
\[
 J_{\rm maj}\geq J_0=\min\left\{2.8265\cdot1.9436(1+\log 8)
               (l/(1+l))^2,\ 1.9436,\ 5.5l/(1+l)\right\}.
\]
Because \(8\leq X\leq x\leq H/(2\pi)\), its \(K_\Delta\) is at least \(k_0=1+\log(36W/H)\); also \((xH/W)^{-a}\geq(2\pi/H)^u\). The explicit frequency spacing cost in the dual term alone gives
\[
 B_\Delta\geq Q X^2,\qquad Q=(J_0/u)(2\pi/H)^u\,4Wk_0/(H\Delta).
\]
Here \(xH/W\) might be below 1, in which case this last lower comparison remains immediate. Writing \(p=2/(2+u),\,q=u/(2+u)\), minimizing the sum of the square roots over **all** \(X>0\) gives
\[
 V_\Delta\geq(\sqrt{P}\,X^{-u/2}+\sqrt{Q}\,X)^2
      \geq P^p Q^q p^{-2p}q^{-2q}.
\]
This last inequality follows directly from weighted AM–GM on the two terms divided by their weights. For \(l=0\) keep the head bound alone. Each cell now gives its own lower bound on \(\Delta\log(1+V_\Delta)/(2\pi(\sigma-\sigma'))\), and the program takes the smallest over all cells. In particular at .850 the head and dual-activation costs force the proposed output above \(519,398,092\) while the target is below \(783,726\). Changing the two AFE remainders alone cannot fix that discrepancy.

~~~sh
python -B round5/low/first_box.py
~~~

The table lists conservative outward roundings. Each entry in the count column is attained or improved by a parameter choice in the script. The final column is a lower bound on the output of the separate Selberg/AFE expression after removing its remainders and rectangle edges.

| \(\sigma\) | Target, rounded up | Upper bound on the actual count | Ratio of upper bound to target, rounded up | Selberg/AFE expression divided by target |
|---:|---:|---:|---:|---:|
| .800 | 43,065,067 | 613,924,533 | 14.26 | >71.37 |
| .820 | 7,856,651 | 168,353,299 | 21.43 | >194.28 |
| .837 | 2,057,409 | 54,261,468 | 26.38 | >404.26 |
| .850 | 783,726 | 22,377,974 | 28.56 | >662.72 |
| .852 | 678,490 | 19,497,412 | 28.74 | >711.67 |
| .865 | 272,893 | 7,699,092 | 28.22 | >1098.12 |
| .874 | 149,037 | 4,009,425 | 26.91 | >1440.80 |
