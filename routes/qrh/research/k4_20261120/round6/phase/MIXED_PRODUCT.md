# The forward–dual product and residue-dependent shift counts

Write \(A_u,B_u\) for the paired AFE polynomials in [the phase proof](SMOOTH_PHASE.md). The direct mixed estimate below bounds \(Z=\int\!\mathbb E_u|A_u B_u|^2\,dt/(T\log^4T)\). If \(f,d,h\) denote the two normalized fourth moments and the normalized absolute fourth harmonic, the paired fourth-root main term is then at most
\[
 \left[\sqrt{f+d+2Z}+\sqrt{2(Z+h)}\right]^{1/2}.
\]
This follows by the same \(L^2\) expansion as in the phase proof, now retaining the mixed moment in both squares. Taking \(Z\le\sqrt{fd}\) remains available.

## The arithmetic diagonal

Write \(F,D\) for the two raw cutoffs, let \(Y=\sigma\sqrt{T/(2\pi)}\), and \(\sigma=\sqrt Q\,e^w\max(\alpha,1/\alpha)\) so both are bounded by \(Y\). Before the divisor relaxation, equal products in \(|A_uB_u|^2\) have forward factors \(ir,is\) and dual factors \(js,jr\) with \((r,s)=1\). This forces \(i,r,s\) to be units modulo \(Q\). Hence \(c_Q(js)c_Q(jr)=c_Q(j)^2\), and all remaining inner coefficients are nonnegative. Dropping the further coprimality restriction, and separately extending the true two cutoffs to the common maximal scale, gives an upper cumulative convolution. Its outer measure has cumulative \(H_{\rm unit}(x)^2\), and its inner measure has cumulative \(H_{\rm unit}(x)H_{c_Q^2}(x)\). The positive-measure envelopes, finite moments and antiderivative are those in the [sharp periodic proof](PERIODIC_FOURTH.md). The raw low-time pointwise bound for the diagonal before dividing by \(Q\) is \(\max|c_Q|^2(1+2\log Z_0)^4\) with \(Z_0\) the arithmetic prefix length.

For the same reason the Hilbert upper endpoint uses only unit outer pairs and the inner cumulative \(V_j=N_{\rm unit}(j)\sum_{n\le j}c_Q(n)^2\). All these increments are nonnegative. The exact prefix is summed through \(K\) as in the phase proof. For the remaining \(M=\max(r,s)\le Y/(K+1)\), write \(r_0,d_0\) for the mean and absolute upper discrepancy of the unit count, and \(\mu,D_0\) for the same data of \(c_Q^2\). The product of inner counts, after normalization by \(Y^2\), has upper sum
\[
 r_0\mu\sum M^{-2}
 +(r_0D_0+\mu d_0)Y^{-1}\sum M^{-1}
 +d_0D_0Y^{-2}N_{\rm unit}(Y/(K+1))^2.
\]
These three outer sums have the same bounds as before. Use unit spacing \(g=1\) for the mixed product frequencies in the upper Hilbert endpoint. The normalization of the mixed raw product square is \(1/Q\).

## Averaging the mixed time cutoff

For a quadruple let \(M_f\) be the maximum of its two forward indices and \(M_d\) the maximum of its two dual indices. At time \(t\) the permitted \(u\)'s form the interval obtained by intersecting \([-w,w]\) with
\[
 \left[\log\{M_f/(a\sqrt{t/(2\pi)})\},
       \log\{b\sqrt{t/(2\pi)}/M_d\}\right] .
\]
Its normalized length increases in \(\log t\); its derivative is the sum of at most two terms \(1/(4wt)\) supported on intervals. The lower support satisfies \(t\ge 2\pi M_fM_d/(Qe^{2w})\). Thus the residual shift factor is bounded by \(\min(1,J/h)\) for \(J=Qe^{2w}/(2\pi w)\), where \(h\) is the physical integer difference of the products. The .118 kernel contribution now involves the product of the two squared coefficient mean bounds. Fix one forward index in one product and one dual index in the other; then the inner sequences are the absolute dual and the unit indicator. This gives the two unequal periodic row weights for the orbit scan.

## Constraints from the two fixed residue classes

This improvement is used for both individual fourth moments and for the mixed moment. Write \(a,c\) for fixed outer indices, \(G=(a,c)\), \(P=a/G,S=c/G\). For \(p\mid Q\) with \(p\nmid\gcd(a,c,Q)\), reduction modulo \(p\) gives
\[
 [P:S]=[a:c]\ \text{ in }\mathbb P^1(\mathbb F_p).
\]
If \(p\mid\gcd(a,c,Q)\), either projective coordinate is possible. For each tuple of projective coordinates over all \(p\mid Q\), the code bounds the weighted harmonic discrepancy \(D_J=\sum d_j b_j\) and row-mean sum \(R_J=\sum r_j b_j\) over precisely the primitive triples with those coordinates. Sign reversal of both \(P,S\) preserves the line, and evenness of both raw weights at the reflected pair preserves the interval discrepancy and its mean. Thus the scan may use \(0\le P\le Q/2\), with all \(S\bmod Q\), for unequal periodic weights as well. The coding uses slope \(S/P\) when \(P\ne0\bmod p\), and the extra projective coordinate when \(P=0\bmod p\).

For each fixed pair of outer classes \(a,c\bmod Q\) let \(\overline D(a,c)\), \(\overline R(a,c)\) be the maximum over the compatible extensions. In the discrepancy term \(G^{-1}\le1/\gcd(a,c,Q)\). Each residue pair has at most \((Y/Q+1)^2\) lattice points. The signed inverse-distance term sums \(Y/\max(a,c)\) on each pair with the universal square-expansion bound from the sharp periodic proof. It follows that the quantity \(FD_J+SR_J\) in the residual can be replaced by
\[
 (1+Q/Y_0)^2 Q^{-2}\sum_{a,c\bmod Q}
 \frac{\tau_1(a)\tau_2(c)\overline D(a,c)}{\gcd(a,c,Q)}
 +
 \left[2+\frac{4Q(1+\log Y_0)+4Q^2}{Y_0}\right] Q^{-2}
 \sum_{a,c\bmod Q}\tau_1(a)\tau_2(c)\overline R(a,c).
\]
Here \(\tau_1,\tau_2\) are the fixed outer absolute weights, and the two inner weights come from the complementary factors. All residue and discrepancy accumulators are exact integers before the final Arb division, with the same explicit overflow check as in the previous scan.

At \(U=37,Q=210,\alpha=1,w=.04,Z_0=384\), **projected_fourth** in [mixed_product.py](mixed_product.py) gives a normalized fourth-moment coefficient below \(0.001132901\), while the paired disjoint estimate with uniform shift maxima gives \(0.001243571\). Reproduce in this directory with

~~~powershell
python -B -c "from mixed_product import projected_fourth; from flint import arb,ctx; ctx.prec=160; print(projected_fourth(arb(37),210,arb(1),arb('.04'),384))"
~~~
