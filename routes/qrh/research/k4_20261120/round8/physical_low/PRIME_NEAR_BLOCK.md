# Paying the complementary near-unit semiprimes and the full upper-modulus prefix

Use \(P_q,{\cal S},Q,Y,\kappa_*,X,X_-\) from [the true negative phase block](PRIME_GAP_BLOCK.md). With its refined 640-bin frequency and prime count, \(\sum_{q\in{\cal S}}P_q<-.02330281\). The following are three separate sufficient tasks at \(L=116\). In each row it is enough that the four-sided signed sum **outside both** \({\cal S}\) and the listed semiprimes, over every \(Y<q\le X/m,\ 2<hX/(Qq)\le2.5\cdot10^{17}\), is below the given last number. All moduli \(q>X/m\) have already been fully included by the physical and inverse estimates, irrespective of their factorization. All moduli \(q\le Y=e^{75}\) have also already been included.

| \(m\) | All semiprimes removed at the additional \(w=e^c/q\) | Near-unit cost at most | Remaining sufficient allowance |
|---:|---|---:|---:|
|200|\(2500\le w\le10^6\)|.023283080|.00005879|
|700|\(2500\le w\le11000\)|.003100120|.00414903|
|1000|\(2500\le w\le3500\)|.000596132|.00059747|

The three statements concern the same location and each gives a different estimate of its complement. The complement in each row remains open.

## Upper bound for the physical cost without a gap restriction

Throughout \(w\ge2500\) and \(B_Q(q)>0\), the main term \(\eta P_0\int F\) dominates the absolute price of removing the low and high frequencies. This is the two-turn Ramanujan and high-tail estimate in the preceding proof, with the nonnegative physical term omitted during this comparison. Consequently \(P_q\le B_Q(q)P_0\sum_{(k,Q)=1}F(kq)\) even for a multiplier \(k\) arbitrarily close to the target center.

For each tested range \(A\le w\le B\), sum over *all* positive unit \(Ae^{-2r}\le k\le Be^{2r}\), with the outer integer endpoints enlarged. Fix \(k_0<k\le k_1\) and an outer prime \(p\) in a log bin \((l,h]\). Intersect its lower endpoint with \(X_-/(k_1 z)\), because a supported product \(kpv\) with \(v\le z\) requires this. Every prime factor in the calculation lies above \(p_0=X_-/(k_{\max} z)>5000\). For \(q=pv>z\) with distinct primes its coefficient is \(2|\lambda_p\lambda_v|\). The ordered prime-pair sum accounts for the two. Including \(p=v\) in the positive upper is harmless. There is no coprimality assumption on \(k\) against \(p\) or \(v\).

Let \(N_p,H_p\) be upper bounds on the prime count and reciprocal prime sum in \((l,h]\). With Johnston (3.2), take \(N_p=(h-l+2E(h))/\log l+1,\ H_p=[\log(h/l)+2E(h)/l]/\log l+1/l\). Let \({\cal A}=XA/H+2\delta S_0\) bound \(\int F\), and \(S_0\) be the sum of the original sidelobe peaks. The smooth majorant comes from the supremum dilation followed by averaging over translations. For the dilated function, superlevel sets are finite unions of intervals and the integral of the number of active intervals over level is at most \(S_0\). The final translation average preserves both the estimates of the total interval length and the number charged at each level. Thus use these estimates *before* interchanging the convolution with the prime count. Dilation and translations are in the physical variable, as required for interval lengths \(y/(kp)\).

For an interval of length \(v\ge e^2\), the number of primes is bounded by \(2v/\log v\). For smaller lengths use \(v+1\). Choose \(V_k={\cal A} H_p/(S_0 kN_p)\). The tangent to \(2v/\log v\) at \(V_k\) is an upper on either regime since its intercept \(2V_k/\log^2 V_k>10\) and its slope is positive. A possible closed endpoint in a superlevel can be treated as an open interval enlarged on the left and then taking its decreasing limit. Integrating this affine estimate in level and summing the outer primes gives \(2{\cal A}H_p/(k\log V_k)\), using the two nonnegative tangent coefficients. In a whole \(k\) bin, \(V_k\ge V_{k_1}\), so one common logarithm suffices; the program checks the intercept at \(V_{k_1}>100\).

On this same pair of bins the two Selberg numerators are at most \(G_Q(z/l)G_Q(zk_1 h/X_-)\), besides \([p_0/(p_0-1)]^2\) and the common \(G_-^{-2}\). Sum the actual unit reciprocals \(1/k\) over the integer bin. Sum over all bins and multiply by \(P_0\). This pays the entire positive physical cost of the semiprimes in the selected \(w\)-band, including repeated factors of the *integer multiple* \(kpv\). It therefore covers the semiprimes outside \({\cal S}\); an upper bound here can include the positive physical cost of additional semiprimes already inside \({\cal S}\).

## Combining three disjoint costs

For \(m=200,700,1000\) the full wheel-prefix allowances *before* paying the upper cut at \(\kappa_*\) respectively exceed \(.0001061061590,\,-.0159866082080,\,-.0220421646851\). The fixed upper-tail absolute cost through \(q\le X/200\) is \(<.000067041579\) and also bounds either smaller set. Every member of \({\cal S}\) has \(q\le e^c/2500<X/m\). Therefore the four-sided sum over \({\cal S}\) is still present in each of the three original allowances. Add its verified negative margin, subtract the positive semiprime upper for the complement, and round down to obtain the displayed table. These are bounds on actual modulus sets and complete harmonic bands. Neither the absolute Farey-pair savings nor a different prime wheel supplies any credit here.

~~~powershell
python -B round8/physical_low/prime_gap_block.py --top 10000000000 --grid 640 --spatial-tail --refined --lower .02330281
python -B round8/physical_low/prime_near_block.py --end 1000000 --cells 112 --slabs 64 --upper .023283080
python -B round8/physical_low/prime_near_block.py --end 11000 --upper .003100120
python -B round8/physical_low/prime_near_block.py --end 3500 --upper .000596132
python -B round8/physical_low/wheel_prefix.py --Q 223092870 --cut 700 --harmonic-limit 446185740 --tiny-log 75 --unit-small --ordered-small --selberg-small --fast-low --physical-spectrum --exact-spectrum --signed-prefix --lower=-.0159866082080
python -B round8/physical_low/wheel_prefix.py --Q 223092870 --cut 1000 --harmonic-limit 446185740 --tiny-log 75 --unit-small --ordered-small --selberg-small --fast-low --physical-spectrum --exact-spectrum --signed-prefix --lower=-.0220421646851
python -B round8/physical_low/spectral_tail.py --Q 223092870 --cut 200 --kappa 2.5e17 --upper .000067041579
~~~

2026-11-20. Joint project attribution to Claude and Codex.
