# Integrating the prime-count tangents on positive exterior lobes

For every real \(x\) with \(115.033338\leq \log x\leq115.033660\), the interval \((x,x+4x^{3/4})\) contains a prime, using published finite-height RH and the elementary Farey sieve. Assuming QRH(7/8), the upper endpoint can be replaced by \(115.033663\). At \(x=n^4\), these upper endpoints give \(n=3,087,599,363,886\) and \(3,087,601,679,586\), respectively. The result connects with the [previous cover](../../round4/low/CORRELATED_FAREY.md). The interval computations use [192-bit Arb](physical_tail.py).

Retain all analytic terms and the two far arithmetic regions from the [finite-height edge proof](../../round2/local/EDGE.md). Retain its \(Q=10^4\), \(r=10^{-6}\), \(a=(1-10^{-12})K d(h)\), \(I=\pi\sin(a)/a\), the normalized sieve coefficients \(C_1(s,r),C_2(s,r)\), and \(g(u)=(\cos a-\cos u)/(u^2-a^2)\). The sieve addition \(\eta=1.1328\) holds for interval lengths \(y\geq e^{70}\) by the [correlated Farey argument](../../round4/low/CORRELATED_FAREY.md). For \(y< e^{70}\), enclose the interval in one of length \(e^{70}\). Every tangent used here has arithmetic intercept greater than \(2e^{70}/(70+\eta)+1\), by checking its lower bound \(2 e^l s_{\min}/(120^2 K)\), where \(s_{\min}=2(\pi-a)/16384\) and \(\log(e^c s/K)+\eta<120\). This also handles a closed endpoint by taking the limit from outside. Tangent coefficients decrease with \(c\) by the inequalities from the edge proof.

On each first positive exterior lobe apply the existing exact-area adjustment, now dividing its width \(b=2(\pi-a)\) into 8192 parts. For a pair of successive widths \(w_0,w_1\) and height difference \(\Delta\), charge twice
\[
 \Delta\left[C_2(s,r)+\max_{w=w_0,w_1}(C_1(s,r)-C_1(1.55,r))w\right],
 \qquad s=(w_0+w_1)/2.
\]
The update subtracts the old 256-part expression and adds the new one. A replacement is valid because the old expression occurs explicitly in the running upper bound. The total positive exterior area charged at the original reference slope remains exact.

For each secondary lobe \(j=1,\ldots,64\), set \(u_*=2\pi j+a\) and divide \([u_*,u_*+b]\) into 256 equal cells \([u_k,u_{k+1}]\). The positive numerator increases up to the midpoint of the lobe and decreases afterwards. It is bounded in each cell by its value at the endpoint closer to the midpoint. Divide this value by \(u_k^2-a^2\) to obtain \(V_k\), an upper bound for \(g\) on the cell. Because \(g\) is log-concave on the open lobe, \(v_k=\min(g(u_k),g(u_{k+1}))\) is a lower bound. The exact endpoint values vanish. Replace the old verified peak upper bound by \(\max_k V_k\) in the reference intercept charge. All these complete lobes are in \(|u|<Kr\). On lobes \(j>64\) retain the previous estimate, including the whole remaining tail.

Put \(m=g(u_*+b/2)\) and divide the levels \([0,m]\) into 128 equal intervals \([z_0,z_1]\). For any level inside one of these intervals, its angular superlevel width belongs to \([w_-,w_+]\), where
\[
 w_-=(b/256)\#\{k:v_k>z_1\},\qquad
 w_+=(b/256)\#\{k:V_k\geq z_0\}.
\]
For the upper count, the implementation retains every cell not provably below \(z_0\) in interval arithmetic. Log concavity makes each positive superlevel connected, so each candidate tangent counts the primes in one interval. Write \(C_i^0=C_i(1.55,r)\). For any \(s>0\) used in the program, the reduction from the reference charge is at least
\[
 \max\left(0,C_2^0-C_2(s,r)+
             \min_{w=w_-,w_+}(C_1^0-C_1(s,r))w\right).
\]
Indeed one can select the better of the reference tangent and this tangent for that level. The program takes the maximum over up to three scales \(s=ib/40\), \(1\leq i\le39\). A floating-point index only chooses their locations. The inequalities for every selected scale use Arb. Integrate the reduction over the level band and count its reflection. The part above \(m\) retains the reference charge. At the first new slab, the saved normalized costs from the first lobe, the secondary peaks, and the secondary level integration are respectively about \(3.3851\cdot10^{-5},3.3815\cdot10^{-5},6.1385\cdot10^{-5}\).

| Lower \(L\) | Upper \(L\) | \(K-H\) | Certified upper bound |
|---:|---:|---:|---:|
| 115.033338 | 115.033646 | −1280000 | 0.999994201 |
| 115.033646 | 115.033660 | −1280000 | 0.999998984 |
| 115.033660 | 115.033663 | 300000 | 0.999999387 |

The negative frequency shifts put the Gaussian high-zero tail under an unconditional count. For the positive shift the edge proof also uses QRH(7/8). The subscripts \(l,h\) in each row give uniform comparisons throughout the closed slab. This is a handwritten analytic argument with a scalar interval certificate.
