# A single remaining signed phase band at L=116

Fix \(x=e^{116}, K=H=3000175332800,\ Q=210,\ z=1732099\sqrt{x/H},\ r=10^{-6},\ c=116+\tfrac12\log(1+4e^{-29}),\ X=e^{c+2r}\), and put \(q_0=X/23,\ Y=e^{70.7}\). The proof of the prime-interval inequality at this one location reduces to the following sufficient condition, with only the previously stated QRH and finite verifications in the other terms:
\[
 \boxed{\quad
  \frac{2P_0}{Q}\Re
  \sum_{Y<q\le q_0}\frac{B_z(q)}q
  \sum_{\substack{n\ge1\\1<nX/(Qq)\le 9200000000000000000/21}}
      c_Q(n)\int_{\mathbb R} F(t)e^{2\pi i nt/(Qq)}\,dt
       <.00236860 .\quad}                                             \tag{1}
\]
This signed condition remains open. The lower endpoints in both inequalities are excluded and both upper endpoints are included. Here \(B_z(q)=\sum_{[d,e]=q,(de,Q)=1}\lambda_d\lambda_e\) uses the physical presieved Selberg coefficients; \(c_Q(n)=\mu(Q/(n,Q))\varphi((n,Q))\). Put \(a=(1-10^{-12})K(c-116),\ I=\pi\sin(a)/a\), and \(P_0=(c+2r)e^r K e^{-c}/I\). These constants correspond to the physical variable \(t\), not its logarithm.

**Weight in (1).** Start with \(W(t)=(g_a(u))_+\,{\bf1}_{a\le |u|\le Kr}\) for \(t>0,\ u=K\log(t/e^c),\ g_a(u)=(\cos a-\cos u)/(u^2-a^2)\); set \(W=0\) for \(t\le0\). Define it at boundaries by its upper limiting value. Let \(\delta=.0002\,x/K,\ F_*(t)=\sup_{|h|\le\delta}W(t+h)\). Convolve \(F_*\) with 64 uniform probability densities on \([-\delta/64,\delta/64]\) to form \(F\). The resulting \(F\) majorizes \(W\) pointwise and lies in \(e^{c-2r}<t<X\). The pole, zero terms and estimates for \(r<|\log(t/e^c)|\) in the original explicit formula remain valid; the enlargement occurs only in the positive prime upper bound. Fourier inversion for this compactly supported continuous weight is absolutely convergent at each fixed modulus.

| Paid term at this location | Upper bound |
|---|---:|
| Original ordinary main term | .983484173844 |
| Other prior analytic and remote terms | .000001755341 |
| Added ordinary main term from dilation | .000282039356 |
| Entire \(q>X/23\) prefix, before multiplying the area increment | .012935847025 |
| All \(nX/(Qq)\le1,\ q\le X/23\), before the same increment | .000920899685 |
| Entire high diagonal \(nX/(Qq)>9200000000000000000/21,\ q\le X/23\) | \(2.030\,10^{-13}\) |
| All nonzero modes at \(q\le e^{70.7}\) | .000002791 |

The multiplier for the two area-increment rows is at most \(1.000280562\). The actual remaining positive allowance in the computation is .00236860633774. The small-\(q\) and low-phase regions are disjoint because \(X/(QY)>1\). The high-phase absolute bound may be restricted to \(q>Y\).

**Physical area and Poisson bounds.** The total original outer area in the \(u\) variable is at most \(A=I(1-a/\pi)\), and the sum of the peaks of its monotone lobes is at most \(S=\sin(a)/a+(1+\cos a)/12\), counting both directions. In the \(t\) variable, dilation adds at most \(2\delta S\) of area, by integrating the added lengths of superlevel intervals. Convolution preserves area. Each translate of a dilated superlevel set can be covered by the individually translated dilated intervals of the original lobes. Consequently the previous area-plus-intercept estimates apply with the area increment \(1+2\delta S/(XA/K)\) and their old summed peaks. The same holds for the \(q>X/23\) estimate from [the presieved prefix calculation](PRESIEVED_PREFIX.md). In using an upper count on a union of possibly overlapping intervals, split the union into disjoint components first when retaining a signed correction; the number of components never increases. The extra ordinary term is \(P_0(2\delta S)\eta/G_-\), where \(\eta=\varphi(Q)/Q,\ G_-=\eta(\log z+1.331)\).

Writing \(\widehat F(\xi)=\int F(t)e^{2\pi i\xi t}dt\), the probability convolutions give
\[
 |\widehat F(\xi)|\le\left(XA/K+2\delta S\right)
                 \min\left(1,\frac{64}{2\pi\delta|\xi|}\right)^{64}.
\]
For a unit-sieve modulus \(q\), Poisson summation on the reduced residue classes modulo \(Q\) gives main \(\eta\,\widehat F(0)/q\) and nonzero terms \(2\Re\sum_{n\ge1}c_Q(n)\widehat F(n/(Qq))/(Qq)\). Denote \(m=64,\ J=4\cdot10^{18},\ C_*=J/q_0\). The absolute Ramanujan weight has period \(Q\) and mean \(v=2^{\omega(Q)}\eta\), since at each prime its absolute value is \(1\) off the zero class and \(p-1\) on it. Any interval of length \(y\) has absolute weight at most \(v(y+Q)\), so
\[
 \sum_{n>s}|c_Q(n)|n^{-m}\le v(s^{1-m}/(m-1)+Qs^{-m})\quad(s>0).
\]
Use \(s=C_*q\). The positive moments needed after summation are \(\sum_{q\le q_0}|B_z(q)|\le(z K_0/G_-)^2\), where \(K_0\) is the [ordinary absolute Selberg coefficient bound](../../round7/physical/extras/weight_energy.py), and \(\sum_{q\le q_0}|B_z(q)|/q\le(1+\log q_0)^3\). The latter follows from \(|\lambda_d|\le1\) and \(|B_z(q)|\le d_3(q)\) on squarefree \(q\), then expanding the ternary divisor function. Likewise \(\sum_{q\le Y} d_3(q)\le Y(1+\log Y)^2\) for the tiny-modulus estimate, for which all \(n\ge1\) are covered using \(\varphi(Q)\zeta(m)\).

**Low-frequency curved sums.** Let \(D(t)=\sum_{q>t}B_z(q)/q\). The [signed inverse estimates](PRESIEVED_EMPTY.md) bound \(|D(t)|\) after the scalar \(\eta\) from that earlier code is removed. A uniform bound for every \(t\ge X/u\) comes from applying the one-sided curved rectangle estimate on *all* potentially contributing rectangles in \(q>X/u\). Its fixed-row one-variable Abel bound holds even when a cell is whole. For a single \(n\) in the low phase, summing over \(Xn/Q\le q\le X/23\) uses the two endpoint \(D\)-bounds and
\[
 \frac{2\pi n}{Q}\int_{23}^{Q/n}\sup_{t\ge X/u}|D(t)|\,du .
\]
This is partial summation of \(e^{2\pi int/(Qq)}\) in \(q\), uniformly for real physical \(t\le X\). The endpoint \(Xn/Q\) is noninteger in the implementation sense unnecessary for the bound: taking the one-sided limit of the same estimates also covers a possible equality. The ratio of consecutive numerical integration points is at most \(23/20\); each increment uses the right-endpoint uniform majorant. Multiply by \(2|c_Q(n)|/Q\), sum at most nine modes, then multiply by the mass bound for \(P_0F\). The optional mean Mertens table is used in this one-dimensional inverse estimate.

~~~powershell
python -B round8/physical_low/remaining_phase.py
python -B round8/physical_low/phase_window.py --phase 1 --upper .000920900
python -B round8/physical_low/compact_spline.py --tiny 70.7 --upper 2.03e-13
~~~
